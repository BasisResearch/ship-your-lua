import Lua.Vm.Sim.Kit.Console
import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Arms.Segs.Hwrite
import Lua.Vm.LayoutRt

/-!
# htif.c's `_write` on the console (A0.2, lane F1-6)

`_write(1, buf, n)` (`0x80000ae8`) with the descriptor table initialised
(`fs_ready ≠ 0`, `fds[1].kind = FD_STDOUT`): `getfd`'s bound and kind tests,
then the `htif_putc` loop (`0x80000d2c`) whose `tohost` store is the console
seam (`Kit/Console.lean`, `segSt_putc`), then the epilogue. It returns `n`,
appends the `n` bytes at `buf` to the console, and its one store is the saved
`ra` (`wrMem`).

The lazy `fs_init` is not on this path: on `print`'s path `__smakebuf_r`'s
`_fstat` runs it before the first `_write` (`gen_lua_arms.py` stops).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **A C callee's caller frame**: the callee-saved `s0`–`s11`, which a
callee returns unchanged (`gp` is pinned apart, at its value). -/
structure AbiFrame where
  (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64)

abbrev AbiFrame.pins (f : AbiFrame) : List Pin :=
  [⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x18, f.s2⟩, ⟨Register.x19, f.s3⟩,
   ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩,
   ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩]

/-- The bytes `[buf, buf + n)` of `m`, in order. -/
def bytesAt (m : Mem) (buf n : Nat) : List (BitVec 8) := (List.range n).map fun i => bytesT1 m (buf + i)

theorem bytesAt_succ (m : Mem) (buf n : Nat) :
    bytesAt m buf (n + 1) = bytesAt m buf n ++ [bytesT1 m (buf + n)] := by
  simp [bytesAt, List.range_succ]

/-- `htif_putc`'s command base `0x0101 << 48` (`li a4, 257; slli a4, a4, 48`). -/
abbrev htifBase : BitVec 64 :=
  shift_bits_left ((0#64) + sign_extend (m := 64) (0x101#12)) (Sail.BitVec.extractLsb (0x30#6) 5 0)

/-- The loop's store word is the putchar word of the byte. -/
theorem putc_data (c : BitVec 8) :
    (zero_extend (m := 64) (c : BitVec (8 * 1))) ||| htifBase = putcWord c := by
  rw [BitVec.or_comm]
  have e : htifBase = 0x0101000000000000#64 := by decide
  rw [e]; rfl

/-- The console store's address `auipc a2, 0x5c` + `-1656` is `tohost`. -/
theorem write_tohost :
    ((0x80000d38#64) + sign_extend (m := 64) ((0x0005c#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0x988#12) = BitVec.ofNat 64 tohostAddr := by decide

/-- **htif.c's console store** (`sd a5, -1656(a2)` at `0x80000d3c`). -/
theorem write_putc {L : List Pin} {m : Mem} {o : Array String} {c : BitVec 8}
    (hq : L.all (fun p => putcQuiet p.1) = true) :
    Triple (SegSt 0x80000d3c#64
        (⟨Register.x12, (0x80000d38#64) + sign_extend (m := 64) ((0x0005c#20) +++ 0x000#12)⟩ ::
          ⟨Register.x15, (zero_extend (m := 64) (c : BitVec (8 * 1))) ||| htifBase⟩ :: L) (ArmPay m o))
      (SegSt 0x80000d40#64
        (⟨Register.x12, (0x80000d38#64) + sign_extend (m := 64) ((0x0005c#20) +++ 0x000#12)⟩ ::
          ⟨Register.x15, (zero_extend (m := 64) (c : BitVec (8 * 1))) ||| htifBase⟩ :: L)
        (ArmPay m (o.push (putcStr c)))) :=
  segSt_putc (pc := 0x80000d3c#64) (w := 0x98f63423#32) (imm := 0x988#12) (r1 := 12) (r2 := 15)
    (b0 := 0x23#8) (b1 := 0x34#8) (b2 := 0xf6#8) (b3 := 0x98#8)
    (by decide) (by decide)
    (fun σ hG => Vsa.Sim.decodeW (w := 0x98f63423#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (fun _ hT => Lua.Vm.Code._write_at_80000d3c (Lua.Vm.Code.textLoaded__writeLoaded hT))
    write_tohost (by decide) (by decide) (fun _ h => h.1) (fun _ h => h.2.1) (putc_data c)
    (by decide) (by decide) (by decide) (by simpa [List.all_cons, putcQuiet] using hq)

/-! ## The summary -/

/-- **What `_write(1, buf, n)` needs**: the return address aligned, the
frame `[sp - 96, sp)` in RAM above htif.c's tables, the bytes below the
frame, the descriptor table initialised with `fds[1]` the console. -/
structure WrCtx (m : Mem) (sp buf n : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : symFds + symFdsSize + 96 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  buf_lo : tohostAddr + 16 ≤ buf
  buf_hi : buf + n + 96 ≤ sp
  /-- `fs_ready` (`fs_init` ran) -/
  ready : bytesT4 m symFsReady ≠ 0#32
  /-- `fds[1].kind = FD_STDOUT` (`struct mfd` is 24 bytes: `symFdsSize = 32 · 24`) -/
  stdout : bytesT4 m (symFds + 24) = 2#32

/-- `_write`'s one store: the saved `ra` at `88(sp - 96)`. -/
abbrev wrMem (m : Mem) (sp : Nat) (r : BitVec 64) : Mem := writeMap8 m (sp - 8) (sdData_val r)

/-- `_write`'s entry: `a0 = 1`, `a1 = buf`, `a2 = n`. -/
abbrev wrPre (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 1⟩ :: ⟨Register.x11, BitVec.ofNat 64 buf⟩ ::
    ⟨Register.x12, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- The putchar loop at `0x80000d2c`, `i` bytes written. -/
abbrev wrLoop (sp buf n i : Nat) (f : AbiFrame) : List Pin :=
  ⟨Register.x11, BitVec.ofNat 64 (buf + i)⟩ :: ⟨Register.x14, htifBase⟩ ::
    ⟨Register.x13, BitVec.ofNat 64 (buf + n)⟩ :: ⟨Register.x16, BitVec.ofNat 64 n⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 (sp - 96)⟩ :: ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- **`_write`'s return**: `a0 = n`, `sp` and the caller's frame restored. -/
abbrev wrRet (r : BitVec 64) (sp n : Nat) (f : AbiFrame) (m : Mem) (o : Array String) : Config → Prop :=
  SegSt r (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins) (ArmPay m o)

/-- `bne a3, a1` against the end. -/
theorem wr_end_guard {P n i : Nat} (h : P + n < 2 ^ 64) (hi : i < n) :
    (BitVec.ofNat 64 (P + n) != BitVec.ofNat 64 (P + i) + sign_extend (m := 64) (0x001#12)) =
      !decide (i + 1 = n) := by
  rw [add_imm _ 1 (by decide)]
  by_cases e : i + 1 = n
  · subst e; simp [Nat.add_assoc]
  · simp only [e, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    intro h2; have := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)] at this; omega

/-- The saved `ra`, reloaded. -/
theorem wr_ra {m : Mem} {sp : Nat} {r : BitVec 64} (h1 : 96 ≤ sp) (h2 : sp < 2 ^ 64) :
    sign_extend (m := 64) (bytesT8 (wrMem m sp r)
      (BitVec.ofNat 64 (sp - 96) + sign_extend (m := 64) (0x058#12)).toNat : BitVec (8 * 8)) = r := by
  rw [add_imm _ _ (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show sp - 96 + 0x058 = sp - 8 by omega, bytesT8_writeMap8, sext64_id, sdData_id]

/-- `addi sp, sp, 96`. -/
theorem wr_sp {sp : Nat} (h : 96 ≤ sp) :
    BitVec.ofNat 64 (sp - 96) + sign_extend (m := 64) (0x060#12) = BitVec.ofNat 64 sp := by
  rw [add_imm _ _ (by decide), show sp - 96 + 0x060 = sp by omega]

/-- `bnez a4` on `fs_ready` (`lw a4, 1264(gp)`). -/
theorem wr_ready {m : Mem} {gp : BitVec 64} (hgp : gp = BitVec.ofNat 64 symGlobalPointer)
    (h : bytesT4 m symFsReady ≠ 0#32) :
    ((sign_extend (m := 64) (bytesT4 m (gp + sign_extend (m := 64) (0x4f0#12)).toNat : BitVec (8 * 4))) !=
      (0#64)) = true := by
  subst hgp
  rw [show (BitVec.ofNat 64 symGlobalPointer + sign_extend (m := 64) (0x4f0#12)).toNat = symFsReady by decide]
  simp only [bne_iff_ne, ne_eq]
  intro e; apply h
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (·.getLsbD i) e
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.getLsbD_signExtend, BitVec.getLsbD_zero] at this
  simpa [hi, show i < 64 by omega] using this

/-- `bltu a4, a3` (`a4 = 31`, `a3 = fd = 1`): the descriptor is in range. -/
theorem wr_fd : zopz0zI_u ((0#64) + sign_extend (m := 64) (0x01f#12))
    (BitVec.ofNat 64 1 + sign_extend (m := 64) (0x000#12)) = false := by decide

/-- `&fds[1]` (`a4 = gp + 1424 + 24·fd`, `fd = 1`). -/
abbrev wrKindAddr (gp : BitVec 64) : BitVec 64 :=
  ((gp + sign_extend (m := 64) (0x590#12)) + (shift_bits_left ((shift_bits_left (BitVec.ofNat 64 1 +
    sign_extend (m := 64) (0x000#12)) (Sail.BitVec.extractLsb (0x01#6) 5 0)) + (BitVec.ofNat 64 1 +
      sign_extend (m := 64) (0x000#12))) (Sail.BitVec.extractLsb (0x03#6) 5 0))) + sign_extend (m := 64) (0x000#12)

theorem wrKindAddr_eq : (wrKindAddr (BitVec.ofNat 64 symGlobalPointer)).toNat = symFds + 24 := by decide

/-- `bgeu a1, a2` (`a1 = 1`): the kind is above `FD_STDIN`. -/
theorem wr_kind {M : Mem} {gp : BitVec 64} (hgp : gp = BitVec.ofNat 64 symGlobalPointer)
    (h : bytesT4 M (symFds + 24) = 2#32) :
    zopz0zKzJ_u ((0#64) + sign_extend (m := 64) (0x001#12))
      (sign_extend (m := 64) (bytesT4 M (wrKindAddr gp).toNat : BitVec (8 * 4))) = false := by
  subst hgp; rw [wrKindAddr_eq, h]; decide

/-- `bne a2, a1` (`a1 = 4`): the kind is not `FD_FILE`. -/
theorem wr_kind4 {M : Mem} {gp : BitVec 64} (hgp : gp = BitVec.ofNat 64 symGlobalPointer)
    (h : bytesT4 M (symFds + 24) = 2#32) :
    ((sign_extend (m := 64) (bytesT4 M (wrKindAddr gp).toNat : BitVec (8 * 4))) !=
      ((0#64) + sign_extend (m := 64) (0x004#12))) = true := by
  subst hgp; rw [wrKindAddr_eq, h]; decide

/-- `addi sp, sp, -96`. -/
theorem wr_fr {sp : Nat} (h1 : 96 ≤ sp) (h2 : sp < 2 ^ 64) :
    BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfa0#12) = BitVec.ofNat 64 (sp - 96) := by
  rw [imm_neg_add sp 0xfa0 (by decide) (by decide)]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- `sd ra, 88(sp)`'s address. -/
theorem wr_slot {sp : Nat} (h1 : 96 ≤ sp) (h2 : sp < 2 ^ 64) :
    (BitVec.ofNat 64 (sp - 96) + sign_extend (m := 64) (0x058#12)).toNat = sp - 8 := by
  rw [add_imm _ _ (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega

/-- `beqz a6`. -/
theorem wr_n0 {n : Nat} (h : n < 2 ^ 64) :
    (BitVec.ofNat 64 n + sign_extend (m := 64) (0x000#12) == 0#64) = decide (n = 0) := by
  rw [Vsa.Sim.sext_zero, BitVec.add_zero]
  by_cases e : n = 0
  · subst e; rfl
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; have := congrArg BitVec.toNat h2; simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt h] at this; exact e this

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [wr_ra (by omega) (by omega), Vsa.Sim.ret_tgt _ hra]; exact hra))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_val) => `(tactic| first
      | (rw [add_imm _ _ (by decide), Nat.add_assoc] <;> rfl)
      | exact wr_sp (by omega)
      | (simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat] <;> rfl))

set_option hygiene false in
/-- The context's numeric facts, for `kit_disch`. -/
local macro "wr_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hFD : symFds = 0x8005d460 := rfl
  have hFS : symFdsSize = 768 := rfl
  have hra := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).buf_lo; have := ($hx).buf_hi))

/-- **The putchar loop** from `i` bytes written. -/
theorem write_loop (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : WrCtx m sp buf n r) : ∀ i, i < n →
    Triple (SegSt 0x80000d2c#64 (wrLoop sp buf n i f) (ArmPay (wrMem m sp r) (pushes o (bytesAt m buf i))))
      (wrRet r sp n f (wrMem m sp r) (pushes o (bytesAt m buf n))) := by
  intro i₀ hi₀ c₀ h₀
  refine seg_loop (S := fun i c => i < n ∧
      SegSt 0x80000d2c#64 (wrLoop sp buf n i f) (ArmPay (wrMem m sp r) (pushes o (bytesAt m buf i))) c)
    (fun i => n - i) (fun i c ⟨hi, h⟩ => ?_) i₀ c₀ ⟨hi₀, h₀⟩
  have acc := Steps.refl c
  wr_ctx hx
  kit_run h acc until [0x80000d3c]
  obtain ⟨_, acc, h⟩ := h.run acc h.pins (write_putc rfl)
  have hb : bytesT1 (wrMem m sp r) ((BitVec.ofNat 64 (buf + i) + sign_extend (m := 64) (0x000#12)).toNat) =
      bytesT1 m (buf + i) := by
    rw [addr0 (by omega)]; exact bytesT1_writeMap8_out _ _ _ (by omega)
  rw [hb, ← pushes_snoc, ← bytesAt_succ] at h
  have hg := wr_end_guard (P := buf) (n := n) (i := i) (by omega) hi
  by_cases hend : i + 1 = n
  · simp only [hend, decide_true, Bool.not_true] at hg
    subst hend
    kit_run h acc
    rw [wr_ra (by omega) (by omega)] at h
    have h := h.at (Vsa.Sim.ret_tgt r hra)
    rw [wr_sp (by omega), Vsa.Sim.sext_zero, BitVec.add_zero] at h
    exact ⟨_, acc, .inr (h.repin (by pins_of h))⟩
  · simp only [hend, decide_false, Bool.not_false] at hg
    kit_run h acc until [0x80000d2c]
    exact ⟨_, acc, .inl ⟨i + 1, by omega, by omega, h.repin (by pins_of h)⟩⟩

/-- **`_write(1, buf, n)` on the console**: it appends the `n` bytes at
`buf` to the console and returns `n`, `sp` and the caller's frame restored;
its one store is the saved `ra` (`wrMem`). -/
theorem write_sum (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : WrCtx m sp buf n r) :
    Triple (SegSt 0x80000ae8#64 (wrPre sp buf n r f) (ArmPay m o))
      (wrRet r sp n f (wrMem m sp r) (pushes o (bytesAt m buf n))) := by
  intro c h
  have acc := Steps.refl c
  wr_ctx hx
  have hkind : bytesT4 (writeMap8 m (sp - 8) (sdData_val r)) (symFds + 24) = 2#32 := by
    rw [bytesT4_wm8_out (by omega)]; exact hx.stdout
  have hg1 := wr_ready (m := m) rfl hx.ready
  have hg2 := wr_fd
  have hg3 := wr_kind rfl hkind
  have hg4 := wr_kind4 rfl hkind
  simp only [wrKindAddr] at hg3 hg4
  kit_run h acc until [0x80000b34]
  rw [wr_fr (by omega) (by omega), wr_slot (by omega) (by omega)] at h
  have hn := wr_n0 (n := n) (by omega)
  by_cases h0 : n = 0
  · subst h0
    simp only [decide_true] at hn
    kit_run h acc
    rw [wr_ra (by omega) (by omega)] at h
    have h := h.at (Vsa.Sim.ret_tgt r hra)
    rw [wr_sp (by omega), Vsa.Sim.sext_zero, BitVec.add_zero] at h
    exact ⟨_, acc, h.repin (by pins_of h)⟩
  · simp only [h0, decide_false] at hn
    kit_run h acc until [0x80000d2c]
    simp only [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat] at h
    have h := h.repin (L' := wrLoop sp buf n 0 f) (by pins_of h)
    obtain ⟨c', hs, h'⟩ := write_loop sp buf n r f m o hx 0 (by omega) _ h
    exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit

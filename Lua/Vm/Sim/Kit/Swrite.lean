import Lua.Vm.Sim.Kit.Write
import Lua.Vm.Sim.Kit.Adjvar
import Lua.Vm.Arms.Segs.Hwrite_r
import Lua.Vm.Arms.Segs.Hswrite

/-!
# newlib's write hook at the Lua ELF's addresses (A0.2, lane F1-6)

The two frames above htif.c's `_write` on `print`'s path:

* `_write_r(ptr, fd, buf, n)` (`0x8003b3b0`): `errno = 0`, `_write(fd, buf,
  n)`, and on `-1` the copy of `errno` into `ptr->_errno` (not reached: the
  console write returns `n`, `write_sum`). `write_r_sum`.
* `__swrite(ptr, fp, buf, n)` (`0x80034f18`): stdio's `_write` hook in the
  `FILE`; it clears `__SOFF` in `fp->_flags` (an `sh`) and tail-calls
  `_write_r(ptr, fp->_file, buf, n)`; the `__SAPP` seek is not reached
  (stdout is not opened for append). `swrite_sum`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- newlib's `errno` (`sw zero, 1336(gp)`). -/
def errnoAddr : Nat := symGlobalPointer + 0x538

/-- The bytes at `buf` are those of any memory agreeing there. -/
theorem bytesAt_congr {m m' : Mem} {buf n : Nat} (h : ∀ i, i < n → bytesT1 m' (buf + i) = bytesT1 m (buf + i)) :
    bytesAt m' buf n = bytesAt m buf n := by
  unfold bytesAt
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

/-! ## `_write_r` -/

/-- `_write_r`'s stores before the call: `s0` and `ra` saved in `[sp - 16, sp)`,
`errno = 0`. -/
abbrev wrrMem (m : Mem) (sp : Nat) (s0 r : BitVec 64) : Mem :=
  writeMap4 (writeMap8 (writeMap8 m (sp - 16) (sdData_val s0)) (sp - 8) (sdData_val r)) errnoAddr (swData 0#64)

/-- What `_write_r(ptr, 1, buf, n)` needs: `_write`'s facts one frame lower,
and the bytes apart from `errno`. -/
structure WrrCtx (m : Mem) (sp buf n : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : symFds + symFdsSize + 112 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  buf_lo : errnoAddr + 4 ≤ buf
  buf_hi : buf + n + 112 ≤ sp
  ready : bytesT4 m symFsReady ≠ 0#32
  stdout : bytesT4 m (symFds + 24) = 2#32

/-- `_write_r`'s entry: `a0 = ptr`, `a1 = 1`, `a2 = buf`, `a3 = n`. -/
abbrev wrrPre (ptr : BitVec 64) (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  ⟨Register.x10, ptr⟩ :: ⟨Register.x11, BitVec.ofNat 64 1⟩ :: ⟨Register.x12, BitVec.ofNat 64 buf⟩ ::
    ⟨Register.x13, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- `_write_r`'s memory on return: its stores and `_write`'s saved `ra`. -/
abbrev wrrRetMem (m : Mem) (sp : Nat) (s0 r : BitVec 64) : Mem :=
  wrMem (wrrMem m sp s0 r) (sp - 16) 0x8003b3d8#64

/-- The caller's frame with `s0 := ptr` (`mv s0, a0`). -/
abbrev AbiFrame.withS0 (f : AbiFrame) (v : BitVec 64) : AbiFrame :=
  ⟨v, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- `addi sp, sp, -k`. -/
theorem sp_sub {y k : Nat} (hk : 2048 ≤ k ∧ k < 4096) (hy : 4096 - k ≤ y) (hy2 : y < 2 ^ 64) :
    BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (y - (4096 - k)) :=
  sl_neg hk hy hy2

/-- An address `y + k`, `k < 2048`, in RAM. -/
theorem addr_add {y k : Nat} (hk : k < 2048) (h : y + k < 2 ^ 64) :
    (BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat = y + k := by
  rw [add_imm _ _ hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `beq a0, a5` against `-1`. -/
theorem wrr_m1 {n : Nat} (h : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == ((0#64) + sign_extend (m := 64) (0xfff#12))) = false := by
  rw [show (0#64) + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide]
  simp only [beq_eq_false_iff_ne, ne_eq]
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this; omega

/-- `addi rd, rs, -d` (the immediate's sign extension is `2^64 - d`). -/
theorem imm_sub {y : Nat} (d : Nat) (k : BitVec 12) (hk : sign_extend (m := 64) k = BitVec.ofNat 64 (2 ^ 64 - d))
    (hd : d ≤ y) (hy : y < 2 ^ 64) : BitVec.ofNat 64 y + sign_extend (m := 64) k = BitVec.ofNat 64 (y - d) := by
  rw [hk, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem b4_wm4_out {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 4 ≤ a ∨ a + 4 ≤ x) :
    bytesT4 (writeMap4 m a d) x = bytesT4 m x := by
  simp only [bytesT4]
  rw [getElem?_writeMap4_out m a d x (by omega), getElem?_writeMap4_out m a d (x + 1) (by omega),
    getElem?_writeMap4_out m a d (x + 2) (by omega), getElem?_writeMap4_out m a d (x + 3) (by omega)]

/-- A read of `_write_r`'s frame on return (`ld ra, 8(sp)`, `ld s0, 0(sp)`). -/
theorem wrr_ld {m : Mem} {sp j : Nat} {s0 r : BitVec 64} (hj : j = 0 ∨ j = 8) (h1 : errnoAddr + 4 + 32 ≤ sp)
    (h2 : sp ≤ 2 ^ 32) :
    sign_extend (m := 64) (bytesT8 (wrrRetMem m sp s0 r)
      (BitVec.ofNat 64 (sp - 16) + sign_extend (m := 64) (BitVec.ofNat 12 j)).toNat : BitVec (8 * 8)) =
      if j = 0 then s0 else r := by
  rw [addr_add (by omega) (by omega), sext64_id, bytesT8_wm8_out (by omega), bytesT8_wm4_out (by omega)]
  rcases hj with rfl | rfl
  · rw [bytesT8_wm8_out (by omega), Nat.add_zero, bytesT8_writeMap8, sdData_id]; rfl
  · rw [show sp - 16 + 8 = sp - 8 by omega, bytesT8_writeMap8, sdData_id]; rfl

theorem wrr_ra {m : Mem} {sp : Nat} {s0 r : BitVec 64} (h1 : errnoAddr + 4 + 32 ≤ sp) (h2 : sp ≤ 2 ^ 32) :
    sign_extend (m := 64) (bytesT8 (wrrRetMem m sp s0 r)
      (BitVec.ofNat 64 (sp - 16) + sign_extend (m := 64) (0x008#12)).toNat : BitVec (8 * 8)) = r :=
  wrr_ld (j := 8) (.inr rfl) h1 h2

theorem wrr_s0 {m : Mem} {sp : Nat} {s0 r : BitVec 64} (h1 : errnoAddr + 4 + 32 ≤ sp) (h2 : sp ≤ 2 ^ 32) :
    sign_extend (m := 64) (bytesT8 (wrrRetMem m sp s0 r)
      (BitVec.ofNat 64 (sp - 16) + sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)) = s0 :=
  wrr_ld (j := 0) (.inl rfl) h1 h2

/-- `addi sp, sp, 16`. -/
theorem wrr_sp {sp : Nat} (h : 16 ≤ sp) :
    BitVec.ofNat 64 (sp - 16) + sign_extend (m := 64) (0x010#12) = BitVec.ofNat 64 sp := by
  rw [add_imm _ _ (by decide), show sp - 16 + 0x010 = sp by omega]

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [wrr_ra hsp1 hsp2, Vsa.Sim.ret_tgt _ hra]; exact hra))

set_option hygiene false in
local macro "wrr_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hFD : symFds = 0x8005d460 := rfl
  have hFS : symFdsSize = 768 := rfl
  have hGP : symGlobalPointer = 0x8005ced0 := rfl
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hFR : symFsReady = 0x8005d3c0 := rfl
  have hra := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).buf_lo; have := ($hx).buf_hi
  have hsp1 : errnoAddr + 4 + 32 ≤ sp := by omega
  have hsp2 : sp ≤ 2 ^ 32 := by omega))

/-- **`_write_r(ptr, 1, buf, n)` on the console**: `errno = 0`, the console
write (`write_sum`), the return of `n` with `s0`, `sp` and the frame restored. -/
theorem write_r_sum (ptr : BitVec 64) (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : WrrCtx m sp buf n r) :
    Triple (SegSt 0x8003b3b0#64 (wrrPre ptr sp buf n r f) (ArmPay m o))
      (wrRet r sp n f (wrrRetMem m sp f.s0 r) (pushes o (bytesAt m buf n))) := by
  intro c h
  have acc := Steps.refl c
  wrr_ctx hx
  kit_run h acc until [0x80000ae8]
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  rw [imm_sub 16 (0xff0#12) (by decide) (by omega) (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show sp - 16 < 2 ^ 64 by omega), addr_add (k := 8) (by decide) (by omega),
    addr_add (y := symGlobalPointer) (k := 0x538) (by decide) (by omega),
    show sp - 16 + 8 = sp - 8 by omega] at h
  have hW : WrCtx (wrrMem m sp f.s0 r) (sp - 16) buf n 0x8003b3d8#64 := by
    refine ⟨by decide, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [b4_wm4_out (by omega), bytesT4_wm8_out (by omega), bytesT4_wm8_out (by omega)]; exact hx.ready
    · rw [b4_wm4_out (by omega), bytesT4_wm8_out (by omega), bytesT4_wm8_out (by omega)]; exact hx.stdout
  obtain ⟨_, acc, h⟩ := h.call acc (by pins_of h) (write_sum (sp - 16) buf n 0x8003b3d8#64 (f.withS0 ptr)
    (wrrMem m sp f.s0 r) o hW)
  have hm1 := wrr_m1 (n := n) (by omega)
  dsimp only [wrRet] at h
  kit_run h acc
  rw [wrr_ra (by omega) (by omega)] at h
  have h := h.at (Vsa.Sim.ret_tgt r hra)
  rw [wrr_sp (by omega), wrr_s0 (by omega) (by omega),
    bytesAt_congr (m := m) fun i hi => by
      rw [bytesT1_wm4_out (by omega), bytesT1_writeMap8_out _ _ _ (by omega),
        bytesT1_writeMap8_out _ _ _ (by omega)]] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ## `__swrite` -/

/-- newlib's `stdout`, the second of the three standard `FILE`s (`__sf`). -/
def stdoutFile : Nat := symSf + fileSize

theorem stdoutFile_eq : stdoutFile = 0x8005e668 := rfl

/-- Reads through the stores `__swrite` makes. -/
theorem b2_wm8_out {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 2 ≤ a ∨ a + 8 ≤ x) :
    bytesT2 (writeMap8 m a d) x = bytesT2 m x := by
  simp only [bytesT2]
  rw [getElem?_writeMap8_out m a d x (by omega), getElem?_writeMap8_out m a d (x + 1) (by omega)]

theorem b4_wm2_out {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x + 4 ≤ a ∨ a + 2 ≤ x) :
    bytesT4 (writeMap2 m a d) x = bytesT4 m x := by
  simp only [bytesT4]
  rw [getElem?_writeMap2_out m a d x (by omega), getElem?_writeMap2_out m a d (x + 1) (by omega),
    getElem?_writeMap2_out m a d (x + 2) (by omega), getElem?_writeMap2_out m a d (x + 3) (by omega)]

theorem b1_wm2_out {m : Mem} {a x : Nat} {d : BitVec (8 * 2)} (h : x < a ∨ a + 2 ≤ x) :
    bytesT1 (writeMap2 m a d) x = bytesT1 m x := by
  simp only [bytesT1]; rw [getElem?_writeMap2_out m a d x h]

/-- `__SOFF` cleared (`lui a3, 0xfffff; addi a3, a3, -1; and a5, a5, a3`). -/
abbrev soffMask : BitVec 64 :=
  (sign_extend (m := 64) ((0xfffff#20) +++ 0x000#12)) + sign_extend (m := 64) (0xfff#12)

/-- `__swrite`'s stores: the saved `ra`, and `_flags` without `__SOFF`. -/
abbrev swMem (m : Mem) (sp : Nat) (r : BitVec 64) (fl : BitVec 16) : Mem :=
  writeMap2 (writeMap8 m (sp - 8) (sdData_val r)) (stdoutFile + fileFlagsOff)
    (shData (sign_extend (m := 64) fl &&& soffMask))

/-- What `__swrite(ptr, stdout, buf, n)` needs: `_write_r`'s facts, stdout's
descriptor `1`, its flags `fl` without `__SAPP`, the bytes apart from stdout. -/
structure SwCtx (m : Mem) (sp buf n : Nat) (r : BitVec 64) (fl : BitVec 16) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : stdoutFile + fileSize + 112 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  buf_lo : errnoAddr + 4 ≤ buf
  buf_hi : buf + n + 112 ≤ sp
  buf_file : buf + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ buf
  ready : bytesT4 m symFsReady ≠ 0#32
  stdout : bytesT4 m (symFds + 24) = 2#32
  flags : bytesT2 m (stdoutFile + fileFlagsOff) = fl
  /-- not `__SAPP` (no seek before the write) -/
  sapp : ((sign_extend (m := 64) fl &&& sign_extend (m := 64) (0x100#12)) != (0#64)) = false
  fd : bytesT2 m (stdoutFile + fileFileOff) = 1#16

/-- `__swrite`'s entry: `a0 = ptr`, `a1 = stdout`, `a2 = buf`, `a3 = n`. -/
abbrev swPre (ptr : BitVec 64) (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) : List Pin :=
  ⟨Register.x10, ptr⟩ :: ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩ :: ⟨Register.x12, BitVec.ofNat 64 buf⟩ ::
    ⟨Register.x13, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins

/-- A saved register read back. -/
theorem ld_saved {m : Mem} {a : Nat} {r : BitVec 64} :
    sign_extend (m := 64) (bytesT8 (writeMap8 m a (sdData_val r)) a : BitVec (8 * 8)) = r := by
  rw [bytesT8_writeMap8, sext64_id, sdData_id]

/-- `lh` of a halfword: its sign extension. -/
theorem sext16_one : sign_extend (m := 64) (1#16 : BitVec (8 * 2)) = BitVec.ofNat 64 1 := by decide

set_option hygiene false in
local macro "sw_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hFD : symFds = 0x8005d460 := rfl
  have hFS : symFdsSize = 768 := rfl
  have hGP : symGlobalPointer = 0x8005ced0 := rfl
  have hEA : errnoAddr = 0x8005d408 := rfl
  have hFR : symFsReady = 0x8005d3c0 := rfl
  have hSF : stdoutFile = 0x8005e668 := rfl
  have hFZ : fileSize = 184 := rfl
  have hFL : fileFlagsOff = 16 := rfl
  have hFF : fileFileOff = 18 := rfl
  have hra := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).buf_lo; have := ($hx).buf_hi; have := ($hx).buf_file))

/-- **`__swrite(ptr, stdout, buf, n)`**: `__SOFF` cleared, then `_write_r`
(`write_r_sum`) as a tail call: the bytes appended, `n` returned. -/
theorem swrite_sum (ptr : BitVec 64) (sp buf n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (fl : BitVec 16) (hx : SwCtx m sp buf n r fl) :
    Triple (SegSt 0x80034f18#64 (swPre ptr sp buf n r f) (ArmPay m o))
      (wrRet r sp n f (wrrRetMem (swMem m sp r fl) sp f.s0 r) (pushes o (bytesAt m buf n))) := by
  intro c h
  have acc := Steps.refl c
  sw_ctx hx
  have hg := hx.sapp
  rw [← hx.flags, show stdoutFile + fileFlagsOff = (BitVec.ofNat 64 stdoutFile +
    sign_extend (m := 64) (0x010#12)).toNat by rw [addr_add (by decide) (by omega)]; rfl] at hg
  kit_run h acc until [0x8003b3b0]
  rw [imm_sub 48 (0xfd0#12) (by decide) (by omega) (by omega)] at h
  simp (disch := first | decide | omega) only [Vsa.Sim.sext_zero, BitVec.add_zero, add_imm,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt] at h
  have hfl := hx.flags; have hfd := hx.fd
  rw [hFL] at hfl; rw [hFF] at hfd
  rw [show sp - 48 + 48 = sp by omega, show sp - 48 + 40 = sp - 8 by omega, ld_saved,
    b2_wm8_out (by omega), hfl, hfd, sext16_one] at h
  have hW : WrrCtx (swMem m sp r fl) sp buf n r := by
    refine ⟨hra, by omega, by omega, by omega, by omega, by omega, ?_, ?_⟩
    · rw [b4_wm2_out (by omega), bytesT4_wm8_out (by omega)]; exact hx.ready
    · rw [b4_wm2_out (by omega), bytesT4_wm8_out (by omega)]; exact hx.stdout
  obtain ⟨c', hs, h'⟩ := h.call acc (by pins_of h) (write_r_sum ptr sp buf n r f (swMem m sp r fl) o hW)
  refine ⟨c', hs, ?_⟩
  rw [bytesAt_congr (m := m) fun i hi => by
    rw [b1_wm2_out (by omega), bytesT1_writeMap8_out _ _ _ (by omega)]] at h'
  exact h'

end Lua.Vm.Sim.Kit

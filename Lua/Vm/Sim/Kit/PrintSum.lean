import Lua.Vm.Sim.Kit.PrintIO
import Lua.Vm.Sim.Kit.LuaApi
import Lua.Vm.AtF.Print

/-!
# `luaB_print` from its callees (lane F1-11)

`luaB_print(L)` (`0x80022f18`) on the callee-context route
(`Lua/Vm/AtF/Print.lean`, `gen_lua_at.py --fn luaB_print`): `lua_gettop`,
then for each argument `luaL_tolstring(L, i, &l)`, a `"\t"` before all but
the first, the string, `lua_pop(L, 1)`; then `"\n"` and `fflush(stdout)`.

The writes are `fwrite_print` (every phase of `stdout`, proved from
`MallocR_Statement`), the flush `fflush_stdout`. The Lua side is abstract:
an invariant `S k H m` (the C frame holding `k` values, over the heap `H`)
and the bytes `bs i` argument `i` prints, with `luaL_tolstring`, `lua_settop`
and `lua_gettop` as named premises over it (`PrintLua`): a value class
discharges `PrintLua.tolstring` for its values.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- The words `luaB_print` reads itself (`_impure_ptr`, `_REENT->_stdout`) and
its two literals (`"\t"`, `"\n"` in `.rodata`). -/
structure PrintCells (m : Mem) : Prop where
  impure : bytesT8 m 0x8005d398 = 0x8005d1b8#64
  stdout : bytesT8 m 0x8005d1c8 = 0x8005e668#64
  tab : bytesAt m 0x8004ff40 1 = [0x09#8]
  nl : bytesAt m 0x8004fb48 1 = [0x0a#8]

/-- **The I/O state `luaB_print` threads**: `stdout` in phase `ph` with the
heap `H` (of the zero fill), and its cells. -/
structure PrintSt (m : Mem) (ph : StdoutPh) (H : HeapIx) : Prop where
  io : StdoutIn m H ph
  heap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins
  cells : PrintCells m

/-- The cells off what a write may change (the buffer, if any, in the arena). -/
theorem PrintCells.keep {m m' : Mem} {sp : Nat} {H : HeapIx} {ph : StdoutPh} (h : PrintCells m)
    (hsp : 0x8005e7d8 + 4096 ≤ sp) (hb : ∀ a, ph.Buf a → 0x8006ecd0 ≤ a)
    (hk : ∀ a, ¬ PrintW sp H ph a → bytesT1 m' a = bytesT1 m a) : PrintCells m' := by
  have hn : ∀ a, (0x8004fb48 ≤ a ∧ a < 0x8004ff48) ∨ (0x8005d398 ≤ a ∧ a < 0x8005d3a0) ∨
      (0x8005d1c8 ≤ a ∧ a < 0x8005d1d0) → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    refine hk a fun hw => ?_
    pw_nums
    have e4 : symMallocAv = 0x8005c6d0 := rfl
    have e5 : symMallocSbrkBase = 0x8005d388 := rfl
    have e6 : symBrk = 0x8005d3b8 := rfl
    have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
    have e9 : symMallocMallinfo = 0x8005e560 := rfl
    have e2 : heapStart = 0x8006ecd0 := rfl
    have : symFiles = 0x8005d760 := rfl
    rcases hw with hw | hw | hw | hw | hw | hw
    · simp only [FsGlobal] at hw; omega
    · rcases hw with hw | ⟨h1, _, _⟩
      · simp only [MallocGlobal] at hw; omega
      · omega
    · simp only [SinitW, Rng] at hw; omega
    · simp only [Rng] at hw; omega
    · have := hb a hw; omega
    · simp only [Below] at hw; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [bytesT8_congrT (m' := m) fun i hi => hn _ (by omega)]; exact h.impure
  · rw [bytesT8_congrT (m' := m) fun i hi => hn _ (by omega)]; exact h.stdout
  · rw [bytesAt_congr fun i hi => hn _ (by omega)]; exact h.tab
  · rw [bytesAt_congr fun i hi => hn _ (by omega)]; exact h.nl

/-- A phase's buffer lies in the arena. -/
theorem StdoutIn.buf_lo {m : Mem} {H : HeapIx} {ph : StdoutPh} (h : StdoutIn m H ph) :
    ∀ a, ph.Buf a → heapStart + 16 ≤ a := by
  intro a ha
  cases h with
  | up _ _ hb => exact Nat.le_trans hb.lo ha.1
  | boot => exact ha.elim
  | fresh => exact ha.elim

/-- More chunks in use, fewer bytes `_malloc_r` may write. -/
theorem MallocW.anti {H H' : HeapIx} (hk : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) {a : Nat}
    (h : MallocW H'.chunks a) : MallocW H.chunks a := by
  rcases h with h | ⟨h1, h2, h3⟩
  · exact .inl h
  · exact .inr ⟨h1, h2, fun ⟨c, hc, hu, hl, hh⟩ => h3 ⟨c, hk c hc hu, hu, hl, hh⟩⟩

/-- `PrintW` over more chunks in use is smaller. -/
theorem PrintW.anti {sp : Nat} {H H' : HeapIx} {ph : StdoutPh}
    (hk : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) {a : Nat} (h : PrintW sp H' ph a) :
    PrintW sp H ph a := by
  rcases h with h | h | h
  · exact .inl h
  · exact .inr (.inl (MallocW.anti hk h))
  · exact .inr (.inr h)

/-- `PrintW` reads a phase only through its buffer. -/
theorem PrintW.buf_eq {sp : Nat} {H : HeapIx} {ph ph' : StdoutPh} (he : ∀ a, ph.Buf a ↔ ph'.Buf a) {a : Nat}
    (h : PrintW sp H ph a) : PrintW sp H ph' a := by
  rcases h with h | h | h | h | h | h
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr (.inl h)))
  · exact .inr (.inr (.inr (.inr (.inl ((he a).1 h)))))
  · exact .inr (.inr (.inr (.inr (.inr h))))

/-- **`fflush(stdout)`'s keep is a write's** (`PrintW` of the set-up phase). -/
theorem StdoutKeep.printW {m m' : Mem} {sp buf : Nat} {H : HeapIx} {pend : List (BitVec 8)}
    (h : StdoutKeep m m' sp buf) : ∀ a, ¬ PrintW sp H (.up buf pend) a → bytesT1 m' a = bytesT1 m a := by
  intro a ha
  simp only [PrintW, StdoutPh.Buf, not_or] at ha
  obtain ⟨hg, _, _, hst, hb, hbl⟩ := ha
  simp only [Below, Rng, not_and, Nat.not_lt] at hbl hb hst
  by_cases h1 : sp ≤ a
  · exact h.keep_hi a h1
  · pw_nums
    exact h.keep_lo a (by omega) (by omega) (by omega) (by simp only [FsGlobal, not_or, not_and] at hg; omega)

/-- Nothing at or above the callees' `sp` is a write's (the stack above the
heap). -/
theorem PrintW.not_above {sp : Nat} {H : HeapIx} {ph : StdoutPh} (hsp : heapEnd ≤ sp)
    (hb : ∀ a, ph.Buf a → a < heapEnd) {a : Nat} (ha : sp ≤ a) : ¬ PrintW sp H ph a := by
  obtain ⟨E, hE⟩ : ∃ E, heapEnd = E := ⟨_, rfl⟩
  have hE' : E = 0x87800000 := hE ▸ rfl
  rw [hE] at hsp hb
  intro hw
  pw_nums
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symFiles = 0x8005d760 := rfl
  rcases hw with hw | hw | hw | hw | hw | hw
  · simp only [FsGlobal] at hw; omega
  · rcases hw with hw | ⟨_, hw, _⟩
    · simp only [MallocGlobal] at hw; omega
    · rw [hE] at hw; omega
  · simp only [SinitW, Rng] at hw; omega
  · simp only [Rng] at hw; omega
  · have := hb a hw; omega
  · simp only [Below] at hw; omega

/-- A buffer owned by the heap lies below its end. -/
theorem StdoutIn.buf_hi {m : Mem} {H : HeapIx} {ph : StdoutPh} (h : StdoutIn m H ph) :
    ∀ a, ph.Buf a → a < heapEnd := by
  intro a ha
  cases h with
  | up _ _ hb => exact Nat.lt_of_lt_of_le ha.2 hb.hi
  | boot => exact ha.elim
  | fresh => exact ha.elim

/-- The callee frame of `luaB_print`'s calls: `s0`, `s1`, `s4` its own or the
caller's, `s2 = &_impure_ptr`, `s3 = L`, `s5`–`s11` the caller's. -/
abbrev prFr (s0 s1 s4 : BitVec 64) (L : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨s0, s1, 0x8005d398#64, BitVec.ofNat 64 L, s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- The context of `luaB_print`'s rows: `sp`, `L`, `n`, the string, its
length, `i`; `ra`, the caller's frame, the loop's dead `s1` (`w13`) and its
`s0` after a write (`w20`). -/
@[at_row] abbrev prX (sp0 L n s len i : Nat) (r w13 w20 : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp0, L, n, s, len, i] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10,
    f.s11, w13, 0, 0, 0, 0, 0, 0, w20] m o

/-- `luaB_print`'s entry facts. -/
structure PrOk (sp0 L : Nat) (r : BitVec 64) : Prop where
  sp_lo : heapEnd + 8192 + 64 ≤ sp0
  sp_hi : sp0 ≤ 2 ^ 32
  sp_al : sp0 % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_hi : L + 256 ≤ 2 ^ 32
  L_al : L % 8 = 0

theorem PrOk.nums {sp0 L : Nat} {r : BitVec 64} (h : PrOk sp0 L r) :
    0x87800000 + 8192 + 64 ≤ sp0 := by
  have h1 := h.sp_lo
  obtain ⟨E, hE⟩ : ∃ E, heapEnd = E := ⟨_, rfl⟩
  have h2 : E = 0x87800000 := hE ▸ rfl
  rw [hE] at h1; omega

/-- **`luaB_print`'s tail**: `"\n"` (`fwrite_print`), `fflush(stdout)`, the
return. -/
theorem pr_tail (hM : MallocR_Statement) (sp0 L : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (ph : StdoutPh) (H : HeapIx) (hok : PrOk sp0 L r) (hP : PrintSt m ph H)
    (hra : bytesT8 m (sp0 - 8) = r) (hs2 : bytesT8 m (sp0 - 32) = f.s2) (hs3 : bytesT8 m (sp0 - 40) = f.s3)
    (c : Config) (h : SegSt 0x80022fd0#64 (Lua.Vm.AtF.Print.r5 (prX sp0 L 0 0 0 0 r 0 0 f m o)) (ArmPay m o) c) :
    ∃ c' m' out buf H', Steps c c' ∧ wrRet r sp0 0 f m' (pushes o out) c' ∧ out = ph.pend ++ [0x0a#8] ∧
      PrintSt m' (.up buf []) H' ∧ (∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) ∧
      ∀ a, ¬ PrintW (sp0 - 64) H (.up buf []) a → bytesT1 m' a = bytesT1 m a := by
  have q := hok.nums
  have q2 := hok.sp_hi
  have hhe : heapEnd = 0x87800000 := rfl
  have hX : Lua.Vm.AtF.Print.Ok (prX sp0 L 0 0 0 0 r 0 0 f m o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have hc0 := hP.cells.impure; have hc1 := hP.cells.stdout
  have h : SegSt 0x80022fd0#64 (Lua.Vm.AtF.Print.r5 (prX sp0 L 0 0 0 0 r 0 0 f m o))
      (ArmPay (prX sp0 L 0 0 0 0 r 0 0 f m o).m (prX sp0 L 0 0 0 0 r 0 0 f m o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Print h acc until [0x800342e4]
  fcx_unfold at h
  have h1 : SegSt 0x800342e4#64 (fwPre 0x8004fb48 1 (sp0 - 64) 0x80022fec#64 (prFr f.s0 f.s1 f.s4 L f))
      (ArmPay m o) _ := h.repin (by pins_of h)
  have hbl := hP.io.buf_lo
  obtain ⟨c2, s2, m1, out1, ph1, H1, hret, P1⟩ :=
    fwrite_print hM (sp0 - 64) 0x8004fb48 1 0x80022fec#64 (prFr f.s0 f.s1 f.s4 L f) m o ph H hP.io hP.heap
      (by decide) (by omega) (by have := hok.sp_al; omega) (by rw [hhe]; omega)
      ⟨by decide, .inl ⟨by decide, by decide⟩⟩ (by omega)
      (fun a h1 h2 => by
        pw_nums
        have e9 : symMallocMallinfo = 0x8005e560 := rfl
        have e4 : symMallocAv = 0x8005c6d0 := rfl
        have e5 : symMallocSbrkBase = 0x8005d388 := rfl
        have e6 : symBrk = 0x8005d3b8 := rfl
        have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
        have : symFiles = 0x8005d760 := rfl
        refine ⟨?_, ?_, ?_⟩
        · simp only [FsGlobal]; omega
        · rintro (hw | ⟨hw, _, _⟩)
          · simp only [MallocGlobal] at hw; omega
          · have : heapStart = 0x8006ecd0 := rfl; omega
        · simp only [SinitW, Rng]; omega)
      (by stdio_nums; omega)
      (fun buf pend he => by
        subst he
        have := hbl buf (by simp only [StdoutPh.Buf, Rng]; omega)
        have : heapStart = 0x8006ecd0 := rfl
        omega) _ h1
  have acc := acc.trans s2
  obtain ⟨buf, pend1, rfl⟩ := P1.up_of (Nat.le_refl 1)
  have hbuf1 : ∀ a, (StdoutPh.up buf pend1).Buf a → 0x8006ecd0 ≤ a := fun a ha => by
    have := P1.phase.buf_lo a ha; have : heapStart = 0x8006ecd0 := rfl; omega
  have hcl1 : PrintCells m1 := hP.cells.keep (by omega) hbuf1 P1.keep
  -- the root after the write
  simp only [wrRet] at hret
  have hX1 : Lua.Vm.AtF.Print.Ok (prX sp0 L 0 0 0 0 r 0 0 f m1 (pushes o out1)) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h2 : SegSt 0x80022fec#64 (Lua.Vm.AtF.Print.r5 (prX sp0 L 0 0 0 0 r 0 0 f m1 (pushes o out1)))
      (ArmPay (prX sp0 L 0 0 0 0 r 0 0 f m1 (pushes o out1)).m
        (prX sp0 L 0 0 0 0 r 0 0 f m1 (pushes o out1)).o) c2 := hret.repin (by pins_of hret)
  have hc0 := hcl1.impure; have hc1 := hcl1.stdout
  fat_run Lua.Vm.AtF.Print h2 acc until [0x80032a1c]
  fcx_unfold at h2
  have h3 : SegSt 0x80032a1c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 stdoutFile⟩] (sp0 - 64) 0x80022ff8#64
      (prFr f.s0 f.s1 f.s4 L f)) (ArmPay m1 (pushes o out1)) _ := h2.repin (by pins_of h2)
  obtain ⟨hs1, hu1, hb1⟩ : StdoutAt m1 buf pend1 ∧ StdioUp m1 ∧ BufOwned H1 buf := by
    cases P1.phase with
    | up hs hu hb => exact ⟨hs, hu, hb⟩
  have hbh := hb1.hi
  obtain ⟨c4, s4, m2, hret2, hsA, huA, hk2⟩ := fflush_stdout (sp0 - 64) buf pend1 0x80022ff8#64
    (prFr f.s0 f.s1 f.s4 L f) m1 (pushes o out1)
    ⟨by decide, by rw [hhe] at hbh; omega, by omega, by have := hok.sp_al; omega⟩ hs1 hu1 _ h3
  have acc := acc.trans s4
  -- the bytes at and above the callees' `sp`
  have kk : ∀ a, sp0 - 64 ≤ a → bytesT1 m2 a = bytesT1 m a := fun a ha =>
    (hk2.keep_hi a ha).trans (P1.keep a (PrintW.not_above (by rw [hhe]; omega) P1.phase.buf_hi ha))
  have k8 : ∀ a, sp0 - 64 ≤ a → bytesT8 m2 a = bytesT8 m a := fun a ha =>
    bytesT8_congrT fun i _ => kk _ (by omega)
  simp only [wrRet] at hret2
  have hX2 : Lua.Vm.AtF.Print.Ok (prX sp0 L 0 0 0 0 r 0 0 f m2 (pushes (pushes o out1) pend1)) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h4 : SegSt 0x80022ff8#64 (Lua.Vm.AtF.Print.r7 (prX sp0 L 0 0 0 0 r 0 0 f m2 (pushes (pushes o out1) pend1)))
      (ArmPay (prX sp0 L 0 0 0 0 r 0 0 f m2 (pushes (pushes o out1) pend1)).m
        (prX sp0 L 0 0 0 0 r 0 0 f m2 (pushes (pushes o out1) pend1)).o) c4 := hret2.repin (by pins_of hret2)
  have hc2 : bytesT8 m2 (sp0 - 8) = r := (k8 _ (by omega)).trans hra
  have hc3 : bytesT8 m2 (sp0 - 32) = f.s2 := (k8 _ (by omega)).trans hs2
  have hc4 : bytesT8 m2 (sp0 - 40) = f.s3 := (k8 _ (by omega)).trans hs3
  fat_run Lua.Vm.AtF.Print h4 acc
  fcx_unfold at h4
  refine ⟨_, m2, out1 ++ pend1, buf, H1, acc, by rw [pushes_append]; exact h4.repin (by pins_of h4), ?_,
    ⟨.up hsA huA hb1, ?_, ?_⟩, P1.kept, fun a ha => ?_⟩
  · have ho := P1.out
    rw [show (StdoutPh.up buf pend1).pend = pend1 from rfl, hP.cells.nl] at ho
    exact ho
  · have hd : heapEnd + 32 + 2048 ≤ sp0 - 64 := by rw [hhe]; omega
    exact P1.heap.ofStdioKeep hb1.block hb1.lo hd fun a h1 h2 h3 h4 =>
      (hk2.keep_lo a h1 h2 h3 h4).trans (bytesT1_fill m1 a).symm
  · exact hcl1.keep (H := H1) (ph := .up buf []) (by omega) (fun a ha => by
      have := hb1.lo; have := ha.1; have : heapStart = 0x8006ecd0 := rfl; omega) hk2.printW
  · exact (hk2.printW (H := H1) a fun hw => ha (PrintW.anti P1.kept hw)).trans
      (P1.keep a fun hw => ha (PrintW.buf_eq (fun _ => Iff.rfl) hw))

end Lua.Vm.Sim.Kit

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
  | up _ _ hb _ => exact Nat.le_trans hb.lo ha.1
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
  have hE : heapEnd = 0x87800000 := rfl
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
  | up _ _ hb _ => exact Nat.lt_of_lt_of_le ha.2 hb.hi
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
  have hE : heapEnd = 0x87800000 := rfl
  rw [hE] at h1; omega

/-- **`luaB_print`'s tail**: `"\n"` (`fwrite_print`), `fflush(stdout)`, the
return. -/
theorem pr_tail (hM : MallocR_Statement) (sp0 L : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (ph : StdoutPh) (H : HeapIx) (hok : PrOk sp0 L r) (hP : PrintSt m ph H)
    (hra : bytesT8 m (sp0 - 8) = r) (hs2 : bytesT8 m (sp0 - 32) = f.s2) (hs3 : bytesT8 m (sp0 - 40) = f.s3)
    (c : Config) (h : SegSt 0x80022fd0#64 (Lua.Vm.AtF.Print.r5 (prX sp0 L 0 0 0 0 r 0 0 f m o)) (ArmPay m o) c) :
    ∃ c' m' out buf H', Steps c c' ∧ wrRet r sp0 0 f m' (pushes o out) c' ∧ out = ph.pend ++ [0x0a#8] ∧
      PrintSt m' (.up buf []) H' ∧ (∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) ∧
      (∀ a, (StdoutPh.up buf []).Buf a → ph.Buf a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ¬ InUse H.chunks a)) ∧
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
  obtain ⟨hs1, hu1, hb1, hr1⟩ : StdoutAt m1 buf pend1 ∧ StdioUp m1 ∧ BufOwned H1 buf ∧ StdioRest m1 := by
    cases P1.phase with
    | up hs hu hb hr => exact ⟨hs, hu, hb, hr⟩
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
    ⟨.up hsA huA hb1 (hr1.congrT fun a ha => by
      have := ha.range; have := hb1.lo; have := hok.nums
      have : heapStart = 0x8006ecd0 := rfl; have : errnoAddr = 0x8005d408 := rfl
      stdio_nums
      exact hk2.keep_lo a (by omega) (by omega) (by omega) (by omega)), ?_, ?_⟩, P1.kept, fun a ha => P1.buf_new a ha, fun a ha => ?_⟩
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

/-! ## What the I/O state reads -/

/-- **What `PrintSt` reads**: the stdio globals, the buffer, the heap off the
chunks in use, `.rodata`'s literals. -/
def PrintFoot (ph : StdoutPh) (H : HeapIx) (a : Nat) : Prop :=
  StdioGlob a ∨ ph.Buf a ∨ (HeapReads a ∧ ¬ InUse H.chunks a) ∨ (0x8004fb48 ≤ a ∧ a < 0x8004ff48)

theorem StdoutFresh.congrA {m m' : Mem} (h : StdoutFresh m) (hk : ∀ a, StdioFoot a → bytesT1 m' a = bytesT1 m a) :
    StdoutFresh m' := by
  stdio_nums
  have : symFsReady = 0x8005d3c0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  have k8 : ∀ a, StdioGlob a → StdioGlob (a + 7) → (∀ i, i < 8 → ¬ AllocWords (a + i)) → bytesT8 m' a = bytesT8 m a := fun a h1 h2 h3 =>
    bytesT8_congrT fun i hi => hk _ ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩
  have k4 : ∀ a, StdioGlob a → StdioGlob (a + 3) → (∀ i, i < 4 → ¬ AllocWords (a + i)) → bytesT4 m' a = bytesT4 m a := fun a h1 h2 h3 =>
    bytesT4_congrT fun i hi => hk _ ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩
  have k2 : ∀ a, StdioGlob a → StdioGlob (a + 1) → (∀ i, i < 2 → ¬ AllocWords (a + i)) → bytesT2 m' a = bytesT2 m a := fun a h1 h2 h3 =>
    bT2_congrT fun i hi => hk _ ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩
  exact ⟨(k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.impure,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.cleanup,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.flags,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.file,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.pad,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.base,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.cookie,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.write,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.flags2,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.fs,
    h.tail.congrT fun a h1 h2 => hk a ⟨⟨by omega, by omega⟩, by aw_off⟩⟩

theorem StdoutAtW.congrA {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} {wv : BitVec 32}
    (h : StdoutAtW m buf pend wv) (hk : ∀ a, StdioFoot a ∨ Rng buf 1024 a → bytesT1 m' a = bytesT1 m a) :
    StdoutAtW m' buf pend wv := by
  stdio_nums
  have : symFsReady = 0x8005d3c0 := rfl
  have : symFds = 0x8005d460 := rfl
  have hr := h.room
  have k8 : ∀ a, StdioGlob a → StdioGlob (a + 7) → (∀ i, i < 8 → ¬ AllocWords (a + i)) → bytesT8 m' a = bytesT8 m a := fun a h1 h2 h3 =>
    bytesT8_congrT fun i hi => hk _ (.inl ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩)
  have k4 : ∀ a, StdioGlob a → StdioGlob (a + 3) → (∀ i, i < 4 → ¬ AllocWords (a + i)) → bytesT4 m' a = bytesT4 m a := fun a h1 h2 h3 =>
    bytesT4_congrT fun i hi => hk _ (.inl ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩)
  have k2 : ∀ a, StdioGlob a → StdioGlob (a + 1) → (∀ i, i < 2 → ¬ AllocWords (a + i)) → bytesT2 m' a = bytesT2 m a := fun a h1 h2 h3 =>
    bT2_congrT fun i hi => hk _ (.inl ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩)
  refine ⟨(k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.p,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.w,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.flags,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.file,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.base,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.size,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.lbf,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.cookie,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.write,
    ?_, h.room, h.buf_lo, h.buf_hi, ?_, (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off).trans h.stdout⟩
  · rw [bytesAt_congr fun i hi => hk _ (.inr ⟨by omega, by omega⟩)]; exact h.bytes
  · rw [k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ fun i _ => by aw_off]; exact h.ready

theorem StdioUp.congrA {m m' : Mem} (h : StdioUp m) (hk : ∀ a, StdioFoot a → bytesT1 m' a = bytesT1 m a) :
    StdioUp m' := by
  stdio_nums
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  refine ⟨(bytesT8_congrT fun i _ => hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩).trans h.impure, ?_,
    (bytesT4_congrT fun i _ => hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩).trans h.flags2,
    h.tail.congrT fun a h1 h2 => hk a ⟨⟨by omega, by omega⟩, by aw_off⟩,
    h.fds.congrT fun a h1 h2 => hk a ⟨⟨by have : symFds = 0x8005d460 := rfl; omega,
      by have : symFds = 0x8005d460 := rfl; omega⟩, by have : symFds = 0x8005d460 := rfl; aw_off⟩⟩
  rw [bytesT8_congrT fun i _ => hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩]; exact h.init

theorem StdoutFresh.congrT {m m' : Mem} (h : StdoutFresh m) (hk : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a) :
    StdoutFresh m' := h.congrA fun a ha => hk a ha.1

theorem StdoutAtW.congrT {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} {wv : BitVec 32}
    (h : StdoutAtW m buf pend wv) (hk : ∀ a, StdioGlob a ∨ Rng buf 1024 a → bytesT1 m' a = bytesT1 m a) :
    StdoutAtW m' buf pend wv := h.congrA fun a ha => hk a (ha.imp_left fun h => h.1)

theorem StdioUp.congrT {m m' : Mem} (h : StdioUp m) (hk : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a) :
    StdioUp m' := h.congrA fun a ha => hk a ha.1

/-- A `RestFoot` byte is one the stdio state reads. -/
theorem RestFoot.foot {a : Nat} (h : RestFoot a) : StdioFoot a := by
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : fileSize = 184 := rfl
  simp only [RestFoot, stdinFile, stderrFile] at h
  exact ⟨⟨by omega, by omega⟩, by aw_off⟩

/-- The heap room of `stdout`'s phases before the buffer. -/
theorem StdoutIn.room {m : Mem} {H : HeapIx} {ph : StdoutPh} (h : StdoutIn m H ph)
    (hn : ∀ buf pend, ph ≠ .up buf pend) : H.brk + 1024 + 16384 ≤ heapEnd := by
  cases h with
  | boot _ _ hr => exact hr
  | fresh _ hr _ => exact hr
  | up => exact absurd rfl (hn _ _)

/-- (lane F1-14) **`stdout`'s phase across a change off what it reads**
(`StdioFoot`: the stdio globals but the allocator's words; the buffer), with
a new heap that keeps the buffer and the room. -/
theorem StdoutIn.congrA {m m' : Mem} {H H' : HeapIx} {ph : StdoutPh} (h : StdoutIn m H ph)
    (hk : ∀ a, StdioFoot a ∨ ph.Buf a → bytesT1 m' a = bytesT1 m a)
    (hroom : (∀ buf pend, ph ≠ .up buf pend) → H'.brk + 1024 + 16384 ≤ heapEnd)
    (hown : ∀ buf, BufOwned H buf → BufOwned H' buf) : StdoutIn m' H' ph := by
  have hg : ∀ a, StdioFoot a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a (.inl ha)
  have hgf : ∀ a, StdioFoot a → (fillZeroMem m')[a]? = (fillZeroMem m)[a]? := fun a ha =>
    fill_total ⟨by simp only [ramBase]; have := ha.1.1; omega, by simp only [ramBase, ramSize]; have := ha.1.2; omega⟩
      (hg a ha)
  cases h with
  | boot hB hMf _ => exact .boot (hB.congrF hgf) (hMf.congrF hgf) (hroom fun _ _ h => by cases h)
  | fresh hF _ hR =>
    exact .fresh (hF.congrA hg) (hroom fun _ _ h => by cases h) (hR.congrT fun a ha => hg a ha.foot)
  | up hs hu hb hR =>
    exact .up (hs.congrA fun a ha => ha.elim (hg a) fun hb' => hk a (.inr hb')) (hu.congrA hg) (hown _ hb)
      (hR.congrT fun a ha => hg a ha.foot)

/-- **The I/O state across a change off what it reads.** -/
theorem PrintSt.keep {m m' : Mem} {ph : StdoutPh} {H : HeapIx} (h : PrintSt m ph H)
    (hk : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a) : PrintSt m' ph H := by
  have hg : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a (.inl ha)
  have hgf : ∀ a, StdioGlob a → (fillZeroMem m')[a]? = (fillZeroMem m)[a]? := fun a ha =>
    fill_total ⟨by simp only [ramBase]; have := ha.1; omega, by simp only [ramBase, ramSize]; have := ha.2; omega⟩
      (hg a ha)
  refine ⟨?_, h.heap.ofTotal fun a hr hu => (hk a (.inr (.inr (.inl ⟨hr, hu⟩)))).trans (bytesT1_fill m a).symm,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · exact h.io.congrA (fun a ha => ha.elim (fun h => hg a h.1) fun hb => hk a (.inr (.inl hb))) h.io.room
      fun _ hb => hb
  · exact (bytesT8_congrT fun i _ => hg _ ⟨by omega, by omega⟩).trans h.cells.impure
  · exact (bytesT8_congrT fun i _ => hg _ ⟨by omega, by omega⟩).trans h.cells.stdout
  · rw [bytesAt_congr fun i hi => hk _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))]; exact h.cells.tab
  · rw [bytesAt_congr fun i hi => hk _ (.inr (.inr (.inr ⟨by omega, by omega⟩)))]; exact h.cells.nl

/-! ## The Lua side, abstract -/

/-- The line `luaB_print` writes before the newline: the arguments' bytes,
tab-separated. -/
def prLine (bs : Nat → List (BitVec 8)) : Nat → List (BitVec 8)
  | 0 => []
  | 1 => bs 1
  | k + 2 => prLine bs (k + 1) ++ 0x09#8 :: bs (k + 2)

/-- What is written before argument `i`'s string: the line so far and its tab. -/
def prPre (bs : Nat → List (BitVec 8)) (i : Nat) : List (BitVec 8) :=
  prLine bs (i - 1) ++ (if 2 ≤ i then [0x09#8] else [])

theorem prLine_pre (bs : Nat → List (BitVec 8)) {i : Nat} (hi : 1 ≤ i) :
    prLine bs i = prPre bs i ++ bs i := by
  match i, hi with
  | 1, _ => simp [prLine, prPre]
  | k + 2, _ => simp [prLine, prPre]

/-- A buffer that is either the old phase's or a fresh block. -/
def BufFrom (ph ph' : StdoutPh) (H : HeapIx) : Prop :=
  ∀ a, ph'.Buf a → ph.Buf a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ¬ InUse H.chunks a)

/-- **What `luaL_tolstring(L, i, &l)` leaves** for `luaB_print` (argument
`i` printing as `b`): the Lua state with one more value, `stdout` as it was,
the heap's chunks in use kept, the frame but the length word, the length,
the string, where it lies. -/
structure TolPost (sp0 n : Nat) (S : Nat → StdoutPh → HeapIx → Mem → Prop) (b : List (BitVec 8))
    (ph : StdoutPh) (m m' : Mem) (s : Nat) (H H' : HeapIx) : Prop where
  lua : S (n + 1) ph H' m'
  io : PrintSt m' ph H'
  kept : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks
  frame : ∀ a, sp0 - 64 ≤ a → (a < sp0 - 56 ∨ sp0 - 48 ≤ a) → bytesT1 m' a = bytesT1 m a
  len : bytesT8 m' (sp0 - 56) = BitVec.ofNat 64 b.length
  bytes : bytesAt m' s b.length = b
  src_lo : SrcLo s b.length
  src_hi : s + b.length + 4096 ≤ sp0 - 64
  /-- the string and its terminator -/
  src_ok : ∀ a, s ≤ a → a < s + b.length + 1 → ¬ FsGlobal a ∧ ¬ MallocW H'.chunks a ∧ ¬ SinitW a
  src_out : s + b.length ≤ stdoutFile ∨ stdoutFile + fileSize ≤ s
  src_buf : ∀ a, s ≤ a → a < s + b.length + 1 → ¬ ph.Buf a

/-- **`luaB_print`'s Lua-side callees** (the named premises a value class
discharges), over the Lua state `S i k ph H m` (before argument `i`'s
string, lane F1-18: so `S` carries a per-argument budget; `k` values above the
called function, `stdout`'s phase `ph`, the heap `H`) and the bytes `bs i`
argument `i` prints: `lua_gettop`, `luaL_tolstring` (from `S i` to `S (i +
1)`), `lua_settop(L, -2)`, and `S` stable under what a write of `stdout` may
change (with the room a write keeps, `PrintPost.room`). -/
structure PrintLua (L sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8)) :
    Prop where
  n_lt : n + 1 < 2 ^ 31
  gettop : ∀ (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
    S 1 n ph H m → r.toNat % 4 = 0 →
    Triple (SegSt 0x80001bb4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp0 - 64) r f) (ArmPay m o))
      (wrRet r (sp0 - 64) n f m o)
  tolstring : ∀ (i : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64)
    (f : AbiFrame), 1 ≤ i → i ≤ n → S i n ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧ TolPost sp0 n (S (i + 1)) (bs i) ph m m' s H H')
  settop : ∀ (i : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
    S i (n + 1) ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
    Triple (SegSt 0x80001bd4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (2 ^ 64 - 2)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m', apiRet r (sp0 - 64) f m' o c ∧ S i n ph H m' ∧ PrintSt m' ph H ∧
        ∀ a, sp0 - 64 ≤ a → bytesT1 m' a = bytesT1 m a)
  stable : ∀ (i k : Nat) (ph ph' : StdoutPh) (H H' : HeapIx) (m m' : Mem), S i k ph H m →
    (∀ a, ¬ (PrintW (sp0 - 64) H ph' a ∨ Rng (sp0 - 64) 64 a) → bytesT1 m' a = bytesT1 m a) →
    BufFrom ph ph' H →
    (∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) →
    (i ≤ n → ∀ b, PrRoom b ph H → PrRoom b ph' H') → S i k ph' H' m'

/-- `luaB_print`'s saved words (after its first `luaL_tolstring`'s set-up). -/
structure PrFrame (m : Mem) (sp0 : Nat) (r : BitVec 64) (f : AbiFrame) : Prop where
  ra : bytesT8 m (sp0 - 8) = r
  s0 : bytesT8 m (sp0 - 16) = f.s0
  s1 : bytesT8 m (sp0 - 24) = f.s1
  s2 : bytesT8 m (sp0 - 32) = f.s2
  s3 : bytesT8 m (sp0 - 40) = f.s3
  s4 : bytesT8 m (sp0 - 48) = f.s4

theorem PrFrame.keep {m m' : Mem} {sp0 : Nat} {r : BitVec 64} {f : AbiFrame} (h : PrFrame m sp0 r f)
    (hsp : 64 ≤ sp0) (hk : ∀ a, sp0 - 64 ≤ a → (a < sp0 - 56 ∨ sp0 - 48 ≤ a) → bytesT1 m' a = bytesT1 m a) :
    PrFrame m' sp0 r f :=
  ⟨(bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ra,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s0,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s1,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s2,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s3,
   (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.s4⟩

/-- `addiw s0, s0, 1` on a small count. -/
theorem addiw_ofNat (i : Nat) (h : i + 1 < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12)) 31 0) =
      BitVec.ofNat 64 (i + 1) := by
  have e : (BitVec.ofNat 64 i) + sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (i + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    rw [show (sign_extend (m := 64) (0x001#12)).toNat = 1 by decide]
    omega
  rw [e]; exact sext32_ofNat _ h

/-- `bge s4, s0` on small counts. -/
theorem sge_ofNat (n j : Nat) (hn : n < 2 ^ 31) (hj : j < 2 ^ 31) :
    zopz0zKzJ_s (BitVec.ofNat 64 n) (BitVec.ofNat 64 j) = decide (j ≤ n) := by
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_small _ (by omega), toInt_ofNat_small _ (by omega)]
  by_cases h : j ≤ n
  · simp only [h, decide_true]; simp; omega
  · simp only [h, decide_false]; simp; omega

/-! ## The loop -/

/-- **What `luaB_print` leaves**: the console gained the pending bytes, the
line and the newline; `stdout` set up and flushed; the Lua state; the chunks
in use kept; the caller's frames. -/
structure PrEnd (sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (m0 : Mem) (ph0 : StdoutPh) (H0 : HeapIx) (m : Mem) (out : List (BitVec 8)) : Prop where
  out : out = ph0.pend ++ prLine bs n ++ [0x0a#8]
  st : ∃ buf H, PrintSt m (.up buf []) H ∧ S (n + 1) n (.up buf []) H m ∧ (∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks)
  above : ∀ a, sp0 ≤ a → bytesT1 m a = bytesT1 m0 a

/-- **The loop head** (`luaL_tolstring` of argument `i ≥ 2` next). -/
structure PrHead (sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx)
    (i : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx) : Prop where
  i_ge : 2 ≤ i
  i_le : i ≤ n
  lua : S i n ph H m
  io : PrintSt m ph H
  frame : PrFrame m sp0 r f
  console : ∃ out, o = pushes o0 out ∧ out ++ ph.pend = ph0.pend ++ prLine bs (i - 1)
  kept : ∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks
  above : ∀ a, sp0 ≤ a → bytesT1 m a = bytesT1 m0 a

/-- **Before argument `i`'s string is written** (`0x80022f8c`): `s` holds
its bytes, the length word its length, the separator written. -/
structure PrMid (sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx)
    (i s : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx) : Prop where
  i_ge : 1 ≤ i
  i_le : i ≤ n
  lua : S (i + 1) (n + 1) ph H m
  io : PrintSt m ph H
  frame : PrFrame m sp0 r f
  len : bytesT8 m (sp0 - 56) = BitVec.ofNat 64 (bs i).length
  bytes : bytesAt m s (bs i).length = bs i
  src_lo : SrcLo s (bs i).length
  src_hi : s + (bs i).length + 4096 ≤ sp0 - 64
  src_ok : ∀ a, s ≤ a → a < s + (bs i).length + 1 → ¬ FsGlobal a ∧ ¬ MallocW H.chunks a ∧ ¬ SinitW a
  src_out : s + (bs i).length ≤ stdoutFile ∨ stdoutFile + fileSize ≤ s
  src_buf : ∀ a, s ≤ a → a < s + (bs i).length + 1 → ¬ ph.Buf a
  console : ∃ out, o = pushes o0 out ∧ out ++ ph.pend = ph0.pend ++ prPre bs i
  kept : ∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks
  above : ∀ a, sp0 ≤ a → bytesT1 m a = bytesT1 m0 a

/-- **`luaB_print` returned**, leaving `PrEnd`. -/
def PrFin (sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx)
    (c : Config) : Prop :=
  ∃ m' out, wrRet r sp0 0 f m' (pushes o0 out) c ∧ PrEnd sp0 n S bs m0 ph0 H0 m' out

/-- **At the loop head of argument `i`** (`PrHead`, the machine at `0x80022f68`). -/
def PrAtHead (L sp0 n : Nat) (S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx) (i : Nat)
    (c : Config) : Prop :=
  ∃ (w13 : BitVec 64) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx),
    PrHead sp0 n S bs r f m0 o0 ph0 H0 i m o ph H ∧
    SegSt 0x80022f68#64 (Lua.Vm.AtF.Print.r16 (prX sp0 L n 0 0 i r w13 0 f m o)) (ArmPay m o) c

/-- The stack at and above the callees' `sp` is no write's. -/
theorem PrintSt.above {m : Mem} {ph : StdoutPh} {H : HeapIx} (hP : PrintSt m ph H) {sp a : Nat}
    (hsp : heapEnd ≤ sp) (ha : sp ≤ a) : ¬ PrintW sp H ph a :=
  PrintW.not_above hsp hP.io.buf_hi ha

/-- **Argument `i`'s string, `lua_pop`, the loop test**: on to the head of
argument `i + 1`, or the tail. -/
theorem pr_mid (hM : MallocR_Statement) {L sp0 n : Nat} {S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop}
    {bs : Nat → List (BitVec 8)} (hL : PrintLua L sp0 n S bs) (r : BitVec 64) (f : AbiFrame) (m0 : Mem)
    (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx) (hok : PrOk sp0 L r)
    (i s : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx)
    (hm : PrMid sp0 n S bs r f m0 o0 ph0 H0 i s m o ph H) :
    Triple (SegSt 0x80022f8c#64 (Lua.Vm.AtF.Print.r20 (prX sp0 L n s (bs i).length i r 0 0 f m o)) (ArmPay m o))
      (fun c' => PrAtHead L sp0 n S bs r f m0 o0 ph0 H0 (i + 1) c' ∨ PrFin sp0 n S bs r f m0 o0 ph0 H0 c') := by
  intro c h
  have q := hok.nums
  have q2 := hok.sp_hi
  have hhe : heapEnd = 0x87800000 := rfl
  have hnl := hL.n_lt
  have hi1 := hm.i_ge; have hin := hm.i_le
  have hX : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n s (bs i).length i r 0 0 f m o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have hc0 := hm.io.cells.impure; have hc1 := hm.io.cells.stdout; have hc5 := hm.len
  have h : SegSt 0x80022f8c#64 (Lua.Vm.AtF.Print.r20 (prX sp0 L n s (bs i).length i r 0 0 f m o))
      (ArmPay (prX sp0 L n s (bs i).length i r 0 0 f m o).m (prX sp0 L n s (bs i).length i r 0 0 f m o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Print h acc until [0x800342e4]
  fcx_unfold at h
  rw [addiw_ofNat i (by omega)] at h
  have h1 : SegSt 0x800342e4#64 (fwPre s (bs i).length (sp0 - 64) 0x80022fa8#64
      (prFr (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 s) (BitVec.ofNat 64 n) L f)) (ArmPay m o) _ :=
    h.repin (by pins_of h)
  -- argument `i`'s string
  obtain ⟨c2, s2, m1, out1, ph1, H1, hret, P1⟩ :=
    fwrite_print hM (sp0 - 64) s (bs i).length 0x80022fa8#64
      (prFr (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 s) (BitVec.ofNat 64 n) L f) m o ph H hm.io.io hm.io.heap
      (by decide) (by omega) (by have := hok.sp_al; omega) (by rw [hhe]; omega) hm.src_lo hm.src_hi
      (fun a h1 h2 => hm.src_ok a h1 (by omega)) hm.src_out (fun buf pend he => by
        subst he
        by_cases hh : s < buf
        · exact .inl (Classical.byContradiction fun hn =>
            hm.src_buf buf (by omega) (by omega) ⟨Nat.le_refl _, by omega⟩)
        · exact .inr (Classical.byContradiction fun hn =>
            hm.src_buf s (Nat.le_refl _) (by omega) ⟨by omega, by omega⟩)) _ h1
  have acc := acc.trans s2
  have hS1 : S (i + 1) (n + 1) ph1 H1 m1 := hL.stable _ _ _ _ _ _ _ _ hm.lua
    (fun a ha => P1.keep a fun hw => ha (.inl hw)) P1.buf_new P1.kept fun _ => P1.room
  have hbuf1 : ∀ a, ph1.Buf a → 0x8006ecd0 ≤ a := fun a ha => by
    have := P1.phase.buf_lo a ha; have : heapStart = 0x8006ecd0 := rfl; omega
  have hP1 : PrintSt m1 ph1 H1 := ⟨P1.phase, P1.heap, hm.io.cells.keep (by omega) hbuf1 P1.keep⟩
  have kk1 : ∀ a, sp0 - 64 ≤ a → bytesT1 m1 a = bytesT1 m a := fun a ha =>
    P1.keep a (PrintW.not_above (by rw [hhe]; omega) P1.phase.buf_hi ha)
  -- `lua_pop(L, 1)`
  simp only [wrRet] at hret
  have hX1 : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m1
      (pushes o out1)) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h2 : SegSt 0x80022fa8#64 (Lua.Vm.AtF.Print.r22 (prX sp0 L n s (bs i).length i r 0
      (BitVec.ofNat 64 (i + 1)) f m1 (pushes o out1)))
      (ArmPay (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m1 (pushes o out1)).m
        (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m1 (pushes o out1)).o) c2 :=
    hret.repin (by pins_of hret)
  fat_run Lua.Vm.AtF.Print h2 acc until [0x80001bd4]
  fcx_unfold at h2
  have h3 : SegSt 0x80001bd4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
      ⟨Register.x11, BitVec.ofNat 64 (2 ^ 64 - 2)⟩] (sp0 - 64) 0x80022fb4#64
      (prFr (BitVec.ofNat 64 (i + 1)) (BitVec.ofNat 64 s) (BitVec.ofNat 64 n) L f)) (ArmPay m1 (pushes o out1)) _ :=
    h2.repin (by pins_of h2)
  obtain ⟨c3, s3, m2, hret3, hS2, hP2, kk2⟩ := hL.settop (i + 1) ph1 H1 m1 (pushes o out1) 0x80022fb4#64 _ hS1 hP1
    (by decide) _ h3
  have acc := acc.trans s3
  simp only [apiRet] at hret3
  have hX2 : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m2
      (pushes o out1)) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h4 : SegSt 0x80022fb4#64 (Lua.Vm.AtF.Print.r22 (prX sp0 L n s (bs i).length i r 0
      (BitVec.ofNat 64 (i + 1)) f m2 (pushes o out1)))
      (ArmPay (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m2 (pushes o out1)).m
        (prX sp0 L n s (bs i).length i r 0 (BitVec.ofNat 64 (i + 1)) f m2 (pushes o out1)).o) c3 :=
    hret3.repin (by pins_of hret3)
  have kk : ∀ a, sp0 - 64 ≤ a → bytesT1 m2 a = bytesT1 m a := fun a ha => (kk2 a ha).trans (kk1 a ha)
  have hF2 : PrFrame m2 sp0 r f := hm.frame.keep (by omega) fun a ha _ => kk a ha
  obtain ⟨out, ho, hout⟩ := hm.console
  have hout1 : (out ++ out1) ++ ph1.pend = ph0.pend ++ prLine bs i := by
    rw [List.append_assoc, P1.out, ← List.append_assoc, hout, hm.bytes, List.append_assoc,
      ← prLine_pre bs hi1]
  have habove : ∀ a, sp0 ≤ a → bytesT1 m2 a = bytesT1 m0 a := fun a ha =>
    (kk a (by omega)).trans (hm.above a ha)
  by_cases hni : i + 1 ≤ n
  · have hg : zopz0zKzJ_s (BitVec.ofNat 64 n) (BitVec.ofNat 64 (i + 1)) = true := by
      rw [sge_ofNat n (i + 1) (by omega) (by omega)]; simp [hni]
    fat_run Lua.Vm.AtF.Print h4 acc until [0x80022f68]
    fcx_unfold at h4
    refine ⟨_, acc, .inl ⟨BitVec.ofNat 64 s, m2, pushes o out1, ph1, H1, ⟨by omega, hni, hS2, hP2, hF2,
      ⟨out ++ out1, by rw [ho, pushes_append], by rw [hout1]; rfl⟩,
      fun c hc hu => P1.kept c (hm.kept c hc hu) hu, habove⟩, h4.repin (by pins_of h4)⟩⟩
  · have hni' : i = n := by omega
    subst hni'
    have hg : zopz0zKzJ_s (BitVec.ofNat 64 i) (BitVec.ofNat 64 (i + 1)) = false := by
      rw [sge_ofNat i (i + 1) (by omega) (by omega)]; simp
    have hc6 := hF2.s0; have hc7 := hF2.s1; have hc8 := hF2.s4
    fat_run Lua.Vm.AtF.Print h4 acc until [0x80022fd0]
    fcx_unfold at h4
    obtain ⟨c5, m3, out2, buf, H2, s5, hret5, hout2, hP3, hk3, hb3, kk3⟩ :=
      pr_tail hM sp0 L r f m2 (pushes o out1) ph1 H1 hok hP2 hF2.ra hF2.s2 hF2.s3 _ (h4.repin (by pins_of h4))
    refine ⟨_, acc.trans s5, .inr ⟨m3, out ++ out1 ++ out2, by rw [pushes_append, pushes_append, ← ho]; exact hret5,
      ⟨?_, ⟨buf, H2, hP3, hL.stable _ _ _ _ _ _ _ _ hS2 (fun a ha => kk3 a fun hw => ha (.inl hw)) hb3 hk3
          (fun h => absurd h (by omega)), fun c hc hu => hk3 c (P1.kept c (hm.kept c hc hu) hu) hu⟩,
        fun a ha => ?_⟩⟩⟩
    · rw [hout2, ← List.append_assoc, hout1]
    · exact (kk3 a (PrintW.not_above (sp := sp0 - 64) (by rw [hhe]; omega) hP3.io.buf_hi (by omega))).trans (habove a ha)

/-- **A string written after `luaL_tolstring`'s set-up** stays apart from a
write (`PrintW`) whose buffer is the old one or fresh. -/
theorem src_apart {s len sp : Nat} {H : HeapIx} {ph ph' : StdoutPh}
    (hok : ∀ a, s ≤ a → a < s + len + 1 → ¬ FsGlobal a ∧ ¬ MallocW H.chunks a ∧ ¬ SinitW a)
    (hbuf : ∀ a, s ≤ a → a < s + len + 1 → ¬ ph.Buf a) (hout : s + len ≤ stdoutFile ∨ stdoutFile + fileSize ≤ s)
    (hsp : s + len + 4096 ≤ sp) (hB : BufFrom ph ph' H) :
    ∀ a, s ≤ a → a < s + len → ¬ PrintW sp H ph' a := by
  intro a h1 h2 hw
  have ⟨g, w, si⟩ := hok a h1 (by omega)
  rcases hw with hw | hw | hw | hw | hw | hw
  · exact g hw
  · exact w hw
  · exact si hw
  · simp only [Rng] at hw; stdio_nums; omega
  · rcases hB a hw with hb | ⟨l1, l2, l3⟩
    · exact hbuf a h1 (by omega) hb
    · exact w (.inr ⟨l1, l2, l3⟩)
  · simp only [Below] at hw; omega

/-- **The loop's body**: `luaL_tolstring(L, i, &l)`, the tab, then `pr_mid`. -/
theorem pr_step (hM : MallocR_Statement) {L sp0 n : Nat} {S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop}
    {bs : Nat → List (BitVec 8)} (hL : PrintLua L sp0 n S bs) (r : BitVec 64) (f : AbiFrame) (m0 : Mem)
    (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx) (hok : PrOk sp0 L r)
    (i : Nat) (w13 : BitVec 64) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx)
    (hh : PrHead sp0 n S bs r f m0 o0 ph0 H0 i m o ph H) :
    Triple (SegSt 0x80022f68#64 (Lua.Vm.AtF.Print.r16 (prX sp0 L n 0 0 i r w13 0 f m o)) (ArmPay m o))
      (fun c' => PrAtHead L sp0 n S bs r f m0 o0 ph0 H0 (i + 1) c' ∨ PrFin sp0 n S bs r f m0 o0 ph0 H0 c') := by
  intro c h
  have q := hok.nums
  have q2 := hok.sp_hi
  have hhe : heapEnd = 0x87800000 := rfl
  have hnl := hL.n_lt
  have hi2 := hh.i_ge; have hin := hh.i_le
  have hX : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n 0 0 i r w13 0 f m o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h : SegSt 0x80022f68#64 (Lua.Vm.AtF.Print.r16 (prX sp0 L n 0 0 i r w13 0 f m o))
      (ArmPay (prX sp0 L n 0 0 i r w13 0 f m o).m (prX sp0 L n 0 0 i r w13 0 f m o).o) c := h
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Print h acc until [0x80021b2c]
  fcx_unfold at h
  have h1 : SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
      ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) 0x80022f6c#64
      (prFr (BitVec.ofNat 64 i) w13 (BitVec.ofNat 64 n) L f)) (ArmPay m o) _ := h.repin (by pins_of h)
  -- `luaL_tolstring(L, i, &l)`
  obtain ⟨c1, s1, m1, s, H1, hret, T⟩ := hL.tolstring i ph H m o 0x80022f6c#64 _ (by omega) hin hh.lua hh.io
    (by decide) _ h1
  have acc := acc.trans s1
  simp only [wrRet] at hret
  have hX1 : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n s 0 i r w13 0 f m1 o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h2 : SegSt 0x80022f6c#64 (Lua.Vm.AtF.Print.r18 (prX sp0 L n s 0 i r w13 0 f m1 o))
      (ArmPay (prX sp0 L n s 0 i r w13 0 f m1 o).m (prX sp0 L n s 0 i r w13 0 f m1 o).o) c1 :=
    hret.repin (by pins_of hret)
  have hc0 := T.io.cells.impure; have hc1 := T.io.cells.stdout
  fat_run Lua.Vm.AtF.Print h2 acc until [0x800342e4]
  fcx_unfold at h2
  have h3 : SegSt 0x800342e4#64 (fwPre 0x8004ff40 1 (sp0 - 64) 0x80022f8c#64
      (prFr (BitVec.ofNat 64 i) (BitVec.ofNat 64 s) (BitVec.ofNat 64 n) L f)) (ArmPay m1 o) _ :=
    h2.repin (by pins_of h2)
  -- the tab
  have hbl := T.io.io.buf_lo
  obtain ⟨c3, s3, m2, out2, ph2, H2, hret3, P2⟩ :=
    fwrite_print hM (sp0 - 64) 0x8004ff40 1 0x80022f8c#64
      (prFr (BitVec.ofNat 64 i) (BitVec.ofNat 64 s) (BitVec.ofNat 64 n) L f) m1 o ph H1 T.io.io T.io.heap
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
        omega) _ h3
  have acc := acc.trans s3
  simp only [wrRet] at hret3
  have hX2 : Lua.Vm.AtF.Print.Ok_L (prX sp0 L n s (bs i).length i r 0 0 f m2 (pushes o out2)) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h4 : SegSt 0x80022f8c#64 (Lua.Vm.AtF.Print.r20 (prX sp0 L n s (bs i).length i r 0 0 f m2 (pushes o out2)))
      (ArmPay m2 (pushes o out2)) c3 := hret3.repin (by pins_of hret3)
  -- the state before the string
  have hbuf2 : ∀ a, ph2.Buf a → 0x8006ecd0 ≤ a := fun a ha => by
    have := P2.phase.buf_lo a ha; have : heapStart = 0x8006ecd0 := rfl; omega
  have kk2 : ∀ a, sp0 - 64 ≤ a → bytesT1 m2 a = bytesT1 m1 a := fun a ha =>
    P2.keep a (PrintW.not_above (by rw [hhe]; omega) P2.phase.buf_hi ha)
  have hap := src_apart T.src_ok T.src_buf T.src_out T.src_hi P2.buf_new
  obtain ⟨out, ho, hout⟩ := hh.console
  have hm : PrMid sp0 n S bs r f m0 o0 ph0 H0 i s m2 (pushes o out2) ph2 H2 :=
    { i_ge := by omega
      i_le := hin
      lua := hL.stable _ _ _ _ _ _ _ _ T.lua (fun a ha => P2.keep a fun hw => ha (.inl hw)) P2.buf_new P2.kept
        fun _ => P2.room
      io := ⟨P2.phase, P2.heap, T.io.cells.keep (by omega) hbuf2 P2.keep⟩
      frame := (hh.frame.keep (by omega) T.frame).keep (by omega) fun a ha _ => kk2 a ha
      len := (bytesT8_congrT fun j _ => kk2 _ (by omega)).trans T.len
      bytes := by rw [bytesAt_congr fun j hj => P2.keep _ (hap _ (by omega) (by omega))]; exact T.bytes
      src_lo := T.src_lo
      src_hi := T.src_hi
      src_ok := fun a h1 h2 => ⟨(T.src_ok a h1 h2).1, fun hw => (T.src_ok a h1 h2).2.1 (MallocW.anti P2.kept hw),
        (T.src_ok a h1 h2).2.2⟩
      src_out := T.src_out
      src_buf := fun a h1 h2 hb => by
        rcases P2.buf_new a hb with hb' | ⟨l1, l2, l3⟩
        · exact T.src_buf a h1 h2 hb'
        · exact (T.src_ok a h1 h2).2.1 (.inr ⟨l1, l2, l3⟩)
      console := ⟨out ++ out2, by rw [ho, pushes_append], by
        rw [List.append_assoc, P2.out, T.io.cells.tab, ← List.append_assoc, hout]
        simp only [prPre, show 2 ≤ i from hi2, ite_true, List.append_assoc]⟩
      kept := fun c hc hu => P2.kept c (T.kept c (hh.kept c hc hu) hu) hu
      above := fun a ha => (kk2 a (by omega)).trans ((T.frame a (by omega) (by omega)).trans (hh.above a ha)) }
  obtain ⟨c5, s5, hr⟩ := pr_mid hM hL r f m0 o0 ph0 H0 hok i s m2 (pushes o out2) ph2 H2 hm c3 h4
  exact ⟨c5, acc.trans s5, hr⟩

/-- **The loop** (`seg_loop` on `n + 1 - i`): from the head of argument `i`,
the return. -/
theorem pr_loop (hM : MallocR_Statement) {L sp0 n : Nat} {S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop}
    {bs : Nat → List (BitVec 8)} (hL : PrintLua L sp0 n S bs) (r : BitVec 64) (f : AbiFrame) (m0 : Mem)
    (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx) (hok : PrOk sp0 L r) :
    ∀ i, Triple (PrAtHead L sp0 n S bs r f m0 o0 ph0 H0 i) (PrFin sp0 n S bs r f m0 o0 ph0 H0) := by
  refine seg_loop (fun i => n + 1 - i) fun i c ⟨w13, m, o, ph, H, hh, h⟩ => ?_
  obtain ⟨c', s', hr⟩ := pr_step hM hL r f m0 o0 ph0 H0 hok i w13 m o ph H hh c h
  refine ⟨c', s', ?_⟩
  rcases hr with hn | hend
  · exact .inl ⟨i + 1, by have := hh.i_le; omega, hn⟩
  · exact .inr hend

/-- The memory after stores to `luaB_print`'s own frame `[sp0 - 64, sp0)`. -/
theorem pr_framed {m M : Mem} {sp0 : Nat} (h : ∀ a, (a < sp0 - 64 ∨ sp0 ≤ a) → M[a]? = m[a]?) (hsp : heapEnd + 128 ≤ sp0)
    {ph : StdoutPh} {H : HeapIx} (hP : PrintSt m ph H) :
    PrintSt M ph H ∧ ∀ a, ¬ (PrintW (sp0 - 64) H ph a ∨ Rng (sp0 - 64) 64 a) → bytesT1 M a = bytesT1 m a := by
  have hhe : heapEnd = 0x87800000 := rfl
  refine ⟨hP.keep fun a ha => bT1_congr (h a (.inl ?_)), fun a ha => bT1_congr (h a ?_)⟩
  · have hb := hP.io.buf_hi
    rw [hhe] at hsp hb
    rcases ha with ha | ha | ⟨ha, _⟩ | ha
    · simp only [StdioGlob] at ha; omega
    · have := hb a ha; omega
    · have e4 : symMallocAv = 0x8005c6d0 := rfl
      have e5 : symMallocSbrkBase = 0x8005d388 := rfl
      have e6 : symBrk = 0x8005d3b8 := rfl
      have e7 : symMallocTopPad = 0x8005d3d8 := rfl
      have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
      have e9 : symMallocMallinfo = 0x8005e560 := rfl
      have e2 : heapStart = 0x8006ecd0 := rfl
      simp only [HeapReads] at ha; rw [hhe] at ha; omega
    · omega
  · simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    by_cases h1 : sp0 - 64 ≤ a
    · exact .inr (Nat.le_trans (by omega) (ha.2 h1))
    · exact .inl (by omega)

/-- **`luaB_print(L)`** from its Lua-side callees (`PrintLua`): the console
gains `stdout`'s pending bytes, the arguments' bytes tab-separated, and the
newline; `stdout` is set up and flushed; the Lua state holds again; the
chunks in use are kept; the caller's frames are kept. -/
theorem print_sum (hM : MallocR_Statement) {L sp0 n : Nat} {S : Nat → Nat → StdoutPh → HeapIx → Mem → Prop}
    {bs : Nat → List (BitVec 8)} (hL : PrintLua L sp0 n S bs) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (ph : StdoutPh) (H : HeapIx) (hok : PrOk sp0 L r) (hS : S 1 n ph H m)
    (hP : PrintSt m ph H) :
    Triple (SegSt 0x80022f18#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] sp0 r f) (ArmPay m o))
      (PrFin sp0 n S bs r f m o ph H) := by
  intro c h
  have q := hok.nums
  have q2 := hok.sp_hi
  have hhe : heapEnd = 0x87800000 := rfl
  have hnl := hL.n_lt
  have hX : Lua.Vm.AtF.Print.Ok (prX sp0 L n 0 0 0 r 0 0 f m o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80022f18#64 (Lua.Vm.AtF.Print.r0 (prX sp0 L n 0 0 0 r 0 0 f m o))
      (ArmPay (prX sp0 L n 0 0 0 r 0 0 f m o).m (prX sp0 L n 0 0 0 r 0 0 f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Print h acc until [0x80001bb4]
  fcx_unfold at h
  -- the entry's stores: `ra`, `s2`, `s3`
  have hM0 : ∀ a, (a < sp0 - 64 ∨ sp0 ≤ a) →
      (Lua.Vm.AtF.Print.m0 (prX sp0 L n 0 0 0 r 0 0 f m o))[a]? = m[a]? := by
    intro a ha; fcx_unfold
    simp (disch := omega) only [getElem?_writeMap8_out]
  obtain ⟨hP0, kk0⟩ := pr_framed hM0 (by rw [hhe]; omega) hP
  have hS0 := hL.stable _ _ _ _ _ _ _ _ hS kk0 (fun _ h => .inl h) (fun _ h _ => h) fun _ _ h => h
  have h1 : SegSt 0x80001bb4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp0 - 64) 0x80022f30#64
      ⟨f.s0, f.s1, f.s2, BitVec.ofNat 64 L, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩)
      (ArmPay (Lua.Vm.AtF.Print.m0 (prX sp0 L n 0 0 0 r 0 0 f m o)) o) _ := h.repin (by pins_of h)
  obtain ⟨c1, s1, hret1⟩ := hL.gettop ph H _ o 0x80022f30#64 _ hS0 (by decide) _ h1
  have acc := acc.trans s1
  simp only [wrRet] at hret1
  -- the root after `lua_gettop`
  let M0 := Lua.Vm.AtF.Print.m0 (prX sp0 L n 0 0 0 r 0 0 f m o)
  have hX1 : Lua.Vm.AtF.Print.Ok (prX sp0 L n 0 0 0 r 0 0 f M0 o) := by
    have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
    fcx_ok
  have h2 : SegSt 0x80022f30#64 (Lua.Vm.AtF.Print.r2 (prX sp0 L n 0 0 0 r 0 0 f M0 o))
      (ArmPay (prX sp0 L n 0 0 0 r 0 0 f M0 o).m (prX sp0 L n 0 0 0 r 0 0 f M0 o).o) c1 :=
    hret1.repin (by pins_of hret1)
  have hra0 : bytesT8 M0 (sp0 - 8) = r := by simp only [M0]; fcx_unfold; fat_rd
  have hs20 : bytesT8 M0 (sp0 - 32) = f.s2 := by simp only [M0]; fcx_unfold; fat_rd
  have hs30 : bytesT8 M0 (sp0 - 40) = f.s3 := by simp only [M0]; fcx_unfold; fat_rd
  have habove0 : ∀ a, sp0 ≤ a → bytesT1 M0 a = bytesT1 m a := fun a ha => bT1_congr (hM0 a (.inr ha))
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · -- no argument: the newline
    subst hn0
    have hg_2 : zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 0) = true := by decide
    fat_run Lua.Vm.AtF.Print h2 acc until [0x80022fd0]
    fcx_unfold at h2
    obtain ⟨c3, m3, out3, buf, H3, s3, hret3, hout3, hP3, hk3, hb3, kk3⟩ :=
      pr_tail hM sp0 L r f M0 o ph H hok hP0 hra0 hs20 hs30 _ (h2.repin (by pins_of h2))
    refine ⟨c3, acc.trans s3, m3, out3, hret3, ⟨by rw [hout3]; simp [prLine], ⟨buf, H3, hP3,
      hL.stable _ _ _ _ _ _ _ _ hS0 (fun a ha => kk3 a fun hw => ha (.inl hw)) hb3 hk3
        (fun h => absurd h (by omega)), hk3⟩, fun a ha => ?_⟩⟩
    exact (kk3 a (PrintW.not_above (sp := sp0 - 64) (by rw [hhe]; omega) hP3.io.buf_hi (by omega))).trans
      (habove0 a ha)
  · -- the first argument
    have hg_2 : zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 n) = false := by
      rw [show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, sge_ofNat 0 n (by omega) (by omega)]
      simp; omega
    fat_run Lua.Vm.AtF.Print h2 acc until [0x80021b2c]
    fcx_unfold at h2
    have hM1 : ∀ a, (a < sp0 - 64 ∨ sp0 ≤ a) →
        (Lua.Vm.AtF.Print.m1 (prX sp0 L n 0 0 0 r 0 0 f M0 o))[a]? = M0[a]? := by
      intro a ha; fcx_unfold
      simp (disch := omega) only [getElem?_writeMap8_out]
    obtain ⟨hP1, kk1⟩ := pr_framed hM1 (by rw [hhe]; omega) hP0
    have hS1 := hL.stable _ _ _ _ _ _ _ _ hS0 kk1 (fun _ h => .inl h) (fun _ h _ => h) fun _ _ h => h
    let M1 := Lua.Vm.AtF.Print.m1 (prX sp0 L n 0 0 0 r 0 0 f M0 o)
    have hF1 : PrFrame M1 sp0 r f := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [M1] <;> fcx_unfold <;> fat_rd
      all_goals first | rfl | (simp only [M0]; fcx_unfold; fat_rd)
    have h3 : SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 1⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) 0x80022f58#64
        (prFr f.s0 f.s1 (BitVec.ofNat 64 n) L f)) (ArmPay M1 o) _ := h2.repin (by pins_of h2)
    obtain ⟨c4, s4, m4, s, H4, hret4, T⟩ := hL.tolstring 1 ph H M1 o 0x80022f58#64 _ (Nat.le_refl 1) hn0 hS1 hP1
      (by decide) _ h3
    have acc := acc.trans s4
    simp only [wrRet] at hret4
    have hX4 : Lua.Vm.AtF.Print.Ok (prX sp0 L n s 0 0 r 0 0 f m4 o) := by
      have := hok.sp_hi; have := hok.sp_al; have := hok.ra; have := hok.L_lo; have := hok.L_hi; have := hok.L_al
      fcx_ok
    have h4 : SegSt 0x80022f58#64 (Lua.Vm.AtF.Print.r10 (prX sp0 L n s 0 0 r 0 0 f m4 o))
        (ArmPay (prX sp0 L n s 0 0 r 0 0 f m4 o).m (prX sp0 L n s 0 0 r 0 0 f m4 o).o) c4 :=
      hret4.repin (by pins_of hret4)
    fat_run Lua.Vm.AtF.Print h4 acc until [0x80022f8c]
    fcx_unfold at h4
    have hm : PrMid sp0 n S bs r f m o ph H 1 s m4 o ph H4 :=
      { i_ge := Nat.le_refl 1
        i_le := hn0
        lua := T.lua
        io := T.io
        frame := hF1.keep (by omega) T.frame
        len := T.len
        bytes := T.bytes
        src_lo := T.src_lo
        src_hi := T.src_hi
        src_ok := T.src_ok
        src_out := T.src_out
        src_buf := T.src_buf
        console := ⟨[], rfl, by simp [prPre, prLine]⟩
        kept := T.kept
        above := fun a ha => (T.frame a (by omega) (by omega)).trans
          ((bT1_congr (hM1 a (.inr ha))).trans (habove0 a ha)) }
    obtain ⟨c5, s5, hr⟩ := pr_mid hM hL r f m o ph H hok 1 s m4 o ph H4 hm _ (h4.repin (by pins_of h4))
    have acc := acc.trans s5
    rcases hr with hn | hend
    · obtain ⟨c6, s6, hfin⟩ := pr_loop hM hL r f m o ph H hok 2 _ hn
      exact ⟨c6, acc.trans s6, hfin⟩
    · exact ⟨_, acc, hend⟩

end Lua.Vm.Sim.Kit

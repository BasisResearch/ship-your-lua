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
    ⟨.up hsA huA hb1, ?_, ?_⟩, P1.kept, fun a ha => P1.buf_new a ha, fun a ha => ?_⟩
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

/-- The stdio globals: `__sglue`, `_impure_data`, htif.c's tables, the
handlers, `__sf`. -/
def StdioGlob (a : Nat) : Prop := 0x8005cee0 ≤ a ∧ a < 0x8005e7d8

/-- **What `PrintSt` reads**: the stdio globals, the buffer, the heap off the
chunks in use, `.rodata`'s literals. -/
def PrintFoot (ph : StdoutPh) (H : HeapIx) (a : Nat) : Prop :=
  StdioGlob a ∨ ph.Buf a ∨ (HeapReads a ∧ ¬ InUse H.chunks a) ∨ (0x8004fb48 ≤ a ∧ a < 0x8004ff48)

theorem _root_.Lua.Vm.StdioBoot.congr {m m' : Mem} (h : StdioBoot m) (hk : ∀ a, StdioGlob a → m'[a]? = m[a]?) :
    StdioBoot m' := by
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : symSfSize = 552 := rfl
  have : symAtexit = 0x8005d450 := rfl
  have : reentCleanupOff = 72 := rfl
  have : reentStdinOff = 8 := rfl
  have : reentStdoutOff = 16 := rfl
  have : reentStderrOff = 24 := rfl
  have : glueNextOff = 0 := rfl
  have : glueNiobsOff = 8 := rfl
  have : glueIobsOff = 16 := rfl
  have r : ∀ {a n : Nat}, StdioGlob a → StdioGlob (a + n - 1) → 0 < n → rdLE m' a n = rdLE m a n :=
    fun {a n} h1 h2 _ => rdLE_congr fun i hi => hk _ ⟨by have := h1.1; omega, by have := h2.2; omega⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_⟩
  all_goals first
    | (simp only [rd64, rd32]; rw [r ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega)])
    | skip
  · exact h.exit_handler
  · exact h.impure_ptr
  · exact h.stdin
  · exact h.stdout
  · exact h.stderr
  · exact h.glue_next
  · exact h.glue_niobs
  · exact h.glue_iobs
  · exact (hk _ ⟨by omega, by omega⟩).trans (h.files i hi)
  · exact h.atexit
  · exact h.cleanup

theorem _root_.Lua.Vm.MemfsBoot.congr {m m' : Mem} (h : MemfsBoot m) (hk : ∀ a, StdioGlob a → m'[a]? = m[a]?) :
    MemfsBoot m' := by
  have : symFsReady = 0x8005d3c0 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFdsSize = 768 := rfl
  have : symFiles = 0x8005d760 := rfl
  have : symFilesSize = 3584 := rfl
  refine ⟨?_, fun i hi => (hk _ ⟨by omega, by omega⟩).trans (h.fds i hi),
    fun i hi => (hk _ ⟨by omega, by omega⟩).trans (h.files i hi)⟩
  simp only [rd32]
  rw [rdLE_congr fun i hi => hk _ ⟨by omega, by omega⟩]
  exact h.ready

theorem StdoutFresh.congrT {m m' : Mem} (h : StdoutFresh m) (hk : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a) :
    StdoutFresh m' := by
  stdio_nums
  have : symFsReady = 0x8005d3c0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  have k8 : ∀ a, StdioGlob a → StdioGlob (a + 7) → bytesT8 m' a = bytesT8 m a := fun a h1 h2 =>
    bytesT8_congrT fun i _ => hk _ ⟨by have := h1.1; omega, by have := h2.2; omega⟩
  have k4 : ∀ a, StdioGlob a → StdioGlob (a + 3) → bytesT4 m' a = bytesT4 m a := fun a h1 h2 =>
    bytesT4_congrT fun i _ => hk _ ⟨by have := h1.1; omega, by have := h2.2; omega⟩
  have k2 : ∀ a, StdioGlob a → StdioGlob (a + 1) → bytesT2 m' a = bytesT2 m a := fun a h1 h2 =>
    bT2_congrT fun i _ => hk _ ⟨by have := h1.1; omega, by have := h2.2; omega⟩
  exact ⟨(k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.impure,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.cleanup,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.flags,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.file,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.pad,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.base,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.cookie,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.write,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.flags2,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.fs⟩

theorem StdoutAtW.congrT {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} {wv : BitVec 32}
    (h : StdoutAtW m buf pend wv) (hk : ∀ a, StdioGlob a ∨ Rng buf 1024 a → bytesT1 m' a = bytesT1 m a) :
    StdoutAtW m' buf pend wv := by
  stdio_nums
  have : symFsReady = 0x8005d3c0 := rfl
  have : symFds = 0x8005d460 := rfl
  have hr := h.room
  have k8 : ∀ a, StdioGlob a → StdioGlob (a + 7) → bytesT8 m' a = bytesT8 m a := fun a h1 h2 =>
    bytesT8_congrT fun i _ => hk _ (.inl ⟨by have := h1.1; omega, by have := h2.2; omega⟩)
  have k4 : ∀ a, StdioGlob a → StdioGlob (a + 3) → bytesT4 m' a = bytesT4 m a := fun a h1 h2 =>
    bytesT4_congrT fun i _ => hk _ (.inl ⟨by have := h1.1; omega, by have := h2.2; omega⟩)
  have k2 : ∀ a, StdioGlob a → StdioGlob (a + 1) → bytesT2 m' a = bytesT2 m a := fun a h1 h2 =>
    bT2_congrT fun i _ => hk _ (.inl ⟨by have := h1.1; omega, by have := h2.2; omega⟩)
  refine ⟨(k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.p,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.w,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.flags,
    (k2 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.file,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.base,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.size,
    (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.lbf,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.cookie,
    (k8 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.write,
    ?_, h.room, h.buf_lo, h.buf_hi, ?_, (k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩).trans h.stdout⟩
  · rw [bytesAt_congr fun i hi => hk _ (.inr ⟨by omega, by omega⟩)]; exact h.bytes
  · rw [k4 _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]; exact h.ready

theorem StdioUp.congrT {m m' : Mem} (h : StdioUp m) (hk : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a) :
    StdioUp m' := by
  stdio_nums
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  refine ⟨(bytesT8_congrT fun i _ => hk _ ⟨by omega, by omega⟩).trans h.impure, ?_,
    (bytesT4_congrT fun i _ => hk _ ⟨by omega, by omega⟩).trans h.flags2⟩
  rw [bytesT8_congrT fun i _ => hk _ ⟨by omega, by omega⟩]; exact h.init

/-- **The I/O state across a change off what it reads.** -/
theorem PrintSt.keep {m m' : Mem} {ph : StdoutPh} {H : HeapIx} (h : PrintSt m ph H)
    (hk : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a) : PrintSt m' ph H := by
  have hg : ∀ a, StdioGlob a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a (.inl ha)
  have hgf : ∀ a, StdioGlob a → (fillZeroMem m')[a]? = (fillZeroMem m)[a]? := fun a ha =>
    fill_total ⟨by simp only [ramBase]; have := ha.1; omega, by simp only [ramBase, ramSize]; have := ha.2; omega⟩
      (hg a ha)
  refine ⟨?_, h.heap.ofTotal fun a hr hu => (hk a (.inr (.inr (.inl ⟨hr, hu⟩)))).trans (bytesT1_fill m a).symm,
    ⟨?_, ?_, ?_, ?_⟩⟩
  · cases h.io with
    | boot hB hMf hroom => exact .boot (hB.congr hgf) (hMf.congr hgf) hroom
    | fresh hF hroom => exact .fresh (hF.congrT hg) hroom
    | up hs hu hb =>
      exact .up (hs.congrT fun a ha => ha.elim (hg a) fun hb' => hk a (.inr (.inl hb'))) (hu.congrT hg) hb
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
discharges), over the Lua state `S k ph H m` (`k` values above the called
function, `stdout`'s phase `ph`, the heap `H`) and the bytes `bs i` argument
`i` prints: `lua_gettop`, `luaL_tolstring`, `lua_settop(L, -2)`, and `S`
stable under what a write of `stdout` may change. -/
structure PrintLua (L sp0 n : Nat) (S : Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8)) :
    Prop where
  n_lt : n + 1 < 2 ^ 31
  gettop : ∀ (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
    S n ph H m → r.toNat % 4 = 0 →
    Triple (SegSt 0x80001bb4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp0 - 64) r f) (ArmPay m o))
      (wrRet r (sp0 - 64) n f m o)
  tolstring : ∀ (i : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64)
    (f : AbiFrame), 1 ≤ i → i ≤ n → S n ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧ TolPost sp0 n S (bs i) ph m m' s H H')
  settop : ∀ (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
    S (n + 1) ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
    Triple (SegSt 0x80001bd4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (2 ^ 64 - 2)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m', apiRet r (sp0 - 64) f m' o c ∧ S n ph H m' ∧ PrintSt m' ph H ∧
        ∀ a, sp0 - 64 ≤ a → bytesT1 m' a = bytesT1 m a)
  stable : ∀ (k : Nat) (ph ph' : StdoutPh) (H H' : HeapIx) (m m' : Mem), S k ph H m →
    (∀ a, ¬ (PrintW (sp0 - 64) H ph' a ∨ Rng (sp0 - 64) 64 a) → bytesT1 m' a = bytesT1 m a) →
    BufFrom ph ph' H →
    (∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) → S k ph' H' m'

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
structure PrEnd (sp0 n : Nat) (S : Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (m0 : Mem) (ph0 : StdoutPh) (H0 : HeapIx) (m : Mem) (out : List (BitVec 8)) : Prop where
  out : out = ph0.pend ++ prLine bs n ++ [0x0a#8]
  st : ∃ buf H, PrintSt m (.up buf []) H ∧ S n (.up buf []) H m ∧ (∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks)
  above : ∀ a, sp0 ≤ a → bytesT1 m a = bytesT1 m0 a

/-- **The loop head** (`luaL_tolstring` of argument `i ≥ 2` next). -/
structure PrHead (sp0 n : Nat) (S : Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx)
    (i : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx) : Prop where
  i_ge : 2 ≤ i
  i_le : i ≤ n
  lua : S n ph H m
  io : PrintSt m ph H
  frame : PrFrame m sp0 r f
  console : ∃ out, o = pushes o0 out ∧ out ++ ph.pend = ph0.pend ++ prLine bs (i - 1)
  kept : ∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks
  above : ∀ a, sp0 ≤ a → bytesT1 m a = bytesT1 m0 a

/-- **Before argument `i`'s string is written** (`0x80022f8c`): `s` holds
its bytes, the length word its length, the separator written. -/
structure PrMid (sp0 n : Nat) (S : Nat → StdoutPh → HeapIx → Mem → Prop) (bs : Nat → List (BitVec 8))
    (r : BitVec 64) (f : AbiFrame) (m0 : Mem) (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx)
    (i s : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx) : Prop where
  i_ge : 1 ≤ i
  i_le : i ≤ n
  lua : S (n + 1) ph H m
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

/-- The stack at and above the callees' `sp` is no write's. -/
theorem PrintSt.above {m : Mem} {ph : StdoutPh} {H : HeapIx} (hP : PrintSt m ph H) {sp a : Nat}
    (hsp : heapEnd ≤ sp) (ha : sp ≤ a) : ¬ PrintW sp H ph a :=
  PrintW.not_above hsp hP.io.buf_hi ha

/-- **Argument `i`'s string, `lua_pop`, the loop test**: on to the head of
argument `i + 1`, or the tail. -/
theorem pr_mid (hM : MallocR_Statement) {L sp0 n : Nat} {S : Nat → StdoutPh → HeapIx → Mem → Prop}
    {bs : Nat → List (BitVec 8)} (hL : PrintLua L sp0 n S bs) (r : BitVec 64) (f : AbiFrame) (m0 : Mem)
    (o0 : Array String) (ph0 : StdoutPh) (H0 : HeapIx) (hok : PrOk sp0 L r)
    (i s : Nat) (m : Mem) (o : Array String) (ph : StdoutPh) (H : HeapIx)
    (hm : PrMid sp0 n S bs r f m0 o0 ph0 H0 i s m o ph H) (c : Config)
    (h : SegSt 0x80022f8c#64 (Lua.Vm.AtF.Print.r20 (prX sp0 L n s (bs i).length i r 0 0 f m o)) (ArmPay m o) c) :
    ∃ c', Steps c c' ∧
      ((∃ m' o' ph' H', PrHead sp0 n S bs r f m0 o0 ph0 H0 (i + 1) m' o' ph' H' ∧
        SegSt 0x80022f68#64 (Lua.Vm.AtF.Print.r16 (prX sp0 L n 0 0 (i + 1) r (BitVec.ofNat 64 s) 0 f m' o'))
          (ArmPay m' o') c') ∨
       (∃ m' out, wrRet r sp0 0 f m' (pushes o0 out) c' ∧ PrEnd sp0 n S bs m0 ph0 H0 m' out)) := by
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
  have hS1 : S (n + 1) ph1 H1 m1 := hL.stable _ _ _ _ _ _ _ hm.lua (fun a ha => P1.keep a fun hw => ha (.inl hw)) P1.buf_new P1.kept
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
  obtain ⟨c3, s3, m2, hret3, hS2, hP2, kk2⟩ := hL.settop ph1 H1 m1 (pushes o out1) 0x80022fb4#64 _ hS1 hP1
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
    refine ⟨_, acc, .inl ⟨m2, pushes o out1, ph1, H1, ⟨by omega, hni, hS2, hP2, hF2,
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
      ⟨?_, ⟨buf, H2, hP3, hL.stable _ _ _ _ _ _ _ hS2 (fun a ha => kk3 a fun hw => ha (.inl hw)) hb3 hk3, fun c hc hu => hk3 c (P1.kept c (hm.kept c hc hu) hu) hu⟩,
        fun a ha => ?_⟩⟩⟩
    · rw [hout2, ← List.append_assoc, hout1]
    · exact (kk3 a (PrintW.not_above (sp := sp0 - 64) (by rw [hhe]; omega) hP3.io.buf_hi (by omega))).trans (habove a ha)

end Lua.Vm.Sim.Kit

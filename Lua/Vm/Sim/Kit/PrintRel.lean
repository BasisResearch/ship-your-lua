import Lua.Vm.Sim.Kit.CallOpen
import Lua.Vm.Sim.Kit.PushLitProof
import Lua.Vm.Sim.Kit.AllocProof

/-!
# `luaB_print` on the C frame from its per-class parts (lane F1-15)

`PrintRel_Statement` (lane F1-13's coarse premise) is assembled here from
`print_sum` (lane F1-11) over a concrete Lua state `PrSt` (`printLua_st`:
`lua_gettop`, `lua_settop(L, -2)`, the stability under a write), with
`luaL_tolstring` per value class:

* nil and booleans: `tol_nil`, `tol_true`, `tol_false` over
  `PushLit_Statement` (`tolLit_nil`, `tolLit_bool`, through `prLitPost`);
* strings: `TolStr_Statement`;
* integers (lane F1-18): per argument, `TolInt_Statement`, over the
  per-argument budget `print_sum`'s state now carries (`S i k`: before
  argument `i`; `PrSt.room` the break room of the arguments from `i` on,
  `argCost`, kept by a write's `PrintPost.room`; `PrSt.strt` room in
  `g->strt`; `PrSt.safe` its chains), the entry's budget from `callBudget`;
* floats, functions, and integer lists whose entry lacks `AllocIn`: the
  premises `PrintFlt_Statement`, `PrintFn_Statement`,
  `PrintAllocOff_Statement`.

`printRel_of` is the assembly; `CallOpen.print` (`Kit/TolStrProof.lean`, lane
F1-17, with `tolStr_proved`) the field it replaces.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The state's regions -/

/-- A buffer of a later write is the entry's or fresh at the entry. -/
theorem BufFrom.trans {ph0 ph ph' : StdoutPh} {H0 H : HeapIx} (h0 : BufFrom ph0 ph H0) (h : BufFrom ph ph' H)
    (hk : ∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks) : BufFrom ph0 ph' H0 := fun a ha =>
  (h a ha).elim (h0 a) fun ⟨h1, h2, h3⟩ => .inr ⟨h1, h2, fun ⟨c, hc, hu, hl, hh⟩ => h3 ⟨c, hk c hc hu, hu, hl, hh⟩⟩

/-- **A static byte is no write's** (`PrintW`), nor `luaB_print`'s frame. -/
theorem PrintStatic.not_printW {H : HeapIx} {ph : StdoutPh} {a sp : Nat} (h : PrintStatic a)
    (hsp : heapEnd + 4096 ≤ sp) (hbuf : ∀ a, ph.Buf a → heapStart ≤ a) : ¬ (PrintW sp H ph a ∨ Rng sp 64 a) := by
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have ht : symTohost = 0x8005c6c0 := rfl
  have hat : symAtexit = 0x8005d450 := rfl
  have hb := hbuf a
  rw [e3] at hsp
  intro hw
  pw_nums
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symFiles = 0x8005d760 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFsReady = 0x8005d3c0 := rfl
  simp only [PrintStatic, Rng, LocaleW, symImpurePtr] at h
  rcases hw with (hw | hw | hw | hw | hw | hw) | hw
  · simp only [FsGlobal] at hw; omega
  · rcases hw with hw | ⟨h1, _, _⟩
    · simp only [MallocGlobal] at hw; omega
    · omega
  · simp only [SinitW, Rng] at hw; omega
  · simp only [Rng] at hw; omega
  · have := hb hw; omega
  · simp only [Below] at hw; omega
  · simp only [Rng] at hw; omega

/-- A buffer lies in the arena. -/
theorem PrintSt.buf_lo {m : Mem} {ph : StdoutPh} {H : HeapIx} (h : PrintSt m ph H) :
    ∀ a, ph.Buf a → heapStart ≤ a := fun a ha => by have := h.io.buf_lo a ha; omega

/-! ## `luaB_print`'s Lua state: the API calls and the stability -/

/-- The entry's kept bytes, at a later state. -/
theorem PrSt.kept {L nci func tbc sl g n i k : Nat} {ls : LitPtrs} {args : List Value} {D G B FL : Nat → Prop}
    {M0 m : Mem} {ph0 ph : StdoutPh} {H0 H : HeapIx}
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i k ph H m) {a : Nat}
    (h : Kept H0 ph0 a) : Kept H ph a := h.mono hS.chunks hS.buf

/-- A later buffer lies in the arena. -/
theorem PrSt.buf_lo {L nci func tbc sl g n i k : Nat} {ls : LitPtrs} {args : List Value} {D G B FL : Nat → Prop}
    {M0 m : Mem} {ph0 ph : StdoutPh} {H0 H : HeapIx}
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i k ph H m)
    (h0 : ∀ a, ph0.Buf a → heapStart ≤ a) : ∀ a, ph.Buf a → heapStart ≤ a := fun a ha =>
  (hS.buf a ha).elim (h0 a) fun h => h.1

/-- **Where the entry's objects lie**, as numbers (`omega`'s facts). -/
structure PrPlaced (L nci func sl g n : Nat) (ls : LitPtrs) : Prop where
  L_lo : heapStart ≤ L
  L_hi : L + stateSize ≤ heapEnd
  nci_lo : heapStart ≤ nci
  nci_hi : nci + ciSize ≤ heapEnd
  g_lo : heapStart ≤ g
  g_hi : g + gEnd ≤ heapEnd
  f_lo : heapStart ≤ func
  sl_hi : sl ≤ heapEnd
  room : func + 16 * n + 16 + 320 < sl
  L_g : L + stateSize ≤ g ∨ g + gEnd ≤ L
  nci_g : nci + ciSize ≤ g ∨ g + gEnd ≤ nci
  stack_g : sl ≤ g ∨ g + gEnd ≤ func
  L_stack : L + stateSize ≤ func ∨ sl ≤ L
  nci_stack : nci + ciSize ≤ func ∨ sl ≤ nci
  lits : ∀ ts ∈ ls.strs, heapStart ≤ ts ∧ ts + 30 ≤ heapEnd ∧ (ts + 30 ≤ L ∨ L + stateSize ≤ ts) ∧
    (ts + 30 ≤ g ∨ g + gEnd ≤ ts) ∧ (ts + 30 ≤ nci ∨ nci + ciSize ≤ ts) ∧ (ts + 30 ≤ func ∨ sl ≤ ts)

theorem PrintIn.placed {L nci func n tbc sl g : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G : Nat → Prop} {ph : StdoutPh} {H : HeapIx} {M : Mem}
    (h : PrintIn L nci func n tbc sl g ls args ι D G ph H M) : PrPlaced L nci func sl g n ls := by
  have hfs : func < sl := by have := h.room; omega
  have k1 := (h.L_in L (Nat.le_refl _) (by simp only [stateSize]; omega)).lo
  have k2 := (h.L_in (L + stateSize - 1) (by simp only [stateSize]; omega) (by simp only [stateSize]; omega)).hi
  have k3 := (h.nci_in nci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have k4 := (h.nci_in (nci + ciSize - 1) (by simp only [ciSize]; omega) (by simp only [ciSize]; omega)).hi
  have k5 := (h.g_in g (Nat.le_refl _) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).lo
  have k6 := (h.g_in (g + gEnd - 1) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).hi
  have k7 := (h.stack_in func (Nat.le_refl _) hfs).lo
  have k8 := (h.stack_in (sl - 1) (by omega) (by omega)).hi
  have o := h.objs
  have o1 := o.L_g; have o2 := o.nci_g; have o3 := o.stack_g; have o4 := o.L_stack; have o5 := o.nci_stack
  simp only [Apart] at o1 o2 o3 o4 o5
  refine ⟨k1, by omega, k3, by omega, k5, by omega, k7, by omega, h.room, o1, o2, by omega, by omega, by omega,
    fun ts hts => ?_⟩
  obtain ⟨_, hl⟩ := h.lits
  have s1 := (hl.strs ts hts ts (Nat.le_refl _) (by omega)).lo
  have s2 := (hl.strs ts hts (ts + 29) (by omega) (by omega)).hi
  have l1 := o.lit_L ts hts; have l2 := o.lit_g ts hts; have l3 := o.lit_nci ts hts; have l4 := o.lit_stack ts hts
  simp only [Apart] at l1 l2 l3 l4
  exact ⟨s1, by omega, l1, l2, l3, by omega⟩

/-- `omega` with `__heap_end` an atom (its literal unfolded past the
recursion limit otherwise). -/
macro "homega" : tactic => `(tactic| ((try generalize heapEnd = E at *); omega))

/-- `omega` over `luaB_print`'s placement. -/
macro "pr_omega" : tactic => `(tactic| (
  simp only [PrKeep, ArgSlot, ApiFoot, Rng, stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM,
    gMtOff, gGcstpOff, gTotalbytesOff, gGCdebtOff, stateGOff, stateHookmaskOff, stateTopOff, gcMarkedOff,
    heapStart, heapEnd, symEnd, symHeapEnd, symTohost, Image.rodataBase, Image.rodataSize, LocaleW, symImpurePtr,
    not_or, not_and, Nat.not_lt] at *
  omega))

/-- **A byte the state keeps is no store to `L->top`.** -/
theorem PrPlaced.keep_top {L nci func sl g n : Nat} {ls : LitPtrs} {G : Nat → Prop} (hp : PrPlaced L nci func sl g n ls)
    (hG : ∀ a, G a → ¬ Rng (L + stateTopOff) 8 a) {a : Nat} (h : PrKeep L g func n G a) : ¬ Rng (L + 16) 8 a := by
  have := hp.L_lo; have := hp.L_hi; have := hp.g_lo; have := hp.g_hi; have := hp.L_g; have := hp.L_stack
  have := hp.room; have := hp.f_lo
  have hrb : Image.rodataBase = 0x8004ecc8 := rfl
  have hrs : Image.rodataSize = 55776 := rfl
  have hhs : heapStart = 0x8006ecd0 := rfl
  rcases h with h | h | h | h | h | h | h
  · exact hG a h
  all_goals simp only [ArgSlot, Rng, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM, gMtOff, gGcstpOff,
    stateGOff, stateHookmaskOff] at *
  all_goals omega

/-! ## The per-argument budget (lane F1-18) -/

theorem prCost_succ {args : List Value} {i : Nat} {v : Value} (hi : 1 ≤ i) (hv : args[i - 1]? = some v) :
    prCost args i = argCost v + prCost args (i + 1) := by
  have hlt : i - 1 < args.length := by
    rcases Nat.lt_or_ge (i - 1) args.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  have e : args[i - 1] = v := by rw [List.getElem?_eq_getElem hlt] at hv; exact Option.some.inj hv
  have e2 : i + 1 - 1 = i - 1 + 1 := by omega
  simp only [prCost, e2, List.drop_eq_getElem_cons hlt, e, List.map_cons, List.sum_cons]

theorem prAllocs_succ {args : List Value} {i : Nat} {v : Value} (hi : 1 ≤ i) (hv : args[i - 1]? = some v) :
    prAllocs args i = (if 0 < argCost v then 1 else 0) + prAllocs args (i + 1) := by
  have hlt : i - 1 < args.length := by
    rcases Nat.lt_or_ge (i - 1) args.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hv; cases hv
  have e : args[i - 1] = v := by rw [List.getElem?_eq_getElem hlt] at hv; exact Option.some.inj hv
  have e2 : i + 1 - 1 = i - 1 + 1 := by omega
  simp only [prAllocs, e2, List.drop_eq_getElem_cons hlt, e, List.filter_cons]
  split <;> simp_all <;> omega

theorem prCost_past {args : List Value} {i : Nat} (h : args.length < i) : prCost args i = 0 := by
  simp [prCost, List.drop_eq_nil_of_le (show args.length ≤ i - 1 by omega)]

theorem prAllocs_past {args : List Value} {i : Nat} (h : args.length < i) : prAllocs args i = 0 := by
  simp [prAllocs, List.drop_eq_nil_of_le (show args.length ≤ i - 1 by omega)]

/-- An argument of positive cost allocates. -/
theorem allocates_of_cost {v : Value} (h : 0 < argCost v) : Allocates v := by
  cases v <;> simp_all [argCost, Allocates]

theorem anyAlloc_of_cost {args : List Value} (h : 0 < prCost args 1) : AnyAlloc args := by
  simp only [prCost, Nat.sub_self, List.drop_zero] at h
  induction args with
  | nil => simp at h
  | cons v t ih =>
    simp only [List.map_cons, List.sum_cons] at h
    by_cases hv : 0 < argCost v
    · exact ⟨v, List.mem_cons_self .., allocates_of_cost hv⟩
    · obtain ⟨w, hw, ha⟩ := ih (by omega)
      exact ⟨w, List.mem_cons_of_mem _ hw, ha⟩

theorem anyAlloc_of_allocs {args : List Value} (h : 0 < prAllocs args 1) : AnyAlloc args := by
  simp only [prAllocs, Nat.sub_self, List.drop_zero, List.length_pos_iff_exists_mem, List.mem_filter,
    decide_eq_true_eq] at h
  obtain ⟨v, hv, hc⟩ := h
  exact ⟨v, hv, allocates_of_cost hc⟩

/-- `stdout`'s first write needs at most this. -/
theorem stdoutNeed_le (ph : StdoutPh) : stdoutNeed ph ≤ 1024 + 16384 + 4096 := by
  cases ph <;> simp [stdoutNeed]

/-- The string table's safety, with a larger set of kept bytes. -/
theorem StrtSafeIn.mono {L nci g func n sl : Nat} {ls : LitPtrs} {D G B K K' : Nat → Prop} {M : Mem}
    (h : StrtSafeIn L nci g func n sl ls D G B K M) (hK : ∀ a, K a → K' a) :
    StrtSafeIn L nci g func n sl ls D G B K' M :=
  fun rt hrt => (h rt hrt).weaken hK (fun _ _ h => h) fun _ _ h => h

/-- (lane F1-18) **`AllocStatic` depends only on its bytes.** -/
theorem AllocStatic.congr {m m' : Mem} {g : Nat} (h : AllocStatic m g)
    (hk : ∀ a, AllocStaticFoot g a → bytesT1 m' a = bytesT1 m a) : AllocStatic m' g := by
  have k : ∀ {lo n : Nat}, (∀ a, Rng lo n a → AllocStaticFoot g a) → ∀ j, j < n →
      bytesT1 m' (lo + j) = bytesT1 m (lo + j) := fun hr j hj => hk _ (hr _ ⟨by omega, by omega⟩)
  have k8 : ∀ {lo : Nat}, (∀ a, Rng lo 8 a → AllocStaticFoot g a) → bytesT8 m' lo = bytesT8 m lo :=
    fun hr => bytesT8_congrT fun j hj => k hr j hj
  have k4 : ∀ {lo : Nat}, (∀ a, Rng lo 4 a → AllocStaticFoot g a) → bytesT4 m' lo = bytesT4 m lo :=
    fun hr => bytesT4_congrT fun j hj => k hr j hj
  have h1 := h.fmt
  refine ⟨(k8 fun a ha => .inl ha).trans h.frealloc, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · exact (k8 fun a ha => .inr (.inl ha)).trans h1.impure
  · exact (k8 fun a ha => .inr (.inr (.inl ha))).trans h1.decpt
  · exact (k8 fun a ha => .inr (.inr (.inr (.inl ha)))).trans h1.dotw
  · exact (hk _ (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))).trans h1.dot0
  · exact (hk _ (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))).trans h1.dot1
  · exact (k8 fun a ha => .inr (.inr (.inr (.inr (.inl ha))))).trans h1.mbtowc
  · exact (hk _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))))).trans h1.mbmax
  · exact (k4 fun a ha => .inr (.inr (.inr (.inr (.inr (.inr (.inl ha))))))).trans h1.jt_l
  · exact (k4 fun a ha => .inr (.inr (.inr (.inr (.inr (.inr (.inr ha))))))).trans h1.jt_d

/-- (lane F1-18) **`AllocStatic`'s static words are no write's** (`PrintW`):
`_impure_ptr`, the C locale's words (`.data`) and `.rodata`. -/
theorem allocStatic_not_printW {sp g a : Nat} {H : HeapIx} {ph : StdoutPh} (hsp : heapEnd + 4096 ≤ sp)
    (hbuf : ∀ a, ph.Buf a → heapStart ≤ a) (ha : AllocStaticFoot g a) (hg : ¬ Rng g 8 a) :
    ¬ PrintW sp H ph a := by
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have hb := hbuf a
  rw [e3] at hsp
  intro hw
  pw_nums
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symFiles = 0x8005d760 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFsReady = 0x8005d3c0 := rfl
  simp only [AllocStaticFoot, Rng] at ha hg
  rcases hw with hw | hw | hw | hw | hw | hw
  · simp only [FsGlobal] at hw; omega
  · rcases hw with hw | ⟨h1, _, _⟩
    · simp only [MallocGlobal] at hw; omega
    · omega
  · simp only [SinitW, Rng] at hw; omega
  · simp only [Rng] at hw; omega
  · have := hb hw; omega
  · simp only [Below] at hw; omega

/-- (lane F1-19) **`_REENT`'s `_dtoa_r` words are no write's** (`PrintW`), nor
`luaB_print`'s frame. -/
theorem reentWord_not_printW {sp a : Nat} {H : HeapIx} {ph : StdoutPh} (hsp : heapEnd + 4096 ≤ sp)
    (hbuf : ∀ a, ph.Buf a → heapStart ≤ a) (ha : ReentWord a) : ¬ (PrintW sp H ph a ∨ Rng sp 64 a) := by
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have hb := hbuf a
  rw [e3] at hsp
  intro hw
  pw_nums
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symFiles = 0x8005d760 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFsReady = 0x8005d3c0 := rfl
  simp only [ReentWord, reentResultOff, reentFreelistOff] at ha
  rcases hw with (hw | hw | hw | hw | hw | hw) | hw
  · simp only [FsGlobal] at hw; omega
  · rcases hw with hw | ⟨h1, _, _⟩
    · simp only [MallocGlobal] at hw; omega
    · omega
  · simp only [SinitW, Rng] at hw; omega
  · simp only [Rng] at hw; omega
  · have := hb hw; omega
  · simp only [Below] at hw; omega
  · simp only [Rng] at hw; omega

/-- **`luaB_print`'s state after a non-allocating `luaL_tolstring`**: the
budget of the arguments from `i + 1` on is argument `i`'s (it costs nothing),
the table's words and the literals' footprint kept. -/
theorem PrSt.next0 {L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {D G B FL : Nat → Prop}
    {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {i k k' : Nat} {ph : StdoutPh} {H : HeapIx} {m m' : Mem}
    {v : Value} (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i k ph H m) (hi : 1 ≤ i)
    (hv : args[i - 1]? = some v) (h0 : argCost v = 0) (hapi : ApiAt m' L nci func k' tbc)
    (hl : LitsFoot g sl ls H ph D FL m') (hk : ∀ a, PrKeep L g func n G a → bytesT1 m' a = bytesT1 M0 a)
    (kFL : ∀ a, FL a → bytesT1 m' a = bytesT1 m a)
    (kS : ∀ a, PrStatic g a → bytesT1 m' a = bytesT1 m a)
    (kB : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a) :
    PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 (i + 1) k' ph H m' := by
  have kT : ∀ a, g + gStrtNuseOff ≤ a → a < g + gStrtNuseOff + 8 → bytesT1 m' a = bytesT1 m a :=
    fun a h1 h2 => kS a (.inl ⟨h1, h2⟩)
  have hc := prCost_succ hi hv
  have ha := prAllocs_succ hi hv
  rw [h0, Nat.zero_add] at hc
  rw [h0, if_neg (Nat.lt_irrefl 0), Nat.zero_add] at ha
  have hn : strtNuse m' g = strtNuse m g := by
    simp only [strtNuse]; congr 1
    exact bytesT4_congrT fun j hj => kT _ (by omega) (by omega)
  have hz : strtSize m' g = strtSize m g := by
    simp only [strtSize, gStrtSizeOff]; congr 1
    exact bytesT4_congrT fun j hj => kT _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
  refine ⟨hapi, hl, hk, hS.buf, hS.chunks, ?_, ?_, hS.safe.trans kFL, ?_, ?_, hS.big.trans kB, hS.bigIn,
    hS.big_fl⟩
  · rw [← hc]; exact hS.room
  · rw [hn, hz, ← ha]; exact hS.strt
  · rw [← ha]; exact hS.gc
  · rw [← ha]; exact fun h => (hS.stat h).congr fun a ha' => kS a (.inr ha')

/-- **`PrintLua` for `luaB_print`'s Lua state** (`PrSt'`): `lua_gettop`,
`lua_settop(L, -2)` and the stability are proved (lane F1-18: with the
budget, the table's room and its safety); `luaL_tolstring` of each argument
is the premise `htol`. -/
theorem printLua_st {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {bs : Nat → List (BitVec 8)}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (htol : ∀ (i : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
      1 ≤ i → i ≤ n → PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 i n ph H m → PrintSt m ph H →
      r.toNat % 4 = 0 →
      Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
          ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
        (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧
          TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (bs i) ph m m' s H H')) :
    PrintLua L sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0) bs where
  n_lt := hn.n_lt
  gettop := by
    intro ph H m o r f ⟨_, _, hS⟩ hr
    have q := hn.ok
    have := q.sp_hi; have := q.L_lo; have := q.L_hi; have := q.L_al
    have := hn.nci_lo; have := hn.nci_hi; have := hn.f_lo; have := hn.f_hi; have := hn.n_lt
    exact gettop_sum (sp0 - 64) L nci func n tbc r f m o hS.api (by omega) hr (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)
  tolstring := htol
  settop := by
    intro i ph H m o r f ⟨FL, B, hS⟩ hP hr c h
    have q := hn.ok
    have := q.sp_hi; have := q.L_lo; have := q.L_hi; have := q.L_al; have := q.sp_lo
    have := hn.nci_lo; have := hn.f_lo; have := hn.f_hi; have := hn.sep
    have hp := hIn.placed
    obtain ⟨c', s', m', hret, hapi, hag⟩ := settop_pop_sum (sp0 - 64) L nci func n tbc r f m o hS.api hr
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) c h
    have hk : ∀ a, ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a := fun a ha => AtF.bT1_congr (hag a ha)
    have hLk : ∀ a, Rng (L + 16) 8 a → Kept H ph a := fun a ha =>
      hS.kept (hIn.L_in a (by simp only [Rng] at ha; omega) (by simp only [Rng, stateSize] at ha ⊢; omega))
    have hl := hS.lits
    have kFL : ∀ a, FL a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a fun hr' => hl.apart a ha
      (hIn.dirty a (.inl (by simpa only [stateTopOff] using hr')))
    have kT : ∀ a, g + gStrtNuseOff ≤ a → a < g + gStrtNuseOff + 8 → bytesT1 m' a = bytesT1 m a := fun a h1 h2 =>
      hk a (by have := hp.L_g; simp only [gStrtNuseOff] at h1 h2; pr_omega)
    have kA : ∀ a, AllocStaticFoot g a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a (by
      have := hp.L_g; have := hp.L_lo
      simp only [AllocStaticFoot, Rng] at ha; pr_omega)
    have hn' : strtNuse m' g = strtNuse m g := by
      simp only [strtNuse]; congr 1
      exact bytesT4_congrT fun j hj => kT _ (by omega) (by omega)
    have hz : strtSize m' g = strtSize m g := by
      simp only [strtSize, gStrtSizeOff]; congr 1
      exact bytesT4_congrT fun j hj => kT _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
    -- (lane F1-19) `_dtoa_r`'s bignums and `_REENT`'s words are off `L->top`
    have kB : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a fun hr' => by
      have := hp.L_lo; have := hp.L_hi
      rcases ha with hb | hr
      · exact hS.bigIn.x a hb (.inr (.inl (by simp only [Rng, stateSize] at hr' ⊢; omega)))
      · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff, Rng] at hr hr'
        have : heapStart = 0x8006ecd0 := rfl
        omega
    refine ⟨c', s', m', hret, ⟨FL, B, ⟨hapi, hl.trans kFL
        (hl.cache.congr fun a h1 h2 => hk a (by have := hp.L_g; pr_omega)),
      fun a ha => (hk a (hp.keep_top (fun a h => (hIn.keep_apart a h).1) ha)).trans (hS.keep a ha),
      hS.buf, hS.chunks, hS.room, by rw [hn', hz]; exact hS.strt, hS.safe.trans kFL, hS.gc,
      fun h => (hS.stat h).congr kA, hS.big.trans kB, hS.bigIn, hS.big_fl⟩⟩,
      hP.keep fun a ha => hk a fun hr' => (hLk a hr').not_printFoot ha, fun a ha => hk a fun hr' => ?_⟩
    have := hp.L_hi; have : heapEnd = 0x87800000 := rfl
    simp only [Rng] at hr'; omega
  stable := by
    intro i k ph ph' H H' m m' ⟨FL, B, hS⟩ hk hbf hkept hroom
    have q := hn.ok
    have hp := hIn.placed
    have hsp : heapEnd + 4096 ≤ sp0 - 64 := by
      have h1 := q.sp_lo; revert h1; generalize heapEnd = E; intro h1; omega
    have kK : ∀ a, Kept H ph a → bytesT1 m' a = bytesT1 m a := fun a ha => hk a (ha.not_printW hsp hbf)
    have k0 : ∀ a, Kept H0 ph0 a → bytesT1 m' a = bytesT1 m a := fun a ha => kK a (hS.kept ha)
    have hbuf' : ∀ a, ph'.Buf a → heapStart ≤ a := fun a ha =>
      (hbf a ha).elim (hS.buf_lo hIn.st.buf_lo a) fun h => h.1
    have hl := hS.lits
    have kT : ∀ a, g + gStrtNuseOff ≤ a → a < g + gStrtNuseOff + 8 → bytesT1 m' a = bytesT1 m a := fun a h1 h2 =>
      k0 a (hIn.g_in a (by simp only [gStrtNuseOff] at h1; omega)
        (by simp only [gStrtNuseOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at h2 ⊢; omega))
    have hn' : strtNuse m' g = strtNuse m g := by
      simp only [strtNuse]; congr 1
      exact bytesT4_congrT fun j hj => kT _ (by omega) (by omega)
    have hz : strtSize m' g = strtSize m g := by
      simp only [strtSize, gStrtSizeOff]; congr 1
      exact bytesT4_congrT fun j hj => kT _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
    have kA : ∀ a, AllocStaticFoot g a → bytesT1 m' a = bytesT1 m a := fun a ha => by
      by_cases hgr : Rng g 8 a
      · have h8 : (8 : Nat) ≤ gEnd := by decide
        exact k0 a (hIn.g_in a hgr.1 (by have := hgr.2; omega))
      · exact hk a fun hw => hw.elim (allocStatic_not_printW hsp hbuf' ha hgr) fun hr => by
          have e3 : heapEnd = 0x87800000 := rfl
          simp only [Rng, AllocStaticFoot] at hr ha hgr; omega
    have hR : PrRoom (prCost args i) ph' H' := by
      by_cases hi : i ≤ n
      · exact hroom hi _ hS.room
      · rw [prCost_past (by rw [hIn.len]; omega)]; exact fun h => absurd h (Nat.lt_irrefl 0)
    -- (lane F1-19) `_dtoa_r`'s bignums are kept chunks, `_REENT`'s words no write's
    have kB : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a := fun a ha =>
      ha.elim (fun hb => k0 a (hS.bigIn.inK a hb)) fun hr => hk a (reentWord_not_printW hsp hbuf' hr)
    refine ⟨FL, B, hS.api.congrT fun a ha => k0 a ?_, ⟨hl.facts.trans fun a ha => kK a (hl.kept a ha),
        fun a ha => (hl.kept a ha).mono hkept hbf, hl.apart, fun ts hts a h1 h2 => (hl.strs ts hts a h1 h2).mono hkept hbf,
        hl.marks, hl.cache.congr fun a h1 h2 => k0 a (hIn.g_in a (by omega) h2),
        TabFoot.trans hl.tab fun a ha => kK a (hl.kept a ha)⟩,
      fun a ha => (?_ : bytesT1 m' a = bytesT1 m a).trans (hS.keep a ha), hS.buf.trans hbf hS.chunks,
      fun c hc hu => hkept c (hS.chunks c hc hu) hu, hR, by rw [hn', hz]; exact hS.strt,
      (hS.safe.trans fun a ha => kK a (hl.kept a ha)).conseq fun M hM =>
        hM.mono fun a ha => ha.mono hkept hbf, hS.gc, fun h => (hS.stat h).congr kA, hS.big.trans kB, hS.bigIn,
      hS.big_fl⟩
    · rcases ha with h | h | h | h
      · exact hIn.L_in a (by simp only [Rng] at h; omega) (by simp only [Rng, stateSize] at h ⊢; omega)
      · exact hIn.L_in a (by simp only [Rng] at h; omega) (by simp only [Rng, stateSize] at h ⊢; omega)
      · exact hIn.L_in a (by simp only [Rng] at h; omega) (by simp only [Rng, stateSize] at h ⊢; omega)
      · exact hIn.nci_in a (by simp only [Rng] at h; omega) (by simp only [Rng, ciSize] at h ⊢; omega)
    · have hst : ∀ a, PrintStatic a → bytesT1 m' a = bytesT1 m a := fun a h => hk a (h.not_printW hsp hbuf')
      have hrb : Image.rodataBase = 0x8004ecc8 := rfl
      have hrs : Image.rodataSize = 55776 := rfl
      have ht : symTohost = 0x8005c6c0 := rfl
      rcases ha with h | h | h | h | h | h | h
      · exact (hIn.keep_in a h).elim (k0 a) (hst a)
      · exact k0 a (hIn.stack_in a (by simp only [ArgSlot] at h; omega)
          (by have := hp.room; simp only [ArgSlot] at h; omega))
      · exact hst a (.inl ⟨by omega, by omega⟩)
      · exact k0 a (hIn.g_in a (by simp only [Rng] at h; omega)
          (by simp only [Rng, gGcstpOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at h ⊢; omega))
      · exact k0 a (hIn.g_in a (by simp only [Rng] at h; omega)
          (by simp only [Rng, gMtOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at h ⊢; omega))
      · exact k0 a (hIn.L_in a (by simp only [Rng] at h; omega) (by simp only [Rng, stateGOff, stateSize] at h ⊢; omega))
      · exact k0 a (hIn.L_in a (by simp only [Rng] at h; omega)
          (by simp only [Rng, stateHookmaskOff, stateSize] at h ⊢; omega))

/-! ## `luaL_tolstring` on a literal argument -/

/-- (lane F1-18) **A literal's push keeps `g->strt`'s words** (`nuse`,
`size`): they are none of its stores. -/
theorem TolLitPost.strt {m m' : Mem} {sp L lenp g top ts len : Nat} {ls : LitPtrs}
    (hT : TolLitPost m m' sp L lenp g top ts len ls) (hsp : g + 64 + 16384 + 64 ≤ sp)
    (hL : L + 24 ≤ g ∨ g + 64 ≤ L + 16) (htop : top + 16 ≤ g ∨ g + 64 ≤ top)
    (hts : ts + 10 ≤ g ∨ g + 64 ≤ ts + 9)
    (hlo : 0x8005e7d8 ≤ L ∧ 0x8005e7d8 ≤ top ∧ 0x8005e7d8 ≤ ts ∧ 0x8005e7d8 ≤ g) :
    ∀ a, PrStatic g a → bytesT1 m' a = bytesT1 m a := by
  intro a ha
  simp only [PrStatic, AllocStaticFoot, Rng, gStrtNuseOff] at ha
  refine hT.keep a (.inr ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩) <;>
    simp only [Rng, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff, gcMarkedOff, not_and,
      Nat.not_lt] <;> omega

/-- The bytes of a represented string, as total reads. -/
theorem bytesAt_of_repr {m : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr (fillZeroMem m) ts s) :
    bytesAt m (ts + tstringContentsOff) s.length = s.map fun c => BitVec.ofNat 8 c.toNat := by
  have hb : BytesAt (fillZeroMem m) (ts + tstringContentsOff) s := by
    cases h with
    | short _ _ _ hb _ => exact hb
    | long _ _ _ hb _ => exact hb
  apply List.ext_getElem (by simp [bytesAt])
  intro i h1 h2
  simp only [bytesAt, List.length_range] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [← bytesT1_fill]
  simp [bytesT1, hb i (by simpa using h1)]

/-- (lane F1-18) **What a literal's push keeps**, as `prLitPost` reads it
(split off it: one declaration's budget). -/
structure LitKeeps (L nci g func n : Nat) (G B FL : Nat → Prop) (ph : StdoutPh) (H : HeapIx) (m m' : Mem) :
    Prop where
  fl : ∀ a, FL a → bytesT1 m' a = bytesT1 m a
  strt : ∀ a, PrStatic g a → bytesT1 m' a = bytesT1 m a
  keep : ∀ a, PrKeep L g func n G a → bytesT1 m' a = bytesT1 m a
  api : ∀ a, ApiFoot L nci a → ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a
  io : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a
  /-- (lane F1-19) `_dtoa_r`'s bignums and `_REENT`'s words -/
  big : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a

theorem litKeeps {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m m' : Mem}
    {ts len i : Nat}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hT : TolLitPost m m' (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ts len ls)
    (hts : ts ∈ ls.strs) : LitKeeps L nci g func n G B FL ph H m m' := by
  have q := hn.ok
  have hp := hIn.placed
  have hp' := hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp'
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ts hts
  have hl := hS.lits
  -- the run's stores: `L->top`, the slot, `g`'s cache, `totalbytes`, `GCdebt`, the mark, `&l`, below `sp0 - 64`
  have kW : ∀ a, a < heapEnd + 32 → ¬ Rng (L + 16) 8 a → ¬ Rng (func + 16 * n + 16) 16 a →
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a → ¬ Rng (g + gTotalbytesOff) 8 a →
      ¬ Rng (g + gGCdebtOff) 8 a → ¬ Rng (ts + gcMarkedOff) 1 a → bytesT1 m' a = bytesT1 m a :=
    fun a h0 h1 h2 h3 h4 h5 h6 => hT.keep a (.inr ⟨by omega, h1, h2, h3, h4, h5, h6⟩)
  -- the literals' footprint is off them
  have kFL : ∀ a, FL a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have hd : ∀ x, D x → ¬ FL x := fun x hx hf => hl.apart x hf hx
    have hlo := (hl.kept a ha).hi
    refine kW a (by omega) (fun h => hd a (hIn.dirty a (.inl (by simpa only [stateTopOff] using h))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inl (by simp only [Rng] at h; have := hp.room; omega)))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inr (.inr (.inr (by
        simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at h ⊢; omega)))))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inr (.inl h)))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inr (.inr (.inl h))))) ha) fun h => ?_
    have := hl.marks ts hts
    simp only [Rng] at h
    rw [show a = ts + gcMarkedOff by omega] at ha
    exact this ha
  have hl' : LitsFoot g sl ls H ph D FL m' :=
    hl.trans kFL hT.cache
  -- (lane F1-18) `g->strt`'s words are off them
  have kT := hT.strt (by homega) (by simp only [stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at p10; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at p12; have := hp.room; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at tlg; omega)
    ⟨by have : heapStart = 0x8006ecd0 := rfl; omega, by have : heapStart = 0x8006ecd0 := rfl; omega,
      by have : heapStart = 0x8006ecd0 := rfl; omega, by have : heapStart = 0x8006ecd0 := rfl; omega⟩
  -- the kept bytes are off them
  have kK : ∀ a, PrKeep L g func n G a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have hsym : symTohost = 0x8005c6c0 := rfl
    have hat : symAtexit = 0x8005d450 := rfl
    rcases ha with h | h | h | h | h | h | h
    · obtain ⟨g1, g2, g3, g4, g5⟩ := hIn.keep_apart a h
      have g6 := g5 ts hts
      have hlo : a < heapEnd := (hIn.keep_in a h).elim (fun k => k.hi) fun k => by
        simp only [PrintStatic] at k; pr_omega
      refine kW a (by omega) (by simpa only [stateTopOff] using g1) ?_ ?_ ?_ ?_ ?_ <;> pr_omega
    all_goals refine kW a ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> pr_omega
  -- the API frame is off them
  have kA : ∀ a, ApiFoot L nci a → ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a := by
    intro a ha h1
    have := hn.sep
    refine kW a (by pr_omega) h1 ?_ ?_ ?_ ?_ ?_ <;> pr_omega
  -- `stdout`'s footprint is off them
  have kP : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have nK : ∀ {x}, Kept H0 ph0 x → ¬ PrintFoot ph H x := fun h => (hS.kept h).not_printFoot
    have hlo : a < heapEnd + 32 := by
      rcases ha with hg | hb | ⟨hr, _⟩ | hr
      · simp only [StdioGlob] at hg; omega
      · have := hP.io.buf_hi a hb; omega
      · simp only [HeapReads] at hr
        have e4 : symMallocAv = 0x8005c6d0 := rfl
        have e5 : symMallocSbrkBase = 0x8005d388 := rfl
        have e6 : symBrk = 0x8005d3b8 := rfl
        have e7 : symMallocTopPad = 0x8005d3d8 := rfl
        have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
        have e9 : symMallocMallinfo = 0x8005e560 := rfl
        omega
      · omega
    refine kW a hlo (fun h => nK (hIn.L_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.stack_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.g_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.g_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.g_in a (by pr_omega) (by pr_omega)) ha) fun h => ?_
    have := hl.strs ts hts a (by pr_omega) (by pr_omega)
    exact this.not_printFoot ha
  -- (lane F1-19) `_dtoa_r`'s bignums are apart from the objects, `_REENT`'s words below the heap
  have kB : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    rcases ha with hb | hr
    · have hx := hS.bigIn.x a hb
      have hlt := hS.bigIn.lit ts hts a
      have hkh := (hS.bigIn.inK a hb).hi
      simp only [PrX, not_or] at hx
      obtain ⟨-, hxL, hxg, hxs, -, -⟩ := hx
      refine kW a (by omega) (fun h => hxL ?_) (fun h => hxs ?_) (fun h => hxg ?_) (fun h => hxg ?_)
        (fun h => hxg ?_) fun h => hlt ?_ ?_ hb <;> pr_omega
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr
      refine kW a (by omega) ?_ ?_ ?_ ?_ ?_ ?_ <;> pr_omega
  exact ⟨kFL, kT, kK, kA, kP, kB⟩

/-- **`TolPost` from a literal's push** (`tol_nil`, `tol_true`, `tol_false`):
the state with one more value (the literal at the top), `stdout` as it was,
the frame but the length word, the length, the literal's bytes (from the
literals' facts, `hsel`), where they lie. -/
theorem prLitPost {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m m' : Mem}
    {ts len i : Nat} {s : List UInt8} {v : Value}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hi : 1 ≤ i) (hv : args[i - 1]? = some v) (h0 : argCost v = 0)
    (hT : TolLitPost m m' (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ts len ls)
    (hts : ts ∈ ls.strs) (hsel : ∀ M rt, LitsIn M g sl ls rt → TStringRepr (fillZeroMem M) ts s)
    (hlen : s.length = len) (hl5 : len ≤ 5) :
    TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1))
      (s.map fun c => BitVec.ofNat 8 c.toNat) ph m m' (ts + 24) H H := by
  have q := hn.ok
  have hp := hIn.placed
  have hp' := hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp'
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ts hts
  have hl := hS.lits
  have K := litKeeps hIn hn hS hP hT hts
  have kFL := K.fl; have kT := K.strt; have kK := K.keep; have kA := K.api; have kP := K.io
  have hl' : LitsFoot g sl ls H ph D FL m' :=
    hl.trans kFL hT.cache
  -- the literal's bytes, from the literals' facts at `m'`
  obtain ⟨rt, hLI⟩ := hl'.facts.self
  have hb := bytesAt_of_repr (hsel m' rt hLI)
  rw [hlen] at hb
  have hapi := hS.api
  have hlen' : (s.map fun c => BitVec.ofNat 8 c.toNat).length = len := by simp [hlen]
  have kstr : ∀ a, ts ≤ a → a < ts + 30 → Kept H ph a := fun a h1 h2 => hl.strs ts hts a h1 h2
  refine
    { lua := ⟨FL, B, hS.next0 hi hv h0 ⟨?_, ?_, ?_, ?_, by have := hapi.tbc_lt; omega⟩ hl'
        (fun a ha => (kK a ha).trans (hS.keep a ha)) kFL kT K.big⟩
      io := hP.keep kP
      kept := fun c hc _ => hc
      frame := fun a h1 h2 => hT.keep a (.inl ⟨by omega, by simp only [Rng]; omega⟩)
      len := by rw [hT.len_w, hlen']
      bytes := by rw [hlen']; exact hb
      src_lo := SrcLo.of_hi (by have : errnoAddr = 0x8005d408 := rfl; homega)
      src_hi := by rw [hlen']; omega
      src_ok := fun a h1 h2 => ?_
      src_out := by rw [hlen']; have : stdoutFile = 0x8005e668 := rfl; have : fileSize = 184 := rfl; omega
      src_buf := fun a h1 h2 => (kstr a (by omega) (by rw [hlen'] at h2; omega)).nbuf }
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inl ⟨by omega, by omega⟩)) (by simp only [Rng]; omega)).trans
      hapi.ci_w
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inr ⟨by omega, by omega⟩))) (by
      have := hn.sep; simp only [Rng]; omega)).trans hapi.func_w
  · rw [hT.top_w]; congr 1
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inl ⟨by omega, by omega⟩))) (by
      simp only [Rng]; omega)).trans hapi.tbc_w
  · rw [hlen'] at h2
    have hk := kstr a (by omega) (by omega)
    have hsp : heapEnd + 4096 ≤ sp0 - 64 := by homega
    exact ⟨fun hg => hk.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inl hg)),
      fun hm => hk.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inl hm))),
      fun hs => hk.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inr (.inl hs))))⟩

/-- A nil or boolean value (`luaL_tolstring` pushes a C literal). -/
def IsLit : Value → Prop
  | .nil => True
  | .bool _ => True
  | _ => False

theorem argBytes_nil : argBytes .nil = nilB.map (fun c => BitVec.ofNat 8 c.toNat) := by
  simp [argBytes, Value.show, nilB]

theorem argBytes_true : argBytes (.bool true) = trueB.map (fun c => BitVec.ofNat 8 c.toNat) := by
  simp [argBytes, Value.show, trueB]

theorem argBytes_false : argBytes (.bool false) = falseB.map (fun c => BitVec.ofNat 8 c.toNat) := by
  simp [argBytes, Value.show, falseB]

/-- **The facts `tol_nil`/`tol_true`/`tol_false` need**, at `luaB_print`'s
state of `n` values, for argument `i` with tag `tag` at `G(L)->mt[t]`. -/
theorem tolLit_in {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {i : Nat} {r : BitVec 64} {ts : Nat} {t : Nat} {tag : BitVec 8}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hr : r.toNat % 4 = 0) (hts : ts ∈ ls.strs) (ht : t ∈ [luaTnil, luaTboolean, luaTnumber])
    (htag : slotTag m (func + 16 * i) = tag) :
    TolNums (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g ts r ∧
    TolCells m L i nci func (func + 16 * n + 16) g t tag ∧
    TolLitIn m (sp0 - 64) L (func + 16 * n + 16) g sl ls FL := by
  have q := hn.ok
  have q1 := q.sp_lo; have q2 := q.sp_hi; have q3 := q.sp_al; have q4 := q.L_al
  have q5 := hn.sp_big; have q6 := hn.n_small
  have hp := hIn.placed
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ts hts
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  have hga := hIn.g_al
  have kG : ∀ a, Rng (L + stateGOff) 8 a → bytesT1 m a = bytesT1 M0 a := fun a h => hS.keep a (.inr (.inr (.inr
    (.inr (.inr (.inl h))))))
  have kMt : ∀ a, Rng (g + gMtOff) 32 a → bytesT1 m a = bytesT1 M0 a := fun a h => hS.keep a (.inr (.inr (.inr
    (.inr (.inl h)))))
  have hapi := hS.api
  refine ⟨?_, ⟨hapi.ci_w, hapi.func_w, hapi.top_w, ?_, ?_, ?_⟩, ⟨hS.lits.facts, fun a ha => (hS.lits.kept a ha).hi,
    hS.lits.cache, ?_, fun o ho => ?_, ?_, ?_, ?_, ?_⟩⟩
  · constructor <;> first | exact hr | pr_omega
  · exact (bytesT8_congrT fun j _ => kG _ (by simp only [Rng, stateGOff]; omega)).trans hIn.g_w
  · rw [show g + 480 + 8 * t = g + gMtOff + 8 * t by rfl]
    have hto : t ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, luaTnil, luaTboolean, luaTnumber] at ht; omega
    exact (bytesT8_congrT fun j _ => kMt _ (by simp only [Rng, gMtOff]; omega)).trans (hIn.mt t ht)
  · rw [show 16 * i + func + 8 = func + 16 * i + tvalueTagOff by simp only [tvalueTagOff]; omega]; exact htag
  · exact (hS.keep _ (.inr (.inr (.inr (.inl ⟨Nat.le_refl _, Nat.lt_succ_self _⟩))))).trans hIn.gcstp
  · exact (hS.keep _ (.inr (.inr (.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ho _⟩)))).trans (hIn.ro o ho)
  · exact ⟨by decide, by omega, by omega, by pr_omega, by pr_omega, by pr_omega, by pr_omega, by pr_omega,
      by pr_omega, hga, by pr_omega, by pr_omega, by have := hIn.f_al; omega, by simp only [Apart]; pr_omega, by simp only [Apart]; pr_omega,
      by simp only [Apart]; pr_omega⟩
  · pr_omega
  · intro a ha hr
    apply hS.lits.apart a ha
    apply hIn.dirty a
    simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at hr ⊢
    exact .inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))
  · intro ts' hts'
    have ob := hIn.objs
    have e1 := ob.lit_L ts' hts'; have e2 := ob.lit_g ts' hts'; have e3 := ob.lit_stack ts' hts'
    simp only [Apart] at e1 e2 e3 ⊢
    exact ⟨e1, e2, by simp only [Apart]; pr_omega⟩

theorem _root_.Lua.Vm.Sim.ValRepr.tag_nil {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    (h : ValRepr mo ι t x .nil) : t = 0#8 := by cases h; rfl

theorem _root_.Lua.Vm.Sim.ValRepr.tag_true {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    (h : ValRepr mo ι t x (.bool true)) : t = 0x11#8 := by cases h; rfl

theorem _root_.Lua.Vm.Sim.ValRepr.tag_false {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    (h : ValRepr mo ι t x (.bool false)) : t = 0x01#8 := by cases h; rfl

/-- **A literal argument's `luaL_tolstring`** from the run that pushes the
literal (`tol_nil`, `tol_true`, `tol_false`): `TolPost` by `prLitPost`. -/
theorem tolLit_case {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {o : Array String} {r : BitVec 64} {f : AbiFrame} {i ts len : Nat} {s : List UInt8} {v : Value}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hi : 1 ≤ i) (hv : args[i - 1]? = some v) (h0 : argCost v = 0)
    (hrun : Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 i⟩, ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r (sp0 - 64) (ts + 24) f m' o c ∧
        TolLitPost m m' (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ts len ls))
    (hts : ts ∈ ls.strs) (hsel : ∀ M rt, LitsIn M g sl ls rt → TStringRepr (fillZeroMem M) ts s)
    (hlen : s.length = len) (hl5 : len ≤ 5) (hb : argBytes v = s.map fun c => BitVec.ofNat 8 c.toNat) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧
        TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (argBytes v) ph m m' s H H') := by
  intro c h
  obtain ⟨c', s', m', hret, hpost⟩ := hrun c h
  refine ⟨c', s', m', ts + 24, H, hret, ?_⟩
  rw [hb]
  exact prLitPost hIn hn hS hP hi hv h0 hpost hts hsel hlen hl5

/-- **`luaL_tolstring` on a nil or boolean argument in `luaB_print`'s loop**,
from `PushLit_Statement` (`tol_nil`, `tol_true`, `tol_false`, `tolLit_case`). -/
theorem tolLit_proved (hPL : PushLit_Statement) : TolArg IsLit := by
  intro sp0 L nci func n tbc sl g ls args ι D G B FL ph0 H0 M0 i v hIn hn hv hC hi1 hin ph H m o r f hS hP hr
  have hA : ArgsAt func ι args m := hIn.args_fz m fun a ha => hS.keep a (by
    rcases ha with h | h
    · exact .inl h
    · exact .inr (.inl h))
  have hval := hA (i - 1) v hv
  have hidx : func + 16 * (i - 1 + 1) = func + 16 * i := by congr 1; omega
  rw [hidx] at hval
  cases v with
  | nil =>
    obtain ⟨hx, hc, hT⟩ := tolLit_in (ts := ls.nil) (t := luaTnil) hIn hn hS hi1 hin hr (by simp [LitPtrs.strs])
      (by simp) hval.tag_nil
    exact tolLit_case hIn hn hS hP hi1 hv rfl (tol_nil hPL f o hx hc hT) (by simp [LitPtrs.strs]) (fun M rt h => h.nil.repr)
      rfl (by decide) argBytes_nil
  | bool b =>
    cases b with
    | true =>
      obtain ⟨hx, hc, hT⟩ := tolLit_in (ts := ls.tru) (t := luaTboolean) hIn hn hS hi1 hin hr
        (by simp [LitPtrs.strs]) (by simp) hval.tag_true
      exact tolLit_case hIn hn hS hP hi1 hv rfl (tol_true hPL f o hx hc hT) (by simp [LitPtrs.strs])
        (fun M rt h => h.tru.repr) rfl (by decide) argBytes_true
    | false =>
      obtain ⟨hx, hc, hT⟩ := tolLit_in (ts := ls.fls) (t := luaTboolean) hIn hn hS hi1 hin hr
        (by simp [LitPtrs.strs]) (by simp) hval.tag_false
      exact tolLit_case hIn hn hS hP hi1 hv rfl (tol_false hPL f o hx hc hT) (by simp [LitPtrs.strs])
        (fun M rt h => h.fls.repr) rfl (by decide) argBytes_false
  | int _ => exact absurd hC id
  | flt _ _ => exact absurd hC id
  | str _ => exact absurd hC id
  | builtin _ => exact absurd hC id

/-! ## The line -/

/-- A byte as a character (`charsOf`'s). -/
abbrev chr (b : BitVec 8) : Char := Char.ofNat b.toNat

theorem icat_snoc {α : Type} (sep : List α) :
    ∀ (l : List (List α)) (x : List α), l ≠ [] → sep.intercalate (l ++ [x]) = sep.intercalate l ++ sep ++ x
  | [], _, h => absurd rfl h
  | [a], x, _ => by simp [List.intercalate_cons_cons]
  | a :: b :: t, x, _ => by
    rw [List.cons_append, List.cons_append, List.intercalate_cons_cons, ← List.cons_append,
      icat_snoc sep (b :: t) x (by simp), List.intercalate_cons_cons]
    simp [List.append_assoc]

/-- **`luaB_print`'s line, as characters**: the arguments' characters
separated by tabs. -/
theorem prLine_map (bs : Nat → List (BitVec 8)) (xs : List (List Char))
    (h : ∀ i (hi : i < xs.length), (bs (i + 1)).map chr = xs[i]) :
    ∀ k, k ≤ xs.length → (prLine bs k).map chr = ['\t'].intercalate (xs.take k)
  | 0, _ => by simp [prLine]
  | 1, hk => by
    have := h 0 (by omega)
    cases xs with
    | nil => simp at hk
    | cons x t => simpa [prLine] using this
  | k + 2, hk => by
    have ih := prLine_map bs xs h (k + 1) (by omega)
    have hx := h (k + 1) (by omega)
    have hne : xs.take (k + 1) ≠ [] := by
      have : (xs.take (k + 1)).length = k + 1 := by rw [List.length_take]; omega
      intro he; rw [he] at this; simp at this
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp only [prLine, List.map_append, List.map_cons, ih, hx, Option.toList_some]
    rw [icat_snoc _ _ _ hne]
    simp [chr]

/-- (lane F1-18) A decimal digit string's characters are bytes. -/
theorem toDigits_ascii (n : Nat) : ∀ c ∈ Nat.toDigits 10 n, c.toNat < 256 := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    by_cases h : n < 10
    · rw [Nat.toDigits_of_lt_base h]
      intro c hc
      simp only [List.mem_singleton] at hc
      subst hc; rw [Nat.toNat_digitChar_of_lt_ten h]; omega
    · rw [Nat.toDigits_of_base_le (by decide) (by omega)]
      intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact ih (n / 10) (by omega) c hc
      · simp only [List.mem_singleton] at hc
        subst hc; rw [Nat.toNat_digitChar_of_lt_ten (Nat.mod_lt n (by decide))]; omega

/-- (lane F1-18) An integer's decimal characters are bytes. -/
theorem int_ascii (x : Int) : ∀ c ∈ (toString x).toList, c.toNat < 256 := by
  intro c hc
  simp only [toString, Int.repr_eq_ite] at hc
  split at hc
  · simp only [Nat.repr, String.toList_ofList] at hc
    exact toDigits_ascii _ c hc
  · simp only [Nat.repr, String.toList_append, String.toList_ofList, List.mem_append] at hc
    rcases hc with hc | hc
    · simp at hc; subst hc; decide
    · exact toDigits_ascii _ c hc

/-- The characters of a value that is no float and no function are bytes
(lane F1-18: integers too). -/
theorem show_ascii (v : Value) (hf : ¬ IsFlt v) (hn : ¬ IsFn v) :
    ∀ c ∈ (Value.show binaryHost v).toList, c.toNat < 256 := by
  intro c hc
  cases v with
  | nil => simp [Value.show] at hc; rcases hc with rfl | rfl | rfl <;> decide
  | bool b =>
    cases b <;> simp [Value.show] at hc
    · rcases hc with rfl | rfl | rfl | rfl | rfl <;> decide
    · rcases hc with rfl | rfl | rfl | rfl <;> decide
  | str s =>
    simp only [Value.show, bytesToString, String.toList_ofList, List.mem_map] at hc
    obtain ⟨b, -, rfl⟩ := hc
    have := UInt8.toNat_lt b
    rw [show (Char.ofNat b.toNat).toNat = b.toNat by
      rw [Char.ofNat, dif_pos (Or.inl (by omega))]; rfl]
    omega
  | int i => exact int_ascii _ c hc
  | flt _ _ => exact absurd trivial hf
  | builtin _ => exact absurd trivial hn

/-- The characters of a value whose characters are bytes. -/
theorem argBytes_chars (v : Value) (h : ∀ c ∈ (Value.show binaryHost v).toList, c.toNat < 256) :
    (argBytes v).map chr = (Value.show binaryHost v).toList := by
  have key : ∀ (c : Char), c.toNat < 256 → chr (BitVec.ofNat 8 c.toNat) = c := fun c hc => by
    simp only [chr, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc, Char.ofNat_toNat]
  simp only [argBytes, List.map_map]
  conv => rhs; rw [← List.map_id (Value.show binaryHost v).toList]
  apply List.map_congr_left
  intro c hc
  exact key c (h c hc)

/-- **The console's line** from `luaB_print`'s bytes (no float, no function). -/
theorem prLine_chars (args : List Value) (hna : ∀ v ∈ args, ¬ IsFlt v ∧ ¬ IsFn v) :
    charsOf (prLine (fun i => argBytes (args.getD (i - 1) .nil)) args.length ++ [0x0a#8]) =
      printLine binaryHost args := by
  have h : ∀ i (hi : i < (args.map fun v => (Value.show binaryHost v).toList).length),
      ((fun i => argBytes (args.getD (i - 1) .nil)) (i + 1)).map chr =
        (args.map fun v => (Value.show binaryHost v).toList)[i] := by
    intro i hi
    simp only [List.length_map] at hi
    show List.map chr (argBytes (args.getD (i + 1 - 1) .nil)) = _
    rw [Nat.add_sub_cancel, List.getElem_map, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
    have hm := hna _ (List.getElem_mem hi)
    exact argBytes_chars _ (show_ascii _ hm.1 hm.2)
  have hl := prLine_map (fun i => argBytes (args.getD (i - 1) .nil))
    (args.map fun v => (Value.show binaryHost v).toList) h args.length (by simp)
  rw [List.take_of_length_le (by simp)] at hl
  simp only [charsOf, printLine, List.map_append, List.map_cons, List.map_nil]
  rw [← String.ofList_toList (s := String.intercalate "\t" _ ++ "\n")]
  congr 1
  rw [String.toList_append, String.toList_intercalate, hl, List.map_map]
  rfl

/-! ## The assembly -/

/-- (lane F1-19) **`PrintAllocOff_Statement`, proved**: it is vacuous, the
room `PrBudget` gives every new string a bucket (`luaS_resize` is beyond
`HeapBudget`, A8). -/
theorem printAllocOff_proved : PrintAllocOff_Statement := by
  intro sp L nci func n tbc sl g ls args ι D G ph H f M o hQ hIn hn hbud
  exact absurd (hbud hQ.1).strt (Nat.not_le.mpr hQ.2.2)

/-- **`luaB_print` on the C frame from its parts** (lane F1-15; split by value
class, lane F1-18): a list with a float by `PrintFlt_Statement`, with a
function by `PrintFn_Statement`; otherwise `print_sum` over `PrSt'`
(`printLua_st`, the per-argument budget from `PrBudget`, lane F1-19 the
string table's safety and `_dtoa_r`'s bignums from `PrintIn.alloc`),
`luaL_tolstring` per argument by `tolLit_proved` (nil, booleans),
`TolStr_Statement` (strings) and `TolInt_Statement` (integers). -/
theorem printRel_of (hM : MallocR_Statement) (hPL : PushLit_Statement) (hTS : TolStr_Statement)
    (hTI : TolInt_Statement) (hFl : PrintFlt_Statement) (hFn : PrintFn_Statement) : PrintRel_Statement := by
  intro sp L nci func n tbc sl g ls args ι D G ph H f M o _ hIn hn hbud
  by_cases hfl : HasClass IsFlt args
  · exact hFl sp L nci func n tbc sl g ls args ι D G ph H f M o hfl hIn hn hbud
  by_cases hfn : HasClass IsFn args
  · exact hFn sp L nci func n tbc sl g ls args ι D G ph H f M o hfn hIn hn hbud
  have hna : ∀ v ∈ args, ¬ IsFlt v ∧ ¬ IsFn v := fun v hv => ⟨fun h => hfl ⟨v, hv, h⟩, fun h => hfn ⟨v, hv, h⟩⟩
  have hlen := hIn.len
  -- the state before the first argument
  obtain ⟨FL, B, hA⟩ := hIn.alloc
  have hS0 : PrSt L nci func tbc sl g n ls args D G B FL M ph H 1 n ph H M := by
    refine ⟨hIn.api, hA.lits, fun _ _ => rfl, fun _ h => .inl h, fun _ h _ => h, fun hpos => ?_,
      fun hpos => (hbud (anyAlloc_of_allocs hpos)).strt, hA.safe, fun _ => hIn.gc, fun _ => hIn.stat, hA.big,
      hA.bigIn, hA.big_fl⟩
    have hb := (hbud (anyAlloc_of_cost hpos)).brk
    have h1 := stdoutNeed_le ph
    have e : prCost args 1 = (args.map argCost).sum := by simp [prCost]
    rw [e]
    simp only [callBudget, extRoom] at hb
    generalize heapEnd = E at *
    omega
  have hTL := tolLit_proved hPL
  have hL : PrintLua L (sp - 96) n (PrSt' L nci func tbc sl g n ls args D G M ph H)
      (fun i => argBytes (args.getD (i - 1) .nil)) := by
    refine printLua_st hIn hn fun i ph' H' m o' r f' hi1 hin ⟨FL', B', hS⟩ hP hr => ?_
    have hv : args[i - 1]? = some (args.getD (i - 1) .nil) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
    have hnv := hna _ (List.mem_of_getElem? hv)
    cases hw : args.getD (i - 1) .nil with
    | nil => rw [hw] at hv; exact hTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIn hn hv trivial hi1 hin _ _ _ _ _ _ hS hP hr
    | bool b => rw [hw] at hv; exact hTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIn hn hv trivial hi1 hin _ _ _ _ _ _ hS hP hr
    | str s => rw [hw] at hv; exact hTS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIn hn hv trivial hi1 hin _ _ _ _ _ _ hS hP hr
    | int _ => rw [hw] at hv; exact hTI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hIn hn hv trivial hi1 hin _ _ _ _ _ _ hS hP hr
    | flt _ _ => rw [hw] at hnv; exact absurd trivial hnv.1
    | builtin _ => rw [hw] at hnv; exact absurd trivial hnv.2
  intro c h
  obtain ⟨c', hs, m', out, hret, hend⟩ :=
    print_sum hM hL 0x8000ac8c#64 (pcFr L f) M o ph H hn.ok ⟨FL, B, hS0⟩ hIn.st c h
  refine ⟨c', hs, m', out, hret, ?_⟩
  obtain ⟨buf, H', hP', ⟨FL', B', hS'⟩, hk⟩ := hend.st
  refine ⟨?_, .intro buf H' ⟨hP', hk, hS'.buf, .intro FL' B' ⟨hS'.lits, hS'.safe, hS'.big,
    ⟨fun a hb => (hS'.bigIn.inK a hb).mono hS'.chunks hS'.buf, hS'.bigIn.x, hS'.bigIn.lit⟩, hS'.big_fl⟩⟩,
    fun a ha => hS'.keep a (.inl ha), hend.above⟩
  rw [hend.out, hIn.pend, List.nil_append, ← hlen]
  exact prLine_chars args hna

end Lua.Vm.Sim.Kit

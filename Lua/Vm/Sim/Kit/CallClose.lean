import Lua.Vm.Sim.Kit.CallOpen
import Lua.Vm.Sim.Entry

/-!
# `OP_CALL print`'s close: the relation after the call (lane F1-13)

`call_close`: the facts `PrintCall_Statement`'s post needs (`CallOut` and the
`CALL` invariant at the pointers after the call) from what the call's run
leaves (`CloseIn`): the line, `stdout` set up with the heap, the interned
literals, and region facts relative to the head's memory and complement.
The new complement is the zero fill of the final memory; the objects a `print`
leaves alone come from the invariant's frozen facts (`CallInvAt.stat` at the
final memory: one application of the frozen facts, no per-object frame), the
`CallInfo`'s words and the caller frames from the region facts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## Reads of a zero fill -/

/-- A little-endian read of present bytes is some value. -/
theorem rdLE_isSome {m : Mem} {a n : Nat} (h : ∀ j, j < n → (m[a + j]?).isSome) : (rdLE m a n).isSome := by
  unfold rdLE
  have : ∀ l : List Nat, (∀ j ∈ l, j < n) →
      (l.foldr (fun i acc => do let b ← m[a + i]?; let r ← acc; pure (b.toNat + 256 * r)) (some 0)).isSome := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x t ih =>
      simp only [List.foldr_cons]
      obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 (h x (hl x (List.mem_cons_self ..)))
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (ih fun j hj => hl j (List.mem_cons_of_mem _ hj))
      rw [hb, hr]; rfl
  exact this _ fun j hj => List.mem_range.mp hj

/-- A zero fill reads its RAM words as the total reads. -/
theorem rd64_fill (m : Mem) {a : Nat} (h1 : 0x80000000 ≤ a) (h2 : a + 8 ≤ 0x88000000) :
    rd64 (fillZeroMem m) a = some (bytesT8 m a).toNat := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (rdLE_isSome (m := fillZeroMem m) (a := a) (n := 8)
    fun j hj => by rw [fill_get m (a := a + j) (by omega) (by omega)]; rfl)
  have hx' : rd64 (fillZeroMem m) a = some x := hx
  have e := bytesT8_of_rd64 hx'
  have hlt := rd64_lt hx'
  rw [hx', ← bytesT8_congrT (m := fillZeroMem m) (m' := m) fun i _ => bytesT1_fill m _, e,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- A read of a dense memory transfers to the zero fill of a memory that
agrees with it there. -/
theorem rdLE_fill {m mo : Mem} (hd : ∀ a, 0x80000000 ≤ a → a < 0x88000000 → (mo[a]?).isSome) {a n : Nat}
    (h1 : 0x80000000 ≤ a) (h2 : a + n ≤ 0x88000000) (hk : ∀ j, j < n → bytesT1 m (a + j) = bytesT1 mo (a + j)) :
    rdLE (fillZeroMem m) a n = rdLE mo a n :=
  rdLE_congr fun j hj => by
    rw [fill_get m (a := a + j) (by omega) (by omega), hk j hj]
    have := hd (a + j) (by omega) (by omega)
    cases hmo : mo[a + j]? with
    | none => rw [hmo] at this; cases this
    | some b => simp [bytesT1, hmo]

/-- A value's representation carried to a memory where the owned strings are. -/
theorem _root_.Lua.Vm.Sim.ValRepr.transfer {mo mo' : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {v : Value}
    (h : ValRepr mo ι t x v) (hs : ∀ ts s, ι.own ts s → TStringRepr mo' ts s) : ValRepr mo' ι t x v := by
  cases h with
  | nil => exact .nil
  | false_ => exact .false_
  | true_ => exact .true_
  | int => exact .int
  | flt => exact .flt
  | str _ hp ho => exact .str (hs _ _ ho) hp ho
  | print hx => exact .print hx

/-- The bins of a heap as the witness's list. -/
def binsList (bins : Nat → List Nat) : List (List Nat) := (List.range numBins).map bins

theorem binsList_get (bins : Nat → List Nat) {i : Nat} (hi : i < numBins) :
    (binsList bins).getD i [] = bins i := by
  simp [binsList, List.getD_eq_getElem?_getD, hi]

/-- `HeapAt` over the witness's list of bins. -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.toBinsList {m : Mem} {top brk : Nat} {cs : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m top brk cs bins) : HeapAt m top brk cs (fun i => (Kit.binsList bins).getD i []) := by
  have e : ∀ i, i < numBins → (Kit.binsList bins).getD i [] = bins i := fun i hi => binsList_get bins hi
  refine ⟨h.sbrk_base, h.brk, h.brk_le, h.top_ptr, h.top_le, h.top_size, h.top_header, h.top_pad,
    h.max_sbrked, h.mallinfo, h.first_prev, h.walk, h.coalesced, h.footer,
    fun i h0 hi => by rw [e i hi]; exact h.bins_list i h0 hi, fun i => ?_,
    fun i q h0 hi hq => by rw [e i hi] at hq; exact h.bin_free i q h0 hi hq, fun c hc hu => ?_,
    by rw [e 1 (by decide)]; exact h.remainder, h.binblocks_present,
    fun bb hb i h1 hi hn => by rw [e i hi] at hn; exact h.binblocks bb hb i h1 hi hn⟩
  · by_cases hi : i < numBins
    · rw [e i hi]; exact h.bins_nodup i
    · simp [Kit.binsList, List.getD_eq_getElem?_getD, hi]
  · have := h.free_binned c hc hu
    rwa [List.filter_congr fun i hi => by rw [e i (List.mem_range.mp hi)]]

/-- The witness after a call: the heap's indices replaced. -/
def _root_.Lua.Vm.RtPtrs.withHeap (rt : RtPtrs) (H : HeapIx) : RtPtrs :=
  { rt with top := H.top, brkv := H.brk, chunks := H.chunks, bins := binsList H.bins }

/-! ## The close -/

/-- **What the call's run leaves**, at the final memory `m` (the head's
memory `c.σ.mem`, the complement `w.mo`): the line; `stdout` set up and
flushed with the heap `H` (the old chunks in use kept, the buffer the old
one or fresh); the literals interned again (`FL`); the frozen footprint `F`,
the Lua `CallInfo` but `next` and `savedpc`, `__atexit` kept from the
complement; the frames from `sp` up and the registers below `R[A]` kept from
the head; the results nil; `L->ci` back; the C `CallInfo` `nci` after the Lua
one, where it lies. -/
structure CloseIn (p : Proto) (c : Config) (w : RelPtrs) (ins : Word) (args : List Value) (ph : StdoutPh)
    (F : Nat → Prop) (ls : LitPtrs) (m : Mem) (out : List (BitVec 8)) (nci buf : Nat) (H : HeapIx)
    (FL : Nat → Prop) : Prop where
  line : charsOf out = printLine binaryHost args
  text : Arms.TextLoaded m
  st : PrintSt m (.up buf []) H
  kept : ∀ c ∈ w.rt.chunks, c.inuse = true → c ∈ H.chunks
  bufFrom : BufFrom ph (.up buf []) w.rt.hix
  lits : LitsFoot w.rt.g w.rt.stackLast ls H (.up buf [])
    (fun a => CallLitDirty w a ∨ (nci ≤ a ∧ a < nci + ciSize)) FL m
  foot : ∀ a, F a → bytesT1 m a = bytesT1 w.mo a
  ci : ∀ a, w.ci ≤ a → a < w.ci + ciSize → ¬ Rng (w.ci + ciNextOff) 8 a → ¬ Rng (w.ci + ciSavedpcOff) 8 a →
    bytesT1 m a = bytesT1 w.mo a
  above : ∀ a, w.sp ≤ a → bytesT1 m a = bytesT1 c.σ.mem a
  below : ∀ a, w.base ≤ a → a < w.slot ins.a → bytesT1 m a = bytesT1 c.σ.mem a
  atexit : ∀ j, j < 8 → bytesT1 m (symAtexit + j) = bytesT1 w.mo (symAtexit + j)
  nil : ∀ j, ins.a ≤ j → j < ins.a + ins.c - 1 → slotTag m (w.slot j) = BitVec.ofNat 8 vNil
  lci : bytesT8 m (w.L + stateCiOff) = BitVec.ofNat 64 w.ci
  next : bytesT8 m (w.ci + ciNextOff) = BitVec.ofNat 64 nci
  nci_ne : nci ≠ 0
  nci_lo : symEnd ≤ nci
  nci_hi : nci + ciSize ≤ RuntimeData.spEntry - cStackBudget
  nci_al : nci % 8 = 0
  nci_prev : bytesT8 m (nci + ciPreviousOff) = BitVec.ofNat 64 w.ci
  nci_kept : ∀ a, nci ≤ a → a < nci + ciSize → Kept H (.up buf []) a ∧ ¬ F a
  nci_L : Apart nci ciSize w.L stateSize
  nci_g : Apart nci ciSize w.rt.g gEnd
  nci_ci : Apart nci ciSize w.ci ciSize
  nci_stack : Apart nci ciSize w.func (w.rt.stackLast - w.func)
  nci_lits : ∀ ts ∈ ls.strs, Apart nci ciSize ts 30

/-- `omega` over the relation's ranges, the layout and the window. -/
macro "close_omega" : tactic => `(tactic| (
  simp only [Win, Slots, Scratch, RelPtrs.base, RelPtrs.slot, stackValueSize, execFrame, ciSavedpcOff,
    ciSize, stateTopOff, stateSize, cStackBudget, RuntimeData.spEntry, ciNextOff, ciFuncOff, ciTopOff,
    ciTrapOff, ciPreviousOff, ciNresultsOff, ciCallstatusOff, stateCiOff, tohostAddr, Rng, symAtexit,
    RuntimeData.ljAddr, ljPreviousOff, ljBOff, RuntimeData.jbRa, RuntimeData.jbSp, RuntimeData.jbS0,
    not_or, not_and, Nat.not_lt] at *
  omega))


/-- A heap range the relation reads, at the pointers after a call (the window is the same). -/
theorem _root_.Lua.Vm.Sim.HeapRead.after {p : Proto} {w : RelPtrs} {lo n : Nat} (h : HeapRead p w lo n)
    (mo : Mem) (ι : Strs) (rt : RtPtrs) : HeapRead p (w.after mo ι rt) lo n :=
  ⟨h.above, h.below, h.out⟩

/-- The frozen objects at the pointers after a call that keeps the closure and
the Lua stack's and `g`'s pointers. -/
theorem _root_.Lua.Vm.Sim.StatFacts.after {p : Proto} {w : RelPtrs} {M : Mem} (h : StatFacts p w M) (mo : Mem)
    (H : HeapIx) : StatFacts p (w.after mo w.ι (w.rt.withHeap H)) M :=
  ⟨h.rodata, h.proto, h.proto_code, h.strs, fun ts ho => (h.env ts ho).mono fun _ _ hr => hr.after _ _ _,
    h.lua.hookmask, h.lua.errfunc, h.lua.nCcalls, h.lua.openupval, h.lua.tbclist, h.lua.stack,
    h.lua.stack_last, h.lua.g, h.lua.mt_nil, h.lua.mt_boolean, h.lua.mt_number, h.lua.errjmp⟩

/-- **The relation after `CALL print`** (lane F1-13): the run's facts
(`CloseIn`) give `CallOut` and the `CALL` invariant at the pointers after the
call, the complement the final memory's zero fill and the heap `H`. The
post-print `exit` is `ExitUp_Statement`. -/
theorem call_close (hX : ExitUp_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL0 : Nat → Prop} {ls : LitPtrs} {m : Mem}
    {out : List (BitVec 8)} {nci buf : Nat} {H : HeapIx} {FL : Nat → Prop} (hR : VmRelAt p c s w)
    (hI : CallInvAt p w ph F FL0 ls) (h : CloseIn p c w ins args ph F ls m out nci buf H FL) :
    CallOut p w c.σ.mem ins args m out (w.after (fillZeroMem m) w.ι (w.rt.withHeap H)) ∧
      CallInv p (w.after (fillZeroMem m) w.ι (w.rt.withHeap H)) := by
  have hc := hR.core
  have hr := hc.ranges
  have hd := hI.dense
  have hlua := hc.comp.runtime.lua
  have SF : StatFacts p w (fillZeroMem m) := hI.stat m h.foot
  have := hr.ci_lo; have := hr.ci_top; have := hr.L_lo; have := hr.L_top; have := hr.sp_eq
  have := hr.frame_sep; have := hr.slots_top
  -- the `CallInfo`'s words but `next` and `savedpc`
  have ciT : ∀ a, w.ci ≤ a → a < w.ci + ciSize → ¬ Rng (w.ci + ciNextOff) 8 a →
      ¬ Rng (w.ci + ciSavedpcOff) 8 a → bytesT1 (fillZeroMem m) a = bytesT1 w.mo a :=
    fun a h1 h2 h3 h4 => (bytesT1_fill m a).trans (h.ci a h1 h2 h3 h4)
  have ciRd : ∀ o n, o + n ≤ ciNextOff ∨ (ciSavedpcOff + 8 ≤ o ∧ o + n ≤ ciSize) →
      rdLE (fillZeroMem m) (w.ci + o) n = rdLE w.mo (w.ci + o) n := fun o n ho =>
    rdLE_fill hd (by close_omega) (by close_omega) fun j hj => h.ci _ (by omega) (by close_omega)
      (by close_omega) (by close_omega)
  -- the caller frames above `luaV_execute`'s
  have upT : ∀ a, RuntimeData.spEntry ≤ a → bytesT1 m a = bytesT1 w.mo a := fun a ha =>
    (h.above a (by close_omega)).trans (hc.frame a (by close_omega))
  have upRd : ∀ a n, RuntimeData.spEntry ≤ a → a + n ≤ 0x88000000 →
      rdLE (fillZeroMem m) a n = rdLE w.mo a n := fun a n h1 h2 =>
    rdLE_fill hd (by close_omega) h2 fun j _ => upT _ (by omega)
  have hlci : rd64 (fillZeroMem m) (w.L + stateCiOff) = some w.ci := by
    rw [rd64_fill m (by close_omega) (by close_omega), h.lci, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by close_omega)]
  have hnext : rd64 (fillZeroMem m) (w.ci + ciNextOff) = some nci := by
    have := h.nci_hi
    rw [rd64_fill m (by close_omega) (by close_omega), h.next, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by close_omega)]
  have hprev : rd64 (fillZeroMem m) (nci + ciPreviousOff) = some w.ci := by
    have := h.nci_lo; have := h.nci_hi
    rw [rd64_fill m (by simp only [symEnd] at *; close_omega) (by close_omega), h.nci_prev,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by close_omega)]
  have hatx : bytesT8 (fillZeroMem m) symAtexit = 0#64 := by
    rw [← hI.atexit]
    exact bytesT8_congrT fun j hj => (bytesT1_fill m _).trans (h.atexit j hj)
  have hP := h.st.keep fun a _ => bytesT1_fill m a
  have hio : StdoutIn (fillZeroMem m) (w.rt.withHeap H).hix (.up buf []) := by
    cases hP.io with
    | up a b c => exact .up a b ⟨c.block, c.lo, c.hi⟩
  have hheap : HeapAt (fillZeroMem m) (w.rt.withHeap H).top (w.rt.withHeap H).brkv (w.rt.withHeap H).chunks
      (fun i => (w.rt.withHeap H).bins.getD i []) := h.st.heap.toBinsList
  have kept' : ∀ {a}, Kept w.rt.hix ph a → Kept (w.rt.withHeap H).hix (.up buf []) a := fun ha =>
    ha.mono h.kept h.bufFrom
  have keptH : ∀ {a}, Kept H (.up buf []) a → Kept (w.rt.withHeap H).hix (.up buf []) a := fun ha =>
    ⟨ha.inuse, ha.lo, ha.hi, ha.nbuf⟩
  -- the new complement
  have comp : Complement p (w.after (fillZeroMem m) w.ι (w.rt.withHeap H)) := by
    obtain ⟨hsz, hwords⟩ := SF.proto.code SF.proto_code
    refine
      { text := fun o ho => fillZeroMem_some (h.text o ho)
        rodata := SF.rodata
        proto := SF.proto
        proto_code := SF.proto_code
        code_word := fun i ins hf => by
          obtain ⟨hlt, hi⟩ := List.getElem?_eq_some_iff.1 hf
          show bytesT4 (fillZeroMem m) (w.code + 4 * i) = ins
          rw [bytesT4_of_rd32 (hwords i hlt), hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        func_word := (bytesT8_congrT fun j _ => ciT _ (by close_omega) (by close_omega) (by close_omega)
          (by close_omega)).trans hc.comp.func_word
        trap_word := (bytesT4_congrT fun j _ => ciT _ (by close_omega) (by close_omega) (by close_omega)
          (by close_omega)).trans hc.comp.trap_word
        runtime := ⟨hc.comp.runtime.func, ?_, hheap, ?_⟩
        kconst := fun i v hv => ?_
        own := fun ts s ho => ?_
        callers := fun sg hs i hi => ?_
        callerL := fun a ha => ?_
        exit := hX p _ buf hio hheap hatx
        env := (SF.after (fillZeroMem m) H).env
        call := ?_ }
    · -- the Lua state
      refine ⟨SF.lua.hookmask, (ciRd ciTrapOff 4 (by close_omega)).trans hlua.trap, SF.lua.errfunc,
        SF.lua.nCcalls, SF.lua.openupval, SF.lua.tbclist, SF.lua.stack, SF.lua.stack_last,
        (ciRd ciFuncOff 8 (by close_omega)).trans hlua.func, hlua.stack_le,
        (ciRd ciTopOff 8 (by close_omega)).trans hlua.ci_top, hlua.ci_top_le,
        (ciRd ciCallstatusOff 2 (by close_omega)).trans hlua.callstatus,
        (ciRd ciNresultsOff 2 (by close_omega)).trans hlua.nresults,
        (ciRd ciPreviousOff 8 (by close_omega)).trans hlua.previous,
        .inr ⟨nci, hnext, h.nci_lo, h.nci_hi, h.nci_al, hprev⟩, SF.lua.g, SF.lua.mt_nil, SF.lua.mt_boolean,
        SF.lua.mt_number, hlci⟩
    · -- the error handler
      have he := hc.comp.runtime.error_jmp
      exact ⟨SF.lua.errjmp, (upRd _ 8 (by close_omega) (by close_omega)).trans he.previous,
        (upRd _ 8 (by close_omega) (by close_omega)).trans he.ret,
        (upRd _ 8 (by close_omega) (by close_omega)).trans he.sp,
        fun i hi => by
          rw [show rd64 (fillZeroMem m) _ = rd64 w.mo _ from upRd _ 8 (by close_omega) (by close_omega)]
          exact he.saved i hi⟩
    · -- the constants
      have hk := hc.comp.kconst i v hv
      have hi : i < p.k.length := by
        simp only [kval, Proto.const, Option.bind_eq_some_iff] at hv
        obtain ⟨_, hc', _⟩ := hv
        exact (List.getElem?_eq_some_iff.1 hc').1
      have kb : ∀ j, j < 16 → bytesT1 (fillZeroMem m) (w.k + stackValueSize * i + j) =
          bytesT1 w.mo (w.k + stackValueSize * i + j) := fun j hj =>
        (bytesT1_fill m _).trans (h.foot _ (by
          have := hI.kslots (tvalueSize * i + j) (by simp only [tvalueSize] at *; omega)
          simp only [stackValueSize, tvalueSize] at this ⊢; rwa [Nat.add_assoc]))
      have et : slotTag (fillZeroMem m) (w.k + stackValueSize * i) = slotTag w.mo (w.k + stackValueSize * i) :=
        kb tvalueTagOff (by decide)
      have ev : slotVal (fillZeroMem m) (w.k + stackValueSize * i) = slotVal w.mo (w.k + stackValueSize * i) :=
        bytesT8_congrT fun j hj => by
          simpa only [Nat.add_assoc] using kb (tvalueValOff + j) (by simp only [tvalueValOff]; omega)
      show ValRepr (fillZeroMem m) w.ι (slotTag (fillZeroMem m) (w.k + stackValueSize * i))
        (slotVal (fillZeroMem m) (w.k + stackValueSize * i)) v
      rw [et, ev]; exact hk.transfer SF.strs
    · -- the owned strings: their chunks stay in use
      obtain ⟨cc, hcc⟩ := hc.comp.own ts s ho
      exact ⟨cc, h.kept cc hcc.walk hcc.inuse, hcc.inuse, hcc.lo, hcc.hi, hcc.out⟩
    · -- the caller frames
      obtain ⟨hlo, hhi⟩ := callerFrames_above sg hs
      have hb := hc.comp.callers sg hs i hi
      have hsp : RuntimeData.spEntry = 0x87fffe20 := rfl
      rw [fill_get m (a := sg.1 + i) (by omega) (by omega), upT _ (by omega)]
      simp only [bytesT1, hb, Option.getD_some]
    · have := callerLSlots_above a ha
      exact (bytesT8_congrT fun j _ => (bytesT1_fill m _).trans (upT _ (by omega))).trans (hc.comp.callerL a ha)
    · -- the `CALL` invariant again
      refine ⟨.up buf [], F, FL, ls,
        { dense := fun a h1 h2 => by rw [fill_get m h1 (by omega)]; rfl
          io := hio
          pend := rfl
          cells := hP.cells
          room := fun hh => hh.elim (fun hb => absurd rfl (hb buf [])) fun h0 => by
            have e := Option.some.inj (hnext.symm.trans h0); have := h.nci_lo
            simp only [symEnd] at this; omega
          atexit := hatx
          stat := (hI.stat.trans fun a ha => (bytesT1_fill m a).trans (h.foot a ha)).conseq
            fun M hM => hM.after (fillZeroMem m) H
          stat_in := fun a ha => (hI.stat_in a ha).imp kept' id
          stat_apart := hI.stat_apart
          fits := hI.fits
          kslots := hI.kslots
          lits := h.lits.facts.trans fun a _ => bytesT1_fill m a
          lits_in := fun a ha => keptH (h.lits.kept a ha)
          lits_apart := fun a ha hd => h.lits.apart a ha (.inl hd)
          lit_strs := fun ts hts a h1 h2 => keptH (h.lits.strs ts hts a h1 h2)
          marks := hI.marks
          L_in := fun a h1 h2 => kept' (hI.L_in a h1 h2)
          g_in := fun a h1 h2 => kept' (hI.g_in a h1 h2)
          ci_in := fun a h1 h2 => kept' (hI.ci_in a h1 h2)
          stack_in := fun a h1 h2 => kept' (hI.stack_in a h1 h2)
          nci := fun n hn h0 => ?_
          objs := ⟨hI.objs.g_L, hI.objs.g_ci, hI.objs.g_stack, hI.objs.ci_stack, hI.objs.lit_L,
            hI.objs.lit_g, hI.objs.lit_ci, hI.objs.lit_stack⟩ }⟩
      obtain rfl : n = nci := Option.some.inj (hn.symm.trans hnext)
      exact ⟨fun a h1 h2 => keptH (h.nci_kept a h1 h2).1,
        fun a h1 h2 => ⟨(h.nci_kept a h1 h2).2, fun hf => h.lits.apart a hf (.inr ⟨h1, h2⟩)⟩,
        h.nci_L, h.nci_g, h.nci_ci, h.nci_stack, h.nci_lits⟩
  refine ⟨{ line := h.line
            comp := comp
            frame := fun a _ => (bytesT1_fill m a).symm
            above := h.above
            below := h.below
            nil := h.nil
            trap := (bytesT4_congrT fun j _ => h.ci _ (by close_omega) (by close_omega) (by close_omega)
              (by close_omega)).trans hc.comp.trap_word
            vrepr := fun t x v hv => hv.transfer SF.strs
            cl := rfl }, comp.call⟩

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.CallClose
import Lua.Vm.Sim.Kit.ExitUp
import Lua.Vm.Sim.Kit.PoscallN
import Lua.Vm.Sim.Kit.ExtendCI
import Lua.Vm.Sim.Kit.TolStrProof
import Lua.Vm.Sim.Kit.TolIntProof

/-!
# `PrintCall_Statement CallInv` from `CALL`'s open parts (lane F1-13)

`printCall_of : CallOpen → PrintCall_Statement CallInv`: `luaD_precall`'s C
path on `print` from `OP_CALL`'s `jal` (`precall_reuse`, `precall_ext`), at
the join the C function (`luaB_print`, `PrintRel_Statement`) and
`luaD_poscall` (`poscall_sum` with `C = 1`, `PoscallN_Statement` with `C ≥ 2`),
and the relation after the call (`call_close`). The join is one lemma for both
ways `next_ci` takes (`JoinIn`: the memory at the join relative to the head's
and the complement), so the C function and `luaD_poscall` are composed once.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- The bytes `luaD_precall`'s join writes before the C function
(`pcCallMem`): the C `CallInfo`, `L->ci`, the `CallInfo` saved at `0(sp)`. -/
def PcW (L nci sp : Nat) (a : Nat) : Prop := Rng nci ciSize a ∨ Rng (L + stateCiOff) 8 a ∨ Rng (sp - 96) 8 a

theorem pcCallMem_out {M : Mem} {sp L func nres top nci a : Nat} (h : ¬ PcW L nci sp a) :
    (pcCallMem M sp L func nres top nci)[a]? = M[a]? := by
  simp only [PcW, Rng, ciSize, stateCiOff, not_or, not_and, Nat.not_lt] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [pcCallMem]
  rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
    getElem?_writeMap2_out _ _ _ _ (by omega), getElem?_writeMap2_out _ _ _ _ (by omega),
    getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]

/-- **The memory at `luaD_precall`'s join**, relative to the head's memory
and the complement, with the heap `H` and the C `CallInfo` `nci`. -/
structure JoinIn (p : Proto) (c : Config) (w : RelPtrs) (ins : Word) (ph : StdoutPh) (F FL : Nat → Prop)
    (ls : LitPtrs) (r : BitVec 64) (f : AbiFrame) (MJ : Mem) (nci : Nat) (H : HeapIx) : Prop where
  foot : ∀ a, F a → bytesT1 MJ a = bytesT1 w.mo a
  ci : ∀ a, w.ci ≤ a → a < w.ci + ciSize → ¬ Rng (w.ci + ciNextOff) 8 a → ¬ Rng (w.ci + ciSavedpcOff) 8 a →
    bytesT1 MJ a = bytesT1 w.mo a
  above : ∀ a, w.sp ≤ a → bytesT1 MJ a = bytesT1 c.σ.mem a
  slots : ∀ a, w.base ≤ a → a < w.slot ins.a + 16 * ins.b → bytesT1 MJ a = bytesT1 c.σ.mem a
  atexit : ∀ j, j < 8 → bytesT1 MJ (symAtexit + j) = bytesT1 w.mo (symAtexit + j)
  top_w : bytesT8 MJ (w.L + stateTopOff) = BitVec.ofNat 64 (w.slot ins.a + 16 * ins.b)
  tbc_w : bytesT8 MJ (w.L + stateTbclistOff) = BitVec.ofNat 64 w.rt.stack
  g_w : bytesT8 MJ (w.L + stateGOff) = BitVec.ofNat 64 w.rt.g
  hook_w : bytesT4 MJ (w.L + stateHookmaskOff) = 0#32
  mt_w : ∀ t ∈ [luaTnil, luaTboolean, luaTnumber], bytesT8 MJ (w.rt.g + gMtOff + 8 * t) = 0#64
  st : PrintSt MJ ph H
  kept : ∀ c ∈ w.rt.chunks, c.inuse = true → c ∈ H.chunks
  brk : H.brk ≤ w.rt.brkv + extRoom
  lits : Frozen FL (fun M => LitsHold M w.rt.g w.rt.stackLast ls) MJ
  /-- (lane F1-15) the string cache's candidates -/
  cache : LitCache MJ w.rt.g ls
  next : bytesT8 MJ (w.ci + ciNextOff) = BitVec.ofNat 64 nci
  prev : bytesT8 MJ (nci + ciPreviousOff) = BitVec.ofNat 64 w.ci
  nci_lo : symEnd ≤ nci
  nci_hi : nci + ciSize ≤ RuntimeData.spEntry - cStackBudget
  nci_al : nci % 8 = 0
  nci_kept : ∀ a, nci ≤ a → a < nci + ciSize → Kept H ph a ∧ ¬ F a ∧ ¬ FL a
  nci_L : Apart nci ciSize w.L stateSize
  nci_g : Apart nci ciSize w.rt.g gEnd
  nci_ci : Apart nci ciSize w.ci ciSize
  nci_stack : Apart nci ciSize w.func (w.rt.stackLast - w.func)
  nci_lits : ∀ ts ∈ ls.strs, Apart nci ciSize ts 30
  frame_ra : bytesT8 MJ (w.sp - 8) = r
  frame_s0 : bytesT8 MJ (w.sp - 16) = f.s0
  /-- (lane F1-19) the literals' footprint kept from the complement -/
  fl_w : ∀ a, FL a → bytesT1 MJ a = bytesT1 w.mo a
  /-- (lane F1-19) a byte of a chunk in use off what the caller keeps, or of
  `_REENT`'s words, kept from the complement -/
  keepK : ∀ a, (Kept w.rt.hix ph a ∧ ¬ CallX0 w F a) ∨ ReentWord a → bytesT1 MJ a = bytesT1 w.mo a
  /-- (lane F1-19) the C `CallInfo`'s bytes in the head's chunks in use are the caller's -/
  nci_x : ∀ a, nci ≤ a → a < nci + ciSize → Kept w.rt.hix ph a → NciAt w a
  /-- (lane F1-19) `g->strt`'s count and size kept -/
  strt_w : ∀ j, j < 8 → bytesT1 MJ (w.rt.g + gStrtNuseOff + j) = bytesT1 w.mo (w.rt.g + gStrtNuseOff + j)

/-- `OP_CALL print`'s operands and the relation at its head. -/
structure CallCx (p : Proto) (c : Config) (s : State) (w : RelPtrs) (ins : Word) (args : List Value) : Prop where
  rel : VmRelAt p c s w
  b_ne : ins.b ≠ 0
  c_ne : ins.c ≠ 0
  a_lt : ins.a < 256
  b_lt : ins.b < 256
  c_lt : ins.c < 256
  ab : ins.a + ins.b ≤ p.maxstacksize
  ac : ins.a + ins.c - 1 ≤ p.maxstacksize
  regs : (List.range' ins.a ins.b).mapM s.regs = some (.builtin .print :: args)
  room : w.slot ins.a + 16 * ins.b + 320 < w.rt.stackLast

/-- The values of a register range. -/
theorem mapM_range'_get {f : Nat → Option Value} : ∀ {n a : Nat} {l : List Value},
    (List.range' a n).mapM f = some l → l.length = n ∧ ∀ i v, l[i]? = some v → f (a + i) = some v
  | 0, a, l, h => by simp at h; subst h; simp
  | n + 1, a, l, h => by
    simp only [List.range'_succ, List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, xs, hxs, rfl⟩ := h
    obtain ⟨hl, hi⟩ := mapM_range'_get hxs
    refine ⟨by simp [hl], fun i v hv => ?_⟩
    cases i with
    | zero => simp at hv; subst hv; simpa using hx
    | succ i =>
      simp only [List.getElem?_cons_succ] at hv
      have := hi i v hv
      rwa [show a + (i + 1) = a + 1 + i by omega]

/-- The bytes the caller needs kept across `luaB_print` (`PrintIn`'s `G`):
the frozen objects, the Lua `CallInfo`, the C one, the registers below
`R[A]`, `__atexit`. -/
def CallG (w : RelPtrs) (F : Nat → Prop) (ins : Word) (nci : Nat) (a : Nat) : Prop :=
  F a ∨ Rng w.ci ciSize a ∨ Rng nci ciSize a ∨ (w.base ≤ a ∧ a < w.slot ins.a) ∨ Rng symAtexit 8 a

/-- What the literals' facts stay apart from across the call (`PrintIn`'s `D`). -/
def CallD (w : RelPtrs) (nci : Nat) (a : Nat) : Prop := CallLitDirty w a ∨ (nci ≤ a ∧ a < nci + ciSize)

/-- **What `luaB_print` leaves** at the join (`PcC`'s post). -/
def PrintQ (w : RelPtrs) (ins : Word) (args : List Value) (ph : StdoutPh) (F : Nat → Prop) (ls : LitPtrs)
    (nci : Nat) (H : HeapIx) (o : Array String) (MC : Mem) (m' : Mem) (o' : Array String) : Prop :=
  ∃ out, o' = pushes o out ∧
    PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H MC m' out

/-- `omega` over a `CALL`'s facts. -/
macro "call_omega" : tactic => `(tactic| (
  simp only [PcW, CallG, CallD, CallLitDirty, CallDirty, Apart, Rng, Win, Slots, Scratch, RelPtrs.base,
    RelPtrs.slot, stackValueSize, execFrame, ciSavedpcOff, ciSize, stateTopOff, stateSize, cStackBudget,
    RuntimeData.spEntry, ciNextOff, ciFuncOff, ciTopOff, ciTrapOff, ciPreviousOff, ciNresultsOff,
    ciCallstatusOff, stateCiOff, stateGOff, stateTbclistOff, stateHookmaskOff, tohostAddr, symAtexit,
    symEnd, symTohost, heapStart, heapEnd, symHeapEnd, gEnd, gStrcacheOff, strcacheN, strcacheM, gMtOff,
    tvalueTagOff, tvalueValOff, PrintStatic, not_or, not_and, Nat.not_lt] at *
  omega))


/-- The memory `luaD_precall` builds for the C function. -/
abbrev callMC (w : RelPtrs) (ins : Word) (MJ : Mem) (nci : Nat) : Mem :=
  pcCallMem MJ w.sp w.L (w.slot ins.a) (ins.c - 1) (w.slot ins.a + 16 * ins.b) nci

/-- **Where a `CALL`'s objects lie**, as numbers (`omega`'s facts): `sp`, the
`lua_State`, the Lua `CallInfo`, `g` up to its string cache, the Lua stack
above `ci->func`, the register slots, the C `CallInfo`, and their
separations. -/
structure CallNums (p : Proto) (w : RelPtrs) (ins : Word) (nci : Nat) : Prop where
  sp : w.sp = 0x87fffd70
  base : w.base = w.func + 16
  slot : w.slot ins.a = w.func + 16 + 16 * ins.a
  L_lo : 0x8006ecd0 ≤ w.L
  L_hi : w.L + 200 ≤ 0x87800000
  ci_lo : 0x8006ecd0 ≤ w.ci
  ci_hi : w.ci + 64 ≤ 0x87800000
  g_lo : 0x8006ecd0 ≤ w.rt.g
  g_hi : w.rt.g + 1400 ≤ 0x87800000
  f_lo : 0x8006ecd0 ≤ w.func
  sl_hi : w.rt.stackLast ≤ 0x87800000
  room : w.func + 16 + 16 * ins.a + 16 * ins.b + 320 < w.rt.stackLast
  ms : w.func + 16 + 16 * p.maxstacksize ≤ w.rt.stackLast
  ab : ins.a + ins.b ≤ p.maxstacksize
  ac : ins.a + ins.c - 1 ≤ p.maxstacksize
  b_pos : 1 ≤ ins.b
  c_pos : 1 ≤ ins.c
  c_lt : ins.c < 256
  L_ci : w.L + 200 ≤ w.ci ∨ w.ci + 64 ≤ w.L
  L_g : w.rt.g + 1400 ≤ w.L ∨ w.L + 200 ≤ w.rt.g
  ci_g : w.rt.g + 1400 ≤ w.ci ∨ w.ci + 64 ≤ w.rt.g
  g_stack : w.rt.g + 1400 ≤ w.func ∨ w.rt.stackLast ≤ w.rt.g
  ci_stack : w.ci + 64 ≤ w.func ∨ w.rt.stackLast ≤ w.ci
  L_slots : w.L + 200 ≤ w.func + 16 ∨ w.func + 16 + 16 * p.maxstacksize ≤ w.L
  nci_lo : 0x8006ecd0 ≤ nci
  nci_hi : nci + 64 ≤ 0x87800000
  nci_al : nci % 8 = 0
  nci_L : nci + 64 ≤ w.L ∨ w.L + 200 ≤ nci
  nci_g : nci + 64 ≤ w.rt.g ∨ w.rt.g + 1400 ≤ nci
  nci_ci : nci + 64 ≤ w.ci ∨ w.ci + 64 ≤ nci
  nci_stack : nci + 64 ≤ w.func ∨ w.rt.stackLast ≤ nci
  L_al : w.L % 8 = 0

/-- **A `CALL`'s numbers** from its head, the invariant and its join. -/
theorem callNums {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) : CallNums p w ins nci := by
  have hr := cx.rel.core.ranges
  have hfs : w.func < w.rt.stackLast := by
    have := cx.room; simp only [RelPtrs.slot, RelPtrs.base, stackValueSize] at this; omega
  have k1 := (hI.L_in w.L (Nat.le_refl _) (by simp only [stateSize]; omega)).lo
  have k2 := (hI.L_in (w.L + stateSize - 1) (by simp only [stateSize]; omega) (by simp only [stateSize]; omega)).hi
  have k3 := (hI.ci_in w.ci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have k4 := (hI.ci_in (w.ci + ciSize - 1) (by simp only [ciSize]; omega) (by simp only [ciSize]; omega)).hi
  have k5 := (hI.g_in w.rt.g (Nat.le_refl _) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).lo
  have k6 := (hI.g_in (w.rt.g + gEnd - 1) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).hi
  have k7 := (hI.stack_in w.func (Nat.le_refl _) hfs).lo
  have k8 := (hI.stack_in (w.rt.stackLast - 1) (by omega) (by omega)).hi
  have k9 := ((hJ.nci_kept nci (Nat.le_refl _) (by simp only [ciSize]; omega)).1).lo
  have k10 := ((hJ.nci_kept (nci + ciSize - 1) (by simp only [ciSize]; omega)
    (by simp only [ciSize]; omega)).1).hi
  have o1 := hI.objs.g_L; have o2 := hI.objs.g_ci; have o3 := hI.objs.g_stack; have o4 := hI.objs.ci_stack
  have n1 := hJ.nci_L; have n2 := hJ.nci_g; have n3 := hJ.nci_ci; have n4 := hJ.nci_stack
  have r1 := hr.L_sep_ci; have r2 := hr.L_sep; have r3 := hr.sp_eq; have r4 := hr.slots_top
  have r5 := hr.L_al
  have r6 := hI.fits
  have := cx.room; have := cx.ab; have := cx.ac; have := cx.b_ne; have := cx.c_ne; have := cx.c_lt
  have := hJ.nci_al
  clear hJ hI cx hr
  simp only [Apart, gEnd, gStrcacheOff, strcacheN, strcacheM, ciSize, stateSize, heapStart,
    heapEnd, symEnd, symHeapEnd, RelPtrs.slot, RelPtrs.base, stackValueSize, execFrame, RuntimeData.spEntry,
    cStackBudget] at *
  constructor <;> first | assumption | omega | (simp only [RelPtrs.slot, RelPtrs.base, stackValueSize]; try omega)

/-- `PcW` refuted by numbers. -/
macro "pcw_omega" : tactic => `(tactic| (
  simp only [PcW, Rng, stateCiOff, ciSize, not_or, not_and, Nat.not_lt]; omega))

set_option hygiene false in
/-- A `CALL`'s numbers in context (`callNums`). -/
macro "call_nums" : tactic => `(tactic| (
  obtain ⟨hsp, hbase, hslot, hL1, hL2, hci1, hci2, hg1, hg2, hf1, hsl2, hroom, hms, hab, hac, hb1, hc1, hc2, hLci,
    hLg, hcig, hgst, hcist, hLsl, hn1, hn2, hnal, hnL, hng, hnci, hnst, hLal⟩ := callNums cx hI hJ))

/-- The join's stores keep a byte off them. -/
theorem callMC_keep {w : RelPtrs} {ins : Word} {MJ : Mem} {nci a : Nat} (h : ¬ PcW w.L nci w.sp a) :
    bytesT1 (callMC w ins MJ nci) a = bytesT1 MJ a := bT1_congr (pcCallMem_out h)

/-- The heap bytes of a `CALL`'s objects are off the join's stores but the C `CallInfo` and `L->ci`. -/
theorem kept_pcw {w : RelPtrs} {nci : Nat} {H : HeapIx} {ph : StdoutPh} {a : Nat} (hsp : w.sp = 0x87fffd70)
    (ha : Kept H ph a) (h1 : ¬ (nci ≤ a ∧ a < nci + ciSize)) (h2 : ¬ Rng (w.L + stateCiOff) 8 a) :
    ¬ PcW w.L nci w.sp a := by
  have := ha.hi
  have hHE : heapEnd = 0x87800000 := rfl
  rintro (h | h | h)
  · exact h1 h
  · exact h2 h
  · simp only [Rng] at h; omega

/-- **The C function's API frame at the join** (`ApiAt`). -/
theorem call_api {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ApiAt (callMC w ins MJ nci) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stack := by
  call_nums
  have hstl := cx.rel.core.comp.runtime.lua.stack_le
  have hfu := cx.rel.core.comp.runtime.func
  refine ⟨?_, ?_, ?_, ?_, by omega⟩
  · simp only [callMC, pcCallMem]; rw [fw8_wm8 (by omega), fw8_same rfl]
  · simp only [callMC, pcCallMem]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), b8_wm2_out (by omega),
      b8_wm2_out (by omega), fw8_same rfl]
  · rw [bytesT8_congrT fun j _ => callMC_keep (by pcw_omega)]
    have := hJ.top_w; simp only [stateTopOff] at this; rw [this]; congr 1; omega
  · rw [bytesT8_congrT fun j _ => callMC_keep (by pcw_omega)]
    have := hJ.tbc_w; simp only [stateTbclistOff] at this; exact this

/-- **`stdout`'s state at the join's stores** (`PrintSt`). -/
theorem call_st {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) : PrintSt (callMC w ins MJ nci) ph H := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  refine hJ.st.keep fun a ha => callMC_keep fun hw => ?_
  have hb := hJ.st.io.buf_hi
  rcases hw with hw | hw | hw
  · have hk := (hJ.nci_kept a hw.1 hw.2).1
    rcases ha with hg | hb' | ⟨_, hu⟩ | hro
    · have := hk.lo; simp only [Kit.StdioGlob] at hg; omega
    · exact hk.nbuf hb'
    · exact hu hk.inuse
    · have := hk.lo; omega
  · have hk := (hI.L_in a (by simp only [Rng, stateCiOff] at hw ⊢; omega)
      (by simp only [Rng, stateCiOff, stateSize] at hw ⊢; omega)).mono hJ.kept fun _ h => .inl h
    rcases ha with hg | hb' | ⟨_, hu⟩ | hro
    · have := hk.lo; simp only [Kit.StdioGlob] at hg; omega
    · exact hk.nbuf hb'
    · exact hu hk.inuse
    · have := hk.lo; omega
  · simp only [Rng] at hw
    rcases ha with hg | hb' | ⟨hr', _⟩ | hro
    · simp only [Kit.StdioGlob] at hg; omega
    · have := hb a hb'; omega
    · have e4 : symMallocAv = 0x8005c6d0 := rfl
      have e5 : symMallocSbrkBase = 0x8005d388 := rfl
      have e6 : symBrk = 0x8005d3b8 := rfl
      have e7 : symMallocTopPad = 0x8005d3d8 := rfl
      have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
      have e9 : symMallocMallinfo = 0x8005e560 := rfl
      simp only [HeapReads] at hr'; omega
    · omega

/-- The frozen footprint at the join's stores. -/
theorem call_footMC {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ∀ a, F a → bytesT1 (callMC w ins MJ nci) a = bytesT1 w.mo a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  intro a ha
  refine (callMC_keep fun hw => ?_).trans (hJ.foot a ha)
  rcases hw with hw | hw | hw
  · exact (hJ.nci_kept a hw.1 hw.2).2.1 ha
  · exact hI.stat_apart a ha (.inr (.inl (by simp only [Rng] at hw; exact hw)))
  · simp only [Rng] at hw
    rcases hI.stat_in a ha with hk | hk | hk
    · have := hk.hi; omega
    · simp only [symTohost] at hk; omega
    · simp only [LocaleW, symImpurePtr] at hk; omega

/-- **The arguments at the join** (`PrintIn.args`). -/
theorem call_args {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ∀ i v, args[i]? = some v → ValRepr (fillZeroMem (callMC w ins MJ nci)) w.ι
      (slotTag (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)))
      (slotVal (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1))) v := by
  intro i v hv
  have SFC := hI.stat _ (call_footMC cx hI hJ)
  obtain ⟨hlen, hget⟩ := mapM_range'_get cx.regs
  have hr1 := hget (i + 1) v (by simpa using hv)
  have hi : i < args.length := (List.getElem?_eq_some_iff.1 hv).1
  call_nums
  simp only [List.length_cons] at hlen
  have hv0 := cx.rel.core.stack (ins.a + (i + 1)) v (by omega) hr1
  have e : w.slot (ins.a + (i + 1)) = w.slot ins.a + 16 * (i + 1) := by
    simp only [RelPtrs.slot, stackValueSize]; omega
  rw [e] at hv0
  have kb : ∀ j, j < 16 → bytesT1 (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1) + j) =
      bytesT1 c.σ.mem (w.slot ins.a + 16 * (i + 1) + j) := fun j hj =>
    (callMC_keep (by pcw_omega)).trans (hJ.slots _ (by omega) (by omega))
  have et : slotTag (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)) =
      slotTag c.σ.mem (w.slot ins.a + 16 * (i + 1)) := kb tvalueTagOff (by decide)
  have ev : slotVal (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)) =
      slotVal c.σ.mem (w.slot ins.a + 16 * (i + 1)) :=
    bytesT8_congrT fun j hj => by
      simpa only [Nat.add_assoc] using kb (tvalueValOff + j) (by simp only [tvalueValOff]; omega)
  rw [et, ev]
  exact hv0.transfer SFC.strs

/-- (lane F1-17) A chunk of a walk from `p` starts at or above `p`. -/
theorem _root_.Lua.Vm.DlHeap.ChunkWalk.addr_lo {m : Mem} {p top : Nat} {cs : List DlHeap.Chunk}
    (h : DlHeap.ChunkWalk m p top cs) : ∀ c ∈ cs, p ≤ c.addr := by
  induction h with
  | top => intro c hc; simp at hc
  | chunk _ _ _ _ _ _ ih =>
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact Nat.le_refl _
    · have := ih c hc; omega

/-- (lane F1-17) **The arguments' strings lie in the heap** (`PrintIn.args_heap`):
the relation owns them (`Complement.own`: an in-use chunk of the allocator's
walk, which starts at `__heap_start`). -/
theorem call_args_heap {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ∀ (i : Nat) (str : List UInt8), args[i]? = some (Value.str str) →
      heapStart ≤ (slotVal (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1))).toNat := by
  intro i str hv
  obtain ⟨hlen, hget⟩ := mapM_range'_get cx.regs
  have hr1 := hget (i + 1) (.str str) (by simpa using hv)
  have hi : i < args.length := (List.getElem?_eq_some_iff.1 hv).1
  call_nums
  simp only [List.length_cons] at hlen
  have hv0 := cx.rel.core.stack (ins.a + (i + 1)) (.str str) (by omega) hr1
  have e : w.slot (ins.a + (i + 1)) = w.slot ins.a + 16 * (i + 1) := by
    simp only [RelPtrs.slot, stackValueSize]; omega
  rw [e] at hv0
  have kb : ∀ j, j < 16 → bytesT1 (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1) + j) =
      bytesT1 c.σ.mem (w.slot ins.a + 16 * (i + 1) + j) := fun j hj =>
    (callMC_keep (by pcw_omega)).trans (hJ.slots _ (by omega) (by omega))
  have ev : slotVal (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)) =
      slotVal c.σ.mem (w.slot ins.a + 16 * (i + 1)) :=
    bytesT8_congrT fun j hj => by
      simpa only [Nat.add_assoc] using kb (tvalueValOff + j) (by simp only [tvalueValOff]; omega)
  rw [ev]
  obtain ⟨ch, hch⟩ := hv0.owned cx.rel.core.comp
  have h1 := hch.lo
  have h2 := cx.rel.core.comp.runtime.heap.walk.addr_lo ch hch.walk
  omega

/-- **The bytes the caller needs kept** lie in chunks in use (or the static
image) and apart from what `luaB_print` writes (`PrintIn.keep_in`,
`keep_apart`). -/
theorem call_keep {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    (∀ a, CallG w F ins nci a → Kept H ph a ∨ PrintStatic a) ∧
    (∀ a, CallG w F ins nci a → ¬ Rng (w.L + stateTopOff) 8 a ∧
      ¬ (w.slot ins.a + 16 * (ins.b - 1) + 16 ≤ a ∧ a < w.rt.stackLast) ∧ ¬ Rng (w.rt.g + 16) 48 a ∧
      ¬ (w.rt.g + gStrcacheOff ≤ a ∧ a < w.rt.g + gEnd) ∧ ∀ ts ∈ ls.strs, a ≠ ts + gcMarkedOff) := by
  have kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H ph a := fun ha => ha.mono hJ.kept fun _ h => .inl h
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS0 : heapStart = symEnd := rfl
  have hHS : symEnd = 0x8006ecd0 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  have hlk : ∀ ts ∈ ls.strs, 0x8006ecd0 ≤ ts := fun ts hts => by
    have := (hI.lit_strs ts hts ts (Nat.le_refl _) (by omega)).lo; omega
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · rcases ha with hF | hci | hn | hsl | hat
    · exact (hI.stat_in a hF).imp kmono fun h => h.elim (fun h => .inl h) fun h => .inr (.inr h)
    · exact .inl (kmono (hI.ci_in a hci.1 hci.2))
    · exact .inl (hJ.nci_kept a hn.1 hn.2).1
    · exact .inl (kmono (hI.stack_in a (by omega) (by omega)))
    · exact .inr (.inr (.inl hat))
  · simp only [CallG, Rng, stateTopOff, gEnd, gStrcacheOff, strcacheN, strcacheM, gcMarkedOff, ciSize, stateSize] at *
    rcases ha with hF | hci | hn | hsl | hat
    · have hd := hI.stat_apart a hF
      simp only [CallDirty, stateTopOff, gEnd, gStrcacheOff, strcacheN, strcacheM, not_or] at hd
      obtain ⟨d1, -, -, d4, d5, d6, -⟩ := hd
      refine ⟨d1, fun h => d4 ⟨by omega, by omega⟩, d5, d6,
        fun ts hts he => hI.marks ts hts (by simp only [gcMarkedOff]; rw [← he]; exact hF)⟩
    · refine ⟨by omega, by omega, by omega, by omega, fun ts hts => ?_⟩
      have := hI.objs.lit_ci ts hts; simp only [Apart, ciSize] at this; omega
    · refine ⟨by omega, by omega, by omega, by omega, fun ts hts => ?_⟩
      have := hJ.nci_lits ts hts; simp only [Apart, ciSize] at this; omega
    · refine ⟨by omega, by omega, by omega, by omega, fun ts hts => ?_⟩
      have := hI.objs.lit_stack ts hts; simp only [Apart] at this; omega
    · refine ⟨by omega, by omega, by omega, by omega, fun ts hts => ?_⟩
      have := hlk ts hts; omega

/-- **The literals at the join's stores** (`PrintIn.lits`). -/
theorem call_lits {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    LitsFoot w.rt.g w.rt.stackLast ls H ph (CallD w nci) FL (callMC w ins MJ nci) := by
  have kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H ph a := fun ha => ha.mono hJ.kept fun _ h => .inl h
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  refine ⟨hJ.lits.trans fun a ha => callMC_keep fun hw => ?_, fun a ha => kmono (hI.lits_in a ha),
    fun a ha hd => hd.elim (hI.lits_apart a ha) fun h => (hJ.nci_kept a h.1 h.2).2.2 ha,
    fun ts hts a h1 h2 => kmono (hI.lit_strs ts hts a h1 h2), hI.lit_marks,
    hJ.cache.congr fun a h1 h2 => callMC_keep fun hw => by
      simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2
      simp only [PcW, Rng, ciSize, stateCiOff, Apart, gEnd, gStrcacheOff, strcacheN, strcacheM] at hw hng hLg
      omega, TabFoot.trans hI.tab_fl fun a ha => (callMC_keep fun hw => ?_).trans (hJ.fl_w a ha)⟩
  all_goals
    rcases hw with hw | hw | hw
    · exact (hJ.nci_kept a hw.1 hw.2).2.2 ha
    · exact hI.lits_apart a ha (.inr (.inl (by simp only [Rng] at hw; exact hw)))
    · have := (hI.lits_in a ha).hi; simp only [Rng] at hw; omega

/-- (lane F1-15) **Where `luaB_print`'s Lua objects lie, apart**, at the join. -/
theorem call_objs {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    PrintObjs w.L nci (w.slot ins.a) w.rt.stackLast w.rt.g ls := by
  have hs : w.func ≤ w.slot ins.a := by simp only [RelPtrs.slot, RelPtrs.base, stackValueSize]; omega
  have hsl : w.slot ins.a ≤ w.rt.stackLast := by have := cx.room; omega
  have g3 := hI.objs.g_stack; have l3 := hI.objs.L_stack; have n4 := hJ.nci_stack
  simp only [Apart] at g3 l3 n4
  refine ⟨hI.objs.g_L.symm, hJ.nci_g, ?_, ?_, ?_, hI.objs.lit_L, hI.objs.lit_g,
    fun ts hts => (hJ.nci_lits ts hts).symm, fun ts hts => ?_⟩
  · simp only [Apart]; omega
  · simp only [Apart]; omega
  · simp only [Apart]; omega
  · have := hI.objs.lit_stack ts hts; simp only [Apart] at this ⊢; omega

/-- (lane F1-15) **The arguments, frozen** on the bytes the caller keeps and
their slots, at the join. -/
theorem call_args_fz {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    Frozen (fun a => CallG w F ins nci a ∨ ArgSlot (w.slot ins.a) (ins.b - 1) a)
      (ArgsAt (w.slot ins.a) w.ι args) (callMC w ins MJ nci) := by
  intro M hM i v hv
  have h0 := call_args cx hI hJ i v hv
  have hi : i < args.length := (List.getElem?_eq_some_iff.1 hv).1
  obtain ⟨hlen, -⟩ := mapM_range'_get cx.regs
  simp only [List.length_cons] at hlen
  have kb : ∀ j, j < 16 → bytesT1 M (w.slot ins.a + 16 * (i + 1) + j) =
      bytesT1 (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1) + j) :=
    fun j hj => hM _ (.inr ⟨by omega, by omega⟩)
  have et : slotTag M (w.slot ins.a + 16 * (i + 1)) =
      slotTag (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)) := kb tvalueTagOff (by decide)
  have ev : slotVal M (w.slot ins.a + 16 * (i + 1)) =
      slotVal (callMC w ins MJ nci) (w.slot ins.a + 16 * (i + 1)) :=
    bytesT8_congrT fun j hj => by
      simpa only [Nat.add_assoc] using kb (tvalueValOff + j) (by simp only [tvalueValOff]; omega)
  rw [et, ev]
  have SF := hI.stat M fun a ha => (hM a (.inl (.inl ha))).trans (call_footMC cx hI hJ a ha)
  exact h0.transfer SF.strs

/-- (lane F1-19) **The static words `snprintf` reads**, from the relation's
`.data` words (`LocaleWords`, frozen on `F`) and `.rodata`. -/
theorem fmtStatic_of {m : Mem} (hL : LocaleWords (fillZeroMem m)) (hr : RodataRead m) : FmtStatic m := by
  have r : ∀ a, 0x8004ecc8 ≤ a → a < 0x8004ecc8 + 55776 →
      (m[a]?).getD 0 = Image.rodataByte (a - 0x8004ecc8) := fun a h1 h2 => by
    have := hr (a - 0x8004ecc8) (by have : Image.rodataSize = 55776 := rfl; omega)
    rwa [show Image.rodataBase + (a - 0x8004ecc8) = a by have : Image.rodataBase = 0x8004ecc8 := rfl; omega]
      at this
  refine ⟨bT8_of_fill (bytesT8_of_rd64 hL.impure), bT8_of_fill (bytesT8_of_rd64 hL.decpt), ?_, ?_, ?_,
    bT8_of_fill (bytesT8_of_rd64 hL.mbtowc), ?_, ?_, ?_⟩
  · dsimp only [bytesT8]
    rw [r 0x8004fb10 (by omega) (by omega), r (0x8004fb10 + 1) (by omega) (by omega),
      r (0x8004fb10 + 2) (by omega) (by omega), r (0x8004fb10 + 3) (by omega) (by omega),
      r (0x8004fb10 + 4) (by omega) (by omega), r (0x8004fb10 + 5) (by omega) (by omega),
      r (0x8004fb10 + 6) (by omega) (by omega), r (0x8004fb10 + 7) (by omega) (by omega)]
    decide
  · show (m[0x8004fb10]?).getD 0 = _
    rw [r 0x8004fb10 (by omega) (by omega)]; decide
  · show (m[0x8004fb11]?).getD 0 = _
    rw [r 0x8004fb11 (by omega) (by omega)]; decide
  · rw [← bytesT1_fill]; exact bytesT1_of_rd8 hL.mbmax
  · dsimp only [bytesT4]
    rw [r 0x800555f4 (by omega) (by omega), r (0x800555f4 + 1) (by omega) (by omega),
      r (0x800555f4 + 2) (by omega) (by omega), r (0x800555f4 + 3) (by omega) (by omega)]
    decide
  · dsimp only [bytesT4]
    rw [r 0x800555d4 (by omega) (by omega), r (0x800555d4 + 1) (by omega) (by omega),
      r (0x800555d4 + 2) (by omega) (by omega), r (0x800555d4 + 3) (by omega) (by omega)]
    decide

/-- (lane F1-19) **What `luaB_print`'s caller holds at the join is the
relation's** (`PrX` within `CallX0`, on the head's chunks in use: the C
`CallInfo` is `ci->next`'s or fresh, `JoinIn.nci_x`). -/
theorem call_x {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ∀ a, Kept w.rt.hix ph a → PrX w.L nci w.rt.g (w.slot ins.a) (ins.b - 1) w.rt.stackLast (CallG w F ins nci) a →
      CallX0 w F a := by
  intro a hk hx
  call_nums
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hk0 := hk.lo
  have hrb : Image.rodataBase = 0x8004ecc8 := rfl
  have hrs : Image.rodataSize = 55776 := rfl
  rcases hx with ((hF | hci | hn | hsl | hat) | hA | hro | hgc | hmt | hlg | hhk) | hL | hg | hs | hn | hlo
  · exact .inl hF
  · exact .inr (.inr (.inr (.inl hci)))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (hJ.nci_x a hn.1 hn.2 hk))))))
  · exact .inr (.inr (.inr (.inr (.inl ⟨by rw [← hbase]; exact hsl.1, by omega⟩))))
  · simp only [Rng, symAtexit] at hat; omega
  · simp only [ArgSlot] at hA
    exact .inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (by omega))))))
  · simp only [Rng, gGcstpOff] at hgc
    exact .inr (.inr (.inl ⟨by omega, by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega⟩))
  · simp only [Rng, gMtOff] at hmt
    exact .inr (.inr (.inl ⟨by omega, by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega⟩))
  · simp only [Rng, stateGOff] at hlg
    exact .inr (.inl ⟨by omega, by simp only [stateSize]; omega⟩)
  · simp only [Rng, stateHookmaskOff] at hhk
    exact .inr (.inl ⟨by omega, by simp only [stateSize]; omega⟩)
  · exact .inr (.inl hL)
  · exact .inr (.inr (.inl hg))
  · exact .inr (.inr (.inr (.inr (.inl ⟨by omega, hs.2⟩))))
  · exact .inr (.inr (.inr (.inr (.inr (.inl (hJ.nci_x a hn.1 hn.2 hk))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr hlo)))))

/-- (lane F1-19) **What an allocating class needs at the join** (`PrintIn.alloc`):
the string table's safety and `_dtoa_r`'s bignums from the invariant
(`CallInvAt.alloc`), carried across `luaD_precall`'s stores. -/
theorem call_alloc {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    PrAlloc w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) := by
  obtain ⟨B, hA⟩ := hI.alloc
  have kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H ph a := fun ha => ha.mono hJ.kept fun _ h => .inl h
  have hx := call_x cx hI hJ
  have hl := call_lits cx hI hJ
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have kFL : ∀ a, FL a → bytesT1 (callMC w ins MJ nci) a = bytesT1 w.mo a := fun a ha => by
    refine (callMC_keep fun hw => ?_).trans (hJ.fl_w a ha)
    rcases hw with hw | hw | hw
    · exact (hJ.nci_kept a hw.1 hw.2).2.2 ha
    · exact hI.lits_apart a ha (.inr (.inl (by simp only [Rng] at hw; exact hw)))
    · have := (hI.lits_in a ha).hi; simp only [Rng] at hw; omega
  have kB : ∀ a, BigFoot B a → bytesT1 (callMC w ins MJ nci) a = bytesT1 w.mo a := fun a ha => by
    rcases ha with hb | hr'
    · have hk := hA.big_in a hb
      refine (callMC_keep fun hw => ?_).trans (hJ.keepK a (.inl ⟨hk, hA.big_x a hb⟩))
      rcases hw with hw | hw | hw
      · exact hA.big_x a hb (.inr (.inr (.inr (.inr (.inr (.inl (hJ.nci_x a hw.1 hw.2 hk)))))))
      · exact hA.big_x a hb (.inr (.inl (by simp only [Rng, stateCiOff, stateSize] at hw ⊢; omega)))
      · have := hk.hi; simp only [Rng] at hw; omega
    · refine (callMC_keep fun hw => ?_).trans (hJ.keepK a (.inr hr'))
      simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr'
      simp only [PcW, Rng, ciSize, stateCiOff] at hw; omega
  exact .intro FL B ⟨hl, (hA.strt.trans kFL).conseq fun M hM rt hrt => (hM rt hrt).weaken
      (fun _ h => kmono h) (fun a hk hx' => hx'.imp (hx a hk) id)
      fun a hk hw => hw.imp id fun hw => hw.elim .inl fun hn => .inr (hJ.nci_x a hn.1 hn.2 hk),
    hA.big.trans kB, ⟨fun a hb => kmono (hA.big_in a hb), fun a hb hp => hA.big_x a hb (hx a (hA.big_in a hb) hp),
      hA.big_lit⟩, hA.big_fl⟩

/-- (lane F1-19) **`g->allgc` is off what `luaB_print`'s state keeps**:
`CallDirty` keeps the frozen objects off it, the other objects lie apart from
`g`. -/
theorem call_gc {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    ∀ a, Rng (w.rt.g + gAllgcOff) 8 a → ¬ PrKeep w.L w.rt.g (w.slot ins.a) (ins.b - 1) (CallG w F ins nci) a := by
  intro a ha hk
  call_nums
  have hrb : Image.rodataBase = 0x8004ecc8 := rfl
  have hrs : Image.rodataSize = 55776 := rfl
  simp only [Rng, gAllgcOff] at ha
  rcases hk with (hF | hci | hn | hsl | hat) | hA | hro | hgc | hmt | hlg | hhk
  · exact hI.stat_apart a hF (.inr (.inr (.inr (.inr (.inr (.inr (.inr ⟨by simp only [gAllgcOff]; omega,
      by simp only [gAllgcOff]; omega⟩)))))))
  all_goals (try simp only [Rng, ArgSlot, ciSize, symAtexit, gGcstpOff, gMtOff, stateGOff, stateHookmaskOff,
    stateSize] at *); omega

/-- (lane F1-19) **`g->strt`'s room at the join** from `HeapBudget`'s: the
table's count and size are none of `luaD_precall`'s stores. -/
theorem call_strt {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H)
    (hb : strtNuse w.mo w.rt.g + newStrs args ≤ strtSize w.mo w.rt.g) :
    strtNuse (callMC w ins MJ nci) w.rt.g + prAllocs args 1 ≤ strtSize (callMC w ins MJ nci) w.rt.g := by
  call_nums
  have k : ∀ j, j < 8 → bytesT1 (callMC w ins MJ nci) (w.rt.g + gStrtNuseOff + j) =
      bytesT1 w.mo (w.rt.g + gStrtNuseOff + j) := fun j hj =>
    (callMC_keep (by simp only [gStrtNuseOff]; pcw_omega)).trans (hJ.strt_w j hj)
  have e1 : strtNuse (callMC w ins MJ nci) w.rt.g = strtNuse w.mo w.rt.g := by
    simp only [strtNuse]; congr 1
    exact bytesT4_congrT fun j hj => k j (by omega)
  have e2 : strtSize (callMC w ins MJ nci) w.rt.g = strtSize w.mo w.rt.g := by
    simp only [strtSize, gStrtSizeOff]; congr 1
    exact bytesT4_congrT fun j hj => by
      have := k (4 + j) (by omega)
      simp only [gStrtNuseOff] at this
      rwa [show w.rt.g + 56 + (4 + j) = w.rt.g + 60 + j by omega] at this
  have e3 : prAllocs args 1 = newStrs args := by simp [prAllocs, newStrs]
  rw [e1, e2, e3]; exact hb

/-- **`luaB_print`'s entry at the join** (`PrintIn`). -/
theorem call_printIn {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame} {MJ : Mem} {nci : Nat}
    {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) :
    PrintIn w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stack w.rt.stackLast w.rt.g ls args w.ι
      (CallD w nci) (CallG w F ins nci) ph H (callMC w ins MJ nci) := by
  obtain ⟨hlen, -⟩ := mapM_range'_get cx.regs
  have hK := call_keep cx hI hJ
  have kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H ph a := fun ha => ha.mono hJ.kept fun _ h => .inl h
  call_nums
  refine
    { api := call_api cx hI hJ
      st := call_st cx hI hJ
      pend := hI.pend
      len := by simp only [List.length_cons] at hlen; omega
      args := call_args cx hI hJ
      args_heap := call_args_heap cx hI hJ
      f_al := by
        have := cx.rel.core.ranges.base_al
        simp only [RelPtrs.slot, stackValueSize]; omega
      room := by omega
      g_w := (bytesT8_congrT fun j _ => callMC_keep (by simp only [stateGOff]; pcw_omega)).trans hJ.g_w
      mt := fun t ht => (bytesT8_congrT fun j _ => callMC_keep (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, luaTnil, luaTboolean, luaTnumber] at ht
        simp only [gMtOff]; pcw_omega)).trans (hJ.mt_w t ht)
      hook := (bytesT4_congrT fun j _ => callMC_keep (by simp only [stateHookmaskOff]; pcw_omega)).trans hJ.hook_w
      lits := ⟨FL, call_lits cx hI hJ⟩
      keep_in := hK.1
      keep_apart := hK.2
      L_in := fun a h1 h2 => kmono (hI.L_in a h1 h2)
      g_in := fun a h1 h2 => kmono (hI.g_in a h1 h2)
      nci_in := fun a h1 h2 => (hJ.nci_kept a h1 h2).1
      stack_in := fun a h1 h2 => kmono (hI.stack_in a (by omega) h2)
      objs := call_objs cx hI hJ
      args_fz := call_args_fz cx hI hJ
      gcstp := by
        have SF := hI.stat _ (call_footMC cx hI hJ)
        rw [← bytesT1_fill]; exact bytesT1_of_rd8 SF.lua.gcstp
      ro := fun o ho => by
        have SF := hI.stat _ (call_footMC cx hI hJ)
        rw [← bytesT1_fill]; simp only [bytesT1, SF.rodata o ho, Option.getD_some]
      g_al := hI.g_al
      dirty := fun a ha => by
        simp only [CallD, CallLitDirty, Rng, stateTopOff, gTotalbytesOff, gGCdebtOff] at ha ⊢
        have : w.func ≤ w.slot ins.a := by simp only [RelPtrs.slot, RelPtrs.base, stackValueSize]; omega
        omega
      alloc := call_alloc cx hI hJ
      gc := call_gc cx hI hJ
      stat := by
        have SF := hI.stat _ (call_footMC cx hI hJ)
        exact ⟨bT8_of_fill (bytesT8_of_rd64 SF.lua.frealloc), fmtStatic_of SF.locale fun o ho => by
          rw [← bytesT1_fill]; simp only [bytesT1, SF.rodata o ho, Option.getD_some]⟩
      mt_fn := by
        have SF := hI.stat _ (call_footMC cx hI hJ)
        exact bT8_of_fill (bytesT8_of_rd64 SF.lua.mt_fn)
      dirty_in := fun a ha => by
        simp only [CallD, CallLitDirty, stateTopOff, stateCiOff, stateNciOff, gGCdebtOff, gTotalbytesOff] at ha
        rcases ha with (h | h | h | h | h | h | h | h) | h
        · exact kmono (hI.L_in a (by omega) (by simp only [stateSize]; omega))
        · exact kmono (hI.L_in a (by omega) (by simp only [stateSize]; omega))
        · exact kmono (hI.ci_in a h.1 h.2)
        · exact kmono (hI.stack_in a h.1 h.2)
        · exact kmono (hI.L_in a (by omega) (by simp only [stateSize]; omega))
        · exact kmono (hI.g_in a (by omega) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))
        · exact kmono (hI.g_in a (by omega) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))
        · exact kmono (hI.g_in a (by have := h.1; simp only [gStrcacheOff] at this; omega) h.2)
        · exact (hJ.nci_kept a h.1 h.2).1
      dirty_g := fun a ha hg => by
        simp only [InsG, Rng, gCurrentwhiteOff, gAllgcOff] at hg
        simp only [CallD, CallLitDirty, stateTopOff, stateCiOff, stateNciOff, gGCdebtOff, gTotalbytesOff,
          gStrcacheOff, gEnd, strcacheN, strcacheM, ciSize] at ha
        omega }

/-- **The C function at the join** (`PcC`): `luaB_print` (`PrintRel_Statement`)
from the memory `luaD_precall` builds, its entry (`call_printIn`) from the
join's facts (`JoinIn`), the `CALL` invariant and the relation. -/
theorem call_pcc (hPR : PrintRel_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) (hbud : AnyAlloc args → HeapBudget w args)
    (o : Array String) :
    PcC w.sp w.L nci f (callMC w ins MJ nci) o (PrintQ w ins args ph F ls nci H o (callMC w ins MJ nci)) := by
  intro c0 h
  have hIn := call_printIn cx hI hJ
  call_nums
  have hNums : PrNums (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) 0x8000ac8c#64 :=
    ⟨⟨by simp only [heapEnd, symHeapEnd]; omega, by omega, by omega, by decide, by omega, by omega, hLal⟩,
      by omega, by omega, by omega, by omega, by omega, by omega,
      by simp only [heapEnd, symHeapEnd]; omega, by have := cx.b_lt; omega⟩
  have hbr := hJ.brk
  obtain ⟨c', s', m', out, hret, hout⟩ := hPR w.sp w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stack
    w.rt.stackLast w.rt.g ls args w.ι (CallD w nci) (CallG w F ins nci) ph H f
    (callMC w ins MJ nci) o trivial hIn hNums
    (fun ha => ⟨by have := (hbud ha).brk; omega, call_strt cx hI hJ (hbud ha).strt⟩) c0 h
  refine ⟨c', s', m', pushes o out, hret, ?_, out, rfl, hout⟩
  rw [bytesT8_congrT fun i _ => hout.above _ (by omega)]
  simp only [callMC, pcCallMem]
  exact fw8_same rfl

/-- `luaD_poscall` with no result wanted (`poscall_sum`'s `pcMem`) leaves `PoscallPost`. -/
theorem pcMem_post (m : Mem) (L ci sp : Nat) (r : BitVec 64) :
    PoscallPost m (Ret.pcMem m L ci sp r) L ci sp 0 := by
  refine ⟨?_, fun j hj => absurd hj (Nat.not_lt_zero _), fun a ha => ?_⟩
  · simp only [Ret.pcMem]; exact bytesT8_writeMap8 _ _ _
  · simp only [Rng, stateTopOff, stateCiOff, not_or, not_and, Nat.not_lt] at ha
    obtain ⟨h1, h2, h3, -⟩ := ha
    exact bT1_congr (by
      simp only [Ret.pcMem, stateTopOff, stateCiOff]
      rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
        getElem?_writeMap8_out _ _ _ _ (by omega)])

/-- A half-word store's value of a small number. -/
theorem shData_ofNat (x : Nat) (h : x < 2 ^ 16) : shData (BitVec.ofNat 64 x) = BitVec.ofNat 16 x := by
  apply BitVec.eq_of_toNat_eq
  simp only [shData, Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

/-- **What the call leaves for the close** (`luaD_poscall`'s post at the
join): the console's new bytes and `CloseIn`. -/
def CloseQ (p : Proto) (c : Config) (w : RelPtrs) (ins : Word) (args : List Value) (ph : StdoutPh)
    (F : Nat → Prop) (ls : LitPtrs) (nci : Nat) (o : Array String) (m'' : Mem) (o' : Array String) : Prop :=
  ∃ out buf H FL B, o' = pushes o out ∧ CloseIn p c w ins args ph F ls m'' out nci buf H FL B

theorem bytesT2_congrT {m m' : Mem} {a : Nat} (h : ∀ i, i < 2 → bytesT1 m (a + i) = bytesT1 m' (a + i)) :
    bytesT2 m a = bytesT2 m' a := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide)
  simp only [bytesT1, Nat.add_zero] at h0 h1
  simp only [bytesT2, h0, h1]

/-- **`luaD_poscall` after `luaB_print`** (`C - 1` results wanted): `poscall_sum`
with `C = 1`, `PoscallN_Statement` with `C ≥ 2`; `L->hookmask` from the
frozen objects, `ci->nresults` from the join's store. -/
theorem call_pos_run (hN : PoscallN_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' : Mem} {o' : Array String} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) :
    Triple (SegSt 0x8000a39c#64 (⟨Register.x10, BitVec.ofNat 64 w.L⟩ :: ⟨Register.x11, BitVec.ofNat 64 nci⟩ ::
        ⟨Register.x12, 0x0#64⟩ :: ⟨Register.x1, 0x8000ac9c#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 (w.sp - 96)⟩ ::
        ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: (pcFr w.L f).pins) (ArmPay m' o'))
      (fun c => ∃ m'', SegSt 0x8000ac9c#64 (⟨Register.x2, BitVec.ofNat 64 (w.sp - 96)⟩ ::
          ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: (pcFr w.L f).pins) (ArmPay m'' o') c ∧
        PoscallPost m' m'' w.L nci (w.sp - 96) (ins.c - 1)) := by
  intro c0 h
  have SF := hI.stat m' fun a ha => (hout.keep a (.inl ha)).trans (call_footMC cx hI hJ a ha)
  have hhook : bytesT4 m' (w.L + stateHookmaskOff) = 0#32 :=
    bT4_of_fill (bytesT4_of_rd32 SF.lua.hookmask)
  call_nums
  have hnres : bytesT2 m' (nci + ciNresultsOff) = BitVec.ofNat 16 (ins.c - 1) := by
    rw [bytesT2_congrT (m' := callMC w ins MJ nci) fun i hi =>
      hout.keep _ (.inr (.inr (.inl ⟨by omega, by simp only [ciNresultsOff, ciSize]; omega⟩)))]
    simp only [callMC, pcCallMem, ciNresultsOff]
    rw [Ret.bytesT2_wm8_out' (by omega), Ret.bytesT2_wm8_out' (by omega), b2_wm2_out (by omega), bytesT2_writeMap2,
      shData_ofNat _ (by omega)]
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  rcases Nat.lt_or_ge ins.c 2 with h1 | h2
  · have hc0 : ins.c - 1 = 0 := by omega
    rw [hc0] at hnres ⊢
    have hx : Ret.PcCx w.L nci (w.sp - 96) 0x8000ac9c#64 m' :=
      ⟨by decide, by omega, by omega, by omega, by omega, by simp only [stateSize]; omega, by omega,
        by simp only [ciSize]; omega, hnal, hLal, hhook, hnres⟩
    obtain ⟨c', s', h'⟩ := Ret.poscall_sum hx ⟨BitVec.ofNat 64 symGlobalPointer, BitVec.ofNat 64 w.L, f.s1,
      f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ 0x0#64 o' c0
      (by simp only [Ret.RFrame.pins]; exact h.repin (by pins_of h))
    simp only [Ret.RFrame.pins] at h'
    exact ⟨c', s', _, h'.repin (by pins_of h'), pcMem_post m' w.L nci (w.sp - 96) 0x8000ac9c#64⟩
  · have hapi := call_api cx hI hJ
    have hres : (bytesT8 m' (nci + ciFuncOff)).toNat = w.slot ins.a := by
      rw [bytesT8_congrT (m' := callMC w ins MJ nci) fun i hi =>
        hout.keep _ (.inr (.inr (.inl ⟨by simp only [ciFuncOff]; omega, by simp only [ciFuncOff, ciSize]; omega⟩))),
        show nci + ciFuncOff = nci from rfl, hapi.func_w, BitVec.toNat_ofNat]
      omega
    have hx : PcCxW w.L nci (w.sp - 96) 0x8000ac9c#64 m' (ins.c - 1) :=
      ⟨by decide, by omega, by omega, by omega, by omega, by simp only [stateSize]; omega, by omega,
        by simp only [ciSize]; omega, hnal, hLal, hhook, hnres, by rw [hres, hslot]; omega,
        by rw [hres, hslot]; omega, by rw [hres, hslot]; simp only [ciSize]; omega,
        by rw [hres, hslot]; simp only [stateSize]; omega⟩
    obtain ⟨c', s', m'', h', hpost⟩ := hN hx (by omega) (by omega) ⟨BitVec.ofNat 64 symGlobalPointer,
      BitVec.ofNat 64 w.L, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ o' c0
      (by simp only [Ret.RFrame.pins]; exact h.repin (by pins_of h))
    simp only [Ret.RFrame.pins] at h'
    exact ⟨c', s', m'', h'.repin (by pins_of h'), hpost⟩

/-- `omega` after the `CallInfo` offsets. -/
macro "pomega" : tactic => `(tactic| ((try simp only [ciPreviousOff, ciNextOff, ciFuncOff, stateSize]); omega))

/-- The bytes `luaD_poscall` writes (`PoscallPost.keep`'s region). -/
def PosW (L ci sp w : Nat) (m : Mem) (a : Nat) : Prop :=
  Rng (sp - 64) 64 a ∨ Rng (L + stateTopOff) 8 a ∨ Rng (L + stateCiOff) 8 a ∨
    ∃ j, j < w ∧ a = (bytesT8 m (ci + ciFuncOff)).toNat + 16 * j + tvalueTagOff

/-- **What `luaD_poscall` keeps after `luaB_print`**, as numbers: its results
from `R[A]`, every byte off its frame, `L->top`, `L->ci` and the results'
tags, the tags nil, `L->ci` from `nci->previous`. -/
structure CloseKeys (w : RelPtrs) (ins : Word) (nci : Nat) (m' m'' : Mem) : Prop where
  pos : ∀ a, (a + 1 ≤ w.sp - 160 ∨ w.sp - 96 ≤ a) → (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) →
    (a + 1 ≤ w.L + 32 ∨ w.L + 40 ≤ a) → (a + 1 ≤ w.slot ins.a ∨ w.slot ins.a + 16 * (ins.c - 1) ≤ a) →
    bytesT1 m'' a = bytesT1 m' a
  nil : ∀ j, j < ins.c - 1 → bytesT1 m'' (w.slot ins.a + 16 * j + tvalueTagOff) = BitVec.ofNat 8 vNil
  lci : bytesT8 m'' (w.L + stateCiOff) = bytesT8 m' (nci + ciPreviousOff)

theorem close_keys {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hpos : PoscallPost m' m'' w.L nci (w.sp - 96) (ins.c - 1)) :
    CloseKeys w ins nci m' m'' := by
  have hapi := call_api cx hI hJ
  call_nums
  have hres : (bytesT8 m' (nci + ciFuncOff)).toNat = w.slot ins.a := by
    rw [bytesT8_congrT (m' := callMC w ins MJ nci) fun i hi =>
      hout.keep _ (.inr (.inr (.inl ⟨by simp only [ciFuncOff]; omega, by simp only [ciFuncOff, ciSize]; omega⟩))),
      show nci + ciFuncOff = nci from rfl, hapi.func_w, BitVec.toNat_ofNat]
    omega
  refine ⟨fun a h1 h2 h2' h3 => hpos.keep a fun hw => ?_, fun j hj => ?_, hpos.lci⟩
  · simp only [PosW, Rng, stateTopOff, stateCiOff, tvalueTagOff, hres] at hw
    rcases hw with hw | hw | hw | ⟨j, hj, rfl⟩ <;> omega
  · have := hpos.nil j hj; rwa [hres] at this

/-- `stdout`'s state after `luaD_poscall`. -/
theorem close_st {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {buf : Nat} {H' : HeapIx}
    (hK : CloseKeys w ins nci m' m'') (hPS : PrintSt m' (.up buf []) H')
    (kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H' (.up buf []) a) : PrintSt m'' (.up buf []) H' := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  refine hPS.keep fun a ha => hK.pos a ?_ ?_ ?_ ?_
  · rcases ha with hg | hb | ⟨hr', _⟩ | hro
    · simp only [Kit.StdioGlob] at hg; omega
    · have := hPS.io.buf_hi a hb; omega
    · have e4 : symMallocAv = 0x8005c6d0 := rfl
      have e5 : symMallocSbrkBase = 0x8005d388 := rfl
      have e6 : symBrk = 0x8005d3b8 := rfl
      have e7 : symMallocTopPad = 0x8005d3d8 := rfl
      have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
      have e9 : symMallocMallinfo = 0x8005e560 := rfl
      simp only [HeapReads] at hr'; omega
    · omega
  all_goals
    refine Classical.byContradiction fun hn => ?_
    first
      | exact (kmono (hI.L_in a (by omega) (by simp only [stateSize]; omega))).not_printFoot ha
      | exact (kmono (hI.stack_in a (by omega) (by omega))).not_printFoot ha

/-- (lane F1-19) The literals' footprint is none of `luaD_poscall`'s stores. -/
theorem close_flKeep {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {buf : Nat} {H' : HeapIx} {FL' : Nat → Prop}
    (hK : CloseKeys w ins nci m' m'')
    (hl : LitsFoot w.rt.g w.rt.stackLast ls H' (.up buf []) (CallD w nci) FL' m') :
    ∀ a, FL' a → bytesT1 m'' a = bytesT1 m' a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  intro a ha
  have hk := hl.kept a ha
  have hd := hl.apart a ha
  simp only [CallD, CallLitDirty, not_or, stateTopOff, stateCiOff] at hd
  obtain ⟨⟨d1, d2, -, d4, -⟩, -⟩ := hd
  have := hk.hi
  clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
  exact hK.pos a (by omega) (by omega) (by omega) (by omega)

/-- (lane F1-19) `_dtoa_r`'s bignums and `_REENT`'s words are none of
`luaD_poscall`'s stores. -/
theorem close_bigKeep {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {K B : Nat → Prop}
    (hK : CloseKeys w ins nci m' m'')
    (hb : PrBigIn w.L nci w.rt.g (w.slot ins.a) (ins.b - 1) w.rt.stackLast ls (CallG w F ins nci) B K)
    (hKh : ∀ a, K a → a < heapEnd) :
    ∀ a, BigFoot B a → bytesT1 m'' a = bytesT1 m' a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  intro a ha
  rcases ha with hb' | hr'
  · have hk := hKh a (hb.inK a hb')
    have hx := hb.x a hb'
    simp only [PrX, not_or] at hx
    obtain ⟨-, hxL, -, hxs, -, -⟩ := hx
    simp only [Rng, stateSize] at hxL
    clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
    exact hK.pos a (by omega) (by omega) (by omega) (by omega)
  · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr'
    clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
    exact hK.pos a (by omega) (by omega) (by omega) (by omega)

/-- (lane F1-19) **What the caller keeps after the call is what `luaB_print`'s
caller held** (`CloseX` within `PrX`). -/
theorem closeX_sub {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {a : Nat} (h : CloseX w F nci a) :
    PrX w.L nci w.rt.g (w.slot ins.a) (ins.b - 1) w.rt.stackLast (CallG w F ins nci) a := by
  call_nums
  rcases h with hF | hL | hg | hc | hs | hn | hlo
  · exact .inl (.inl (.inl hF))
  · exact .inr (.inl hL)
  · exact .inr (.inr (.inl hg))
  · exact .inl (.inl (.inr (.inl hc)))
  · by_cases hlt : a < w.slot ins.a
    · exact .inl (.inl (.inr (.inr (.inr (.inl ⟨by rw [hbase]; exact hs.1, hlt⟩)))))
    · exact .inr (.inr (.inr (.inl ⟨by omega, hs.2⟩)))
  · exact .inr (.inr (.inr (.inr (.inl hn))))
  · exact .inr (.inr (.inr (.inr (.inr hlo))))

/-- The literals after `luaD_poscall`. -/
theorem close_lits {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {buf : Nat} {H' : HeapIx} {FL' : Nat → Prop}
    (hK : CloseKeys w ins nci m' m'')
    (hl : LitsFoot w.rt.g w.rt.stackLast ls H' (.up buf []) (CallD w nci) FL' m') :
    LitsFoot w.rt.g w.rt.stackLast ls H' (.up buf []) (fun a => CallLitDirty w a ∨ (nci ≤ a ∧ a < nci + ciSize))
      FL' m'' := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have kFL : ∀ a, FL' a → bytesT1 m'' a = bytesT1 m' a := by
    intro a ha
    have hk := hl.kept a ha
    have hd := hl.apart a ha
    simp only [CallD, CallLitDirty, not_or, stateTopOff, stateCiOff] at hd
    obtain ⟨⟨d1, d2, -, d4, -⟩, -⟩ := hd
    have := hk.hi
    clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
    exact hK.pos a (by omega) (by omega) (by omega) (by omega)
  refine hl.trans kFL (hl.cache.congr fun a h1 h2 => hK.pos a ?_ ?_ ?_ ?_)
  · simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2; omega
  · simp only [Apart, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at hLg h2; omega
  · simp only [Apart, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at hLg h2; omega
  · simp only [Apart, gEnd, gStrcacheOff, strcacheN, strcacheM] at hgst h2
    simp only [RelPtrs.slot, RelPtrs.base, stackValueSize] at hslot ⊢; omega

/-- The frozen objects after the call. -/
theorem close_foot {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    ∀ a, F a → bytesT1 m'' a = bytesT1 w.mo a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  intro a ha
  have hd := hI.stat_apart a ha
  simp only [CallDirty, not_or, stateTopOff, stateCiOff] at hd
  have hst : a + 1 ≤ w.sp - 160 ∨ w.sp - 96 ≤ a := by
    rcases hI.stat_in a ha with hk | hk | hk
    · have := hk.hi; omega
    · simp only [symTohost] at hk; omega
    · simp only [LocaleW, symImpurePtr] at hk; omega
  clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
  exact (hK.pos a hst (by omega) (by omega) (by omega)).trans ((hout.keep a (.inl ha)).trans
    (call_footMC cx hI hJ a ha))

/-- The Lua `CallInfo` after the call. -/
theorem close_ci {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    ∀ a, w.ci ≤ a → a < w.ci + ciSize → ¬ Rng (w.ci + ciNextOff) 8 a → ¬ Rng (w.ci + ciSavedpcOff) 8 a →
      bytesT1 m'' a = bytesT1 w.mo a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  intro a h1 h2 h3 h4
  simp only [Rng, ciNextOff, ciSavedpcOff, ciSize, not_and, Nat.not_lt] at h2 h3 h4
  clear hLg hcig hgst hLsl hnL hng hnst
  exact (hK.pos a (by omega) (by omega) (by omega) (by omega)).trans ((hout.keep a (.inr (.inl ⟨h1, by simp only [ciSize]; omega⟩))).trans
    ((callMC_keep (by pcw_omega)).trans (hJ.ci a h1 (by simp only [ciSize]; omega) (by simp only [Rng, ciNextOff]; omega)
      (by simp only [Rng, ciSavedpcOff]; omega))))

/-- The frames above `sp` after the call. -/
theorem close_above {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    ∀ a, w.sp ≤ a → bytesT1 m'' a = bytesT1 c.σ.mem a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  intro a ha
  clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
  exact (hK.pos a (by omega) (by omega) (by omega) (by omega)).trans ((hout.above a (by omega)).trans
    ((callMC_keep (by pcw_omega)).trans (hJ.above a ha)))

/-- The registers below `R[A]` after the call. -/
theorem close_below {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    ∀ a, w.base ≤ a → a < w.slot ins.a → bytesT1 m'' a = bytesT1 c.σ.mem a := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  intro a h1 h2
  clear hLci hLg hcig hgst hcist hng hnci
  exact (hK.pos a (by omega) (by omega) (by omega) (by omega)).trans
    ((hout.keep a (.inr (.inr (.inr (.inl ⟨h1, h2⟩))))).trans
    ((callMC_keep (by pcw_omega)).trans (hJ.slots a h1 (by omega))))

/-- `__atexit` after the call. -/
theorem close_atexit {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    ∀ j, j < 8 → bytesT1 m'' (symAtexit + j) = bytesT1 w.mo (symAtexit + j) := by
  call_nums
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  intro j hj
  clear hLci hLg hcig hgst hcist hLsl hnL hng hnci hnst
  exact (hK.pos _ (by omega) (by omega) (by omega) (by omega)).trans
    ((hout.keep _ (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))).trans
    ((callMC_keep (by pcw_omega)).trans (hJ.atexit j hj)))

/-- The C `CallInfo`'s `previous`, `ci->next` and `luaD_precall`'s saved words after the call. -/
theorem close_words {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hK : CloseKeys w ins nci m' m'') :
    bytesT8 m'' (nci + ciPreviousOff) = BitVec.ofNat 64 w.ci ∧
    bytesT8 m'' (w.L + stateCiOff) = BitVec.ofNat 64 w.ci ∧
    bytesT8 m'' (w.ci + ciNextOff) = BitVec.ofNat 64 nci ∧
    bytesT8 m'' (w.sp - 8) = r ∧ bytesT8 m'' (w.sp - 16) = f.s0 := by
  call_nums
  have hprevMC : bytesT8 (callMC w ins MJ nci) (nci + ciPreviousOff) = BitVec.ofNat 64 w.ci := by
    simp only [callMC, pcCallMem, ciPreviousOff]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), b8_wm2_out (by omega), b8_wm2_out (by omega),
      fw8_wm8 (by omega), fw8_wm8 (by omega)]
    exact hJ.prev
  have hprev' : bytesT8 m' (nci + ciPreviousOff) = BitVec.ofNat 64 w.ci := by
    rw [bytesT8_congrT (m' := callMC w ins MJ nci) fun i hi =>
      hout.keep _ (.inr (.inr (.inl ⟨by simp only [ciPreviousOff]; omega, by simp only [ciPreviousOff, ciSize]; omega⟩)))]
    exact hprevMC
  refine ⟨?_, hK.lci.trans hprev', ?_, ?_, ?_⟩
  · rw [bytesT8_congrT (m' := m') fun i hi => hK.pos _ (by pomega) (by pomega) (by pomega) (by pomega)]
    exact hprev'
  · rw [bytesT8_congrT (m' := MJ) fun i hi => (hK.pos _ (by pomega) (by pomega) (by pomega) (by pomega)).trans
      ((hout.keep _ (.inr (.inl ⟨by simp only [ciNextOff]; omega, by simp only [ciNextOff, ciSize]; omega⟩))).trans
      (callMC_keep (by simp only [ciNextOff]; pcw_omega)))]
    exact hJ.next
  · rw [bytesT8_congrT (m' := MJ) fun i hi => (hK.pos _ (by omega) (by omega) (by omega) (by omega)).trans
      ((hout.above _ (by omega)).trans (callMC_keep (by pcw_omega)))]
    exact hJ.frame_ra
  · rw [bytesT8_congrT (m' := MJ) fun i hi => (hK.pos _ (by omega) (by omega) (by omega) (by omega)).trans
      ((hout.above _ (by omega)).trans (callMC_keep (by pcw_omega)))]
    exact hJ.frame_s0

/-- **What the call leaves** (`CloseIn`), from the join (`JoinIn`), what
`luaB_print` leaves (`PrintOut`) and `luaD_poscall` (`PoscallPost`), and
`luaD_precall`'s saved words. -/
theorem call_closeIn {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) {m' m'' : Mem} {out : List (BitVec 8)}
    (hout : PrintOut (w.sp - 96) w.L nci (w.slot ins.a) (ins.b - 1) w.rt.stackLast w.rt.g ls args (CallD w nci) (CallG w F ins nci) ph H
      (callMC w ins MJ nci) m' out) (hpos : PoscallPost m' m'' w.L nci (w.sp - 96) (ins.c - 1))
    (htext : Arms.TextLoaded m'') :
    (∃ buf H' FL' B', CloseIn p c w ins args ph F ls m'' out nci buf H' FL' B') ∧
      bytesT8 m'' (w.sp - 8) = r ∧ bytesT8 m'' (w.sp - 16) = f.s0 := by
  obtain ⟨buf, H', ⟨hPS, hkept, hbf, ⟨FL', B', hA⟩⟩⟩ := hout.st
  have hl := hA.lits
  have hK := close_keys cx hI hJ hout hpos
  have kFL := close_flKeep cx hI hJ hK hl
  have kB := close_bigKeep cx hI hJ hK hA.bigIn fun a h => h.hi
  have kmono : ∀ {a}, Kept w.rt.hix ph a → Kept H' (.up buf []) a := fun ha =>
    (ha.mono hJ.kept fun _ h => .inl h).mono hkept hbf
  have kF := close_foot cx hI hJ hout hK
  have kci := close_ci cx hI hJ hout hK
  have kab := close_above cx hI hJ hout hK
  have kbe := close_below cx hI hJ hout hK
  have kat := close_atexit cx hI hJ hout hK
  obtain ⟨wprev, wlci, wnext, wra, ws0⟩ := close_words cx hI hJ hout hK
  have hn := callNums cx hI hJ
  refine ⟨⟨buf, H', FL', B',
    { line := hout.line
      text := htext
      st := close_st cx hI hJ hK hPS kmono
      kept := fun cc hc hu => hkept cc (hJ.kept cc hc hu) hu
      bufFrom := fun a hb => (hbf a hb).imp id fun ⟨h1, h2, hu⟩ => ⟨h1, h2, fun hu' => hu (by
        obtain ⟨cc, hcc, hu1, h3, h4⟩ := hu'; exact ⟨cc, hJ.kept cc hcc hu1, hu1, h3, h4⟩)⟩
      lits := close_lits cx hI hJ hK hl
      foot := kF
      ci := kci
      above := kab
      below := kbe
      atexit := kat
      nil := fun j h1 h2 => by
        have := hK.nil (j - ins.a) (by omega)
        show bytesT1 m'' (w.slot j + tvalueTagOff) = _
        rw [show w.slot j = w.slot ins.a + 16 * (j - ins.a) by simp only [RelPtrs.slot, stackValueSize]; omega]
        exact this
      lci := wlci
      next := wnext
      nci_ne := by have := hn.nci_lo; omega
      nci_lo := by have := hn.nci_lo; simp only [symEnd]; omega
      nci_hi := hJ.nci_hi
      nci_al := hJ.nci_al
      nci_prev := wprev
      nci_kept := fun a h1 h2 => ⟨(hJ.nci_kept a h1 h2).1.mono hkept hbf, (hJ.nci_kept a h1 h2).2.1⟩
      nci_L := hJ.nci_L
      nci_g := hJ.nci_g
      nci_ci := hJ.nci_ci
      nci_stack := hJ.nci_stack
      nci_lits := hJ.nci_lits
      safe := (hA.safe.trans kFL).conseq fun M hM rt hrt => (hM rt hrt).weaken (fun _ h => h)
        (fun a _ hx => hx.imp (closeX_sub cx hI hJ) id) fun _ _ h => h
      big := hA.big.trans kB
      big_in := hA.bigIn.inK
      big_x := fun a hb hx => hA.bigIn.x a hb (closeX_sub cx hI hJ hx)
      big_fl := hA.big_fl
      big_lit := hA.bigIn.lit }⟩, wra, ws0⟩

/-- **`luaD_poscall` and the close at the join** (`PcPos`): `call_pos_run`, then
`call_closeIn`. -/
theorem call_pcpos (hN : PoscallN_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {r : BitVec 64} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls r f MJ nci H) (o : Array String) :
    PcPos w.sp w.L nci r f (PrintQ w ins args ph F ls nci H o (callMC w ins MJ nci))
      (CloseQ p c w ins args ph F ls nci o) := by
  intro m' o' ⟨out, ho, hout⟩ c0 h
  obtain ⟨c', s', m'', h', hpos⟩ := call_pos_run hN cx hI hJ hout c0 h
  have htext : Arms.TextLoaded m'' := h'.armMem ▸ h'.armText
  obtain ⟨⟨buf, H', FL', B', hcl⟩, hra, hs0⟩ := call_closeIn cx hI hJ hout hpos htext
  exact ⟨c', s', m'', h', hra, hs0, out, buf, H', FL', B', ho, hcl⟩

/-! ## The join's memory, both ways of `next_ci` -/

/-- The window of the relation, refuted by numbers. -/
theorem notWin_of {p : Proto} {w : RelPtrs} {a : Nat} (hr : Ranges p w)
    (h1 : a + 1 ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ a)
    (h2 : a + 1 ≤ w.ci + ciSavedpcOff ∨ w.ci + ciSavedpcOff + 8 ≤ a)
    (h3 : a + 1 ≤ w.L + stateTopOff ∨ w.L + stateTopOff + 8 ≤ a)
    (h4 : a < RuntimeData.spEntry - cStackBudget ∨ RuntimeData.spEntry ≤ a) : ¬ Win p w a := by
  have := hr.sp_eq
  simp only [Win, Slots, Scratch, execFrame, cStackBudget, RuntimeData.spEntry] at *
  omega

/-- The head's memory with `luaD_precall`'s saved words keeps every byte off the four stores. -/
theorem head_keep {c : Config} {w : RelPtrs} {pc : Nat} {ins : Word} {r : BitVec 64} {f : AbiFrame} {a : Nat}
    (h1 : a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) (h2 : a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a)
    (h3 : a + 1 ≤ w.sp - 16 ∨ w.sp ≤ a) (hsp : 16 ≤ w.sp) :
    bytesT1 (pcFrameMem (callMem c.σ.mem w pc ins) w.sp r f) a = bytesT1 c.σ.mem a := by
  apply bT1_congr
  simp only [pcFrameMem, callMem, stateTopOff, ciSavedpcOff]
  rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
    getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]

/-- **A head's numbers** (`omega`'s facts) from the relation and the invariant. -/
structure HeadNums (p : Proto) (w : RelPtrs) : Prop where
  sp : w.sp = 0x87fffd70
  base : w.base = w.func + 16
  sv : stackValueSize * p.maxstacksize = 16 * p.maxstacksize
  fits : w.func + 16 + 16 * p.maxstacksize ≤ w.rt.stackLast
  L_lo : 0x8006ecd0 ≤ w.L
  L_hi : w.L + 200 ≤ 0x87800000
  ci_lo : 0x8006ecd0 ≤ w.ci
  ci_hi : w.ci + 64 ≤ 0x87800000
  g_lo : 0x8006ecd0 ≤ w.rt.g
  g_hi : w.rt.g + 1400 ≤ 0x87800000
  sl_hi : w.rt.stackLast ≤ 0x87800000
  func_lo : 0x8006ecd0 ≤ w.func

theorem headNums {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls) : HeadNums p w := by
  have hr := cx.rel.core.ranges
  have hfs : w.func < w.rt.stackLast := by
    have := cx.room; simp only [RelPtrs.slot, RelPtrs.base, stackValueSize] at this; omega
  have k1 := (hI.L_in w.L (Nat.le_refl _) (by simp only [stateSize]; omega)).lo
  have k2 := (hI.L_in (w.L + stateSize - 1) (by simp only [stateSize]; omega) (by simp only [stateSize]; omega)).hi
  have k3 := (hI.ci_in w.ci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have k4 := (hI.ci_in (w.ci + ciSize - 1) (by simp only [ciSize]; omega) (by simp only [ciSize]; omega)).hi
  have k5 := (hI.g_in w.rt.g (Nat.le_refl _) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).lo
  have k6 := (hI.g_in (w.rt.g + gEnd - 1) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).hi
  have k8 := (hI.stack_in (w.rt.stackLast - 1) (by omega) (by omega)).hi
  have k9 := (hI.stack_in w.func (Nat.le_refl _) hfs).lo
  have r3 := hr.sp_eq
  have r6 := hI.fits
  clear hI cx hr
  simp only [gEnd, gStrcacheOff, strcacheN, strcacheM, ciSize, stateSize, heapStart, heapEnd, symEnd, symHeapEnd,
    stackValueSize, execFrame, RuntimeData.spEntry] at *
  exact ⟨by omega, rfl, rfl, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

/-- The memory at `OP_CALL`'s `jal` keeps every byte off `L->top` and `savedpc`. -/
theorem callMem_keep {m : Mem} {w : RelPtrs} {pc : Nat} {ins : Word} {a : Nat}
    (h1 : a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) (h2 : a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) :
    bytesT1 (callMem m w pc ins) a = bytesT1 m a := by
  apply bT1_congr
  simp only [callMem, stateTopOff, ciSavedpcOff]
  rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]

/-- **A memory of `luaD_precall`'s head against the complement**: one that
keeps the head's bytes off `L->top`, `savedpc` and `luaD_precall`'s frame
agrees with the complement off those and the window, below the C stack. -/
theorem keep_mo {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {M : Mem} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls)
    (hk : ∀ a, (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → (a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) →
      (a + 1 ≤ w.sp - 96 ∨ w.sp ≤ a) → bytesT1 M a = bytesT1 c.σ.mem a) :
    ∀ a, (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → (a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) →
      (a + 1 ≤ w.base ∨ w.base + 16 * p.maxstacksize ≤ a) → a < 0x87fefe20 → bytesT1 M a = bytesT1 w.mo a := by
  intro a h1 h2 h3 h4
  have hr := cx.rel.core.ranges
  obtain ⟨hsp, -, hsv, -⟩ := headNums cx hI
  have hspE : RuntimeData.spEntry - cStackBudget = 0x87fefe20 := rfl
  have e1 : a + 1 ≤ w.sp - 96 ∨ w.sp ≤ a := by rw [hsp]; omega
  have e2 : a + 1 ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ a := by rw [hsv]; exact h3
  have e3 : a + 1 ≤ w.ci + ciSavedpcOff ∨ w.ci + ciSavedpcOff + 8 ≤ a := by simp only [ciSavedpcOff]; omega
  have e4 : a + 1 ≤ w.L + stateTopOff ∨ w.L + stateTopOff + 8 ≤ a := by simp only [stateTopOff]; omega
  have e5 : a < RuntimeData.spEntry - cStackBudget ∨ RuntimeData.spEntry ≤ a := by rw [hspE]; omega
  exact (hk a h1 h2 e1).trans (cx.rel.core.frame a (notWin_of hr e2 e3 e4 e5))

/-- **`stdout`'s state at a head memory**: any memory agreeing with the
complement off `L->top`, the `CallInfo`'s `savedpc`, the window and the C
stack (`stdout`'s footprint lies off all of them). -/
theorem printSt_head {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {M : Mem} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls)
    (kH : ∀ a, (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → (a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) →
      (a + 1 ≤ w.base ∨ w.base + 16 * p.maxstacksize ≤ a) → a < 0x87fefe20 → bytesT1 M a = bytesT1 w.mo a) :
    PrintSt M ph w.rt.hix := by
  have hc := cx.rel.core
  have hPS : PrintSt w.mo ph w.rt.hix := ⟨hI.io, hc.comp.runtime.heap.ext (fill_ext _), hI.cells⟩
  obtain ⟨hsp, hbase, hsv, hfits, hL1, hL2, hci1, hci2, hg1, hg2, hsl, hf0⟩ := headNums cx hI
  have hHE : heapEnd = 0x87800000 := rfl
  refine hPS.keep fun a ha => ?_
  have hL : ¬ (w.L ≤ a ∧ a < w.L + 200) := fun h => (hI.L_in a h.1 (by simp only [stateSize]; omega)).not_printFoot ha
  have hC : ¬ (w.ci ≤ a ∧ a < w.ci + 64) := fun h => (hI.ci_in a h.1 (by simp only [ciSize]; omega)).not_printFoot ha
  have hS : ¬ (w.func ≤ a ∧ a < w.rt.stackLast) := fun h => (hI.stack_in a h.1 h.2).not_printFoot ha
  have hlo : a < 0x87fefe20 := by
    rcases ha with hg | hbf | ⟨hr', _⟩ | hro
    · simp only [Kit.StdioGlob] at hg; omega
    · have := hPS.io.buf_hi a hbf; omega
    · have e4 : symMallocAv = 0x8005c6d0 := rfl
      have e5 : symMallocSbrkBase = 0x8005d388 := rfl
      have e6 : symBrk = 0x8005d3b8 := rfl
      have e7 : symMallocTopPad = 0x8005d3d8 := rfl
      have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
      have e9 : symMallocMallinfo = 0x8005e560 := rfl
      simp only [HeapReads] at hr'; omega
    · omega
  exact kH a (by omega) (by omega) (by omega) hlo

/-- **The join when `ci->next` is reused** (`next_ci`'s `ci->next` a
`CiNext` block): the head's memory with `luaD_precall`'s saved `s0`, `ra`. -/
theorem join_reuse {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} (f : AbiFrame) {nci : Nat}
    (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hnext : rd64 w.mo (w.ci + ciNextOff) = some nci) (hn : CiNext w.mo w.ci nci) (h0 : nci ≠ 0) :
    JoinIn p c w ins ph F FL ls 0x8001c7d8#64 f
      (pcFrameMem (callMem c.σ.mem w s.pc ins) w.sp 0x8001c7d8#64 f) nci w.rt.hix := by
  have hc := cx.rel.core
  have hr := hc.ranges
  have hlua := hc.comp.runtime.lua
  have hNA := hI.nci nci hnext h0
  obtain ⟨hsp, hbase, hsv, hfits, hL1, hL2, hci1, hci2, hg1, hg2, hsl, hf0⟩ := headNums cx hI
  have hslot : w.slot ins.a + 16 * ins.b ≤ w.base + 16 * p.maxstacksize := by
    have := cx.ab; simp only [RelPtrs.slot, stackValueSize]; omega
  have hroom := cx.room
  have hLci := hr.L_sep_ci; have hcis := hr.ci_sep; have hLs := hr.L_sep
  have hcit := hr.ci_top; have hLt := hr.L_top
  have hnk1 := (hNA.kept nci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have hnk2 := (hNA.kept (nci + ciSize - 1) (by simp only [ciSize]; omega) (by simp only [ciSize]; omega)).hi
  have hnL := hNA.L; have hng := hNA.g; have hnci := hNA.ci; have hnst := hNA.stack
  have ogL := hI.objs.g_L; have ogci := hI.objs.g_ci; have ogst := hI.objs.g_stack
  simp only [Apart, ciSize, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM, heapStart, heapEnd, symEnd,
    symHeapEnd, RuntimeData.spEntry, cStackBudget, stackValueSize] at hLci hcis hLs hcit hLt hnk1 hnk2 hnL hng
  simp only [Apart, ciSize, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM, stackValueSize] at hnci hnst ogL
  simp only [Apart, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at ogci ogst
  have hHE : heapEnd = 0x87800000 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  -- the head's memory against the complement
  have kM : ∀ a, ¬ Win p w a → bytesT1 c.σ.mem a = bytesT1 w.mo a := hc.frame
  have kJ : ∀ a, (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → (a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) →
      (a + 1 ≤ w.sp - 16 ∨ w.sp ≤ a) →
      bytesT1 (pcFrameMem (callMem c.σ.mem w s.pc ins) w.sp 0x8001c7d8#64 f) a = bytesT1 c.σ.mem a :=
    fun a h1 h2 h3 => head_keep h1 h2 h3 (by omega)
  have nW : ∀ a, (a + 1 ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ a) →
      (a + 1 ≤ w.ci + ciSavedpcOff ∨ w.ci + ciSavedpcOff + 8 ≤ a) →
      (a + 1 ≤ w.L + stateTopOff ∨ w.L + stateTopOff + 8 ≤ a) →
      (a < RuntimeData.spEntry - cStackBudget ∨ RuntimeData.spEntry ≤ a) → ¬ Win p w a :=
    fun a h1 h2 h3 h4 => notWin_of hr h1 h2 h3 h4
  have hspE : RuntimeData.spEntry - cStackBudget = 0x87fefe20 := rfl
  have hspE' : RuntimeData.spEntry = 0x87fffe20 := rfl
  have kH := keep_mo cx hI fun a h1 h2 h3 => kJ a h1 h2 (by omega)
  have hnlo := hn.lo; have hnhi := hn.hi
  simp only [symEnd, ciSize, RuntimeData.spEntry, cStackBudget] at hnlo hnhi
  -- (lane F1-19) the literals' footprint, the bytes off what the caller keeps, `g->strt`'s words
  have fW : ∀ a, FL a → bytesT1 (pcFrameMem (callMem c.σ.mem w s.pc ins) w.sp 0x8001c7d8#64 f) a =
      bytesT1 w.mo a := fun a ha => by
    have hk := hI.lits_in a ha
    have hd := hI.lits_apart a ha
    simp only [CallLitDirty, not_or, stateTopOff, stateCiOff, ciSize, stateNciOff] at hd
    obtain ⟨d1, d2, d3, d4, -⟩ := hd
    have := hk.hi
    exact kH a (by omega) (by omega) (by omega) (by omega)
  have kX : ∀ a, (Kept w.rt.hix ph a ∧ ¬ CallX0 w F a) ∨ ReentWord a →
      bytesT1 (pcFrameMem (callMem c.σ.mem w s.pc ins) w.sp 0x8001c7d8#64 f) a = bytesT1 w.mo a := fun a ha => by
    rcases ha with ⟨hk, hx⟩ | hr'
    · have := hk.hi
      simp only [CallX0, not_or] at hx
      obtain ⟨-, hxL, -, hxc, hxs, -, -⟩ := hx
      simp only [stateSize, ciSize] at hxL hxc
      exact kH a (by omega) (by omega) (by omega) (by omega)
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr'
      exact kH a (by omega) (by omega) (by omega) (by omega)
  have sW : ∀ j, j < 8 → bytesT1 (pcFrameMem (callMem c.σ.mem w s.pc ins) w.sp 0x8001c7d8#64 f)
      (w.rt.g + gStrtNuseOff + j) = bytesT1 w.mo (w.rt.g + gStrtNuseOff + j) := fun j hj =>
    kH _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
      (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
  refine
    { foot := fun a ha => ?_
      ci := fun a h1 h2 h3 h4 => ?_
      above := fun a ha => kJ a (by omega) (by omega) (by omega)
      slots := fun a h1 h2 => kJ a (by omega) (by omega) (by omega)
      atexit := fun j hj => kH _ (by omega) (by omega) (by omega) (by omega)
      top_w := ?_
      tbc_w := ?_
      g_w := ?_
      hook_w := ?_
      mt_w := fun t ht => ?_
      st := printSt_head cx hI kH
      kept := fun _ h _ => h
      brk := Nat.le_add_right _ _
      lits := hI.lits.trans fW
      fl_w := fW
      keepK := kX
      nci_x := fun a h1 h2 _ => ⟨nci, hnext, h0, h1, h2⟩
      strt_w := sW
      cache := hI.cache.congr fun a h1 h2 => ?_
      next := ?_
      prev := ?_
      nci_lo := hn.lo
      nci_hi := hn.hi
      nci_al := hn.al
      nci_kept := fun a h1 h2 => ⟨hNA.kept a h1 h2, hNA.foot a h1 h2⟩
      nci_L := hNA.L
      nci_g := hNA.g
      nci_ci := hNA.ci
      nci_stack := hNA.stack
      nci_lits := hNA.lits
      frame_ra := ?_
      frame_s0 := ?_ }
  · -- the frozen objects
    have hd := hI.stat_apart a ha
    simp only [CallDirty, not_or, stateTopOff, stateCiOff, ciSize, stateNciOff] at hd
    obtain ⟨d1, -, d3, d4, -⟩ := hd
    have hst : a < 0x87800000 := by
      rcases hI.stat_in a ha with hk | hk | hk
      · have := hk.hi; omega
      · simp only [symTohost] at hk; omega
      · simp only [LocaleW, symImpurePtr] at hk; omega
    exact kH a (by omega) (by omega) (by omega) (by omega)
  · simp only [Rng, ciNextOff, ciSavedpcOff, ciSize, not_and, Nat.not_lt] at h2 h3 h4
    exact kH a (by omega) (by omega) (by omega) (by omega)
  · simp only [pcFrameMem, callMem, stateTopOff, ciSavedpcOff]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_same rfl]
  · rw [bytesT8_congrT fun j _ => kH _ (by simp only [stateTbclistOff]; omega) (by simp only [stateTbclistOff]; omega)
      (by simp only [stateTbclistOff]; omega) (by simp only [stateTbclistOff]; omega)]
    exact bytesT8_of_rd64 hlua.tbclist
  · rw [bytesT8_congrT fun j _ => kH _ (by simp only [stateGOff]; omega) (by simp only [stateGOff]; omega)
      (by simp only [stateGOff]; omega) (by simp only [stateGOff]; omega)]
    exact bytesT8_of_rd64 hlua.g
  · rw [bytesT4_congrT fun j _ => kH _ (by simp only [stateHookmaskOff]; omega)
      (by simp only [stateHookmaskOff]; omega) (by simp only [stateHookmaskOff]; omega)
      (by simp only [stateHookmaskOff]; omega)]
    exact bytesT4_of_rd32 hlua.hookmask
  · have hto : t ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, luaTnil, luaTboolean, luaTnumber] at ht; omega
    rw [bytesT8_congrT fun j _ => kH _ (by simp only [gMtOff]; omega) (by simp only [gMtOff]; omega)
      (by simp only [gMtOff]; omega) (by simp only [gMtOff]; omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact bytesT8_of_rd64 hlua.mt_nil
    · exact bytesT8_of_rd64 hlua.mt_boolean
    · exact bytesT8_of_rd64 hlua.mt_number
  · -- the string cache's words, in `g`
    simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2
    exact kH a (by omega) (by omega) (by omega) (by omega)
  · rw [bytesT8_congrT fun j _ => kH _ (by simp only [ciNextOff]; omega) (by simp only [ciNextOff]; omega)
      (by simp only [ciNextOff]; omega) (by simp only [ciNextOff]; omega)]
    exact bytesT8_of_rd64 hnext
  · rw [bytesT8_congrT fun j _ => kH _ (by simp only [ciPreviousOff]; omega) (by simp only [ciPreviousOff]; omega)
      (by simp only [ciPreviousOff]; omega) (by simp only [ciPreviousOff]; omega)]
    exact bytesT8_of_rd64 hn.previous
  · simp only [pcFrameMem]; exact fw8_same rfl
  · simp only [pcFrameMem]; rw [fw8_wm8 (by omega)]; exact fw8_same rfl

/-! ## The join after `luaE_extendCI` -/

/-- The memory at `luaE_extendCI`'s call from `OP_CALL print`. -/
abbrev callExtMem (c : Config) (w : RelPtrs) (pc : Nat) (ins : Word) (f : AbiFrame) : Mem :=
  pcExtMem (callMem c.σ.mem w pc ins) w.sp (w.slot ins.a) (ins.c - 1) (w.slot ins.a + 16 * ins.b) 0x8001c7d8#64 f

/-- The memory at `luaE_extendCI`'s call keeps every byte off its stores. -/
theorem ext_keep {c : Config} {w : RelPtrs} {pc : Nat} {ins : Word} {f : AbiFrame} {a : Nat}
    (h1 : a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) (h2 : a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a)
    (h3 : a + 1 ≤ w.sp - 96 ∨ w.sp ≤ a) (hsp : 96 ≤ w.sp) :
    bytesT1 (callExtMem c w pc ins f) a = bytesT1 c.σ.mem a := by
  apply bT1_congr
  simp only [callExtMem, pcExtMem, pcFrameMem, callMem, stateTopOff, ciSavedpcOff]
  rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
    getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
    getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
    getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]

/-- (lane F1-19) **A static word the relation reads**: the image below the
HTIF mailbox, the locale words, `_REENT`'s `_dtoa_r` words; below the heap. -/
def StaticW (a : Nat) : Prop := (0x80000000 ≤ a ∧ a < symTohost) ∨ LocaleW a ∨ ReentWord a

theorem StaticW.lt {a : Nat} (h : StaticW a) : a < 0x8006ecd0 := by
  simp only [StaticW, LocaleW, ReentWord, symTohost, symImpurePtr, symImpureData, reentResultOff,
    reentFreelistOff] at h
  omega

/-- A static word is no byte `_malloc_r` writes. -/
theorem StaticW.not_mallocW {chunks : List Chunk} {a : Nat} (h : StaticW a) : ¬ MallocW chunks a := by
  rintro (hg | ⟨h1, -, -⟩)
  · have e4 : symMallocAv = 0x8005c6d0 := rfl
    have e5 : symMallocSbrkBase = 0x8005d388 := rfl
    have e6 : symBrk = 0x8005d3b8 := rfl
    have e9 : symMallocMallinfo = 0x8005e560 := rfl
    have e10 : errnoAddr = 0x8005d408 := rfl
    simp only [MallocGlobal] at hg
    simp only [StaticW, LocaleW, ReentWord, symTohost, symImpurePtr, symImpureData, reentResultOff,
      reentFreelistOff] at h
    omega
  · have := h.lt; have e0 : heapStart = 0x8006ecd0 := rfl; omega

/-- The bytes below `_malloc_r`'s globals, `__atexit` and the bytes past the
arena are no bytes `_malloc_r` writes. -/
theorem not_mallocW_of {chunks : List Chunk} {a : Nat}
    (h : a < 0x8005c6d0 ∨ (0x8005d450 ≤ a ∧ a < 0x8005d458) ∨ 0x87800000 ≤ a) : ¬ MallocW chunks a := by
  rintro (hg | ⟨h1, h2, -⟩)
  · have e0 : heapStart = symEnd := rfl
    have e1 : symEnd = 0x8006ecd0 := rfl
    have e4 : symMallocAv = 0x8005c6d0 := rfl
    have e5 : symMallocSbrkBase = 0x8005d388 := rfl
    have e6 : symBrk = 0x8005d3b8 := rfl
    have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
    have e9 : symMallocMallinfo = 0x8005e560 := rfl
    have e10 : errnoAddr = 0x8005d408 := rfl
    simp only [MallocGlobal] at hg
    omega
  · have e0 : heapEnd = symHeapEnd := rfl
    have e1 : symHeapEnd = 0x87800000 := rfl
    have e2 : heapStart = symEnd := rfl
    have e3 : symEnd = 0x8006ecd0 := rfl
    omega

/-- A range of chunks in use lies apart from a range off them. -/
theorem apart_of_kept {H : HeapIx} {ph : StdoutPh} {x n y k : Nat}
    (hy : ∀ a, y ≤ a → a < y + k → Kept H ph a) (hx : ∀ a, x ≤ a → a < x + n → ¬ InUse H.chunks a)
    (hn : 0 < n) (hk : 0 < k) : Apart x n y k := by
  unfold Apart
  refine Classical.byContradiction fun hc => ?_
  simp only [not_or, Nat.not_le] at hc
  by_cases h : x ≤ y
  · exact hx y h (by omega) (hy y (Nat.le_refl _) (by omega)).inuse
  · exact hx x (Nat.le_refl _) (by omega) (hy x (by omega) (by omega)).inuse

/-- **The join when `ci->next` is NULL**: the memory `luaE_extendCI` leaves
(`ExtPost`), the new `CallInfo` `nci` fresh in the arena. -/
theorem join_ext {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} (f : AbiFrame) {nci : Nat} {m' : Mem} {H' : HeapIx}
    (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hnext0 : rd64 w.mo (w.ci + ciNextOff) = some 0)
    (hX : ExtPost (callExtMem c w s.pc ins f) m' w.sp w.L w.ci w.rt.g w.rt.hix H' nci) :
    JoinIn p c w ins ph F FL ls 0x8001c7d8#64 f m' nci H' := by
  have hc := cx.rel.core
  have hr := hc.ranges
  have hlua := hc.comp.runtime.lua
  obtain ⟨hsp, hbase, hsv, hfits, hL1, hL2, hci1, hci2, hg1, hg2, hsl, hf0⟩ := headNums cx hI
  have hslot : w.slot ins.a + 16 * ins.b ≤ w.base + 16 * p.maxstacksize := by
    have := cx.ab; simp only [RelPtrs.slot, stackValueSize]; omega
  have hroom := cx.room
  have hLci := hr.L_sep_ci; have hcis := hr.ci_sep; have hLs := hr.L_sep
  have ogL := hI.objs.g_L; have ogci := hI.objs.g_ci; have ogst := hI.objs.g_stack
  simp only [ciSize, stateSize, stackValueSize] at hLci hcis hLs
  simp only [Apart, ciSize, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at ogL ogci ogst
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hsym : symAtexit = 0x8005d450 := rfl
  -- the new `CallInfo`: fresh in the arena
  have hfr : ∀ a, nci ≤ a → a < nci + ciSize → ¬ InUse w.rt.hix.chunks a := fun a h1 h2 => (hX.fresh a h1 h2).1
  have hn1 := (hX.fresh nci (Nat.le_refl _) (by simp only [ciSize]; omega)).2.1
  have hn2 := (hX.fresh (nci + ciSize - 1) (by simp only [ciSize]; omega) (by simp only [ciSize]; omega)).2.2
  simp only [ciSize] at hn2
  -- the head's memory against the complement
  have kM : ∀ a, ¬ Win p w a → bytesT1 c.σ.mem a = bytesT1 w.mo a := hc.frame
  have kHE := keep_mo cx hI fun a h1 h2 h3 => ext_keep (c := c) (pc := s.pc) (ins := ins) (f := f) h1 h2 h3 (by omega)
  -- `luaE_extendCI`'s memory against its call's
  have kE : ∀ a, ¬ MallocW w.rt.hix.chunks a → ¬ (nci ≤ a ∧ a < nci + ciSize) → ¬ Rng (w.ci + ciNextOff) 8 a →
      ¬ Rng (w.L + stateNciOff) 2 a → ¬ Below (w.sp - 96) 4096 a → ¬ Rng (w.rt.g + gGCdebtOff) 8 a →
      bytesT1 m' a = bytesT1 (callExtMem c w s.pc ins f) a := fun a h1 h2 h3 h4 h5 h6 =>
    hX.keep a fun h => by rcases h with h | h | h | h | h | h <;> contradiction
  -- a byte of a chunk in use (or below the arena) off `ci->next` and `L->nci`
  have kKE : ∀ a, (Kept w.rt.hix ph a ∨ StaticW a) → ¬ Rng (w.ci + ciNextOff) 8 a →
      ¬ Rng (w.L + stateNciOff) 2 a → ¬ Rng (w.rt.g + gGCdebtOff) 8 a →
      bytesT1 m' a = bytesT1 (callExtMem c w s.pc ins f) a :=
    fun a hk h3 h4 h6 => by
      have hlo : a < 0x87800000 := hk.elim (fun k => hHE ▸ k.hi) fun h => by have := h.lt; omega
      refine kE a (hk.elim Kept.not_mallocW StaticW.not_mallocW)
        (fun hn => hk.elim (fun k => hfr a hn.1 hn.2 k.inuse) fun h => ?_) h3 h4
        (by simp only [Below]; omega) h6
      have := (hX.fresh a hn.1 hn.2).2.1; have := h.lt; omega
  have kK : ∀ a, (Kept w.rt.hix ph a ∨ StaticW a) → ¬ Rng (w.ci + ciNextOff) 8 a →
      ¬ Rng (w.L + stateNciOff) 2 a → (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → (a + 1 ≤ w.ci + 32 ∨ w.ci + 40 ≤ a) →
      (a + 1 ≤ w.base ∨ w.base + 16 * p.maxstacksize ≤ a) → ¬ Rng (w.rt.g + gGCdebtOff) 8 a →
      bytesT1 m' a = bytesT1 w.mo a :=
    fun a hk h3 h4 e1 e2 e3 e6 => by
      have hlo : a < 0x87800000 := hk.elim (fun k => hHE ▸ k.hi) fun h => by have := h.lt; omega
      exact (kKE a hk h3 h4 e6).trans (kHE a e1 e2 e3 (by omega))
  -- the words of `L` but `L->top`, `L->nci`
  have kL : ∀ a, w.L ≤ a → a < w.L + stateSize → (a + 1 ≤ w.L + 12 ∨ w.L + 14 ≤ a) →
      (a + 1 ≤ w.L + 16 ∨ w.L + 24 ≤ a) → bytesT1 m' a = bytesT1 w.mo a := fun a h1 h2 h3 h4 => by
    simp only [stateSize] at h2
    exact kK a (.inl (hI.L_in a h1 (by simp only [stateSize]; omega))) (by simp only [Rng, ciNextOff]; omega)
      (by simp only [Rng, stateNciOff]; omega) h4 (by omega) (by omega) (by simp only [Rng, gGCdebtOff]; omega)
  -- the words of `g`
  have kG : ∀ a, w.rt.g ≤ a → a < w.rt.g + 1400 → ¬ Rng (w.rt.g + gGCdebtOff) 8 a →
      bytesT1 m' a = bytesT1 w.mo a := fun a h1 h2 h3 =>
    kK a (.inl (hI.g_in a h1 (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)))
      (by simp only [Rng, ciNextOff]; omega) (by simp only [Rng, stateNciOff]; omega) (by omega) (by omega)
      (by omega) h3
  -- the bytes of `luaE_extendCI`'s writes off the frame
  have kF : ∀ a, w.sp - 96 ≤ a → bytesT1 m' a = bytesT1 (callExtMem c w s.pc ins f) a := fun a ha =>
    kE a (not_mallocW_of (.inr (.inr (by omega)))) (by simp only [ciSize]; omega)
      (by simp only [Rng, ciNextOff]; omega) (by simp only [Rng, stateNciOff]; omega)
      (by simp only [Below]; omega) (by simp only [Rng, gGCdebtOff]; omega)
  -- (lane F1-19) the literals' footprint, the bytes off what the caller keeps, `g->strt`'s words
  have fW : ∀ a, FL a → bytesT1 m' a = bytesT1 w.mo a := fun a ha => by
    have hd := hI.lits_apart a ha
    simp only [CallLitDirty, not_or, stateTopOff, stateCiOff, ciSize, stateNciOff] at hd
    obtain ⟨d1, -, d3, d4, d5, d6⟩ := hd
    exact kK a (.inl (hI.lits_in a ha)) (by simp only [Rng, ciNextOff]; omega)
      (by simp only [Rng, stateNciOff]; omega) (by omega) (by omega) (by omega)
      (by simp only [Rng, gGCdebtOff] at d6 ⊢; omega)
  have kX : ∀ a, (Kept w.rt.hix ph a ∧ ¬ CallX0 w F a) ∨ ReentWord a → bytesT1 m' a = bytesT1 w.mo a :=
    fun a ha => by
    rcases ha with ⟨hk, hx⟩ | hr'
    · have := hk.hi
      simp only [CallX0, not_or] at hx
      obtain ⟨-, hxL, hxg, hxc, hxs, -, -⟩ := hx
      simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at hxL hxc hxg
      exact kK a (.inl hk) (by simp only [Rng, ciNextOff]; omega) (by simp only [Rng, stateNciOff]; omega)
        (by omega) (by omega) (by omega) (by simp only [Rng, gGCdebtOff]; omega)
    · have hr2 := hr'
      simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr2
      exact kK a (.inr (.inr (.inr hr'))) (by simp only [Rng, ciNextOff]; omega)
        (by simp only [Rng, stateNciOff]; omega) (by omega) (by omega) (by omega)
        (by simp only [Rng, gGCdebtOff]; omega)
  have sW : ∀ j, j < 8 → bytesT1 m' (w.rt.g + gStrtNuseOff + j) = bytesT1 w.mo (w.rt.g + gStrtNuseOff + j) :=
    fun j hj => kG _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
      (by simp only [Rng, gGCdebtOff, gStrtNuseOff]; omega)
  refine
    { foot := fun a ha => ?_
      ci := fun a h1 h2 h3 h4 => ?_
      above := fun a ha => (kF a (by omega)).trans (ext_keep (by omega) (by omega) (.inr ha) (by omega))
      slots := fun a h1 h2 => ?_
      atexit := fun j hj => ?_
      top_w := ?_
      tbc_w := ?_
      g_w := ?_
      hook_w := ?_
      mt_w := fun t ht => ?_
      st := hX.stdio ph (printSt_head cx hI kHE) (fun a hb ho => by
          rcases ho with ha | ha | ha
          · exact (hI.L_in a ha.1 ha.2).nbuf hb
          · exact (hI.ci_in a ha.1 ha.2).nbuf hb
          · exact (hI.g_in a (by simp only [Rng, gGCdebtOff] at ha; omega)
              (by simp only [Rng, gGCdebtOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at ha ⊢; omega)).nbuf hb)
        fun _ => by
          have h1 := hI.room (.inr hnext0); have h2 : H'.brk ≤ w.rt.brkv + extRoom := hX.brk
          simp only [firstRoom, extRoom] at h1 h2; omega
      kept := hX.kept
      brk := hX.brk
      lits := hI.lits.trans fW
      fl_w := fW
      keepK := kX
      nci_x := fun a h1 h2 hk => absurd hk.inuse (hfr a h1 h2)
      strt_w := sW
      cache := hI.cache.congr fun a h1 h2 => kG a (by simp only [gStrcacheOff] at h1; omega)
        (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h2; omega)
        (by simp only [Rng, gGCdebtOff, gStrcacheOff] at h1 ⊢; omega)
      next := hX.next
      prev := hX.prev
      nci_lo := by have : symEnd = 0x8006ecd0 := rfl; omega
      nci_hi := by have : RuntimeData.spEntry - cStackBudget = 0x87fefe20 := rfl; simp only [ciSize]; omega
      nci_al := hX.al
      nci_kept := fun a h1 h2 => ?_
      nci_L := apart_of_kept (fun a h1 h2 => hI.L_in a h1 h2) hfr (by decide) (by decide)
      nci_g := apart_of_kept (fun a h1 h2 => hI.g_in a h1 h2) hfr (by decide) (by decide)
      nci_ci := apart_of_kept (fun a h1 h2 => hI.ci_in a h1 h2) hfr (by decide) (by decide)
      nci_stack := apart_of_kept (fun a h1 h2 => hI.stack_in a h1 (by omega)) hfr (by decide) (by omega)
      nci_lits := fun ts hts => apart_of_kept (fun a h1 h2 => hI.lit_strs ts hts a h1 h2) hfr (by decide) (by decide)
      frame_ra := ?_
      frame_s0 := ?_ }
  · -- the frozen objects
    have hd := hI.stat_apart a ha
    simp only [CallDirty, not_or, stateTopOff, stateCiOff, ciSize, stateNciOff] at hd
    obtain ⟨d1, -, d3, d4, d5, -, d7⟩ := hd
    exact kK a ((hI.stat_in a ha).imp id fun h => h.elim .inl fun h => .inr (.inl h))
      (by simp only [Rng, ciNextOff]; omega) (by simp only [Rng, stateNciOff]; omega)
      (by omega) (by omega) (by omega) (by simp only [Rng, gGCdebtOff]; omega)
  · have h2' : a < w.ci + 64 := h2
    have k := kK a (.inl (hI.ci_in a h1 h2)) h3 (by simp only [Rng, stateNciOff]; omega) (by omega)
    simp only [Rng, ciNextOff, ciSavedpcOff, ciSize, not_and, Nat.not_lt] at h2 h3 h4
    exact k (by omega) (by omega) (by simp only [Rng, gGCdebtOff]; omega)
  · have hk := hI.stack_in a (by omega) (by omega)
    refine (kKE a (.inl hk) (by simp only [Rng, ciNextOff]; omega) (by simp only [Rng, stateNciOff]; omega)
      (by simp only [Rng, gGCdebtOff]; omega)).trans (ext_keep (by omega) (by omega) (.inl (by omega)) (by omega))
  · refine (kE _ (not_mallocW_of (.inr (.inl (by omega)))) (by omega) (by simp only [Rng, ciNextOff]; omega)
      (by simp only [Rng, stateNciOff]; omega) (by simp only [Below]; omega)
      (by simp only [Rng, gGCdebtOff]; omega)).trans
      (kHE _ (by omega) (by omega) (by omega) (by omega))
  · rw [bytesT8_congrT fun j _ => kKE _ (.inl (hI.L_in _ (by omega) (by simp only [stateTopOff, stateSize]; omega)))
      (by simp only [Rng, ciNextOff, stateTopOff]; omega) (by simp only [Rng, stateNciOff, stateTopOff]; omega)
      (by simp only [Rng, gGCdebtOff, stateTopOff]; omega)]
    simp only [callExtMem, pcExtMem, pcFrameMem, callMem, stateTopOff, ciSavedpcOff]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega),
      fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_same rfl]
  · rw [bytesT8_congrT fun j _ => kL _ (by simp only [stateTbclistOff]; omega)
      (by simp only [stateTbclistOff, stateSize]; omega) (by simp only [stateTbclistOff]; omega)
      (by simp only [stateTbclistOff]; omega)]
    exact bytesT8_of_rd64 hlua.tbclist
  · rw [bytesT8_congrT fun j _ => kL _ (by simp only [stateGOff]; omega)
      (by simp only [stateGOff, stateSize]; omega) (by simp only [stateGOff]; omega)
      (by simp only [stateGOff]; omega)]
    exact bytesT8_of_rd64 hlua.g
  · rw [bytesT4_congrT fun j _ => kL _ (by simp only [stateHookmaskOff]; omega)
      (by simp only [stateHookmaskOff, stateSize]; omega) (by simp only [stateHookmaskOff]; omega)
      (by simp only [stateHookmaskOff]; omega)]
    exact bytesT4_of_rd32 hlua.hookmask
  · have hto : t ≤ 3 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, luaTnil, luaTboolean, luaTnumber] at ht; omega
    rw [bytesT8_congrT fun j _ => kG _ (by simp only [gMtOff]; omega) (by simp only [gMtOff]; omega)
      (by simp only [Rng, gMtOff, gGCdebtOff]; omega)]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl
    · exact bytesT8_of_rd64 hlua.mt_nil
    · exact bytesT8_of_rd64 hlua.mt_boolean
    · exact bytesT8_of_rd64 hlua.mt_number
  · -- the new `CallInfo`
    have hf := hX.fresh a h1 h2
    refine ⟨⟨hX.nci_in a h1 h2, hf.2.1, hf.2.2, fun hb => hf.1 (hI.io.buf_inUse hb)⟩, fun hF => ?_,
      fun hL => hf.1 (hI.lits_in a hL).inuse⟩
    rcases hI.stat_in a hF with hk | hk | hk
    · exact hf.1 hk.inuse
    · have := hf.2.1; simp only [symTohost] at hk; omega
    · have := hf.2.1; simp only [LocaleW, symImpurePtr] at hk; omega
  · rw [bytesT8_congrT fun j _ => kF _ (by omega)]
    simp only [callExtMem, pcExtMem, pcFrameMem]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega)]
    exact fw8_same rfl
  · rw [bytesT8_congrT fun j _ => kF _ (by omega)]
    simp only [callExtMem, pcExtMem, pcFrameMem]
    rw [fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_wm8 (by omega)]
    exact fw8_same rfl

/-! ## `PrintCall_Statement CallInv` from `CALL`'s open parts -/

/-- `PcC` with a weaker post. -/
theorem PcC.mono {sp L nci : Nat} {f : AbiFrame} {M : Mem} {o : Array String} {Q Q' : Mem → Array String → Prop}
    (h : PcC sp L nci f M o Q) (hq : ∀ m o', Q m o' → Q' m o') : PcC sp L nci f M o Q' := fun c hc => by
  obtain ⟨c', s', m, o', h1, h2, h3⟩ := h c hc
  exact ⟨c', s', m, o', h1, h2, hq _ _ h3⟩

/-- The C function's post at any join (`JoinIn`). -/
def JoinQ (p : Proto) (c : Config) (w : RelPtrs) (ins : Word) (args : List Value) (ph : StdoutPh)
    (F FL : Nat → Prop) (ls : LitPtrs) (f : AbiFrame) (nci : Nat) (o : Array String) (m : Mem)
    (o' : Array String) : Prop :=
  ∃ H MJ, JoinIn p c w ins ph F FL ls 0x8001c7d8#64 f MJ nci H ∧
    PrintQ w ins args ph F ls nci H o (callMC w ins MJ nci) m o'

/-- **The C function at a join**: `call_pcc`, its post weakened to `JoinQ`. -/
theorem join_pcc (hPR : PrintRel_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {f : AbiFrame}
    {MJ : Mem} {nci : Nat} {H : HeapIx} (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls)
    (hJ : JoinIn p c w ins ph F FL ls 0x8001c7d8#64 f MJ nci H) (hbud : AnyAlloc args → HeapBudget w args)
    (o : Array String) :
    PcC w.sp w.L nci f (callMC w ins MJ nci) o (JoinQ p c w ins args ph F FL ls f nci o) :=
  (call_pcc hPR cx hI hJ hbud o).mono fun _ _ hq => ⟨H, MJ, hJ, hq⟩

/-- **`luaD_poscall` and the close at any join** (`JoinQ`). -/
theorem join_pcpos (hN : PoscallN_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {f : AbiFrame} {nci : Nat}
    (cx : CallCx p c s w ins args) (hI : CallInvAt p w ph F FL ls) (o : Array String) :
    PcPos w.sp w.L nci 0x8001c7d8#64 f (JoinQ p c w ins args ph F FL ls f nci o)
      (CloseQ p c w ins args ph F ls nci o) := fun m' o' ⟨_, _, hJ, hq⟩ =>
  call_pcpos hN cx hI hJ o m' o' hq

/-- **The post of `PrintCall_Statement`** from the close (`call_close`). -/
theorem close_post (hX : ExitUp_Statement) {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    {args : List Value} {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} {f : AbiFrame} {nci : Nat}
    {o o' : Array String} {m'' : Mem} {c' : Config} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls) (hret : wrRet 0x8001c7d8#64 w.sp 0 f m'' o' c')
    (hq : CloseQ p c w ins args ph F ls nci o m'' o') :
    ∃ m' out mo ι rt, wrRet 0x8001c7d8#64 w.sp 0 f m' (pushes o out) c' ∧
      CallOut p w c.σ.mem ins args m' out (w.after mo ι rt) ∧ CallInv p (w.after mo ι rt) := by
  obtain ⟨out, buf, H, FL', B', rfl, hcl⟩ := hq
  obtain ⟨hco, hinv⟩ := call_close hX cx.rel hI hcl
  exact ⟨m'', out, _, _, _, hret, hco, hinv⟩

/-- **`luaD_precall`'s numbers** at `OP_CALL print`'s `jal`. -/
theorem call_pcNum {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls) :
    PcNum w.sp w.L (w.slot ins.a) (ins.c - 1) (w.slot ins.a + 16 * ins.b) w.rt.stackLast w.ci 0x8001c7d8#64 := by
  have hr := cx.rel.core.ranges
  obtain ⟨hsp, hbase, -, hfits, hL1, hL2, hci1, hci2, -, -, hsl, hf0⟩ := headNums cx hI
  have hroom := cx.room; have hcl := cx.c_lt; have hal := hr.base_al; have hLal := hr.L_al
  have hcial := hr.ci_al
  simp only [RelPtrs.slot, stackValueSize] at hroom ⊢
  exact ⟨by omega, by omega, by omega, by decide, by omega, hLal, by omega, by omega, by omega, by omega,
    by omega, by omega, hcial, by omega, by omega, by omega⟩

/-- **What `luaD_precall` reads** at `OP_CALL print`'s `jal`: `L->top` the
arm stored, the rest from the complement and `R[A]` (`print`). -/
theorem call_pcCells {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    {ph : StdoutPh} {F FL : Nat → Prop} {ls : LitPtrs} (cx : CallCx p c s w ins args)
    (hI : CallInvAt p w ph F FL ls) :
    PcCells (callMem c.σ.mem w s.pc ins) w.L (w.slot ins.a) (w.slot ins.a + 16 * ins.b) w.rt.stackLast w.ci := by
  have hc := cx.rel.core
  have hr := hc.ranges
  have hlua := hc.comp.runtime.lua
  obtain ⟨hsp, hbase, hsv, hfits, hL1, hL2, hci1, hci2, hg1, hg2, hsl, hf0⟩ := headNums cx hI
  have hslot : w.slot ins.a + 16 * ins.b ≤ w.base + 16 * p.maxstacksize := by
    have := cx.ab; simp only [RelPtrs.slot, stackValueSize]; omega
  have hroom := cx.room
  have hLci := hr.L_sep_ci; have hcis := hr.ci_sep; have hLs := hr.L_sep
  simp only [ciSize, stateSize, stackValueSize] at hLci hcis hLs
  have kC := keep_mo (M := callMem c.σ.mem w s.pc ins) cx hI fun a h1 h2 _ => callMem_keep h1 h2
  -- `R[A]` is `print`
  obtain ⟨_, hget⟩ := mapM_range'_get cx.regs
  have hv0 := hc.stack ins.a (.builtin .print) (by have := cx.ab; have := cx.b_ne; omega)
    (by simpa using hget 0 (.builtin .print) rfl)
  have hsa : w.slot ins.a + 16 ≤ w.slot ins.a + 16 * ins.b := by have := cx.b_ne; omega
  have kS : ∀ j, j < 16 → bytesT1 (callMem c.σ.mem w s.pc ins) (w.slot ins.a + j) =
      bytesT1 c.σ.mem (w.slot ins.a + j) := fun j hj =>
    callMem_keep (by simp only [RelPtrs.slot, stackValueSize] at hslot hsa ⊢; omega)
      (by simp only [RelPtrs.slot, stackValueSize] at hslot hsa ⊢; omega)
  generalize ht : slotTag c.σ.mem (w.slot ins.a) = t at hv0
  generalize hx : slotVal c.σ.mem (w.slot ins.a) = x at hv0
  cases hv0 with
  | print hxv =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [callMem, stateTopOff, ciSavedpcOff]
      rw [fw8_wm8 (by omega), fw8_same rfl]
    · rw [bytesT8_congrT fun j _ => kC _ (by omega) (by omega) (by omega) (by omega)]
      exact bytesT8_of_rd64 hlua.stack_last
    · rw [bytesT8_congrT fun j _ => kC _ (by omega) (by omega) (by omega) (by omega)]
      exact bytesT8_of_rd64 hlua.lci
    · rw [bytesT8_congrT fun j hj => kS j (by omega)]
      simp only [slotVal, tvalueValOff, Nat.add_zero] at hx
      rw [hx, hxv]; rfl
    · rw [kS 8 (by decide)]
      simp only [slotTag, tvalueTagOff] at ht
      rw [ht]; rfl
    · rw [bytesT4_congrT fun j _ => kC _ (by omega) (by omega) (by omega) (by omega)]
      exact bytesT4_of_rd32 hlua.hookmask

/-- **`OP_CALL print`'s `luaD_precall` summary from the open parts** of
`CALL` (`CallOpen`), on the states with room on the Lua stack: `next_ci`
reusing `ci->next` (`precall_reuse`, `join_reuse`) or extending
(`precall_ext`, `ExtendCI_Statement`, `join_ext`), the C function and
`luaD_poscall` at the join once (`join_pcc`, `join_pcpos`), the close
(`close_post`). -/
theorem printCall_room (O : CallOpen) :
    PrintCallOn CallInv fun _ w ins => w.slot ins.a + 16 * ins.b + 320 < w.rt.stackLast := by
  intro p c s w ins args f o hS hR hinv hf hop hb hcc hregs hbud hroom
  obtain ⟨ph, F, FL, ls, hI⟩ := hinv
  have hB := call_bounds hS hf hop hb hcc
  have cx : CallCx p c s w ins args :=
    ⟨hR, hb, hcc, by simp only [Word.a, Word.field]; exact Nat.mod_lt _ (by decide), by simp only [Word.b, Word.field]; exact Nat.mod_lt _ (by decide),
      by simp only [Word.c, Word.field]; exact Nat.mod_lt _ (by decide), hB.ab, hB.ac, hregs, hroom⟩
  have hx := call_pcNum cx hI
  have hm := call_pcCells cx hI
  have hc := hR.core
  have hlua := hc.comp.runtime.lua
  obtain ⟨hsp, hbase, hsv, hfits, hL1, hL2, hci1, hci2, hg1, hg2, hsl, hf0⟩ := headNums cx hI
  have hr := hc.ranges
  have hLci := hr.L_sep_ci; have hcis := hr.ci_sep; have hLs := hr.L_sep
  simp only [ciSize, stateSize, stackValueSize] at hLci hcis hLs
  have kC := keep_mo (M := callMem c.σ.mem w s.pc ins) cx hI fun a h1 h2 _ => callMem_keep h1 h2
  have hnw : ∀ n, rd64 w.mo (w.ci + ciNextOff) = some n →
      bytesT8 (callMem c.σ.mem w s.pc ins) (w.ci + 24) = BitVec.ofNat 64 n := fun n hn => by
    rw [bytesT8_congrT fun j _ => kC _ (by omega) (by omega) (by omega) (by omega)]
    exact bytesT8_of_rd64 hn
  intro c0 h0
  rcases hlua.next with hn0 | ⟨nci, hnext, hn⟩
  · -- `ci->next` NULL: `luaE_extendCI`
    have kE := keep_mo (M := callExtMem c w s.pc ins f) cx hI fun a h1 h2 h3 =>
      ext_keep (c := c) (pc := s.pc) (ins := ins) (f := f) h1 h2 h3 (by omega)
    have hPS := printSt_head cx hI kE
    have ogL := hI.objs.g_L; have ogci := hI.objs.g_ci; have ogst := hI.objs.g_stack
    simp only [Apart, gEnd, gStrcacheOff, strcacheN, strcacheM, stateSize, ciSize] at ogL ogci ogst
    have SF := hI.stat.self
    have hgw : bytesT8 (callExtMem c w s.pc ins f) (w.L + stateGOff) = BitVec.ofNat 64 w.rt.g := by
      rw [bytesT8_congrT fun j _ => kE _ (by simp only [stateGOff]; omega) (by simp only [stateGOff]; omega)
        (by simp only [stateGOff]; omega) (by simp only [stateGOff]; omega)]
      exact bytesT8_of_rd64 hlua.g
    have hfra : bytesT8 (callExtMem c w s.pc ins f) w.rt.g = BitVec.ofNat 64 symLAlloc := by
      have hg1 := (hI.g_in w.rt.g (Nat.le_refl _) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).hi
      have hHE : heapEnd = 0x87800000 := rfl
      rw [bytesT8_congrT fun j _ => kE _ (by omega) (by omega) (by omega) (by omega)]
      exact bT8_of_fill (bytesT8_of_rd64 SF.lua.frealloc)
    have hE := O.extendCI w.sp w.L w.ci w.rt.g f (callExtMem c w s.pc ins f) o w.rt.hix hPS.heap
      (by have h1 := hI.room (.inr hn0); simp only [firstRoom, extRoom, RtPtrs.hix] at h1 ⊢; omega)
      (by rw [bytesT8_congrT fun j _ => kE _ (by simp only [stateCiOff]; omega) (by simp only [stateCiOff]; omega)
            (by simp only [stateCiOff]; omega) (by simp only [stateCiOff]; omega)]
          exact bytesT8_of_rd64 hlua.lci)
      (by rw [bytesT8_congrT fun j _ => kE _ (by simp only [ciNextOff]; omega) (by simp only [ciNextOff]; omega)
            (by simp only [ciNextOff]; omega) (by simp only [ciNextOff]; omega)]
          exact bytesT8_of_rd64 hn0)
      (by rw [bytesT4_congrT fun j _ => kE _ (by simp only [stateHookmaskOff]; omega)
            (by simp only [stateHookmaskOff]; omega) (by simp only [stateHookmaskOff]; omega)
            (by simp only [stateHookmaskOff]; omega)]
          exact bytesT4_of_rd32 hlua.hookmask)
      hgw hfra hPS.cells.impure
      { L_lo := by have := hL1; have : heapStart = 0x8006ecd0 := rfl; omega
        L_hi := by have := hL2; have : heapEnd = 0x87800000 := rfl; simp only [stateSize]; omega
        L_al := hr.L_al
        ci_lo := by have := hci1; have : heapStart = 0x8006ecd0 := rfl; omega
        ci_hi := by have := hci2; have : heapEnd = 0x87800000 := rfl; simp only [ciSize]; omega
        ci_al := hr.ci_al
        g_lo := by have := hg1; have : heapStart = 0x8006ecd0 := rfl; omega
        g_hi := by have := hg2; have : heapEnd = 0x87800000 := rfl; omega
        g_al := hI.g_al
        L_g := by simp only [stateSize, gGCdebtOff]; omega
        L_ci := hr.L_sep_ci
        live := fun a ha => by
          rcases ha with ha | ha | ha
          · exact (hI.L_in a ha.1 ha.2).inuse
          · exact (hI.ci_in a ha.1 ha.2).inuse
          · exact (hI.g_in a (by simp only [Rng, gGCdebtOff] at ha; omega)
              (by simp only [Rng, gGCdebtOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at ha ⊢; omega)).inuse }
      (by have : heapEnd = 0x87800000 := rfl; omega) (by omega) (by omega)
    obtain ⟨c', st, nci, m'', o', hret, hq⟩ :=
      precall_ext (Q := fun nci => JoinQ p c w ins args ph F FL ls f nci o)
        (Q' := fun nci => CloseQ p c w ins args ph F ls nci o) hx hm (hnw 0 hn0) hE
        (fun _ _ ⟨_, hX⟩ => join_pcc O.print cx hI (join_ext f cx hI hn0 hX) hbud o)
        (fun _ => join_pcpos O.poscall cx hI o) c0 h0
    exact ⟨c', st, close_post O.exitUp cx hI hret hq⟩
  · -- `ci->next` reused
    have hnlo := hn.lo; have hnhi := hn.hi
    simp only [symEnd, ciSize, RuntimeData.spEntry, cStackBudget] at hnlo hnhi
    obtain ⟨c', st, m'', o', hret, hq⟩ :=
      precall_reuse (Q' := CloseQ p c w ins args ph F ls nci o) hx hm ⟨by omega, hn.al, by omega⟩
        (hnw nci hnext) (join_pcc O.print cx hI (join_reuse f cx hI hnext hn (by omega)) hbud o)
        (join_pcpos O.poscall cx hI o) c0 h0
    exact ⟨c', st, close_post O.exitUp cx hI hret hq⟩

/-- **`PrintCall_Statement CallInv` from `CALL`'s open parts** (`CallOpen`):
`printCall_room` with room on the Lua stack, `CallOpen.grow` without. -/
theorem printCall_of (O : CallOpen) : PrintCall_Statement CallInv := by
  intro p c s w ins args f o hS hR hI hf hop hb hcc hregs hbud _
  by_cases h : w.slot ins.a + 16 * ins.b + 320 < w.rt.stackLast
  · exact printCall_room O f o hS hR hI hf hop hb hcc hregs hbud h
  · exact O.grow f o hS hR hI hf hop hb hcc hregs hbud h

end Lua.Vm.Sim.Kit

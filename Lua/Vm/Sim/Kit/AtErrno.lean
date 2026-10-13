import Lua.Vm.Sim.Kit.Errno
import Lua.Vm.Sim.Kit.AtArm

/-!
# The fetch head's close after an `errno` store (lane F1-F7)

A path through libm's `fmod` (`OP_MOD`/`OP_MODK`'s float paths) may store
`errno` (`Kit/Errno.lean`): its log carries the call node's `errno` window
(an `Ent.clob` at `_impure_data`, `gen_lua_at.py` `FOUTER`). Its fin lemma is
`AtFinE`: `AtFin` with the memory free at `errno` too; `AtFinE.close` is the
relation at the pointers after the store (`RelPtrs.errno`), and
`sim_arm_onE` the arm skeleton whose run may move the pointers that way.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.Kit Lua.Vm.DlHeap
open Vsa.Machine (MState Config Steps StepsN)

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- The fetch-head pins at the pointers after an `errno` store. -/
theorem Pins.errno {σ : MState} {pc : Nat} (h : Pins σ w pc) (m : Mem) : Pins σ (w.errno m) pc :=
  ⟨h.sp, h.gp, h.L, h.opMax, h.intTag, h.trap, h.ci, h.jt, h.base, h.pc⟩

/-- **The close with C-frame writes and an `errno` store**: `Core.bleachF`
with the final memory free at `errno` too, at the pointers after it. -/
theorem Core.errnoF (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    {regs' : Nat → Option Value} {out' : String} (hout : out' = s.out) (hpins : Pins c'.σ w pc')
    (hfr : ∀ x, ¬ Slots p w x → ¬ Scratch w x → ¬ CFrame w x → ¬ ErrnoW x → m[x]? = c.σ.mem[x]?)
    (hst : ∀ j v, j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v) :
    Core p c' ⟨pc', regs', out'⟩ (w.errno m) := by
  subst hout
  have hm := hseg.armMem
  subst hm
  have hr := hc.ranges
  have hsp := hr.sp_eq
  have e3 : RuntimeData.spEntry = 0x87fffe20 := rfl
  rw [e3] at hsp; simp only [execFrame] at hsp
  -- `luaV_execute`'s frame is no window part and not `errno`
  have hfS : ∀ x, w.sp ≤ x → x < w.sp + 176 → ¬ (16 ≤ x - w.sp ∧ x - w.sp < 72) →
      c'.σ.mem[x]? = c.σ.mem[x]? := fun x h1 h2 h3 => hfr x
    (fun hs => by have := hr.frame_sep; simp only [Slots] at hs; omega)
    (fun hs => by have := (hr.scratch_out _ hs).2; omega)
    (fun hs => by simp only [CFrame] at hs; omega)
    (notErrno_of_heap (by simp only [heapStart, symEnd]; omega))
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins.errno _, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hseg.armText, fun x hx => ?_, ?_, ?_, fun j v hj hv => (hst j v hj hv).errno hc.comp _,
    hc.comp.errno hr _, hr.after _ _ _,
    ?_⟩
  · have hx' : ¬ Win p w x := hx
    by_cases he : ErrnoW x
    · exact (errnoMo_in he).symm
    · rw [errnoMo_out he]
      simp only [bytesT1, hfr x (Win.of_slots hx') (fun h => hx' (.inr (.inr h)))
        (fun h => hx' (.inr (.inl ⟨by simp only [CFrame] at h; omega,
          by simp only [CFrame] at h; simp only [execFrame]; omega⟩))) he]
      exact hc.frame x hx'
  · show bytesT8 c'.σ.mem w.sp = BitVec.ofNat 64 w.k
    exact (bytesT8_congr fun i hi => hfS _ (by omega) (by omega) (by omega)).trans hc.kptr
  · show bytesT8 c'.σ.mem (w.sp + 8) = BitVec.ofNat 64 w.rt.cl
    exact (bytesT8_congr fun i hi => hfS _ (by omega) (by omega) (by omega)).trans hc.clptr
  · have h := hc.saved.congr fun x h1 h2 => hfS x (by omega) (by simp only [execFrame] at h2; omega) (by omega)
    exact ⟨h.ra, h.s0, h.s⟩

end

namespace At

/-- **At the fetch head, after a path that may store `errno`**: `AtFin` with
the memory free at `errno` too. -/
structure AtFinE (X : Cx) (M : List Ent) (W : List SlotW) (pc' : Nat) (c : Vsa.Machine.Config) : Prop where
  seg : SegSt Arms.headPc [] (ArmPay (Log.den X M) X.c.σ.sailOutput) c
  pins : Pins c.σ X.w pc'
  frame : ∀ x, ¬ Slots X.p X.w x → ¬ Scratch X.w x → ¬ CFrame X.w x → ¬ ErrnoW x →
    (Log.den X M)[x]? = X.c.σ.mem[x]?
  wtag : ∀ e ∈ W, slotTag (Log.den X M) (X.w.slot (e.j X)) = stData 1 (e.t.den X)
  wval : ∀ e ∈ W, slotVal (Log.den X M) (X.w.slot (e.j X)) = e.v.den X
  keep : ∀ x, Slots X.p X.w x → (∀ e ∈ W, x < X.w.slot (e.j X) ∨ X.w.slot (e.j X) + 16 ≤ x) →
    (Log.den X M)[x]? = X.c.σ.mem[x]?
  bound : ∀ e ∈ W, e.j X < X.p.maxstacksize

theorem AtFinE.pc_eq {X : Cx} {M : List Ent} {W : List SlotW} {pc pc' : Nat} {c : Vsa.Machine.Config}
    (h : AtFinE X M W pc c) (e : pc = pc') : AtFinE X M W pc' c := e ▸ h

/-- **The close after an `errno` store**: `AtFin.close` at the pointers after it. -/
theorem AtFinE.close {X : Cx} (hX : X.Ok) {M : List Ent} {W : List SlotW} {pc' : Nat} {c : Vsa.Machine.Config}
    (hF : AtFinE X M W pc' c) {regs' : Nat → Option Value}
    (hold : ∀ j, (∀ e ∈ W, j ≠ e.j X) → regs' j = X.s.regs j)
    (hnew : ∀ e ∈ W, ∀ v, regs' (e.j X) = some v →
      ValRepr X.w.mo X.w.ι (stData 1 (e.t.den X)) (e.v.den X) v) :
    VmRelAt X.p c ⟨pc', regs', X.s.out⟩ (X.w.errno (Log.den X M)) := by
  have hc := hX.core
  refine ⟨hc.errnoF hF.seg rfl hF.pins hF.frame ?_, hF.seg.pcAt⟩
  refine hc.stack_of (fun j => ∃ e ∈ W, j = e.j X) (fun j hj => hold j fun e he h => hj ⟨e, he, h⟩)
    (fun x hx hW => hF.keep x hx fun e he => ?_) ?_
  · have := hW (e.j X) ⟨e, he, rfl⟩
    simp only [RelPtrs.slot, stackValueSize] at this ⊢; omega
  · rintro j v ⟨e, he, rfl⟩ _ hv
    rw [hF.wtag e he, hF.wval e he]
    exact hnew e he v hv

/-- The register slots lie above `errno` (the Lua stack is in the heap's
chunks in use, `CallInvAt.stack_in`). -/
theorem Cx.Ok.errno_lt_base {X : Cx} (hX : X.Ok) : 0x8005d1bc ≤ X.w.base := by
  obtain ⟨ph, F, FL, ls, hI⟩ := hX.core.comp.call
  have hfit := hI.fits
  have := (hI.stack_in X.w.func (Nat.le_refl _) (by simp only [stackValueSize] at hfit; omega)).lo
  simp only [RelPtrs.base, heapStart, symEnd, stackValueSize] at this ⊢; omega

set_option hygiene false in
/-- **`at_finE`**: an `AtFinE` lemma's proof (`at_fin`'s, the `errno` window
apart from the slots by `errno_lt_base`). -/
macro "at_finE" : tactic => `(tactic| (
  have hEB := Cx.Ok.errno_lt_base hX
  at_facts hX
  have hseg := Vsa.Sim.SegSt.repin (L' := []) h trivial
  at_unfold at h
  refine ⟨hseg, at_fin_pins, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try at_unfold
  · intro x h1 h2 h3 h4
    simp only [Slots, Scratch, CFrame, ErrnoW, RelPtrs.slot, ciSavedpcOff, stateTopOff, RuntimeData.spEntry,
      cStackBudget, execFrame, stackValueSize, symImpureData, reentErrnoOff, not_or, not_and, Nat.not_lt] at h1 h2 h3 h4
    try simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out, getElem?_memPatch_out]
  at_fin_slots
  · at_fin_keep
  at_fin_bound))

end At

/-- **The arm skeleton on a path family whose run may store `errno`**:
`sim_arm_on` with the relation at any pointers after the run. -/
theorem sim_arm_onE {o : OpCode} {Q : Proto → State → Word → Prop} (ho : o.toNat < Arms.jtEntries)
    (body : ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs} {ins : Word},
      ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      Q p s ins → ∃ c' w', Steps c c' ∧ VmRelAt p c' s' w') : SimArmOn o Q := by
  intro p hS c s s' hR ins hf hop hstep hQ
  obtain ⟨w, hR⟩ := hR
  have hnum := opNum_of_op? hop
  obtain ⟨c1, hs1, hlt1, hA⟩ := dispatch hR hf (by rw [hnum]; exact ho)
  obtain ⟨c', w', hs, hR'⟩ := body hS hA hf hop hstep hQ
  exact sim_of_run (w := w') ⟨c', hs1.trans hs, Nat.lt_of_lt_of_le hlt1 hs.steps_le, hR'⟩

end Lua.Vm.Sim

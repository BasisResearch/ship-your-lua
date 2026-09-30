import Lua.Vm.Sim.Kit.Run
import Lua.Bytecode.Exec

/-!
# The direct kit's proved library (round-3 bake-off, contender KIT)

* **The arm skeleton** (`sim_arm`): `SimArm o` from a body that runs the arm
  from `ArmAt` (the dispatch is `dispatch`, once) to the fetch head. The body
  starts from `ArmAt.seg`: the fetch-head registers as the pin list the
  generated segments carry (`armPins`).
* **M1, forward kernel evaluation** (`Step.fwd`): a `Step` is the value of
  the stepper `kstep` (`kstep_iff`), so an arm computes its successor state by
  `simp` over the kernel term, with no per-combinator inversion.
* **M3, one close on the final memory** (`Core.bleach`): the final memory
  agrees with the entry memory outside the register slots and `Scratch`, and
  every defined register of the successor is represented there. The two
  shapes an arm meets are `Core.bleach_upd` (one register written: its slot
  stored, the rest of the window and `Scratch` free) and `Core.bleach_same`.
* **Pins at the head** (`kit_pins`): `Pins` looked up by name in the final
  segment state.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-! ## The arm skeleton -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}

/-- **The arm's entry as a segment state.** -/
theorem ArmAt.seg (hA : ArmAt p c s w ins) {pc : BitVec 64} (hpc : armTarget ins.opNum = pc) :
    SegSt pc (armPins w s.pc ins) (ArmPay c.σ.mem c.σ.sailOutput) c :=
  have hc := hA.core
  ⟨hc.good, hpc ▸ hA.pcAt, ⟨hc.pins.sp, hc.pins.gp, hc.pins.L, hc.pins.opMax, hc.pins.intTag,
    hA.s3, hA.s4, hc.pins.trap, hc.pins.ci, hc.pins.jt, hc.pins.base, hc.pins.pc, trivial⟩,
    hc.minstret, hc.tick, ⟨hc.text, rfl, rfl, hc.ok⟩⟩

end

/-- **The arm skeleton**: `SimArm o` from a run of the arm, from `ArmAt` to
the fetch head in the relation with the successor (same pointers `w`). -/
theorem sim_arm {o : OpCode} (ho : o.toNat < Arms.jtEntries)
    (body : ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs} {ins : Word},
      ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      ∃ c', Steps c c' ∧ VmRelAt p c' s' w) : SimArm o := by
  intro p hS c s s' hR ins hf hop hstep
  obtain ⟨w, hR⟩ := hR
  have hnum := opNum_of_op? hop
  obtain ⟨c1, hs1, hlt1, hA⟩ := dispatch hR hf (by rw [hnum]; exact ho)
  obtain ⟨c', hs, hR'⟩ := body hS hA hf hop hstep
  exact sim_of_run ⟨c', hs1.trans hs, Nat.lt_of_lt_of_le hlt1 hs.steps_le, hR'⟩

/-! ## M1: the successor by forward evaluation -/

/-- **A step is the stepper's value** (`kstep_iff`). -/
theorem Step.fwd {H : Host} {p : Proto} {s s' s₀ : State} (h : Step H p s s')
    (e : kstep (printLine H) (kernelAt p) s = some s₀) : s' = s₀ :=
  Option.some.inj (((kstep_iff _ _).1 h).symm.trans e)

/-- **No step** where the stepper is stuck (an error exit: `n % 0`, …). -/
theorem Step.stuck {H : Host} {p : Proto} {s s' : State} (h : Step H p s s')
    (e : kstep (printLine H) (kernelAt p) s = none) : False := by
  rw [(kstep_iff _ _).1 h] at e; cases e

/-- The operands of a two-operand kernel, compared with a pattern. -/
theorem pair_eq {α : Type} {a b c d : α} (h : [a, b] = [c, d]) : a = c ∧ b = d := by
  simp only [List.cons.injEq, and_true] at h; exact h

/-! ## M3: the close on the final memory -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- **The close.** The final segment state `c'` at the head with memory `m`,
the console unchanged: if `m` agrees with the entry memory outside the
register slots and `Scratch`, and every defined register of `regs'` is
represented in `m`, the relation holds of `⟨pc', regs', s.out⟩`. -/
theorem Core.bleach (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    {regs' : Nat → Option Value} (hpins : Pins c'.σ w pc')
    (hfr : ∀ x, ¬ Slots p w x → ¬ Scratch w x → m[x]? = c.σ.mem[x]?)
    (hst : ∀ j v, j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v) :
    Core p c' ⟨pc', regs', s.out⟩ w := by
  have hm := hseg.armMem
  subst hm
  have hr := hc.ranges
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hseg.armText, fun x hx => ?_, ?_, hst, hc.comp, hr⟩
  · simp only [bytesT1, hfr x (Win.of_slots hx) (fun h => hx (.inr (.inr h)))]
    exact hc.frame x hx
  · refine (bytesT8_congr fun i _ => hfr _ (fun hs => ?_) (fun hs => ?_)).trans hc.kptr
    · have := hr.frame_sep; simp only [Slots] at hs; omega
    · have := (hr.scratch_out _ hs).2; omega

/-- The registers of `upd s.regs a v`, from the slot of `a` storing `v` and the
other slots unchanged. -/
theorem Core.stack_upd (hc : Core p c s w) {m : Mem} {a : Nat} {v : Value}
    (hfr : ∀ x, (x < w.slot a ∨ w.slot a + 9 ≤ x) → Slots p w x → m[x]? = c.σ.mem[x]?)
    (hv : ValRepr w.mo w.ι (slotTag m (w.slot a)) (slotVal m (w.slot a)) v) :
    ∀ j v', j < p.maxstacksize → upd s.regs a v j = some v' →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v' := by
  intro j v' hj hv'
  simp only [upd] at hv'
  by_cases hja : j = a
  · subst hja; simp only [if_true, Option.some.injEq] at hv'; subst hv'; exact hv
  · simp only [hja, if_false] at hv'
    obtain ⟨ht, hv2⟩ := slot_congr (m := m) (m' := c.σ.mem) (a := w.slot j) fun i hi =>
      hfr _ (by simp only [RelPtrs.slot, stackValueSize]; omega)
        (by simp only [Slots, RelPtrs.slot, stackValueSize]; omega)
    rw [ht, hv2]
    exact hc.stack j v' hj hv'

/-- The registers unchanged, from the slots unchanged. -/
theorem Core.stack_same (hc : Core p c s w) {m : Mem}
    (hfr : ∀ x, Slots p w x → m[x]? = c.σ.mem[x]?) :
    ∀ j v, j < p.maxstacksize → s.regs j = some v →
      ValRepr w.mo w.ι (slotTag m (w.slot j)) (slotVal m (w.slot j)) v := by
  intro j v hj hv
  obtain ⟨ht, hv2⟩ := slot_congr (m := m) (m' := c.σ.mem) (a := w.slot j) fun i hi =>
    hfr _ (by simp only [Slots, RelPtrs.slot, stackValueSize]; omega)
  rw [ht, hv2]
  exact hc.stack j v hj hv

/-- **Close, one register written**: the slot of `a` stores a representation
of `v`; outside it only `Scratch` changed. -/
theorem Core.bleach_upd (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' a : Nat} {v : Value}
    (hpins : Pins c'.σ w pc') (ha : a < p.maxstacksize)
    (hfr : ∀ x, (x < w.slot a ∨ w.slot a + 9 ≤ x) → ¬ Scratch w x → m[x]? = c.σ.mem[x]?)
    (hv : ValRepr w.mo w.ι (slotTag m (w.slot a)) (slotVal m (w.slot a)) v) :
    Core p c' ⟨pc', upd s.regs a v, s.out⟩ w := by
  have hr := hc.ranges
  refine hc.bleach hseg hpins (fun x hx hs => hfr x ?_ hs) (hc.stack_upd (fun x hx hs => hfr x hx
    fun h => (hr.scratch_out x h).1 hs) hv)
  simp only [Slots, RelPtrs.slot, stackValueSize] at hx ⊢
  omega

/-- **Close, one register stored**: after `Scratch` stores (`m₀`) the arm's
tag and payload stores to the slot of `a` (`SlotStore`) represent `v`. -/
theorem Core.bleach_store (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m m₀ : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' a : Nat} {v : Value}
    {tag : BitVec 8} {val : BitVec 64} (hpins : Pins c'.σ w pc') (ha : a < p.maxstacksize)
    (h₀ : ∀ x, ¬ Scratch w x → m₀[x]? = c.σ.mem[x]?) (hst : SlotStore m₀ m (w.slot a) tag val)
    (hv : ValRepr w.mo w.ι tag val v) :
    Core p c' ⟨pc', upd s.regs a v, s.out⟩ w :=
  hc.bleach_upd hseg hpins ha (fun x hx hs => (hst.frame x hx).trans (h₀ x hs)) (by
    simp only [slotTag, slotVal, tvalueTagOff, tvalueValOff, Nat.add_zero, hst.val, hst.tag]
    exact hv)

/-- **Close, no register written**: only `Scratch` changed. -/
theorem Core.bleach_same (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    (hpins : Pins c'.σ w pc') (hfr : ∀ x, ¬ Scratch w x → m[x]? = c.σ.mem[x]?) :
    Core p c' ⟨pc', s.regs, s.out⟩ w :=
  hc.bleach hseg hpins (fun x _ hs => hfr x hs)
    (hc.stack_same fun x hx => hfr x fun h => (hc.ranges.scratch_out x h).1 hx)

end

/-- `Pins` at the head, each register looked up by name in the final segment
state's pin list `h`; the pc (s11) by `pin_eq` and `slot_arith`. -/
macro "kit_pins " h:ident : tactic => `(tactic|
  exact ⟨by pin_of $h, by pin_of $h, by pin_of $h, by pin_of $h, by pin_of $h, by pin_of $h,
    by pin_of $h, by pin_of $h, by pin_of $h,
    pin_eq (by pin_of $h) (by apply BitVec.eq_of_toNat_eq; slot_arith)⟩)

/-! ## The arm tactics

Unhygienic on purpose: they name the facts an arm proof then uses (`hc`,
`hk`, `h0`, `acc`, …), for a body `fun {p} hS {c s s' w ins} hA hf hop hstep`
of `sim_arm`. -/

set_option hygiene false in
/-- **`kit_setup pc`**: the relation's facts (`hc`, the address ranges for
`slot_arith`), the kernel evaluated forward at the instruction (`hk :
kstep … s = some s'`, M1), the register bound `htop`, and the arm's entry as
a segment state `h0` at `pc` with the empty run `acc`. -/
macro "kit_setup " pc:num : tactic => `(tactic| (
  have hc := hA.core
  have hr := hc.ranges
  have htop := supported_regTop hS hf
  simp [regTop, kernel, hop, opKernel, arithRR, arithRK, opArith, docondjump, Kernel.regTop,
    Opnd.ports, Option.map] at htop
  have hk := (kstep_iff _ _).1 hstep
  simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, arithRR, arithRK, opArith, docondjump,
    Opnd.ports] at hk
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hr.base_lo; have := hr.base_hi; have := hr.base_al; have := hr.ci_lo
  have := hr.ci_hi; have := hr.code_hi; have := hr.code_lo; have := fetch_lt hf
  have := ins.isLt
  simp only [stackValueSize, ciSize] at *
  have h0 := hA.seg (pc := BitVec.ofNat 64 $pc) (by rw [opNum_of_op? hop]; decide)
  have acc := Steps.refl c))

set_option hygiene false in
/-- **`kit_reg hj v hv j`**: register `j` read by the kernel: its value `v`
(`hj`, the undefined case refuted by `hk`) and its representation `hv`. -/
macro "kit_reg " hj:ident v:ident hv:ident j:term : tactic => `(tactic| (
  rcases $hj:ident : s.regs $j with _ | $v:ident <;> simp [$hj:ident] at hk
  have $hv:ident := hc.stack _ _ (by simp only [Word.a, Word.b, Word.c, Word.field] at *; omega) $hj))

set_option hygiene false in
/-- **`kit_bound hj j`**: an operand register below `maxstacksize`, also in
the shift form `slot_arith` reads (`hj'`). -/
macro "kit_bound " hj:ident j:term : tactic => `(tactic| (
  have $hj:ident : $j < p.maxstacksize := by omega
  have := $hj:ident
  simp only [Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow] at this))

set_option hygiene false in
/-- **`kit_next`**: the successor from the evaluated kernel (`hk`), then the
run to the fetch head. -/
macro "kit_next" : tactic => `(tactic| (
  simp [Opnd.fill, δ, BinOp.int, VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  kit_run h0 acc))

set_option hygiene false in
/-- **`kit_same`**: the close when no register and no memory changed. -/
macro "kit_same" : tactic => `(tactic|
  exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (fun _ _ => rfl), h0.pcAt⟩)

/-! ## Memory frames of the arms' stores -/

theorem getElem?_wm8_out {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x < a ∨ a + 8 ≤ x) :
    (writeMap8 m a d)[x]? = m[x]? := getElem?_writeMap8_out m a d x h

theorem getElem?_ins_out {m : Mem} {a x : Nat} {b : BitVec 8} (h : x ≠ a) :
    (m.insert a b)[x]? = m[x]? := getElem?_insert_out h

end Lua.Vm.Sim

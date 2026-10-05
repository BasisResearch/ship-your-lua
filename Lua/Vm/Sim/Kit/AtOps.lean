import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.Sim.Kit.AtArm

/-!
# The arm side of the at-lemma route, once per kernel shape

An arm path on the location-list route is the kernel evaluated forward (M1),
its exit chosen by the operands' tags, and `at_go NS` (the generated
at-lemmas of `Lua/Vm/At/<Op>.lean`, namespace `NS`). This file states that
hand-off once per kernel shape, so an arm's path is a one-line instance:

* `opArith` (`op_arith`, `op_arithK`): `at_fall NS pc` and `at_fallK NS pc`,
  the fall-through to `MMBIN`/`MMBINK` when the operands are not both
  integers (`¬ BothInt`, `¬ BothIntK`);
* the division arms (`DivPath`, `sim_div`): `at_div_m1 (setup) NS eq` (the
  `n = -1` exit, `eq : op m (-1) = some _`) and `at_div_gen (setup) NS eq`
  (the general case, the kernel restated by `eq _ _ hz` in `lvm.c`'s order:
  `imodC_eq`, `idivC_eq`); the stuck `n = 0` case is `kit_div_zero`;
* `setR` on one register (`OP_UNM`): `RegInt`/`RegStr`, `sim_unary`, and
  the paths `at_unary_int NS pc` and `at_unary_stuck pc`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-! ## `opArith`: the fall-through -/

set_option hygiene false in
/-- **`at_fall NS pc`**: an `op_arith` arm at `pc` with `¬ BothInt` (`hI`):
the kernel's exit to `MMBIN` (`pc + 1`), the machine's by the at-lemmas. -/
macro "at_fall " ns:ident pc:num : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep hI
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  kit_reg hb vb hvb ins.b; kit_reg hcc vc hvc ins.c
  have hfb := hvb.ne_float; have hfc := hvc.ne_float
  simp [Opnd.fill] at hk; split at hk
  · rename_i heq
    obtain ⟨e1, e2⟩ := pair_eq heq; subst e1 e2
    exact absurd ⟨hvb.tag_of_int.1, hvc.tag_of_int.1⟩ hI
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · have hC : ¬ slotTag c.σ.mem (w.slot ins.c) = BitVec.ofNat 8 vNumInt := fun hC => hI ⟨hB, hC⟩
    at_go $ns
  · at_go $ns))

set_option hygiene false in
/-- **`at_fallK NS pc`**: `at_fall` with `K[C]` (`¬ BothIntK`). -/
macro "at_fallK " ns:ident pc:num : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep hI
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hb vb hvb ins.b
  have hfb := hvb.ne_float; have hfk := hvk.ne_float
  simp [Opnd.fill] at hk; split at hk
  · rename_i heq
    obtain ⟨e1, e2⟩ := pair_eq heq; subst e1 e2
    exact absurd ⟨hvb.tag_of_int.1, hvk.tag_of_int.1⟩ hI
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · have hC : ¬ slotTag c.σ.mem (w.k + stackValueSize * ins.c) = BitVec.ofNat 8 vNumInt :=
      fun hC => hI ⟨hB, hC⟩
    at_go $ns
  · at_go $ns))

/-! ## The division arms -/

set_option hygiene false in
/-- **`at_div_m1 (st) NS eq`**: the `n = -1` path of a division arm: the
setup `st` (`kit_arith_ints pc`, `kitk_ints pc`), the kernel's value by `eq`,
the at-lemmas. -/
macro "at_div_m1 " "(" st:tacticSeq ")" ns:ident eq:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hm⟩
  simp only [dvR, dvK] at hm
  ($st)
  simp only [Opnd.fill, δ, BinOp.int, stackValueSize, hm, $eq:ident] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go $ns))

set_option hygiene false in
/-- **`at_div_gen (st) NS eq`**: a general path of a division arm (`DivGen`
and the path's sign facts `hq`): the setup `st`, the kernel restated by
`eq _ _ hz` (`imodC_eq`, `idivC_eq`), the at-lemmas through the helpers'
generated call rows. -/
macro "at_div_gen " "(" st:tacticSeq ")" ns:ident eq:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩
  simp only [dvR, dvK] at hy hq
  ($st)
  have hz := fun e => hy (Or.inl e)
  simp only [Opnd.fill, δ, BinOp.int, $eq:ident _ _ hz] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go $ns))

/-! ## `setR` on one register -/

/-- `R[B]` holds an integer. -/
def RegInt (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ i, s.regs ins.b = some (.int i)

/-- `R[B]` holds a string. -/
def RegStr (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ t, s.regs ins.b = some (.str t)

/-- **A one-register `setR` arm from its paths**: an integer, a string, and
the rest. -/
theorem sim_unary {o : OpCode} (ho : o.toNat < Arms.jtEntries) (hint : ArmBody o RegInt)
    (hstr : ArmBody o RegStr)
    (hstuck : ArmBody o fun p c s w ins => ¬ RegInt p c s w ins ∧ ¬ RegStr p c s w ins) :
    SimArm o :=
  sim_arm ho fun {p} hS {c s s' w ins} hA hf hop hstep => by
    by_cases hi : RegInt p c s w ins
    · exact hint hS hA hf hop hstep hi
    by_cases ht : RegStr p c s w ins
    · exact hstr hS hA hf hop hstep ht
    exact hstuck hS hA hf hop hstep ⟨hi, ht⟩

set_option hygiene false in
/-- **`at_unary_int NS pc`**: the integer path of a one-register `setR` arm
at `pc`: the kernel forward, the at-lemmas. -/
macro "at_unary_int " ns:ident pc:num : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨i, hi⟩
  kit_setup $pc
  simp [setR, Opnd.ports] at htop
  simp [setR, Opnd.ports, Opnd.fill, hi, δ, VState.apply, writeDefs, KEdge.kills] at hk
  kit_bound hAt ins.a; kit_bound hBt ins.b
  have hvb := hc.stack _ _ hBt hi
  have hB := hvb.tag_of_int.1
  obtain rfl := hvb.tag_of_int.2
  subst hk
  at_go $ns))

set_option hygiene false in
/-- **`at_unary_stuck pc`**: neither an integer nor a string: the kernel
(`δ` on one register) has no `Step`. -/
macro "at_unary_stuck " pc:num : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hi, ht⟩
  kit_setup $pc
  simp only [RegInt, RegStr, not_exists] at hi ht
  rcases hb : s.regs ins.b with _ | v
  · simp [setR, Opnd.ports, hb] at hk
  rcases v <;> simp_all [setR, Opnd.ports, Opnd.fill, δ]))

end Lua.Vm.Sim.At

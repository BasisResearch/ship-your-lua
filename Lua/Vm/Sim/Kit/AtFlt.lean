import Lua.Vm.Sim.Kit.FltVal

/-!
# The float paths of the arms on the location-list route (lane float-m0, M1)

One hand-off per kernel shape, as `Kit/AtOps.lean` does for the integer
paths; an arm's float path is then a one-line instance:

* `docondjump` on a float `R[A]` and an 8-bit immediate (`EQI`, `LTI`,
  `LEI`, `GTI`, `GEI`): `FltTest` (the test `t` of the kernel against `k`,
  `take` or `skip`), `at_fcond pc NS t e`;

The machine's answer is read off the generated call sites' specifications
(`f<k>_eq`, `@[at_fspec]`, under `SoftFloatSpec`) and `Kit/FltVal.lean`'s
lemmas, by the arm's guard closer (`at_hyp`'s float rule below).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `R[A]` holds a float, and the kernel's test `t ins x` of it equals `k`
(`take`: the jump) or not (`skip`). -/
def FltTest (t : Word → Float.Model → Bool) (take : Bool) (p : Proto) (_c : Config) (s : State)
    (_w : RelPtrs) (ins : Word) : Prop :=
  FltA p s ins ∧ ∀ x n, s.regs ins.a = some (.flt x n) → (t ins x = ins.k ↔ take = true)

/-- A float `R[A]` takes one exit of `FltTest`. -/
theorem FltTest.cases (t : Word → Float.Model → Bool) {p : Proto} {c : Config} {s : State} {w : RelPtrs}
    {ins : Word} (hT : FltA p s ins) : FltTest t true p c s w ins ∨ FltTest t false p c s w ins := by
  obtain ⟨x, n, hx⟩ := hT
  by_cases hk : t ins x = ins.k
  · exact .inl ⟨⟨x, n, hx⟩, fun x' n' hx' => by rw [hx] at hx'; cases hx'; simp [hk]⟩
  · exact .inr ⟨⟨x, n, hx⟩, fun x' n' hx' => by rw [hx] at hx'; cases hx'; simp [hk]⟩

/-- **An arm's float path from its two exits.** -/
theorem sim_fcond {o : OpCode} (ho : o.toNat < Arms.jtEntries) (t : Word → Float.Model → Bool)
    (take : ArmBody o (FltTest t true)) (skip : ArmBody o (FltTest t false)) : SimArmOn o FltA :=
  sim_arm_on ho fun {_} hS {_ _ _ _ _} hA hf hop hstep hT =>
    (FltTest.cases t hT).elim (take hS hA hf hop hstep) (skip hS hA hf hop hstep)

/-- `GETARG_B` is a byte. -/
theorem Word.b_lt (w : Word) : w.b < 256 := by
  simp only [Word.b, Word.field]; exact Nat.mod_lt _ (by decide)

theorem fbool_ne_not {a b : Bool} (h : ¬ b = a) : a = !b := by cases a <;> cases b <;> simp_all

theorem fnot_bne_self (b : Bool) : ((!b) != b) = true := by cases b <;> rfl

theorem bne_ite' (k c : Bool) :
    ((if k then 1#64 else 0#64) != (if c then 1#64 else 0#64)) = (k != c) := by
  cases k <;> cases c <;> decide

/-- `decide` on a closed goal only: a guard left open over the payloads (an
at-lemma of the other exit, whose test the path does not know) fails here
instead of evaluating the soft-float model on free variables. -/
elab "at_dec_closed" : tactic => do
  let t ← Lean.Elab.Tactic.getMainTarget
  if (← Lean.instantiateMVars t).hasFVar then throwError "at_dec_closed: open goal"
  Lean.Elab.Tactic.evalTactic (← `(tactic| decide))

set_option hygiene false in
/-- The float paths' guards: the operand's tag is the float tag (`hta`), the
answer of the soft-float call (the sites' `at_fspec` equations, the
comparisons' 0/1 answers, the model of the payload `hxm`, the immediate) is
the kernel's test, against `k` (`e`). -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| (
      simp (disch := assumption) only [Loc.den, Fld.den, Aff.den, Aff.sum, Atom.den, Nat.add_zero, Nat.one_mul, Nat.zero_add,
        Nat.sub_zero, at_fspec, Lua.Vm.Fn.Floatsidf.S, Lua.Vm.Fn.Adddf3.S, F64.add_eq_model, toModel_toBits, sb_fsi, slt_ledf2, slt1_ledf2, seqz_eqdf2, ge_gedf2, blez_gedf2,
        F64.lt_eq_model, F64.le_eq_model, F64.eq_eq_model, toModel_ofInt, toInt_imm, hxm, zext_bit,
        bne_ite', e, hta, hnj, Option.isSome_some, bne_self_eq_false, fnot_bne_self, zext_beq_lit _ 19 (by decide),
        zext_bne_lit _ 19 (by decide), zext_bne_lit _ vNumInt (by decide), zext_beq_lit _ vNumInt (by decide)]
      first | done | at_dec_closed))

set_option hygiene false in
/-- A stored float result (`setfltvalue`, or `chgfltvalue`'s payload under the
entry's float tag): its payload, read off the call sites' specifications
(`at_fspec`) and `F64`'s bridges, is the kernel's value's bits. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by first | decide | (simp only [stData_zext, Nat.add_zero]; exact hta) | (simp only [Loc.den, stData_zext, Nat.add_zero, hta]; done)) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Aff.den, Aff.sum, Atom.den, Nat.add_zero,
        Nat.one_mul, Nat.sub_zero, at_fspec, Lua.Vm.Fn.Floatsidf.S, Lua.Vm.Fn.Adddf3.S, sb_fsi, sbx_fsi,
        F64.ofInt_eq_model, F64.add_eq_model, toModel_ofInt, toModel_toBits, toInt_imm, ofI, Word.sbx, Word.offsetSBx,
        Word.sc, Word.offsetSC, Int.cast_ofNat_Int]
      first | done | (simp only [hxm]; done) | (simp only [hxm, hxm2]; done)))

set_option hygiene false in
/-- **`at_fcond pc NS e`**: `docondjump` on a float `R[A]` (`hT : FltTest t
take`) at `pc`: the kernel's test `t` (`δ` on the float and the immediate,
`dlem`), `e` the `k` bit as the test or its negation, the run by `at_go NS`. -/
macro "at_fcond " pc:num ns:ident dlem:term "," e:term : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  try simp [immB, Opnd.ports] at htop
  try simp only [immB, Opnd.ports] at hk
  kit_bound hAt ins.a
  kit_reg hba va hva ins.a
  obtain ⟨⟨x, n, hx⟩, hkk⟩ := hT
  rw [hx] at hba; cases hba
  have hkk := hkk x n hx
  have hbb := Word.b_lt ins
  have e : ins.k = _ := $e
  obtain ⟨hta, hxm, -⟩ := hva.flt_parts
  simp [Opnd.fill, Opnd.ports, immB, Word.sb, Word.offsetSC, $dlem:term, ofI_imm _ hbb, VState.apply, writeDefs,
    KEdge.kills, Value.isFalse, e] at hk
  subst hk
  at_go $ns))

set_option hygiene false in
/-- **`at_farith pc NS`**: `op_arithI`'s float case (`hT : FltB`): `R[B]` a
float and the immediate `sC`; the kernel's sum (`rawArith` on a float and an
integer, `numarith`), the run by `at_go NS`, the stored payload by the float
rule of `at_new_ext`. -/
macro "at_farith " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  try simp [immC, Opnd.ports] at htop
  try simp only [immC, Opnd.ports] at hk
  kit_bound hAt ins.a
  kit_bound hBt ins.b
  kit_reg hbr vb hvb ins.b
  obtain ⟨x, n, hx⟩ := hT
  rw [hx] at hbr; cases hbr
  have hbb := Word.c_lt ins
  have e := Word.c_lt ins
  have hnj := Word.b_lt ins
  obtain ⟨hta, hxm, -⟩ := hvb.flt_parts
  simp [Opnd.fill, immC, Word.sc, Word.offsetSC, ofI_imm _ hbb, fastArith, Value.toNum?, Lua.Num.rawArith,
    BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat, Value.ofNum, VState.apply, writeDefs,
    KEdge.kills] at hk
  subst hk
  at_go $ns))

end Lua.Vm.Sim.At

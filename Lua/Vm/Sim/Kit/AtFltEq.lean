import Lua.Vm.Sim.Kit.AtStr
import Lua.Vm.Sim.Kit.AtEqF
import Lua.Vm.At.EqF
import Lua.Vm.At.EqkF

/-!
# `OP_EQ` and `OP_EQK` with a float operand (lane F1-F4)

`Protect(cond = luaV_equalobj(L, s2v(ra), rb))` (`OP_EQ`) and `cond =
luaV_rawequalobj(s2v(ra), K[B])` (`OP_EQK`), then `docondjump`, with a float
among the two values: the generated at-lemmas `Lua/Vm/At/{EqF,EqkF}.lean`
(the `savestate` stores, the call node `eqf_at`, whose answer is
`Value.rawEq`'s, both exits of `docondjump`), one `at_go` per exit. The
kernel's `δ .eq` is `Value.rawEq` (`eqNum` on numbers: `luai_numeq`, or
`luaV_tointegerns(F2Ieq)` of the float against the integer), `floor` by
`floorSpec_proved`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `R[A]` and the other value (`R[B]`, or `K[B]` for `OP_EQK`: `get`), one
a float, the test `Value.rawEq` equal (`take`) or not (`skip`) to `k`. -/
def EqfTest (get : Proto → State → Word → Option Value) (take : Bool) (p : Proto) (_c : Config)
    (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  (FltReg s ins.a ∨ ∃ x n, get p s ins = some (.flt x n)) ∧
    ∀ va vb, s.regs ins.a = some va → get p s ins = some vb → (va.rawEq vb = ins.k ↔ take = true)

/-- A float among the two values takes one exit of `EqfTest`. -/
theorem EqfTest.cases (get : Proto → State → Word → Option Value) {p : Proto} {c : Config} {s : State}
    {w : RelPtrs} {ins : Word} (hT : FltReg s ins.a ∨ ∃ x n, get p s ins = some (.flt x n)) :
    EqfTest get true p c s w ins ∨ EqfTest get false p c s w ins := by
  by_cases hk : ∀ va vb, s.regs ins.a = some va → get p s ins = some vb → va.rawEq vb = ins.k
  · exact .inl ⟨hT, fun va vb ha hb => by simp [hk va vb ha hb]⟩
  · refine .inr ⟨hT, fun va vb ha hb => ⟨fun e => (hk fun va' vb' ha' hb' => ?_).elim, by simp⟩⟩
    rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'; exact e

/-- The two values, one a float: not both `NotFlt`. -/
theorem flt_pair {s : State} {j : Nat} {va vb : Value} {o : Option Value}
    (hT : FltReg s j ∨ ∃ x n, o = some (.flt x n)) (ha : s.regs j = some va) (hb : o = some vb) :
    ¬ (va.NotFlt ∧ vb.NotFlt) := fun ⟨n1, n2⟩ => by
  rcases hT with ⟨x, n, e⟩ | ⟨x, n, e⟩
  · rw [ha] at e; cases e; exact n1 x n rfl
  · rw [hb] at e; cases e; exact n2 x n rfl

set_option hygiene false in
/-- `docondjump`'s test against `k` on `luaV_equalobj`'s 0/1 answer. -/
local macro_rules
  | `(tactic| at_hyp) => `(tactic| (
      simp only [Loc.den, hsx, hsy, bne_ite_prop, decide_eq_true_eq, e, bne_self_eq_false, not_bne_self']
      done))

set_option hygiene false in
/-- The two exits' common part (after the operands' set-up: `va`, `vb`, their
facts `hba`, `h2`, `hsy`): the pair has a float (`hfab`), the test against
`k` (`e`), the kernel's step, the at-lemmas from the head (`at_go ns`). -/
macro "at_eqf_tail " h2:ident ns:ident e:term : tactic => `(tactic| (
  obtain ⟨hT0, hkk⟩ := hT
  have hfab := flt_pair hT0 hba $h2
  have hkk := hkk va vb hba $h2
  have e : ins.k = _ := $e
  have hsx : vOf ⟨p, c, s, w, ins⟩ .a = va := by simp [vOf, Fld.den, hba]
  have hsa := hba
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, e] at hk
  subst hk
  at_go $ns))

set_option hygiene false in
/-- **`at_eqf_path e`**: `OP_EQ` with a float operand (`hT`), one exit of
`docondjump` (`e`: the `k` bit as the test or its negation). -/
macro "at_eqf_path " e:term : tactic => `(tactic| (
  kit_setup 0x8001c690
  flt_views
  have htb : True := trivial
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  have hsy : vOf ⟨p, c, s, w, ins⟩ .b = vb := by simp [vOf, Fld.den, hbb]
  have hsb := hbb
  at_eqf_tail hbb Lua.Vm.At.EQ_F $e))

/-- `OP_EQ` with a float operand, the jump taken. -/
theorem eq_flt_take : ArmBody .EQ (EqfTest (fun _ s ins => s.regs ins.b) true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqf_path ((hkk.2 rfl).symm)

/-- `OP_EQ` with a float operand, the jump skipped. -/
theorem eq_flt_skip : ArmBody .EQ (EqfTest (fun _ s ins => s.regs ins.b) false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqf_path (bool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`OP_EQ` with a float operand** (`FloatArms.EQ`). -/
theorem sim_EQ_flt : SimArmOn .EQ FltAB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT =>
    ArmBody.byTest _ (fun hT => EqfTest.cases (fun _ s ins => s.regs ins.b) hT)
      (eq_flt_take) (eq_flt_skip) hS hA hf hop hstep hT

set_option hygiene false in
/-- **`at_eqkf_path e`**: `OP_EQK` with a float `R[A]` or `K[B]` (`hT`), one
exit of `docondjump`. -/
macro "at_eqkf_path " e:term : tactic => `(tactic| (
  kit_setup 0x8001c850
  flt_views
  have htb : True := trivial
  rcases hkv : kval p ins.b with _ | vb <;> simp [hkv] at hk htop
  kit_nj
  kit_bound hAt ins.a
  have hkb := kval_lt hkv
  kit_reg hba va hva ins.a
  have hsy : kvOf ⟨p, c, s, w, ins⟩ = vb := by simp [kvOf, hkv]
  have hky := hkv
  at_eqf_tail hkv Lua.Vm.At.EQK_F $e))

/-- `OP_EQK` with a float `R[A]` or `K[B]`, the jump taken. -/
theorem eqk_flt_take : ArmBody .EQK (EqfTest (fun p _ ins => kval p ins.b) true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqkf_path ((hkk.2 rfl).symm)

/-- `OP_EQK` with a float `R[A]` or `K[B]`, the jump skipped. -/
theorem eqk_flt_skip : ArmBody .EQK (EqfTest (fun p _ ins => kval p ins.b) false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_eqkf_path (bool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`OP_EQK` with a float `R[A]` or `K[B]`** (`FloatArms.EQK`). -/
theorem sim_EQK_flt : SimArmOn .EQK FltAKb :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT =>
    ArmBody.byTest _ (fun hT => EqfTest.cases (fun p _ ins => kval p ins.b) hT)
      (eqk_flt_take) (eqk_flt_skip) hS hA hf hop hstep hT

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.At
import Lua.Vm.Sim.Kit.DivBits
import Lua.Vm.Sim.Kit.Moddi3

/-!
# The arm side of the location-list route (B-SEGLOCAL)

An arm proof on this route is the kernel's case split (the kit's M1:
`kit_setup`, `kstep` evaluated forward) followed by `at_go NS`:

* the arm's entry as a row (`At.entry`'s form of `hA.seg`);
* `at_run NS`: the generated at-lemmas of the arm (`Lua/Vm/At/<Op>.lean`,
  namespace `NS`), chained by `At.run` from the current pc to the fetch head,
  each picked by its pc and by whether `at_hyp` closes its hypotheses (the
  slot bounds by `omega`, the guards and the helpers' preconditions about
  *locations* by `at_vals`, from the path's value facts in context; no memory
  is read here);
* `at_close NS`: the generated `fin` lemma of the final row (`AtFin`) and
  `AtFin.close`, the successor's registers by `at_hold`/`at_new`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.Kit

theorem stData_three_lit : stData 1 (0x3#64 : BitVec 64) = BitVec.ofNat 8 vNumInt := by decide
theorem stData_three_n : stData 1 (BitVec.ofNat 64 vNumInt) = BitVec.ofNat 8 vNumInt := by decide

theorem xor_true_of_ne {a b : Bool} (h : ¬ a = b) : (a ^^ b) = true := by
  cases a <;> cases b <;> simp_all

theorem beq_false_of_ne {x y : BitVec 64} (h : x ≠ y) : (x == y) = false := by simpa using h

theorem bne_true_of_ne {x y : BitVec 64} (h : x ≠ y) : (x != y) = true := by simpa using h

open Lean Elab Tactic Meta in
/-- **`at_vals`**: a guard or a precondition about locations, from the
path's value facts in context (one `simp` over them, then `decide`), as the
kit's `kit_bv` does but over location values, never over memory. -/
elab "at_vals" : tactic => withMainContext do
  let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for ldecl in (← getLCtx) do
    if ldecl.isImplementationDetail || ldecl.userName.hasMacroScopes then continue
    let t ← instantiateMVars ldecl.type
    unless ← Meta.isProp t do continue
    if t.getAppFn.isConst && [``Vsa.Sim.SegSt, ``Vsa.Machine.Steps, ``Lua.Vm.Sim.ArmAt, ``Lua.Vm.Sim.Core,
        ``Lua.Vm.Sim.Ranges, ``Lua.Bytecode.Step, ``At, ``Cx.Ok, ``Lua.Vm.Sim.VmRelAt,
        ``Lua.Vm.Sim.ValRepr].contains t.getAppFn.constName! then continue
    if natFact t then continue
    facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent ldecl.userName):term))
  evalTactic (← `(tactic| (
    simp (config := { decide := true }) only [Loc.den, Fld.den, Nat.add_zero, bgeu_one, slt_zero,
      sge_zero, BitVec.msb_xor, Bool.xor_self, Bool.xor_false, Bool.false_xor, Bool.xor_true, Bool.true_xor,
      Bool.not_eq_true, xor_true_of_ne, beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, $facts,*]
    first | done | decide)))

/-- The arm's closer of an at-lemma's hypothesis: a slot bound (`omega`
over the arm's register bounds), else a guard or precondition (`at_vals`). -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| first
    | (simp only [Fld.den, Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow] at *; omega)
    | at_vals)

/-- The registers the successor keeps: every register but the stored slots'. -/
macro "at_hold" : tactic => `(tactic| (
  intro j hj
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    SlotW.j, Fld.den, Nat.add_zero, ne_eq] at hj
  simp_all))

/-- The stored slots represent the successor's values. -/
macro "at_new" : tactic => `(tactic| (
  intro e he v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl <;>
  ( simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den] at hv ⊢
    simp at hv
    subst hv
    simp only [stData_three_lit, stData_three_n]
    first | exact .int | (simp_all [snez_eq, BitVec.msb_xor]; done) |
      (simp_all [snez_eq, BitVec.msb_xor]; exact .int))))

open Lean Elab Tactic Meta in
/-- **`at_close NS h acc`**: the close at the fetch head: the generated
`fin` lemma of `NS` whose row is `h`'s, then `AtFin.close`. -/
elab "at_close " ns:ident h:ident acc:ident : tactic => do
  let env ← getEnv
  let mut errs : Array MessageData := #[]
  for k in ["fin"] ++ (List.range 40).map (fun i => s!"fin_{i + 1}") do
    let n := ns.getId ++ Name.mkSimple k
    unless env.contains n do continue
    let s ← saveState
    try
      let args ← Tactic.runTermElab (atRunArgs n)
      let args := args.pop
      let lem ← `($(mkIdent n) $args* $h)
      withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
        exact ⟨_, $acc, ($lem).close $(mkIdent `hX) (by at_hold) (by at_new)⟩))
      return
    catch e =>
      errs := errs.push m!"{n}: {e.toMessageData}"
      s.restore
  throwError "at_close: no fin lemma closes:{indentD (MessageData.joinSep errs.toList "\n")}"

set_option hygiene false in
/-- **`at_go NS`**: after the arm's setup (`kit_setup`: `hc`, `hf`, `h0`,
`acc`, the successor evaluated), the run by the at-lemmas of `NS` and the
close. -/
macro "at_go " ns:ident : tactic => `(tactic| (
  have hX : Cx.Ok ⟨p, c, s, w, ins⟩ := ⟨hc, hf⟩
  have h0 : At ⟨p, c, s, w, ins⟩ _ (headRow ⟨p, c, s, w, ins⟩) [] c := h0
  try simp only [stackValueSize] at *
  at_run $ns h0 acc
  at_close $ns h0 acc))

end Lua.Vm.Sim.At

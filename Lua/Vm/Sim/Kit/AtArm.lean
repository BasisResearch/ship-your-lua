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

/-- `blt`/`bge` over two registers, as `Int` comparisons. -/
theorem slt_toInt (x y : BitVec 64) : zopz0zI_s x y = decide (x.toInt < y.toInt) := by
  unfold zopz0zI_s; simp
theorem sge_toInt (x y : BitVec 64) : zopz0zKzJ_s x y = decide (y.toInt ≤ x.toInt) := by
  unfold zopz0zKzJ_s; simp

/-- The successor pc in another form. -/
theorem AtFin.pc_eq {X : Cx} {M : List Ent} {W : List SlotW} {pc pc' : Nat} {c : Vsa.Machine.Config}
    (h : AtFin X M W pc c) (e : pc = pc') : AtFin X M W pc' c := e ▸ h

/-- A tag guard (`li 19; bne`, `beq a, s2`) as a comparison of tag bytes. -/
theorem zext_beq_lit (b : BitVec 8) (t : Nat) (ht : t < 256) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) == BitVec.ofNat 64 t) = decide (b = BitVec.ofNat 8 t) :=
  zext_tag_beq b t ht

theorem zext_bne_lit (b : BitVec 8) (t : Nat) (ht : t < 256) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) != BitVec.ofNat 64 t) = !decide (b = BitVec.ofNat 8 t) := by
  simp only [bne, zext_tag_beq b t ht]

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
  evalTactic (← `(tactic| first
    | (simp (config := { decide := true }) only [Loc.den, Fld.den, Nat.add_zero, bgeu_one, slt_zero,
        sge_zero, BitVec.msb_xor, Bool.xor_self, Bool.xor_false, Bool.false_xor, Bool.xor_true,
        Bool.true_xor, Bool.not_eq_true, xor_true_of_ne, beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne,
        ne_eq, BitVec.zero_sub, BitVec.neg_eq_zero_iff, $facts,*]
       first | done | decide)
    | (simp (config := { decide := true }) only [Loc.den, Fld.den, Nat.add_zero,
        zext_beq_lit _ 19 (by decide), zext_bne_lit _ 19 (by decide), zext_beq_lit _ vNumInt (by decide),
        zext_bne_lit _ vNumInt (by decide), decide_eq_true_eq, decide_eq_false_iff_not,
        Bool.not_eq_true', Bool.not_eq_false', $facts,*]
       first | done | decide)
    | (simp (config := { decide := true }) only [Loc.den, Fld.den, Nat.add_zero, slt_toInt, sge_toInt,
        beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne, ne_eq, decide_eq_true_eq, decide_eq_false_iff_not,
        Int.not_lt, Int.not_le, $facts,*]
       first | done | decide | omega)))

/-- The arm's closer of an at-lemma's hypothesis: a slot bound (`omega`
over the arm's register bounds), else a guard or precondition (`at_vals`). -/
macro_rules
  | `(tactic| at_hyp) => `(tactic| first
    | (simp only [Fld.den, Word.a, Word.b, Word.c, Word.field, Nat.shiftRight_eq_div_pow] at *; omega)
    | at_vals)

set_option hygiene false in
/-- The registers the successor keeps: every register but the stored slots'. -/
macro "at_hold" : tactic => `(tactic| (
  intro j hj
  simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true,
    SlotW.j, Fld.den, Nat.add_zero, ne_eq] at hj
  simp_all))

set_option hygiene false in
/-- The stored slots represent the successor's values. -/
macro "at_new" : tactic => `(tactic| (
  intro e he v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  all_goals rcases he with he | he | he <;>
  ( try subst he
    try simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den] at hv
    try simp only [SlotW.j, Fld.den, Nat.add_zero, Loc.den]
    try simp at hv
    try subst hv
    try simp only [stData_three_lit, stData_three_n]
    first | exact .int | (simp_all [snez_eq, BitVec.msb_xor]; done) |
      (simp_all [snez_eq, BitVec.msb_xor]; exact .int))))

/-- An extension point of `at_close`'s successor pc (`Kit/AtCond.lean`:
`donextjump`'s target `jmpPc`). Fails by default. -/
syntax "at_pc_ext" : tactic
macro_rules | `(tactic| at_pc_ext) => `(tactic| fail "at_pc_ext")

open Lean Elab Tactic Meta in
/-- **`at_close NS h acc`**: the close at the fetch head: the generated
`fin` lemma of `NS` whose row is `h`'s, then `AtFin.close`. -/
elab "at_close " ns:ident h:ident acc:ident : tactic => do
  let env ← getEnv
  let mut errs : Array MessageData := #[]
  let key ← withMainContext do
    let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_close: no {h}"
    atKey ld.type
  for k in ["fin"] ++ (List.range 40).map (fun i => s!"fin_{i + 1}") do
    let n := ns.getId ++ Name.mkSimple k
    unless env.contains n do continue
    unless (← lemmaKey n) == key do
      errs := errs.push m!"{n}: key {(← lemmaKey n)} ≠ {key}"
      continue
    let s ← saveState
    try
      let args ← Tactic.runTermElab (atRunArgs n)
      let args := args.pop
      let lem ← `($(mkIdent n) $args* $h)
      withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic| (
        refine ⟨_, $acc, (($lem).pc_eq ?_).close $(mkIdent `hX) ?_ ?_⟩
        first | rfl | omega | (simp only []; omega) | at_pc_ext
        at_hold
        at_new)))
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

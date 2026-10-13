import Lua.Vm.Sim.Kit.AtFn
import Lua.Vm.Fn.Spec
import Lua.Vm.Fn.Floor

/-!
# Soft-float call nodes and Boolean forks on the callee route (lane F1-F4)

The callee-context rows (`Kit/AtFn.lean`, `scripts/gen_lua_at.py --fn`) of a
C callee that calls libgcc's soft-float routines or libm's `floor` (a spec
with `float=True`):

* **call nodes** (`FCALLS`, the arm route's table): the call at-lemma pins
  the registers the caller's row leaves dead (`SegSt.pin22`, `pin26`: the
  routines' summaries keep the whole `HFrame`) and applies the routine's
  summary (`fat_fcall`); its result is the lifted function `Lua.Vm.Fn.<R>.F`
  of its arguments, a framed routine's frame the log entry `memPatch m
  (Lua.Vm.Fn.<R>.Fm …) (sp - F) F` (read past by `fw*_patch`, compared by
  `fat_mem`);
* **Boolean forks** (`fat_walk`): `fat_run`'s chaining, but where no
  at-lemma applies because a branch guard over a routine's answer is not in
  context, the run splits on that very `Bool` (`hf_<pc>`, two goals) and goes
  on in both; it stops at the callee's return.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.AtF

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

set_option hygiene false in
/-- **`fat_fcall sum`**: a soft-float call at-lemma's proof (after `intro c
h`, the context's facts and the dead registers pinned): the routine's
summary at the row, the return row by `at_pins`, the memory (a framed
routine's `memPatch`) by `fat_mem`. -/
macro "fat_fcall " sum:term : tactic => `(tactic| (
  have acc := Vsa.Machine.Steps.refl c
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.call acc h (by pins_of h) $sum
  exact ⟨_, acc, Vsa.Sim.SegSt.mem_eq (Vsa.Sim.SegSt.repin h (by at_pins h)) (by fat_mem)⟩))

set_option hygiene false in
/-- A framed routine's stack facts (`FnSp`) from the context's (`omega`). -/
macro "fat_fnsp" : tactic => `(tactic|
  exact ⟨by rw [hTH]; omega, by omega, by omega⟩)

set_option hygiene false in
/-- `.rodata` at a framed routine's call: the root's (`RodataRead X.m`)
through the path's stores and frames above the HTIF mailbox. -/
macro "fat_rod" : tactic => `(tactic| (
  simp only [at_row]
  repeat (first
    | assumption
    | (refine RodataRead.wm8 ?_ (by rw [hTH]; omega))
    | (refine RodataRead.patch ?_ (by rw [hTH]; omega)))))

open Lean Elab Tactic Meta

/-- The fork guard of a callee at-lemma (its `hg*` binder) at the context
`X`, if it has one. -/
def fatGuard? (n : Name) (X : Expr) : MetaM (Option Expr) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.toString.startsWith "hg" then
        return some ((← inferType x).replaceFVar xs[0]! X)
    return none

/-- **`fat_walk ns h acc`**: `fat_run ns h acc` up to the callee's return,
splitting on the `Bool` of a branch guard no fact decides (`hf_<pc>`), in
every goal. -/
partial def fatWalk (ns h acc : Ident) : TacticM Unit := do
  let mut fuel := 96
  while fuel > 0 do
    fuel := fuel - 1
    let (pc, key, ret, X) ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "fat_walk: no {h}"
      let ty ← instantiateMVars ld.type
      return (← segPc ty, ← segKey ty, ← segRet ty, ty.getAppArgs[1]!.appArg!)
    let some pc := pc | return
    let cands ← (← At.atCands ns.getId pc ret).filterM fun n => return (← fatLemmaKey n) == key
    let mut done := false
    for n in cands do
      let s ← saveState
      try
        let args ← Tactic.runTermElab (fatRunArgs n)
        let lem ← `($(mkIdent n) $args*)
        withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
          obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (Vsa.Sim.SegSt.pins $h) $lem))
        done := true
        break
      catch _ => s.restore
    if done then continue
    -- a fork: split on the guard's `Bool`, then on in both goals
    for n in cands do
      let some g ← withMainContext (fatGuard? n X) | continue
      let some (_, lhs, _) := g.eq? | continue
      for d in ← withMainContext getLCtx do
        if let some (_, l, _) := (← instantiateMVars d.type).eq? then
          if l == lhs then throwError "fat_walk: no at-lemma for this side of the fork at 0x{hex8 pc}"
      let stx ← withMainContext (Term.exprToSyntax lhs)
      let hn := mkIdent (Name.mkSimple s!"hf_{hex8 pc}")
      evalTactic (← `(tactic| rcases Bool.eq_false_or_eq_true $stx with $hn:ident | $hn:ident))
      let gs ← getUnsolvedGoals
      let mut out := []
      for g in gs do
        setGoals [g]
        fatWalk ns h acc
        out := out ++ (← getUnsolvedGoals)
      setGoals out
      return
    throwError "fat_walk: nothing applies at 0x{hex8 pc}"
  throwError "fat_walk: out of fuel"

elab "fat_walk " ns:ident h:ident acc:ident : tactic => fatWalk ns h acc

end Lua.Vm.Sim.AtF

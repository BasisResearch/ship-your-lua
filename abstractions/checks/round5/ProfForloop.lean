import Lua.Vm.Sim.Kit.AtFltForloop

/-!
# Round 5: where `sim_FORLOOP_flt`'s cost goes, by tactic

`Lua/Vm/Sim/Kit/AtFltForloop.lean`'s proof with `at_go` expanded
(`at_run` then `at_close`) and `hb` logging the heartbeat counter (in
thousands of `maxHeartbeats` units, cumulative within the declaration)
between the steps. Measurement only: not imported by `Lua`.

    systemd-run --user --scope -p MemoryMax=8G -q lake env lean abstractions/checks/round5/ProfForloop.lean
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At.Prof5

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Vm.Sim.At Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

elab "hb " s:str : tactic => do
  let n ← IO.getNumHeartbeats
  Lean.logInfo m!"HB {s.getString} {n / 1000}"

open Lean Elab Tactic Meta in
/-- `at_run` (`Kit/At.lean`) with each step's heartbeats logged: the lemma
taken, and the heartbeats spent on candidates rejected before it. -/
elab "at_run_log " ns:ident h:ident acc:ident : tactic => do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let (pc, ret) ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_run: no {h}"
      return (← atPc ld.type, ← atRet ld.type)
    let some pc := pc | throwError "at_run: no pc"
    if pc == 0x8001bfe4 || errEntryPcs.contains pc then return
    let cands ← atCands ns.getId pc ret
    let mut done := false
    let key ← withMainContext do
      let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_run: no {h}"
      atKey ld.type
    let t0 ← IO.getNumHeartbeats
    let mut rej : Nat := 0
    for n in cands do
      unless (← lemmaKey n) == key do continue
      let s ← saveState
      let a ← IO.getNumHeartbeats
      let ok ← tryCatchRuntimeEx (do
          let args ← Tactic.runTermElab (atRunArgs n)
          let lem ← `($(mkIdent n) $args*)
          withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
            obtain ⟨_, $acc, $h⟩ := At.run $acc $h $lem))
          pure true)
        (fun _ => pure false)
      let b ← IO.getNumHeartbeats
      if ok then
        logInfo m!"STEP {n.getString!} taken {(b - a) / 1000} rejected-before {rej / 1000}"
        done := true; break
      else
        rej := rej + (b - a); s.restore
    unless done do throwError "at_run_log: stuck at {pc}"
    let _ := t0
  throwError "at_run: out of fuel"

set_option Elab.async false
set_option profiler true
set_option profiler.threshold 20

set_option hygiene false in
theorem sim_FORLOOP_flt' (hsf : SoftFloatSpec) : SimArmOn .FORLOOP FltStep :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  hb "start"
  kit_setup 0x8001c1ec
  hb "kit_setup"
  rcases hj : jumpTo (s.pc + 1) (-(ins.bx : Int)) with _ | t <;> simp [hj] at hk htop
  hb "jumpTo split"
  simp [forloopK, Kernel.regTop] at hk htop
  hb "simp forloopK"
  kit_bound hA2 (ins.a + 2)
  kit_reg hr0 v0 hv0 ins.a
  kit_reg hr1 v1 hv1 (ins.a + 1)
  kit_reg hr2 v2 hv2 (ins.a + 2)
  hb "kit_reg x3"
  obtain ⟨st, ns, hst⟩ := hT
  rw [hst] at hr2; cases hr2
  obtain ⟨i, ni, l, nl, rfl, rfl⟩ : ∃ i ni l nl, v0 = .flt i ni ∧ v1 = .flt l nl := by
    cases v0 <;> cases v1 <;> simp at hk ⊢
  hb "refute non-float (cases v0 v1)"
  have hbx : ins.bx ≤ s.pc + 1 := by simp [jumpTo] at hj; omega
  have ht : t = s.pc + 1 - ins.bx := by simp [jumpTo] at hj; omega
  subst ht
  hb "jump target"
  obtain ⟨hta0, hxm0, -⟩ := hv0.flt_parts
  obtain ⟨hta2, hxm2', -⟩ := hv2.flt_parts
  obtain ⟨-, hxm1, -⟩ := hv1.flt_parts
  have hta := And.intro hta2 hta0
  have hxm := And.intro hxm0 (And.intro hxm1 hxm2')
  have hnj := toModel_zero
  simp only [model_add_comm i st] at hk
  hb "payload bundle + comm"
  rcases Bool.eq_false_or_eq_true (Float.Model.lt Lua.Num.zero st) with hp | hp <;>
    simp only [hp, ite_true, ite_false, Bool.false_eq_true] at hk <;> split at hk <;> rename_i hq <;>
    (have e := And.intro hp hq
     hb "branch: kernel split"
     simp [VState.apply, writeDefs, KEdge.kills] at hk
     subst hk
     hb "branch: successor"
     have hX : Cx.Ok ⟨p, c, s, w, ins⟩ := ⟨hc, hf⟩
     have h0 : At ⟨p, c, s, w, ins⟩ _ (headRow ⟨p, c, s, w, ins⟩) [] c := h0
     try simp only [stackValueSize] at *
     hb "branch: at_go prelude"
     at_run_log Lua.Vm.At.FORLOOP h0 acc
     hb "branch: at_run"
     at_close Lua.Vm.At.FORLOOP h0 acc
     hb "branch: at_close")

end Lua.Vm.Sim.At.Prof5

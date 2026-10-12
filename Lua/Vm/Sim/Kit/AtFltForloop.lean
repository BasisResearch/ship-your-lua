import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Forloop

/-!
# `OP_FORLOOP` on a float step on the location-list route (lane float-m0, M1 held out)

`floatforloop` (`lvm.c:270`): the index plus the step by `__adddf3`, the
direction of the step by `__gedf2` against `0.0`, the bound by `__ledf2` or
`__gedf2`, then `R[A] := R[A+3] := index` and the jump back; the generated
at-lemmas `Lua/Vm/At/Forloop.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_FORLOOP` on a float step** (`FloatArms.FORLOOP`). -/
theorem sim_FORLOOP_flt (hsf : SoftFloatSpec) : SimArmOn .FORLOOP FltStep :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  kit_setup 0x8001c1ec
  rcases hj : jumpTo (s.pc + 1) (-(ins.bx : Int)) with _ | t <;> simp [hj] at hk htop
  simp [forloopK, Kernel.regTop] at hk htop
  kit_bound hA2 (ins.a + 2)
  kit_reg hr0 v0 hv0 ins.a
  kit_reg hr1 v1 hv1 (ins.a + 1)
  kit_reg hr2 v2 hv2 (ins.a + 2)
  obtain ⟨st, ns, hst⟩ := hT
  rw [hst] at hr2; cases hr2
  obtain ⟨i, ni, l, nl, rfl, rfl⟩ : ∃ i ni l nl, v0 = .flt i ni ∧ v1 = .flt l nl := by
    cases v0 <;> cases v1 <;> simp at hk ⊢
  have hbx : ins.bx ≤ s.pc + 1 := by simp [jumpTo] at hj; omega
  have ht : t = s.pc + 1 - ins.bx := by simp [jumpTo] at hj; omega
  subst ht
  obtain ⟨hta0, hxm0, -⟩ := hv0.flt_parts
  obtain ⟨hta2, hxm2', -⟩ := hv2.flt_parts
  obtain ⟨-, hxm1, -⟩ := hv1.flt_parts
  have hta := And.intro hta2 hta0
  have hxm := And.intro hxm0 (And.intro hxm1 hxm2')
  have hnj := toModel_zero
  simp only [model_add_comm i st] at hk
  rcases Bool.eq_false_or_eq_true (Float.Model.lt Lua.Num.zero st) with hp | hp <;>
    simp only [hp, ite_true, ite_false, Bool.false_eq_true] at hk <;> split at hk <;> rename_i hq <;>
    (have e := And.intro hp hq
     simp [VState.apply, writeDefs, KEdge.kills] at hk
     subst hk
     at_go Lua.Vm.At.FORLOOP)

end Lua.Vm.Sim.At

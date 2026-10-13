import Lua.Vm.Sim.Kit.AtJoin
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

/-- **`OP_FORLOOP` on a float step** (`FloatArms.FORLOOP`): the step a float
(`flt_reg_q`), the index and limit by the kernel's float clause; the run split
at `0x8001e17c` (the step's sign) and cut at the join `0x8001e194`; each leaf
by the pair atoms `{0, step}`, `{index, limit}`. -/
theorem sim_FORLOOP_flt (hsf : SoftFloatSpec) : SimArmOn .FORLOOP FltStep :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  kit_setup 0x8001c1ec
  rcases hj : jumpTo (s.pc + 1) (-(ins.bx : Int)) with _ | t <;> simp [hj] at hk htop
  simp [forloopK, Kernel.regTop] at hk htop
  kit_bound hA2 (ins.a + 2)
  flt_views; flt_reg_q st (ins.a + 2), hT; flt_reg2 i ins.a, l (ins.a + 1)
  have hbx : ins.bx ≤ s.pc + 1 := by simp [jumpTo] at hj; omega
  obtain rfl : t = s.pc + 1 - ins.bx := by simp [jumpTo] at hj; omega
  simp only [model_add_comm i st] at hk
  at_walk Lua.Vm.At.FORLOOP

end Lua.Vm.Sim.At

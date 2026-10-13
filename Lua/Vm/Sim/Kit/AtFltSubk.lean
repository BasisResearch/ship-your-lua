import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.Subk

/-!
# `OP_SUBK` with a float operand on the join route (lane F2)

`op_arithfK`: `R[B]` or `K[C]` a float, the other by its per-operand view;
`luai_numsub` by `__subdf3`.
The generated at-lemmas
`Lua/Vm/At/Subk.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_SUBK` with a float operand** (`FloatArms.ADD`). -/
theorem sim_SUBK_flt (hsf : SoftFloatSpec) : SimArmOn .SUBK FltBK :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarithK 0x8001c984 Lua.Vm.At.SUBK

end Lua.Vm.Sim.At

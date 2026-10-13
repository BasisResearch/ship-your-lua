import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.Add

/-!
# `OP_ADD` with a float operand on the join route (lane F2)

`op_arithf`: `R[B]` or `R[C]` a float, the other by its per-operand view;
`luai_numadd` by `__adddf3`, which the compiler calls with the operands
commuted (`__adddf3(c, b)`: `model_add_comm`). The generated at-lemmas
`Lua/Vm/At/Add.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_ADD` with a float operand** (`FloatArms.ADD`). -/
theorem sim_ADD_flt (hsf : SoftFloatSpec) : SimArmOn .ADD FltBC :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarith 0x8001d9c8 Lua.Vm.At.ADD

end Lua.Vm.Sim.At

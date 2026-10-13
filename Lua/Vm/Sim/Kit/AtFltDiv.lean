import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.At.Div

/-!
# `OP_DIV` on the join route (lane F1-F6)

`op_arithf`: `R[B]` and `R[C]` by their per-operand views (an integer through
`__floatdidf`); `luai_numdiv` by `__divdf3`. Every path: `rawArith .div` has
no integer case. The generated at-lemmas `Lua/Vm/At/Div.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_DIV`** (was `FloatArms.DIV`). -/
theorem sim_DIV : SimArm .DIV :=
  sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  at_jarithA 0x8001d494 Lua.Vm.At.DIV

end Lua.Vm.Sim.At

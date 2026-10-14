import Lua.Vm.Sim.Kit.AtJoinMod
import Lua.Vm.At.ModkF

/-!
# `OP_MODK` with a float operand on the join route (lane F1-F7)

`op_arithfK`: `R[B]` or `K[C]` a float, the other by its per-operand view;
`luai_nummod` by libm `fmod` and the sign correction (`Kit/AtJoinMod.lean`).
The generated at-lemmas `Lua/Vm/At/ModkF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_MODK` with a float operand** (was `FloatArms.MODK`): one
-- declaration per (float operand, the other's class)
modk_flt_arm sim_MODK_flt .MODK 0x8001dad0 Lua.Vm.At.MODK_F

end Lua.Vm.Sim.At

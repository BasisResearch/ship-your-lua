import Lua.Vm.Sim.Kit.AtJoinMod
import Lua.Vm.At.ModF

/-!
# `OP_MOD` with a float operand on the join route (lane F1-F7)

`op_arithf`: `R[B]` or `R[C]` a float, the other by its per-operand view;
`luai_nummod` by libm `fmod` and the sign correction (`Kit/AtJoinMod.lean`).
The generated at-lemmas `Lua/Vm/At/ModF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_MOD` with a float operand** (was `FloatArms.MOD`): one declaration
-- per (float operand, the other's class)
mod_flt_arm sim_MOD_flt .MOD 0x8001dc58 Lua.Vm.At.MOD_F

end Lua.Vm.Sim.At

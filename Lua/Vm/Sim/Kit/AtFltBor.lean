import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.At.BorF

/-!
# `OP_BOR` with a float operand on the join route (lane F2)

`op_bitwise`: each operand through `tointegerns` (an integer, or a float by
`luaV_flttointeger(F2Ieq)` inlined: `floor`, `__eqdf2`, the range,
`__fixdfdi`), else the fall-through to `MMBIN`; one declaration per (float
operand, the other's class) (`bitwise_flt_arm`, `at_jbit`). The generated at-lemmas `Lua/Vm/At/BorF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_BOR` with a float operand** (`FloatArms.BOR`), under `floor`'s premise.
bitwise_flt_arm sim_BOR_flt .BOR 0x8001da70 Lua.Vm.At.BOR_F

end Lua.Vm.Sim.At

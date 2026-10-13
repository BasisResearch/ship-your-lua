import Lua.Vm.Sim.Kit.AtJoinShift
import Lua.Vm.At.ShlF

/-!
# `OP_SHL` with a float operand on the join route (lane F3)

`luaV_shiftl(R[B], R[C])`: a float operand through `tointegerns` (`floor`, `__eqdf2`, the
range, `__fixdfdi`), the other by its class; the machine tests the amount
`R[C]`, `__fixdfdi`'s value when `R[C]` is the float: residual atoms
under the range atom (`shift2_flt_arm`: one declaration per float operand,
`F2Ieq` outcome and class). The generated at-lemmas `Lua/Vm/At/ShlF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_SHL` with a float operand** (`FloatArms.SHL`), under `floor`'s premise.
shift2_flt_arm sim_SHL_flt .SHL 0x8001d5f0 Lua.Vm.At.SHL_F

end Lua.Vm.Sim.At

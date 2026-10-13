import Lua.Vm.Sim.Kit.AtJoinShift
import Lua.Vm.At.ShrF

/-!
# `OP_SHR` with a float operand on the join route (lane F3)

`luaV_shiftr(R[B], R[C])`: a float operand through `tointegerns` (`floor`, `__eqdf2`, the
range, `__fixdfdi`), the other by its class; the machine tests the amount
`0 - R[C]`, `__fixdfdi`'s value when `R[C]` is the float: residual atoms
under the range atom (`shift2_flt_arm`: one declaration per float operand,
`F2Ieq` outcome and class). The generated at-lemmas `Lua/Vm/At/ShrF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_SHR` with a float operand** (`FloatArms.SHR`) (`floor` by `floorSpec_proved`).
shift2_flt_arm sim_SHR_flt .SHR 0x8001d57c Lua.Vm.At.SHR_F

end Lua.Vm.Sim.At

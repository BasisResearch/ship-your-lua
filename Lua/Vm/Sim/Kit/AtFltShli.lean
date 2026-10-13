import Lua.Vm.Sim.Kit.AtJoinShift
import Lua.Vm.At.ShliF

/-!
# `OP_SHLI` with a float `R[B]` on the join route (lane F3)

`luaV_shiftl(sC, R[B])`: the amount `R[B]` through `tointegerns` (`floor`,
`__eqdf2`, the range, `__fixdfdi`), tested by the machine as `__fixdfdi`'s
value: residual atoms under the range atom (`shift_flt_arm`, `shiftl_m`,
`slt_fixL`/`R`). The generated at-lemmas `Lua/Vm/At/ShliF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_SHLI` with a float `R[B]`** (`FloatArms.SHLI`), under `floor`'s premise.
shift_flt_arm sim_SHLI_flt .SHLI 0x8001dd30 Lua.Vm.At.SHLI_F

end Lua.Vm.Sim.At

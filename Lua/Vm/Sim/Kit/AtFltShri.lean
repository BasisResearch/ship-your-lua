import Lua.Vm.Sim.Kit.AtJoinShift
import Lua.Vm.At.ShriF

/-!
# `OP_SHRI` with a float `R[B]` on the join route (lane F3)

`luaV_shiftr(R[B], sC)`: `R[B]` through `tointegerns` (`floor`, `__eqdf2`,
the range, `__fixdfdi`), shifted on the machine's tests of the field `C`
(`shift_flt_arm`, `shiftr_K`). The generated at-lemmas `Lua/Vm/At/ShriF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_SHRI` with a float `R[B]`** (`FloatArms.SHRI`) (`floor` by `floorSpec_proved`).
shift_flt_arm sim_SHRI_flt .SHRI 0x8001dd8c Lua.Vm.At.SHRI_F

end Lua.Vm.Sim.At

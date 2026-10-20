import Lua.Vm.Sim.Kit.AtJoinPow
import Lua.Vm.At.Powk

/-!
# `OP_POWK` on the join route (lane F1-21)

`op_arithfK`: `R[B]` by its per-operand view, the constant `K[C]` by its own
(`num_k`; an integer through `__floatdidf`, read back past its frame,
`Kit/AtFrame.lean`); `luai_numpow` by `__eqdf2(b, 2.0)`, then `__muldf3(a, a)`
or libm `pow` (`Kit/AtJoinPow.lean`). Every path on quiet operands
(`PowKQuiet`), given `__ieee754_pow`'s level (b). The generated at-lemmas
`Lua/Vm/At/Powk.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_POWK` on quiet operands** (was `FloatArms.POWK`): one declaration per
-- class of `R[B]`, given `__ieee754_pow`'s level (b)
powk_arm sim_POWK .POWK PowKQuiet 0x8001d804 Lua.Vm.At.POWK

end Lua.Vm.Sim.At

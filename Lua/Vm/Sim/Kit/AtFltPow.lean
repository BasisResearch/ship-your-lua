import Lua.Vm.Sim.Kit.AtJoinPow
import Lua.Vm.At.Pow

/-!
# `OP_POW` on the join route (lane F1-21)

`op_arithf`: `R[B]` and `R[C]` by their per-operand views (an integer through
`__floatdidf`); `luai_numpow` by `__eqdf2(b, 2.0)`, then `__muldf3(a, a)` or
libm `pow` (`Kit/AtJoinPow.lean`). Every path on quiet operands
(`PowQuiet`), given `__ieee754_pow`'s level (b). The generated at-lemmas
`Lua/Vm/At/Pow.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

-- **`OP_POW` on quiet operands** (was `FloatArms.POW`): one declaration per
-- class of `R[B]`, given `__ieee754_pow`'s level (b)
pow_arm sim_POW .POW PowQuiet 0x8001d4f0 Lua.Vm.At.POW

end Lua.Vm.Sim.At

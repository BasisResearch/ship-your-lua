import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.At.Divk

/-!
# `OP_DIVK` on the join route (lane F1-F6)

`op_arithfK`: `R[B]` and `K[C]` by their per-operand views (an integer through
`__floatdidf`); `luai_numdiv` by `__divdf3`. Every path: `rawArith .div` has
no integer case. The generated at-lemmas `Lua/Vm/At/Divk.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_DIVK`** (was `FloatArms.DIVK`). -/
theorem sim_DIVK : SimArm .DIVK :=
  sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  at_jarithAK 0x8001d7d8 Lua.Vm.At.DIVK

end Lua.Vm.Sim.At

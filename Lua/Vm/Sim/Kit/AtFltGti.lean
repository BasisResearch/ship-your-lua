import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.Gti

/-!
# `OP_GTI` on a float on the join route (lane F2)

`op_orderI(L, luai_numgt, luai_numgt, 1, TM_LT)`: `R[A]` a float, compared
with `cast_num(sB)` (`__floatsidf`) by `__gedf2` (`sgtz`), then
`docondjump`'s fork on the answer against `k`; the generated at-lemmas
`Lua/Vm/At/Gti.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_GTI` on a float** (`FloatArms.GTI`). -/
theorem sim_GTI_flt (hsf : SoftFloatSpec) : SimArmOn .GTI FltA :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jorderI 0x8001c5ac Lua.Vm.At.GTI

end Lua.Vm.Sim.At

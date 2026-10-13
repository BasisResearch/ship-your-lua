import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.Lei

/-!
# `OP_LEI` on a float on the join route (lane F2)

`op_orderI(L, luai_numle, luai_numle, 0, TM_LE)`: `R[A]` a float, compared
with `cast_num(sB)` (`__floatsidf`) by `__ledf2` (`slti 1`), then
`docondjump`'s fork on the answer against `k`; the generated at-lemmas
`Lua/Vm/At/Lei.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_LEI` on a float** (`FloatArms.LEI`). -/
theorem sim_LEI_flt (hsf : SoftFloatSpec) : SimArmOn .LEI FltA :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jorderI 0x8001c40c Lua.Vm.At.LEI

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.Sub

/-!
# `OP_SUB` with a float operand on the location-list route (round 5, A-JOIN held out)

`op_arithf`: `R[B]` or `R[C]` a float; the other operand by its per-operand
view (`num_reg`): a float, an integer (`__floatdidf`) or no number (the
fall-through to `MMBIN`); `luai_numsub` by `__subdf3`. The generated
at-lemmas `Lua/Vm/At/Sub.lean`; no machine fork on a soft-float answer.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_SUB` with a float operand** (`FloatArms.SUB`). -/
theorem sim_SUB_flt (hsf : SoftFloatSpec) : SimArmOn .SUB FltBC :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarith 0x8001d964 Lua.Vm.At.SUB

end Lua.Vm.Sim.At

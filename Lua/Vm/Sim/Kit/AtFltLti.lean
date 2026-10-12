import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Lti

/-!
# `OP_LTI` on a float on the location-list route (lane float-m0, M1 training)

`op_orderI(L, luai_numlt, luai_numlt, 0, TM_LT)`: `R[A]` a float, compared
with `cast_num(sB)` (`__floatsidf`) by `__ltdf2` (`= __ledf2`, `slti 0`),
then `docondjump`; the generated at-lemmas `Lua/Vm/At/Lti.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `LTI`'s test on a float: `x < sB`. -/
abbrev ltiT (ins : Word) (x : Float.Model) : Bool := Float.Model.lt x (Float.Model.ofInt ((ins.b : Int) - 127))

theorem lti_flt_take (hsf : SoftFloatSpec) : ArmBody .LTI (FltTest ltiT true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c46c Lua.Vm.At.LTI (δ_lt_fi x n ins.b hbb), ((hkk.2 rfl).symm)

theorem lti_flt_skip (hsf : SoftFloatSpec) : ArmBody .LTI (FltTest ltiT false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c46c Lua.Vm.At.LTI (δ_lt_fi x n ins.b hbb), (fbool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`OP_LTI` on a float** (`FloatArms.LTI`). -/
theorem sim_LTI_flt (hsf : SoftFloatSpec) : SimArmOn .LTI FltA :=
  sim_fcond (by decide) ltiT (lti_flt_take hsf) (lti_flt_skip hsf)

end Lua.Vm.Sim.At

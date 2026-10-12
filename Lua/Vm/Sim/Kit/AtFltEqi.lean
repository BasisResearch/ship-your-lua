import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Eqi

/-!
# `OP_EQI` on a float on the location-list route (lane float-m0, M1 training)

`OP_EQI`'s float case `luai_numeq(fltvalue(ra), cast_num(im))`: `R[A]` a
float, compared with `cast_num(sB)` (`__floatsidf`) by `__eqdf2` (`seqz`),
then `docondjump`; the generated at-lemmas `Lua/Vm/At/Eqi.lean`. The kernel's
test is `δ .eq` (`luaV_equalobj`'s mixed case), equal to `luai_numeq` for an
8-bit immediate (`EqiFlt_Statement`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `EQI`'s test on a float: `x == sB`. -/
abbrev eqiT (ins : Word) (x : Float.Model) : Bool := Float.Model.beq x (Float.Model.ofInt ((ins.b : Int) - 127))

theorem eqi_flt_take (hsf : SoftFloatSpec) (heq : EqiFlt_Statement) : ArmBody .EQI (FltTest eqiT true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c7f0 Lua.Vm.At.EQI (heq x n ins.b hbb), ((hkk.2 rfl).symm)

theorem eqi_flt_skip (hsf : SoftFloatSpec) (heq : EqiFlt_Statement) : ArmBody .EQI (FltTest eqiT false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c7f0 Lua.Vm.At.EQI (heq x n ins.b hbb), (fbool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`OP_EQI` on a float** (`FloatArms.EQI`). -/
theorem sim_EQI_flt (hsf : SoftFloatSpec) (heq : EqiFlt_Statement) : SimArmOn .EQI FltA :=
  sim_fcond (by decide) eqiT (eqi_flt_take hsf heq) (eqi_flt_skip hsf heq)

end Lua.Vm.Sim.At

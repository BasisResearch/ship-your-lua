import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Gei

/-!
# `OP_GEI` on a float on the location-list route (lane float-m0, M1 held out)

`op_orderI(L, luai_numge, luai_numge, 1, TM_LE)`: `R[A]` a float, compared
with `cast_num(sB)` (`__floatsidf`) by `__gedf2` (`not; srli 63`), then
`docondjump`; the generated at-lemmas `Lua/Vm/At/Gei.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `GEI`'s test on a float: `sB <= x`. -/
abbrev geiT (ins : Word) (x : Float.Model) : Bool := Float.Model.le (Float.Model.ofInt ((ins.b : Int) - 127)) x

theorem gei_flt_take (hsf : SoftFloatSpec) : ArmBody .GEI (FltTest geiT true) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c548 Lua.Vm.At.GEI (δ_le_if x n ins.b hbb), ((hkk.2 rfl).symm)

theorem gei_flt_skip (hsf : SoftFloatSpec) : ArmBody .GEI (FltTest geiT false) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_fcond 0x8001c548 Lua.Vm.At.GEI (δ_le_if x n ins.b hbb), (fbool_ne_not fun h => absurd (hkk.1 h) (by decide))

/-- **`OP_GEI` on a float** (`FloatArms.GEI`). -/
theorem sim_GEI_flt (hsf : SoftFloatSpec) : SimArmOn .GEI FltA :=
  sim_fcond (by decide) geiT (gei_flt_take hsf) (gei_flt_skip hsf)

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.Sim.Kit.AtFltLe

/-!
# `OP_LT`'s and `OP_LE`'s f2i paths on the join route (lane F2)

An integer outside `l_intfitsf` against a float (`LTintfloat`/`LTfloatint`,
`LEintfloat`/`LEfloatint`: `luaV_flttointeger` with `F2Iceil`/`F2Ifloor`):
`at_jf2i`, one declaration per class (`F2IL`: the integer in `R[A]`,
`F2IR`: in `R[B]`), `floor` by `floorSpec_proved`. These
discharge `LtF2I_Statement` and `LeF2I_Statement`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

theorem lt_f2iL (hsf : SoftFloatSpec) : ArmBody .LT F2IL :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jf2i 0x8001c894 Lua.Vm.At.LT_F L

theorem lt_f2iR (hsf : SoftFloatSpec) : ArmBody .LT F2IR :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jf2i 0x8001c894 Lua.Vm.At.LT_F R

/-- **`LT`'s f2i paths** (`LtF2I_Statement`) (`floor` by `floorSpec_proved`). -/
theorem lt_flt_f2i (hsf : SoftFloatSpec) : LtF2I_Statement :=
  armBody_f2i (lt_f2iL hsf) (lt_f2iR hsf)

theorem le_f2iL (hsf : SoftFloatSpec) : ArmBody .LE F2IL :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jf2i 0x8001c60c Lua.Vm.At.LE_F L

theorem le_f2iR (hsf : SoftFloatSpec) : ArmBody .LE F2IR :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jf2i 0x8001c60c Lua.Vm.At.LE_F R

/-- **`LE`'s f2i paths** (`LeF2I_Statement`) (`floor` by `floorSpec_proved`). -/
theorem le_flt_f2i (hsf : SoftFloatSpec) : LeF2I_Statement :=
  armBody_f2i (le_f2iL hsf) (le_f2iR hsf)

end Lua.Vm.Sim.At

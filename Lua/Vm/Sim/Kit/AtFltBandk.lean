import Lua.Vm.Sim.Kit.AtJoinInt
import Lua.Vm.At.BandkF

/-!
# `OP_BANDK` with a float `R[B]` on the join route (lane F3)

`op_bitwiseK(l_band)`: `R[B]` through `tointegerns` (`floor`, `__eqdf2`, the
range, `__fixdfdi`), `K[C]` an integer read after `floor`'s frame
(`at_jbitk`). The generated at-lemmas `Lua/Vm/At/BandkF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_BANDK` with a float `R[B]`** (`FloatArms.BANDK`) (`floor` by `floorSpec_proved`). -/
theorem sim_BANDK_flt (hsf : SoftFloatSpec) : SimArmOn .BANDK FltB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jbitk 0x8001d710 Lua.Vm.At.BANDK_F

end Lua.Vm.Sim.At

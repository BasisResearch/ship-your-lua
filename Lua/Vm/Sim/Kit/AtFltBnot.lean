import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.At.BnotF

/-!
# `OP_BNOT` of a float on the join route (lane F2)

`luaV_tointegerns(F2Ieq)` inlined: `floor`, `__eqdf2`, the range check on
`.rodata`'s bounds, `__fixdfdi`, then `not`; a float that is not an integer
goes to `luaT_trybinTM` (the kernel has no `Step` there: `δ .bnot` is
`none`). The generated at-lemmas `Lua/Vm/At/BnotF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_BNOT` of a float** (`FloatArms.BNOT`), under `floor`'s premise. -/
theorem sim_BNOT_flt (hsf : SoftFloatSpec) (hfl : FloorSpec) : SimArmOn .BNOT FltB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_junary 0x8001df18 Lua.Vm.At.BNOT_F

end Lua.Vm.Sim.At

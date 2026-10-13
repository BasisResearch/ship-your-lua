import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.At.UnmF

/-!
# `OP_UNM` of a float on the join route (lane F2)

`luai_numunm`: `R[B]` a float, its sign bit flipped inline (`xor` with
`1 << 63`, no call); the stored payload is the kernel's `Float.Model.neg`
by `ValRepr.flt_neg`. The generated at-lemmas `Lua/Vm/At/UnmF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_UNM` of a float** (`FloatArms.UNM`). -/
theorem sim_UNM_flt : SimArmOn .UNM FltB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_junary 0x8001d8a4 Lua.Vm.At.UNM_F

end Lua.Vm.Sim.At

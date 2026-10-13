import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.At.IdivkF

/-!
# `OP_IDIVK` with a float operand on the join route (lane F1-F6)

`op_arithfK`: `R[B]` or `K[C]` a float, the other by its per-operand view;
`luai_numidiv` by `__divdf3` then `floor` (`FloorR`). The generated
at-lemmas `Lua/Vm/At/IdivkF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_IDIVK` with a float operand** (was `FloatArms.IDIVK`). -/
theorem sim_IDIVK_flt : SimArmOn .IDIVK FltBK :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarithK 0x8001d768 Lua.Vm.At.IDIVK_F

end Lua.Vm.Sim.At

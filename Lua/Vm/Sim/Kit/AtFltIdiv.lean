import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.At.IdivF

/-!
# `OP_IDIV` with a float operand on the join route (lane F1-F6)

`op_arithf`: `R[B]` or `R[C]` a float, the other by its per-operand view;
`luai_numidiv` by `__divdf3` then `floor` (`FloorR`). The generated
at-lemmas `Lua/Vm/At/IdivF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_IDIV` with a float operand** (was `FloatArms.IDIV`). -/
theorem sim_IDIV_flt : SimArmOn .IDIV FltBC :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarith 0x8001deac Lua.Vm.At.IDIV_F

end Lua.Vm.Sim.At

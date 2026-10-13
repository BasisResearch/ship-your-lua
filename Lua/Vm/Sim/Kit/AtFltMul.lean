import Lua.Vm.Sim.Kit.AtJoinMul
import Lua.Vm.At.Mul

/-!
# `OP_MUL` with a float operand on the join route (lane F1-F5)

`op_arithf`: `R[B]` or `R[C]` a float, the other by its per-operand view;
`luai_nummul` by `__muldf3`, called with the operands commuted
(`__muldf3(c, b)`: `model_mul_comm`). The generated at-lemmas
`Lua/Vm/At/Mul.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_MUL` with a float operand** (`FloatArms.MUL`). -/
theorem sim_MUL_flt : SimArmOn .MUL FltBC :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jarith 0x8001dcc8 Lua.Vm.At.MUL

end Lua.Vm.Sim.At

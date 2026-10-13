import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.LeF

/-!
# `OP_LE` with a float operand on the join route (lane F2)

`LEnum` (`lvm.c:502`): `R[A]` or `R[B]` a float, the other by its view
(`num_regf`): a float (`__ledf2`, `slti 1`), an integer inside `l_intfitsf`
(`__floatdidf`, then `__ledf2`/`__gedf2`), or no number (the kernel is stuck:
`luaG_ordererror`). The machine's one fork on a soft-float answer is
`docondjump`'s test against `k`; the leaves are decided over the pair atom
and the `k` bit (`at_jorder`, as `OP_LT`). The generated at-lemmas
`Lua/Vm/At/LeF.lean`.

**Open: `LeF2I_Statement`**, an integer operand outside `l_intfitsf`
(`LEintfloat`/`LEfloatint`'s `luaV_flttointeger` chain through `floor`), as
`LtF2I_Statement`; the walk stops at `jal floor`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **Open (lane F2): `LE`'s `luaV_flttointeger` paths** (see the module
doc; `FltF2I`). Supplied by `floor`'s summary and the chain's value equation. -/
def LeF2I_Statement : Prop := ArmBody .LE FltF2I

/-- **`OP_LE` with a float operand** (`FloatArms.LE`), its f2i paths open. -/
theorem sim_LE_flt (hsf : SoftFloatSpec) (hf2i : LeF2I_Statement) : SimArmOn .LE FltAB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jorder 0x8001c60c Lua.Vm.At.LE_F hf2i

end Lua.Vm.Sim.At

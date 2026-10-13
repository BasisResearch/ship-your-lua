import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.At.LtF

/-!
# `OP_LT` with a float operand on the location-list route (round 5, A-JOIN held out)

`LTnum` (`lvm.c:480`): `R[A]` or `R[B]` a float, the other by its view
(`num_regf`): a float (`__ltdf2` = `__ledf2`, `slti 0`), an integer inside
`l_intfitsf` (`__floatdidf`, then `__gedf2`/`__ledf2`), or no number (the
kernel is stuck: `luaG_ordererror`). The machine's one fork on a soft-float
answer is `docondjump`'s test against `k` (`0x8001c900`); the leaves are
decided over the pair atom and the `k` bit. The generated at-lemmas
`Lua/Vm/At/LtF.lean`.

**Open: `LtF2I_Statement`**, an integer operand outside `l_intfitsf`
(`LTintfloat`/`LTfloatint`'s `luaV_flttointeger` chain: `floor`, `__eqdf2`,
`__adddf3`, the range tests, `__fixdfdi`, then an integer compare). It
needs `floor`'s summary (newlib `s_floor.c` calls `__adddf3` and `__gedf2`
itself; `gen_lua_fn.py` lifts no routine that calls a soft-float routine)
and the value equation `__fixdfdi (floor x) = (floor x).toInt64` under the
range atoms; the walk stops at `jal floor` (`0x8001f900`, `0x8001fb00`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **Open (round 5): `LT`'s `luaV_flttointeger` paths** (see the module
doc; `FltF2I`). Supplied by `floor`'s summary and the chain's value equation. -/
def LtF2I_Statement : Prop := ArmBody .LT FltF2I

/-- **`OP_LT` with a float operand** (`FloatArms.LT`), its f2i paths open. -/
theorem sim_LT_flt (hsf : SoftFloatSpec) (hf2i : LtF2I_Statement) : SimArmOn .LT FltAB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_jorder 0x8001c894 Lua.Vm.At.LT_F hf2i

end Lua.Vm.Sim.At

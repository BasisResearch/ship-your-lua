import Lua.Vm.Sim.Kit.Add
import Lua.Vm.Sim.Kit.Mul
import Lua.Vm.Sim.Kit.Mod
import Lua.Vm.Sim.Kit.Eq
import Lua.Vm.Sim.Kit.Lt
import Lua.Vm.Sim.Kit.Le
import Lua.Vm.Sim.Kit.Eqk
import Lua.Vm.Sim.Kit.Loadnil
import Lua.Vm.Sim.Kit.Tointeger
import Lua.Vm.Sim.Kit.Mulk
import Lua.Vm.Sim.Kit.Modk

/-!
# The direct kit (round-3 bake-off, contender KIT)

The library (`Kit/Run.lean`: the segment runner `kit_run`; `Kit/Close.lean`:
the arm skeleton, M1 forward evaluation, M3 close, the arm tactics), the
call-node summaries of the libgcc helpers at the Lua ELF's addresses
(`Kit/Muldi3.lean`, `Kit/Udivdi3.lean`, `Kit/Moddi3.lean`), `luaV_mod`
restated (`Kit/ModEq.lean`), and the arms `sim_ADD` (refactor), `sim_MUL`,
`sim_MOD` (held out), `luaV_equalobj`'s summary (`Kit/Equalobj.lean`) and `OP_EQ` but
two long strings (`Kit/Eq.lean`: `eq_short`, `sim_EQ_of_long`).
-/

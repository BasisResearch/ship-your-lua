import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.At.Unm

/-!
# `OP_UNM` on the location-list route

`lvm.c`'s `OP_UNM`: an integer `R[B]` is negated in place (`intop(-, 0, ib)`,
the machine's `neg`); a float is negated by the sign bit (no F1 value); any
other value goes to `luaT_trybinTM(L, rb, rb, ra, TM_UNM)` (`0x8001ec2c`, a
runtime metamethod call). The kernel (`δ .unm`) has a step for an integer and
for a string that converts to one (`str2int`: the string library's `__unm`,
reached through `luaT_trybinTM`), and none for the other values.

* the integer path is `unm_int`, the stuck values `unm_stuck`
  (`Kit/AtOps.lean`'s one-register `setR` shape);
* the string path runs `luaT_trybinTM` and the string metamethod, a runtime
  call that belongs with the `MMBIN`/`CALL` runtime summaries: it is the
  named premise `UnmStr_Statement` of `sim_UNM_of_str`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- **The string path of `OP_UNM`** (open; the `MMBIN`/`CALL` runtime-summary
work supplies it): from the arm's entry with a string in `R[B]`, the machine
runs `luaT_trybinTM` (`0x800194f4`) and the string library's `__unm`
(`lstrlib.c` `arith_unm`: `tonum`, `lua_arith`) to the fetch head, related to
the kernel's successor (`str2int`). -/
def UnmStr_Statement : Prop := ArmBody .UNM RegStr

theorem unm_int : ArmBody .UNM RegInt := by at_unary_int Lua.Vm.At.UNM 0x8001d8a4

/-- Neither an integer nor a string: no `Step` (`δ .unm` is `none`). -/
theorem unm_stuck : ArmBody .UNM UnaryOther := by
  at_unary_stuck 0x8001d8a4

/-- **`OP_UNM`** on the location-list route, given the string path. -/
theorem sim_UNM_of_str (hstr : UnmStr_Statement) :
    SimArmOn .UNM (Off FltB) :=
  sim_unary (by decide) unm_int hstr unm_stuck

end Lua.Vm.Sim.At

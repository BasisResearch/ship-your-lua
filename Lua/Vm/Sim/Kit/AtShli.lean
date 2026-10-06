import Lua.Vm.Sim.Kit.AtShift
import Lua.Vm.At.Shli

/-!
# `OP_SHLI` on the location-list route

`luaV_shiftl(sC, R[B])`: an integer `R[B]` is the amount (`bltz`, `blt`
against `±63`, `sll`/`srl`/`0`; `Kit/Shift.lean`) of the immediate `sC`
(`addiw a6, c, -127`, `sc_eq`), each path one instance of `at_shift`;
otherwise the fall-through to `MMBINI` (`at_fall1`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem shli_p1 : ArmBody .SHLI (Sh1 TagB amtB BitVec.msb qL) := by
  at_shift (at_int1 0x8001dd30) Lua.Vm.At.SHLI shiftlC_big
theorem shli_p2 : ArmBody .SHLI (Sh2 TagB amtB BitVec.msb qL) := by
  at_shift (at_int1 0x8001dd30) Lua.Vm.At.SHLI shiftlC_run
theorem shli_p3 : ArmBody .SHLI (Sh3 TagB amtB BitVec.msb rL) := by
  at_shift (at_int1 0x8001dd30) Lua.Vm.At.SHLI shiftlC_neg_big
theorem shli_p4 : ArmBody .SHLI (Sh4 TagB amtB BitVec.msb rL) := by
  at_shift (at_int1 0x8001dd30) Lua.Vm.At.SHLI shiftlC_neg_run
theorem shli_fall : ArmBody .SHLI fun p c s w ins =>
    ¬ TagB p c s w ins ∧ ¬ FltB p s ins := by
  at_fall1 Lua.Vm.At.SHLI 0x8001dd30

/-- **`OP_SHLI`** on the location-list route. -/
theorem sim_SHLI : SimArmOn .SHLI fun p s ins => ¬ FltB p s ins := sim_shift (by decide) _ _ _ shli_p1 shli_p2 shli_p3 shli_p4 shli_fall

end Lua.Vm.Sim.At

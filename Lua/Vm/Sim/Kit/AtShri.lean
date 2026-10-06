import Lua.Vm.Sim.Kit.AtShift
import Lua.Vm.At.Shri

/-!
# `OP_SHRI` on the location-list route

`luaV_shiftr(R[B], sC)`: an integer `R[B]` shifted by the immediate, the
machine branching on the field `C` (`bltu 127`, then `bgeu 63` or
`bltu 190`; `subw`/`negw`, `sll`/`srl`/`0`; `Kit/Shift.lean`, `shiftrK_*`),
each path one instance of `at_shift`; otherwise the fall-through to
`MMBINI` (`at_fall1`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem shri_p1 : ArmBody .SHRI (Sh1 TagB amtF pU qU) := by
  at_shift (at_int1 0x8001dd8c) Lua.Vm.At.SHRI shiftrK_big
theorem shri_p2 : ArmBody .SHRI (Sh2 TagB amtF pU qU) := by
  at_shift (at_int1 0x8001dd8c) Lua.Vm.At.SHRI shiftrK_run
theorem shri_p3 : ArmBody .SHRI (Sh3 TagB amtF pU rU) := by
  at_shift (at_int1 0x8001dd8c) Lua.Vm.At.SHRI shiftrK_neg_big
theorem shri_p4 : ArmBody .SHRI (Sh4 TagB amtF pU rU) := by
  at_shift (at_int1 0x8001dd8c) Lua.Vm.At.SHRI shiftrK_neg_run
theorem shri_fall : ArmBody .SHRI fun p c s w ins =>
    ¬ TagB p c s w ins ∧ ¬ FltB p s ins := by
  at_fall1 Lua.Vm.At.SHRI 0x8001dd8c

/-- **`OP_SHRI`** on the location-list route. -/
theorem sim_SHRI : SimArmOn .SHRI fun p s ins => ¬ FltB p s ins := sim_shift (by decide) _ _ _ shri_p1 shri_p2 shri_p3 shri_p4 shri_fall

end Lua.Vm.Sim.At

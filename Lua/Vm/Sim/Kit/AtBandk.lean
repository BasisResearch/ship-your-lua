import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.At.Bandk

/-!
# `OP_BANDK` on the location-list route

`op_bitwiseK(l_band)`: `R[B]` through `tointegerns` (an integer, else the
fall-through to `MMBINK`), `K[C]` read as `ivalue` with no tag test (the
kernel `bitwiseRK` exists only for an integer constant). Each path is one
instance of `Kit/AtOps.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem bandk_int : ArmBody .BANDK TagB := by at_bitk Lua.Vm.At.BANDK 0x8001d710 BitVec.and_comm
theorem bandk_fall : ArmBody .BANDK fun p c s w ins =>
    ¬ TagB p c s w ins ∧ ¬ FltB p s ins := by
  at_bitk_fall Lua.Vm.At.BANDK 0x8001d710

/-- **`OP_BANDK`** on the location-list route. -/
theorem sim_BANDK : SimArmOn .BANDK fun p s ins => ¬ FltB p s ins := sim_tagB (by decide) bandk_int bandk_fall

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.At.Bxork

/-!
# `OP_BXORK` on the location-list route

`op_bitwiseK(l_bxor)`: `R[B]` through `tointegerns` (an integer, else the
fall-through to `MMBINK`), `K[C]` read as `ivalue` with no tag test (the
kernel `bitwiseRK` exists only for an integer constant). Each path is one
instance of `Kit/AtOps.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem bxork_int : ArmBody .BXORK TagB := by at_bitk Lua.Vm.At.BXORK 0x8001d660 BitVec.xor_comm
theorem bxork_fall : ArmBody .BXORK FallB := by
  at_bitk_fall Lua.Vm.At.BXORK 0x8001d660

/-- **`OP_BXORK`** on the location-list route. -/
theorem sim_BXORK : SimArmOn .BXORK (Off FltB) := sim_tagB (by decide) bxork_int bxork_fall

end Lua.Vm.Sim.At

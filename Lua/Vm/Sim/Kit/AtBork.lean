import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.At.Bork

/-!
# `OP_BORK` on the location-list route

`op_bitwiseK(l_bor)`: `R[B]` through `tointegerns` (an integer, else the
fall-through to `MMBINK`), `K[C]` read as `ivalue` with no tag test (the
kernel `bitwiseRK` exists only for an integer constant). Each path is one
instance of `Kit/AtOps.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem bork_int : ArmBody .BORK TagB := by at_bitk Lua.Vm.At.BORK 0x8001d6b8 BitVec.or_comm
theorem bork_fall : ArmBody .BORK FallB := by
  at_bitk_fall Lua.Vm.At.BORK 0x8001d6b8

/-- **`OP_BORK`** on the location-list route. -/
theorem sim_BORK : SimArmOn .BORK (Off FltB) := sim_tagB (by decide) bork_int bork_fall

end Lua.Vm.Sim.At

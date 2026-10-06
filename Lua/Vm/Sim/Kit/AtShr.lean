import Lua.Vm.Sim.Kit.AtShift
import Lua.Vm.At.Shr

/-!
# `OP_SHR` on the location-list route

`op_bitwise(luaV_shiftr)`: both registers integers, then `luaV_shiftl` of
`0 - R[C]` inlined (`neg`, `bltz`, `blt` against `±63`, `sll`/`srl`/`0`;
`Kit/Shift.lean`, `shiftrC_*`), each path one instance of `at_shift`;
otherwise the fall-through to `MMBIN` (`at_fall`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem shr_p1 : ArmBody .SHR (Sh1 BothInt amtNC BitVec.msb qL) := by
  at_shift (kit_arith_ints 0x8001d57c) Lua.Vm.At.SHR shiftrC_big
theorem shr_p2 : ArmBody .SHR (Sh2 BothInt amtNC BitVec.msb qL) := by
  at_shift (kit_arith_ints 0x8001d57c) Lua.Vm.At.SHR shiftrC_run
theorem shr_p3 : ArmBody .SHR (Sh3 BothInt amtNC BitVec.msb rL) := by
  at_shift (kit_arith_ints 0x8001d57c) Lua.Vm.At.SHR shiftrC_neg_big
theorem shr_p4 : ArmBody .SHR (Sh4 BothInt amtNC BitVec.msb rL) := by
  at_shift (kit_arith_ints 0x8001d57c) Lua.Vm.At.SHR shiftrC_neg_run
theorem shr_fall : ArmBody .SHR fun p c s w ins => ¬ BothInt p c s w ins := by
  at_fall Lua.Vm.At.SHR 0x8001d57c

/-- **`OP_SHR`** on the location-list route. -/
theorem sim_SHR : SimArm .SHR := sim_shift (by decide) _ _ _ shr_p1 shr_p2 shr_p3 shr_p4 shr_fall

end Lua.Vm.Sim.At

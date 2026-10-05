import Lua.Vm.Sim.Kit.AtShift
import Lua.Vm.At.Shl

/-!
# `OP_SHL` on the location-list route

`op_bitwise(luaV_shiftl)`: both registers integers, then `luaV_shiftl`
inlined on the amount `R[C]` (`bltz`, `blt` against `±63`, `sll`/`srl`/`0`;
`Kit/Shift.lean`), each path one instance of `at_shift`; otherwise the
fall-through to `MMBIN` (`at_fall`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem shl_p1 : ArmBody .SHL (Sh1 BothInt amtC BitVec.msb qL) := by
  at_shift (kit_arith_ints 0x8001d5f0) Lua.Vm.At.SHL shiftlC_big
theorem shl_p2 : ArmBody .SHL (Sh2 BothInt amtC BitVec.msb qL) := by
  at_shift (kit_arith_ints 0x8001d5f0) Lua.Vm.At.SHL shiftlC_run
theorem shl_p3 : ArmBody .SHL (Sh3 BothInt amtC BitVec.msb rL) := by
  at_shift (kit_arith_ints 0x8001d5f0) Lua.Vm.At.SHL shiftlC_neg_big
theorem shl_p4 : ArmBody .SHL (Sh4 BothInt amtC BitVec.msb rL) := by
  at_shift (kit_arith_ints 0x8001d5f0) Lua.Vm.At.SHL shiftlC_neg_run
theorem shl_fall : ArmBody .SHL fun p c s w ins => ¬ BothInt p c s w ins := by
  at_fall Lua.Vm.At.SHL 0x8001d5f0

/-- **`OP_SHL`** on the location-list route. -/
theorem sim_SHL : SimArm .SHL := sim_shift (by decide) _ _ _ shl_p1 shl_p2 shl_p3 shl_p4 shl_fall

end Lua.Vm.Sim.At

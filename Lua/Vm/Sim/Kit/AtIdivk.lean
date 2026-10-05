import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.Sim.Kit.IdivEq
import Lua.Vm.At.Idivk

/-!
# `OP_IDIVK` on the location-list route

`savestate`, then `op_arithK(luaV_idiv)`: `sim_IDIV`'s paths with the
divisor `K[C]` (`dvK`, `kitk_ints`), each one instance of `Kit/AtOps.lean`.
The general case calls `__divdi3` and, when the operands' signs differ,
`__moddi3` (`idivC_eq`); both returns are generated rows of
`Lua/Vm/At/Idivk.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem idivk_zero : ArmBody .IDIVK (DivPath BothIntK dvK fun _ y => y = 0#64) := by
  kit_div_zero (kitk_ints 0x8001d768)

theorem idivk_m1 : ArmBody .IDIVK (DivPath BothIntK dvK fun _ y => y = -1#64) := by
  at_div_m1 (kitk_ints 0x8001d768) Lua.Vm.At.IDIVK Kit.idiv_m1

theorem idivk_same : ArmBody .IDIVK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.msb = y.msb) := by
  at_div_gen (kitk_ints 0x8001d768) Lua.Vm.At.IDIVK idivC_eq

theorem idivk_diff : ArmBody .IDIVK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.msb = y.msb ∧ True) := by
  at_div_gen (kitk_ints 0x8001d768) Lua.Vm.At.IDIVK idivC_eq

/-- Not both integers: the kernel's fall-through to `MMBINK`. -/
theorem idivk_fall : ArmBody .IDIVK fun p c s w ins => ¬ BothIntK p c s w ins := by
  at_fallK Lua.Vm.At.IDIVK 0x8001d768

/-- **`OP_IDIVK`** on the location-list route. -/
theorem sim_IDIVK : SimArm .IDIVK := sim_div (by decide) (fun x y => x.msb = y.msb) (fun _ _ => True)
  idivk_zero idivk_m1 idivk_same idivk_diff (fun {_} _ {_ _ _ _ _} _ _ _ _ hq => absurd trivial hq.2.2.2)
  idivk_fall

end Lua.Vm.Sim.At

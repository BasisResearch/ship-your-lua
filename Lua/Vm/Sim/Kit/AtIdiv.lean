import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.Sim.Kit.IdivEq
import Lua.Vm.At.Idiv

/-!
# `OP_IDIV` on the location-list route (B-SEGLOCAL, held-out case)

`savestate`, then `op_arith(luaV_idiv)`: `sim_div`'s paths, each ONE
declaration, an instance of `Kit/AtOps.lean`. The general case calls `__divdi3` (`divdi3_sum`) and, when the
operands' signs differ, `__moddi3` for the correction (`idivC_eq`); the two
helper returns are generated rows (`call_8001f740`, `call_8001f968`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem idiv_zero : ArmBody .IDIV (DivPath BothInt dvR fun _ y => y = 0#64) := by
  kit_div_zero (kit_arith_ints 0x8001deac)

theorem idiv_m1 : ArmBody .IDIV (DivPath BothInt dvR fun _ y => y = -1#64) := by
  at_div_m1 (kit_arith_ints 0x8001deac) Lua.Vm.At.IDIV Kit.idiv_m1

theorem idiv_same : ArmBody .IDIV (DivPath BothInt dvR fun x y => DivGen y ∧ x.msb = y.msb) := by
  at_div_gen (kit_arith_ints 0x8001deac) Lua.Vm.At.IDIV idivC_eq

theorem idiv_diff : ArmBody .IDIV (DivPath BothInt dvR fun x y => DivGen y ∧ ¬ x.msb = y.msb ∧ True) := by
  at_div_gen (kit_arith_ints 0x8001deac) Lua.Vm.At.IDIV idivC_eq

/-- Not both integers: the kernel's fall-through to `MMBIN`. -/
theorem idiv_fall : ArmBody .IDIV FallBC := by
  at_fall Lua.Vm.At.IDIV 0x8001deac

/-- **`OP_IDIV`** on the location-list route. -/
theorem sim_IDIV : SimArmOn .IDIV (Off FltBC) := sim_div (by decide) (fun x y => x.msb = y.msb) (fun _ _ => True)
  idiv_zero idiv_m1 idiv_same idiv_diff (fun {_} _ {_ _ _ _ _} _ _ _ _ hq => absurd trivial hq.2.2.2)
  idiv_fall

end Lua.Vm.Sim.At

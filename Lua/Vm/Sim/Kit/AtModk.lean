import Lua.Vm.Sim.Kit.AtOps
import Lua.Vm.At.Modk

/-!
# `OP_MODK` on the location-list route (B-SEGLOCAL refactor of `Kit/Modk.lean`)

The paths of `sim_div` (zero, minus one, the three general cases, the
fall-through), each ONE declaration: the kit's setup and forward kernel
evaluation, then `at_go`, the generated at-lemmas of `Lua/Vm/At/Modk.lean`
chained to the fetch head and closed. No `ArmPre`/`armBody_split`/`divFrame`:
the state at `__moddi3`'s return is a generated row (`call_8001f7bc`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem modk_zero : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = 0#64) := by
  kit_div_zero (kitk_ints 0x8001dad0)

theorem modk_m1 : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = -1#64) := by
  at_div_m1 (kitk_ints 0x8001dad0) Lua.Vm.At.MODK imod_m1

theorem modk_rz : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.srem y = 0#64) := by
  at_div_gen (kitk_ints 0x8001dad0) Lua.Vm.At.MODK imodC_eq

theorem modk_same : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    y.msb = (x.srem y).msb) := by
  at_div_gen (kitk_ints 0x8001dad0) Lua.Vm.At.MODK imodC_eq

theorem modk_corr : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    ¬ y.msb = (x.srem y).msb) := by
  at_div_gen (kitk_ints 0x8001dad0) Lua.Vm.At.MODK imodC_eq

/-- Not both integers: the kernel's fall-through to `MMBINK`. -/
theorem modk_fall : ArmBody .MODK FallBK := by
  at_fallK Lua.Vm.At.MODK 0x8001dad0

/-- **`OP_MODK`** on the location-list route. -/
theorem sim_MODK : SimArmOn .MODK (Off FltBK) := sim_div (by decide) _ _ modk_zero modk_m1 modk_rz modk_same
  modk_corr modk_fall

end Lua.Vm.Sim.At

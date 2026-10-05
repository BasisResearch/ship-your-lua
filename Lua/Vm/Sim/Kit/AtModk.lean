import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.Sim.Kit.AtArm
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

set_option hygiene false in
/-- A general `MODK` path: the setup, `luaV_mod` restated (`imodC_eq`), the run. -/
local macro "modk_gen" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩
  simp only [dvK] at hy hq
  kitk_ints 0x8001dad0
  have hz := fun e => hy (Or.inl e)
  simp only [Opnd.fill, δ, BinOp.int, imodC_eq _ _ hz] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.MODK))

theorem modk_zero : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = 0#64) := by
  kit_div_zero (kitk_ints 0x8001dad0)

theorem modk_m1 : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = -1#64) := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hm⟩
  simp only [dvK] at hm
  kitk_ints 0x8001dad0
  simp only [Opnd.fill, δ, BinOp.int, stackValueSize, hm, imod_m1] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.MODK

theorem modk_rz : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.srem y = 0#64) := by
  modk_gen

theorem modk_same : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    y.msb = (x.srem y).msb) := by
  modk_gen

theorem modk_corr : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    ¬ y.msb = (x.srem y).msb) := by
  modk_gen

/-- **`OP_MODK`** on the location-list route. -/
theorem sim_MODK : SimArm .MODK := sim_div (by decide) _ _ modk_zero modk_m1 modk_rz modk_same
  modk_corr fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kitk_fall 0x8001dad0

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.Arms

/-!
# `OP_MODK` by the direct kit

`savestate`, then `op_arithK(luaV_mod)`: `OP_MOD` (`Kit/Mod.lean`) with the
divisor `K[C]` (`Kit/K.lean`); the general case calls `__moddi3`
(`moddi3_sum`) and the paths are `sim_div`'s, with `imodC_eq`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem modk_zero : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = 0#64) := by
  kit_div_zero (kitk_ints 0x8001dad0)

theorem modk_m1 : ArmBody .MODK (DivPath BothIntK dvK fun _ y => y = -1#64) := by
  kit_div_m1 (kitk_ints 0x8001dad0) (w.k + 16 * ins.c) imod_m1

/-- The general case to `__moddi3`'s return (`0x8001f7bc`): `a0 = m % n`. -/
theorem modk_call : ArmPre .MODK (DivPath BothIntK dvK fun _ y => DivGen y) 0x8001f7bc
    (fun c s w ins => divFrame s w ins (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) (sign_extend ins)
      (slotVal c.σ.mem (w.k + 16 * ins.c)))
    (fun c w ins => (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.k + 16 * ins.c))) := by
  kit_div_pre (kitk_ints 0x8001dad0) (w.k + 16 * ins.c) 0x8002f7b0
    (moddi3_sum _ _ _ hframe? _ _ hz (by decide))

theorem modk_rz : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.srem y = 0#64) :=
  armBody_split (fun h => ⟨h.1, h.2.1⟩) modk_call (by
    kit_div_post (kitk_ints 0x8001dad0) (w.k + 16 * ins.c) imodC_eq [hq])

theorem modk_same : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    y.msb = (x.srem y).msb) :=
  armBody_split (fun h => ⟨h.1, h.2.1⟩) modk_call (by
    kit_div_post (kitk_ints 0x8001dad0) (w.k + 16 * ins.c) imodC_eq [hq.1, hq.2])

theorem modk_corr : ArmBody .MODK (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.srem y = 0#64 ∧
    ¬ y.msb = (x.srem y).msb) :=
  armBody_split (fun h => ⟨h.1, h.2.1⟩) modk_call (by
    kit_div_post (kitk_ints 0x8001dad0) (w.k + 16 * ins.c) imodC_eq [hq.1, hq.2])

theorem sim_MODK : SimArm .MODK := sim_div (by decide) _ _ modk_zero modk_m1 modk_rz modk_same modk_corr
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kitk_fall 0x8001dad0

end Lua.Vm.Sim.Kit

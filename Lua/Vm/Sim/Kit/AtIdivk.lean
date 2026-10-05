import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.IdivEq
import Lua.Vm.At.Idivk

/-!
# `OP_IDIVK` on the location-list route

`savestate`, then `op_arithK(luaV_idiv)`: `sim_IDIV`'s paths with the
divisor `K[C]` (`dvK`, `kitk_ints`), each ONE declaration. The general case
calls `__divdi3` and, when the operands' signs differ, `__moddi3`
(`idivC_eq`); both returns are generated rows of `Lua/Vm/At/Idivk.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
/-- A general `IDIVK` path: the setup, `luaV_idiv` restated (`idivC_eq`), the run. -/
local macro "idivk_gen" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩
  simp only [dvK] at hy hq
  kitk_ints 0x8001d768
  have hz := fun e => hy (Or.inl e)
  simp only [Opnd.fill, δ, BinOp.int, idivC_eq _ _ hz] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.IDIVK))

theorem idivk_zero : ArmBody .IDIVK (DivPath BothIntK dvK fun _ y => y = 0#64) := by
  kit_div_zero (kitk_ints 0x8001d768)

theorem idivk_m1 : ArmBody .IDIVK (DivPath BothIntK dvK fun _ y => y = -1#64) := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hm⟩
  simp only [dvK] at hm
  kitk_ints 0x8001d768
  simp only [Opnd.fill, δ, BinOp.int, hm, Kit.idiv_m1] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.IDIVK

theorem idivk_same : ArmBody .IDIVK (DivPath BothIntK dvK fun x y => DivGen y ∧ x.msb = y.msb) := by
  idivk_gen

theorem idivk_diff : ArmBody .IDIVK
    (DivPath BothIntK dvK fun x y => DivGen y ∧ ¬ x.msb = y.msb ∧ True) := by
  idivk_gen

/-- Not both integers: the kernel's fall-through to `MMBINK`, on the at-lemmas. -/
theorem idivk_fall : ArmBody .IDIVK fun p c s w ins => ¬ BothIntK p c s w ins := by
  rintro p hS c s s' w ins hA hf hop hstep hI
  kit_setup 0x8001d768
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hb vb hvb ins.b
  have hfb := hvb.ne_float; have hfk := hvk.ne_float
  simp [Opnd.fill] at hk; split at hk
  · rename_i heq
    obtain ⟨e1, e2⟩ := pair_eq heq; subst e1 e2
    exact absurd ⟨hvb.tag_of_int.1, hvk.tag_of_int.1⟩ hI
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · have hC : ¬ slotTag c.σ.mem (w.k + stackValueSize * ins.c) = BitVec.ofNat 8 vNumInt :=
      fun hC => hI ⟨hB, hC⟩
    at_go Lua.Vm.At.IDIVK
  · at_go Lua.Vm.At.IDIVK

/-- **`OP_IDIVK`** on the location-list route. -/
theorem sim_IDIVK : SimArm .IDIVK := sim_div (by decide) (fun x y => x.msb = y.msb) (fun _ _ => True)
  idivk_zero idivk_m1 idivk_same idivk_diff (fun {_} _ {_ _ _ _ _} _ _ _ _ hq => absurd trivial hq.2.2.2)
  idivk_fall

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.IdivEq
import Lua.Vm.At.Idiv

/-!
# `OP_IDIV` on the location-list route (B-SEGLOCAL, held-out case)

`savestate`, then `op_arith(luaV_idiv)`: `sim_div`'s paths, each ONE
declaration. The general case calls `__divdi3` (`divdi3_sum`) and, when the
operands' signs differ, `__moddi3` for the correction (`idivC_eq`); the two
helper returns are generated rows (`call_8001f740`, `call_8001f968`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
/-- A general `IDIV` path: the setup, `luaV_idiv` restated (`idivC_eq`), the run. -/
local macro "idiv_gen" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hy, hq⟩
  simp only [dvR] at hy hq
  kit_arith_ints 0x8001deac
  have hz := fun e => hy (Or.inl e)
  simp only [Opnd.fill, δ, BinOp.int, idivC_eq _ _ hz] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.IDIV))

theorem idiv_zero : ArmBody .IDIV (DivPath BothInt dvR fun _ y => y = 0#64) := by
  kit_div_zero (kit_arith_ints 0x8001deac)

theorem idiv_m1 : ArmBody .IDIV (DivPath BothInt dvR fun _ y => y = -1#64) := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨hI, hm⟩
  simp only [dvR] at hm
  kit_arith_ints 0x8001deac
  simp only [Opnd.fill, δ, BinOp.int, hm, Kit.idiv_m1] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  at_go Lua.Vm.At.IDIV

theorem idiv_same : ArmBody .IDIV (DivPath BothInt dvR fun x y => DivGen y ∧ x.msb = y.msb) := by
  idiv_gen

theorem idiv_diff : ArmBody .IDIV (DivPath BothInt dvR fun x y => DivGen y ∧ ¬ x.msb = y.msb ∧ True) := by
  idiv_gen

/-- Not both integers: the kernel's fall-through to `MMBIN`, on the at-lemmas. -/
theorem idiv_fall : ArmBody .IDIV fun p c s w ins => ¬ BothInt p c s w ins := by
  rintro p hS c s s' w ins hA hf hop hstep hI
  kit_setup 0x8001deac
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  kit_reg hb vb hvb ins.b; kit_reg hcc vc hvc ins.c
  have hfb := hvb.ne_float; have hfc := hvc.ne_float
  simp [Opnd.fill] at hk; split at hk
  · rename_i heq
    obtain ⟨e1, e2⟩ := pair_eq heq; subst e1 e2
    exact absurd ⟨hvb.tag_of_int.1, hvc.tag_of_int.1⟩ hI
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · have hC : ¬ slotTag c.σ.mem (w.slot ins.c) = BitVec.ofNat 8 vNumInt := fun hC => hI ⟨hB, hC⟩
    at_go Lua.Vm.At.IDIV
  · at_go Lua.Vm.At.IDIV

/-- **`OP_IDIV`** on the location-list route. -/
theorem sim_IDIV : SimArm .IDIV := sim_div (by decide) (fun x y => x.msb = y.msb) (fun _ _ => True)
  idiv_zero idiv_m1 idiv_same idiv_diff (fun {_} _ {_ _ _ _ _} _ _ _ _ hq => absurd trivial hq.2.2.2)
  idiv_fall

end Lua.Vm.Sim.At

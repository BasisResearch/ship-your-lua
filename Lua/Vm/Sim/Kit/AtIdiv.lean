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

/-- **`OP_IDIV`** on the location-list route. -/
theorem sim_IDIV : SimArm .IDIV := sim_div (by decide) (fun x y => x.msb = y.msb) (fun _ _ => True)
  idiv_zero idiv_m1 idiv_same idiv_diff (fun {_} _ {_ _ _ _ _} _ _ _ _ hq => absurd trivial hq.2.2.2)
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kit_arith_fall 0x8001deac

end Lua.Vm.Sim.At

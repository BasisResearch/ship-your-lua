import Lua.Vm.Sim.Kit.Cond
import Lua.Vm.Arms

/-!
# `OP_LT` by the direct kit (lane KIT-2)

`op_order(L, l_lti, LTnum, lessthanothers)`: two integers compare by `slt`
(`0x8001efec`), then `docondjump` (`kit_cond`). Off the float paths
(`FloatArms`); an integer against a non-number, or two non-numbers
other than two strings, go to `luaT_callorderTM`, where `δ .lt` is `none`
(the kernel is stuck). Two strings go to `l_strcmp` (`strcoll` → `strcmp`
over the string bytes): `sim_LT_of_str` takes that path as its premise.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [kraw_eq, bitb, mb_lt,
      bne_ite, ld_slot_gen (w.slot ins.a), ld_slot_gen (w.slot ins.b)])

theorem lt_int : ArmBody .LT BothIntAB := fun {p} hS {c s s' w ins} hA hf hop hstep hI => by
  kit_order_int 0x8001c894
    decide ((slotVal c.σ.mem (w.slot ins.a)).toInt < (slotVal c.σ.mem (w.slot ins.b)).toInt)

theorem lt_stuck : ArmBody .LT fun p c s w ins =>
    ¬ BothIntAB p c s w ins ∧ ¬ BothStrAB p c s w ins ∧ ¬ FltAB p s ins :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hT, hN⟩ => by kit_order_stuck 0x8001c894

/-- **`sim_LT` from the string path**: `SimArm .LT` holds as soon as the
run with two strings in `R[A]`, `R[B]` (`l_strcmp` → `strcoll`/`strcmp`
over the string bytes) is supplied. The bytes are described in the
complement `w.mo` only (`ValRepr.str`), while `strcmp` reads the live memory
and needs the `'\0'` after each string, which `TStringRepr` does not state:
a relation widening plus a `strcmp`/`strlen` summary (PHASES A1). -/
theorem sim_LT_of_str (hstr : ArmBody .LT BothStrAB) :
    SimArmOn .LT fun p s ins => ¬ FltAB p s ins :=
  sim_order (by decide) lt_int hstr lt_stuck

end Lua.Vm.Sim.Kit

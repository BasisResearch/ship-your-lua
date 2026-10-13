import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.Fn.SfRefMul

/-!
# `luai_nummul` on the join route (lane F1-F5)

`op_arithf(K)`'s `luai_nummul` is `__muldf3` (`Lua.Vm.Fn.Muldf3`, its level-2
equation `Muldf3.spec_proved : F = F64.mul`, lane float-sf3), a call node of
`scripts/gen_lua_at.py` (`FCALLS`). The compiler calls it with the operands
commuted (`__muldf3(c, b)`), so the stored float is the kernel's product by
`model_mul_comm`. The arms are `at_jarith`/`at_jarithK` (`Kit/AtJoinOps.lean`)
with this file's stored-float rule.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num

/-- `luai_nummul` commutes (`F64.mul_comm` through the round trip). -/
theorem model_mul_comm (a b : Float.Model) : Float.Model.mul a b = Float.Model.mul b a := by
  have h := F64.mul_comm a.toBits.toBitVec b.toBits.toBitVec
  rw [F64.mul_eq_model, F64.mul_eq_model, toModel_toBits, toModel_toBits] at h
  have := congrArg F64.toModel h
  rwa [toModel_toBits, toModel_toBits] at this

set_option hygiene false in
/-- A stored float computed by `__muldf3` (after `__floatdidf` for an
integer operand): its bits are the kernel's product's. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.Muldf3.S,
        Lua.Vm.Fn.Floatdidf.S, F64.mul_eq_model, toModel_toBits, toModel_ofInt, ofI, hxm, true_and,
        and_true, model_mul_comm]
      done))

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtJoinOps
import Lua.Vm.Fn.SfRefDiv
import Lua.Vm.Fn.FloorR

/-!
# `luai_numdiv` and `luai_numidiv` on the join route (lane F1-F6)

`op_arithf(K)`'s `luai_numdiv` is `__divdf3` (`Lua.Vm.Fn.Divdf3`, its level-2
equation `Divdf3.spec_proved : F = F64.div`, lane float-sf4), a call node of
`scripts/gen_lua_at.py` (`FCALLS`; its frame stores the caller's `s0`–`s3`,
`FRAME_G`, `Kit/AtFloat.lean`'s `divdf3_sumG`). `OP_DIV` and `OP_DIVK` have no
integer case (`rawArith .div`: always the float quotient), so their arms are
every path, not a float path family:

* `at_jarithA pc NS`: both operands by their per-operand views (`num_reg`:
  a float, an integer through `__floatdidf`, or no number, the fall-through
  to `MMBIN`), the kernel's `rawArith`, then `at_walk NS`;
* `at_jarithAK pc NS`: the same with the constant `K[C]` (`num_k`);
* the stored float of `__divdf3` (an `at_new_ext` rule).

The float paths of `OP_IDIV`/`OP_IDIVK` are `luai_numidiv`, `floor(a / b)`,
on `at_jarith`/`at_jarithK` (`Kit/AtJoinOps.lean`). The result is stored, so
`floor`'s call node is `FloorR` (`gen_lua_at.py` `FCALL_ARM`), whose result
is the reference `SfRef.floor`, the canonical datum of `Lua.Num.floor`
(`FloorR.S_bits`); the same stored-float rule covers it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num

set_option hygiene false in
/-- The first operand's tag facts (`num_reg`'s `htn`, `htn'`) kept under
names of their own before the second operand's view shadows them (`at_tags`
reads the context by name). -/
macro "at_keep_tags" : tactic => `(tactic| (
  have htb := htn
  clear htn
  try (have htb' := htn'; clear htn')))

set_option hygiene false in
/-- The kernel on the two views (`hn`, `hn'`): `rawArith`, the successor
substituted, then `at_walk NS`, on every goal. -/
macro "at_jarith_both " ns:ident : tactic => `(tactic| (
  all_goals
    simp only [Opnd.fill, fastArith, hn, hn'] at hk
    simp [Value.toNum?, Lua.Num.rawArith, BinOp.toOp, Lua.Num.numarith, Lua.Num.Numeral.toFloat,
      Value.ofNum, VState.apply, writeDefs, KEdge.kills] at hk
    subst hk
    at_walk $ns))

set_option hygiene false in
/-- **`at_jarithA pc NS`**: `op_arithf` on every operand class (`OP_DIV`):
`R[B]` and `R[C]` by their per-operand views, the kernel's `rawArith`, then
`at_walk NS`. -/
macro "at_jarithA " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  flt_views
  num_reg ins.b, hn
  all_goals at_keep_tags
  all_goals num_reg ins.c, hn'
  at_jarith_both $ns))

set_option hygiene false in
/-- **`at_jarithAK pc NS`**: `op_arithfK` on every operand class (`OP_DIVK`):
`at_jarithA` with the constant `K[C]` (`kitk_const`, `num_k`). -/
macro "at_jarithAK " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kitk_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  num_reg ins.b, hn
  all_goals at_keep_tags
  all_goals num_k hn'
  at_jarith_both $ns))

set_option hygiene false in
/-- A stored float computed by `__divdf3` (after `__floatdidf` for an
integer operand), or by `floor` of it (`luai_numidiv`, `FloorR.S_bits`): its
bits are the kernel's quotient's. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.FloorR.S_bits,
        Lua.Vm.Fn.Divdf3.S, Lua.Vm.Fn.Floatdidf.S, F64.div_eq_model, toModel_toBits, toModel_ofInt, ofI,
        hxm, true_and, and_true, Lua.Num.numidiv]
      done))

end Lua.Vm.Sim.At

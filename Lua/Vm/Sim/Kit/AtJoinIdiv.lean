import Lua.Vm.Sim.Kit.AtJoinDiv
import Lua.Vm.Fn.FloorR

/-!
# `luai_numidiv` on the join route (lane F1-F6)

`op_arithf(K)`'s float case of `OP_IDIV`/`OP_IDIVK` is `luai_numidiv`,
`floor(a / b)`: `__divdf3` (`Divdf3.spec_proved`), then libm `floor`. The
result is stored, so `floor`'s call node is `FloorR` (`gen_lua_at.py`
`FCALL_ARM`), whose result is the reference `SfRef.floor`, the canonical
datum of `Lua.Num.floor` (`FloorR.S_bits`). The arms are `at_jarith` /
`at_jarithK` (`Kit/AtJoinOps.lean`) with this file's stored-float rule.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num

set_option hygiene false in
/-- A stored float computed by `floor` of `__divdf3` (after `__floatdidf`
for an integer operand): its bits are the kernel's `luai_numidiv`'s. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.FloorR.S_bits,
        Lua.Vm.Fn.Divdf3.S, Lua.Vm.Fn.Floatdidf.S, F64.div_eq_model, toModel_toBits, toModel_ofInt, ofI,
        hxm, true_and, and_true, Lua.Num.numidiv]
      done))

end Lua.Vm.Sim.At

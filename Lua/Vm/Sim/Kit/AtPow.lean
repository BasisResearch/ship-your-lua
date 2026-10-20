import Lua.Vm.Sim.Kit.AtFmod
import Lua.Vm.Fn.PowQ

/-!
# libm's `pow` as a call node of the arms (lane F1-21)

`OP_POW`'s and `OP_POWK`'s `luai_numpow` calls `pow` when `b ≠ 2`: the call
node `PowQ` (`gen_lua_at.py` `FCALL_ARM`, `Lua.Vm.Fn.PowQ.sum`, the level (a)
`Pow.sum`). What its summary needs at the row is `fmod`'s
(`Kit/AtFmod.lean`: `at_fnSp'`, `at_gp`, `at_imp`), with its 320-byte window:

* `at_sIp`: the stack above `_impure_ptr` with room for `pow`'s window.

Its `errno` stores are the log's second window (`FOUTER`), whose fin lemma is
`AtFinE` (`Kit/AtErrno.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Layout

/-- The stack lies above `_impure_ptr` with room for `pow`'s window. -/
theorem at_sIp {X : Cx} (hX : X.Ok) : 8 + 320 + symImpurePtr ≤ X.w.sp := by
  have := hX.core.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry, symImpurePtr] at this ⊢
  omega

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.Sext32

/-!
# Narrow counts in callee rows (lane F1-20)

A 32-bit count the generator reads as its `Nat` (`gen_lua_at.py`: a root's
narrow word `rcellsw` with a `Nat` value, a `sw` then `lw` of a count in the
signed range): the machine's `lw` is `sign_extend` of `BitVec.ofNat 32 n`,
which is `BitVec.ofNat 64 n` below `2 ^ 31` (`fmt_sext32_ofNat`, the bound
from the root's facts). The hook fires only on a goal holding a 32-bit
literal (`at_narrow`), never matching the rewrite against other
`sign_extend`s (which unfolds past the recursion limit).
-/

open Lean Elab Tactic Meta

namespace Lua.Vm.Sim.Kit

/-- Fails unless the goal holds a `BitVec.ofNat 32 _`. -/
elab "at_has_ofNat32" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some _ := t.find? fun e =>
      e.isAppOfArity ``BitVec.ofNat 2 && e.appFn!.appArg!.nat? == some 32
    | throwError "at_has_ofNat32: none"

macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (at_has_ofNat32; rw [fmt_sext32_ofNat (by omega)]))

macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (fat_rd; at_has_ofNat32; rw [fmt_sext32_ofNat (by omega)]))

macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (at_has_ofNat32; rw [addiw32_ofNat (by omega) (by omega)]))

end Lua.Vm.Sim.Kit

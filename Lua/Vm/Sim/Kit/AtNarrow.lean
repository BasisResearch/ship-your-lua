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
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

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

/-- A word inside a stored zero doubleword (`sd zero`, then `lw`). -/
theorem fw4_in8_zero {m : Mem} {a x : Nat} (h1 : a ≤ x) (h2 : x + 4 ≤ a + 8) :
    bytesT4 (writeMap8 m a (sdData_val 0x0#64)) x = 0#32 := by
  obtain ⟨k, rfl⟩ : ∃ k, x = a + k := ⟨x - a, by omega⟩
  simp only [bytesT4]
  rw [show a + k + 3 = a + (k + 3) by omega, show a + k + 2 = a + (k + 2) by omega,
    show a + k + 1 = a + (k + 1) by omega, getElem_writeMap8 _ _ _ (k + 3) (by omega),
    getElem_writeMap8 _ _ _ (k + 2) (by omega), getElem_writeMap8 _ _ _ (k + 1) (by omega),
    getElem_writeMap8 _ _ _ k (by omega)]
  simp only [sdData_val]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) with rfl | rfl | rfl | rfl | rfl <;> decide

theorem sext32_zero : sign_extend (m := 64) (0#32) = 0#64 := by decide

/-- A 32-bit count's arithmetic (`sw`/`lw`, `addw` of a literal zero): the
loads forwarded (`fat_rd`), the words as their counts (`swData_ofNat`,
`extract_ofNat`), sums of literal words added, the sign extension of a small
count; a word inside a stored zero doubleword (`fw4_in8_zero`). -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (
      try fat_rd
      simp (disch := omega) only [swData_ofNat, extract_ofNat, BitVec.ofNat_add_ofNat, Nat.add_zero,
        Nat.zero_add, fmt_sext32_ofNat, sext32_zero, fw4_in8_zero]
      done))

end Lua.Vm.Sim.Kit

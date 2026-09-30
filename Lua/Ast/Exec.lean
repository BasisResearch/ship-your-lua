import Lua.Ast.Semantics

/-!
# The interpreter of `LuaSem`'s rulebook

`luaRun` runs a chunk with the generic rulebook interpreter
(`Lua.Rulebook.solve`) on `rules`: it is not written per construct. The
graph law `Lua.Rulebook.sem_iff_solve` makes it sound and complete for
`LuaSem` at once, so the kernel builds `LuaSem` derivations for concrete
programs by `decide +kernel` on a run (`luaRun_sound`), as
`Lua/Bytecode/Exec.lean` does for `BcSem` (`bcSem_of_run`).
-/

namespace Lua.Ast

open Lua.Bytecode (Host)
open Lua.Rulebook (solve solve_sound sem_iff_solve)

/-- Run a chunk from the empty environment: its output, if it completes
normally within `fuel` nested calls. -/
def luaRun (H : Host) (fuel : Nat) (c : Chunk) : Option String :=
  match (solve (rules H) fuel (.block [] "" c) : Option Outcome) with
  | some (_, out, .normal) => some out
  | _ => none

/-- **L-A1**: `LuaSem` is the graph of the interpreter. -/
theorem luaSem_iff_run {H : Host} {c : Chunk} {out : String} :
    LuaSem H c out ↔ ∃ fuel, luaRun H fuel c = some out := by
  constructor
  · rintro ⟨ρ', h⟩
    obtain ⟨n, e⟩ := sem_iff_solve.1 h
    exact ⟨n, by simp only [luaRun, e]⟩
  · rintro ⟨n, h⟩
    unfold luaRun at h
    split at h
    · rename_i ρ' out' e; cases h; exact ⟨ρ', solve_sound e⟩
    · cases h

/-- **Validation route**: a successful run of the interpreter is a
`LuaSem` derivation. -/
theorem luaRun_sound {H : Host} {fuel : Nat} {c : Chunk} {out : String}
    (h : luaRun H fuel c = some out) : LuaSem H c out :=
  luaSem_iff_run.2 ⟨fuel, h⟩

end Lua.Ast

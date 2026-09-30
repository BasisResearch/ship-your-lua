import Lua.Ast.Semantics

/-!
# Determinism of `LuaSem`

An instance of the generic `Lua.Rulebook.Sem.det`: a rulebook's relation is
the graph of a function. Translation validation (`Lua/Compile/TV.lean`) uses
this to turn one agreeing output into `∀ out, LuaSem s out ↔ BcSem p out`.
-/

namespace Lua.Ast

open Lua.Bytecode (Host)

/-- **`LuaSem` is deterministic.** -/
theorem LuaSem.deterministic {H : Host} {c : Chunk} {o o' : String} (h : LuaSem H c o)
    (h' : LuaSem H c o') : o = o' := by
  obtain ⟨_, he⟩ := h
  obtain ⟨_, he'⟩ := h'
  cases Lua.Rulebook.Sem.det he he'
  rfl

end Lua.Ast

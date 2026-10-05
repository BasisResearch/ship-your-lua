import Lean

/-!
# The `at_row` simp set

The rows and logs a generated at-lemma file names (`Lua/Vm/At/*`,
`scripts/gen_lua_at.py`) are `@[at_row]` abbreviations; the at-lemmas'
proofs unfold them by this set (`at_unfold`, `Lua/Vm/Sim/Kit/At.lean`).
-/

register_simp_attr at_row

/-- Log the at-lemma tactics' failed side conditions (debugging). -/
register_option at.debug : Bool := { defValue := false, descr := "log at_sep failures" }

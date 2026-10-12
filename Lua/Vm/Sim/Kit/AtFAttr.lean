import Lean

/-!
# The `at_fspec` simp set (lane float-m0)

A generated float arm's at-lemma file (`scripts/gen_lua_at.py` `FCALLS`)
names each soft-float call's result `f<k>` (and a framed helper's memory
`k<k>`): the rows hold `f<k> X`, never the lifted function, whose
definitional unfolding is exponential in its paths; the call's at-lemma
unfolds `f<k>` once (`at_fsite_delta`) and compares the arguments.
`f<k>_eq` (`@[at_fspec]`) is the result's specification (`SoftFloatSpec`).
-/

register_simp_attr at_fspec

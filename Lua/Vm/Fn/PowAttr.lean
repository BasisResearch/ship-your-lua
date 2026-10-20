import Lean

/-!
# The simp sets of `__ieee754_pow`'s level (b) (lane float-sf7)

`pw_lens`: the machine's normal form (the Int lens of `FmodLens` with the
routine's masks, and the float lens: soft-float results as the bits of their
model datum). `pw_mlens`: the model's words (`Int32`/`UInt32` as `ofInt` of
an `Int`). Both are applied by `Lua/Vm/Fn/PowLens.lean`'s tactics, with
`omega` as the discharger.
-/

register_simp_attr pw_lens
register_simp_attr pw_mlens

/-- The model's stages (`Lua/Vm/Fn/PowStage.lean`), unfolded at a leaf that
reaches one without a cut. -/
register_simp_attr pw_stage

/-- Print the walk's steps (`pw_walk`) to the standard output (debugging). -/
register_option pw.debug : Bool := {
  defValue := false
  descr := "print pw_walk's steps"
}

register_option pw.debug.goal : Bool := {
  defValue := false
  descr := "print the goal of each leaf pw_walk leaves open"
}

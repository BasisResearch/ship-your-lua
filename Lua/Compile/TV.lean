import Lua.Theorems
import Lua.Ast.Determinism
import Lua.Bytecode.Exec

/-!
# Translation validation (Layer B, B1)

For one concrete pair — an F1 source chunk `s` and the `Proto` `p` the host
`luac -s` produced for it — translation validation is a finite check:

* both semantics produce the same output string (`LuaSem` by the
  interpreter `luaRun` and `luaRun_sound`, `BcSem` by `run` and
  `bcSem_of_run`, both evaluated by `decide +kernel`);
* both semantics are deterministic (`LuaSem.deterministic`,
  `BcSem.deterministic`), so one agreeing output is *every* output:
  `∀ out, LuaSem s out ↔ BcSem p out` (`agree_of_outputs`).

`ProgramTV s p` packages this with `AstSupported s` and `Supported p`, and
`CompileTV.of_programTV` turns a compiler relation all of whose pairs are
validated into `CompileTV`, hence `compile_refinement_Statement`.
-/

namespace Lua.Compile

open Lua.Bytecode Lua.Ast Lua.Vm

/-- One output on each side is all outputs, by determinism of both
semantics. -/
theorem agree_of_outputs {s : Chunk} {p : Proto} {out : String}
    (hL : LuaSem binaryHost s out) (hB : BcSem binaryHost p out) :
    ∀ o, LuaSem binaryHost s o ↔ BcSem binaryHost p o := fun _ =>
  ⟨fun h => (LuaSem.deterministic hL h) ▸ hB, fun h => (BcSem.deterministic hB h) ▸ hL⟩

/-- A validated translation: supported on both sides, with the same
behaviours. -/
structure ProgramTV (s : Chunk) (p : Proto) : Prop where
  astSupported : AstSupported s
  supported : Supported p
  agree : ∀ out, LuaSem binaryHost s out ↔ BcSem binaryHost p out

/-- The validation route for one program: both sides supported, and one
common output. -/
theorem ProgramTV.of_outputs {s : Chunk} {p : Proto} {out : String} (hs : AstSupported s)
    (hp : Supported p) (hL : LuaSem binaryHost s out) (hB : BcSem binaryHost p out) :
    ProgramTV s p :=
  ⟨hs, hp, agree_of_outputs hL hB⟩

/-- A compiler relation all of whose pairs are validated meets the
translation-validation obligations. -/
theorem CompileTV.of_programTV {Compiles : Chunk → Proto → Prop}
    (h : ∀ s p, Compiles s p → ProgramTV s p) : CompileTV Compiles where
  supported s p hc _ := (h s p hc).supported
  forward s p out hc _ hL := ((h s p hc).agree out).1 hL
  backward s p out hc _ hB := ((h s p hc).agree out).2 hB

end Lua.Compile

import Lua.Compile.TV
import Lua.Ast.Exec
import Lua.Programs.Validation
import Lua.Programs.Supported
import Lua.Programs.F1OpsAst
import Lua.Programs.F1SrcAst
import Lua.Programs.F1Src

/-!
# Layer B on a corpus: `compile_refinement` for the host `luac`'s outputs

`CorpusCompiles` is the finite compiler relation "`p` is the host
`luac -s` output for `s`", listing the validated pairs: each source AST is
generated from the `.lua` file by `scripts/gen_ast.py` and each `Proto`
from the committed `.luac` chunk by `scripts/gen_proto.py` (check.sh stage
1 keeps both in sync with their inputs).

Per program, the expected output is the ELF's on the Sail model
(`c/tests/*.expected`). `LuaSem` is derived by the interpreter
(`luaRun_sound`), `BcSem` by the stepper (`bcSem_of_run`), both evaluated
by `decide +kernel`; determinism of both semantics gives the `↔`.

* `c/tests/f1_ops.lua`: numeric `for`, `//`/`%`, wraparound, `and`/`or`,
  `not`, comparisons, `while` (uses a multi-name `local`);
* `c/tests/f1_src.lua`: `if`/`elseif`/`else`, `repeat … until` over the
  body's locals, `break` out of `while`/`for`/`repeat` (also from inside an
  `if`), shadowing, `local` with missing and extra values.

`while.lua` needs `goto`, and `print_print.lua` reads the global `print`
as a value; both are outside the F1 AST.
-/

namespace Lua.Compile

open Lua.Bytecode Lua.Ast Lua.Vm Lua.Programs

/-! ## `c/tests/f1_ops.lua` -/

/-- `c/tests/f1_ops.expected`. -/
def f1OpsOut : String :=
  "385\n10\n7\n4\n1\n-3\t-2\t-4\t1\t-7\t-7\n-9223372036854775808\t-2\t-9223372036854775808\n-9223372036854775808\t0\n5\t6\ttrue\tfalse\ttrue\ttrue\tfalse\n8\ttrue\tfalse\ttrue\tfalse\n7\t2187\ttrue\tfalse\n"

theorem f1Ops_astSupported : AstSupported f1OpsAst := by unfold AstSupported; decide +kernel

theorem f1Ops_luaSem : LuaSem binaryHost f1OpsAst f1OpsOut :=
  luaRun_sound (fuel := 100) (by decide +kernel)

/-- **Translation validation of `f1_ops.lua`**: the source and the binary's
output agree on both semantics. -/
theorem f1Ops_tv_pair : LuaSem binaryHost f1OpsAst f1OpsOut ∧ BcSem binaryHost f1OpsProto f1OpsOut :=
  ⟨f1Ops_luaSem, f1Ops_bcSem⟩

theorem f1Ops_tv : ProgramTV f1OpsAst f1OpsProto :=
  .of_outputs f1Ops_astSupported f1Ops_supported f1Ops_tv_pair.1 f1Ops_tv_pair.2

theorem f1Ops_agree : ∀ out, LuaSem binaryHost f1OpsAst out ↔ BcSem binaryHost f1OpsProto out :=
  f1Ops_tv.agree

/-! ## `c/tests/f1_src.lua` -/

/-- `c/tests/f1_src.expected`. -/
def f1SrcOut : String :=
  "1\t2\tnil\tnil\n3\n38\n4\n10\t8\n4\n4\n19\ntrue\n3\n3\t2\t7\tnil\n"

theorem f1Src_astSupported : AstSupported f1SrcAst := by unfold AstSupported; decide +kernel

theorem f1Src_supported : Supported f1SrcProto := by decide +kernel

theorem f1Src_luaSem : LuaSem binaryHost f1SrcAst f1SrcOut :=
  luaRun_sound (fuel := 100) (by decide +kernel)

theorem f1Src_bcSem : BcSem binaryHost f1SrcProto f1SrcOut :=
  bcSem_of_run (n := 4000) (by decide +kernel)

/-- **Translation validation of `f1_src.lua`**. -/
theorem f1Src_tv_pair : LuaSem binaryHost f1SrcAst f1SrcOut ∧ BcSem binaryHost f1SrcProto f1SrcOut :=
  ⟨f1Src_luaSem, f1Src_bcSem⟩

theorem f1Src_tv : ProgramTV f1SrcAst f1SrcProto :=
  .of_outputs f1Src_astSupported f1Src_supported f1Src_tv_pair.1 f1Src_tv_pair.2

theorem f1Src_agree : ∀ out, LuaSem binaryHost f1SrcAst out ↔ BcSem binaryHost f1SrcProto out :=
  f1Src_tv.agree

/-! ## The corpus relation -/

/-- The host `luac -s`'s output on the validated corpus. -/
inductive CorpusCompiles : Chunk → Proto → Prop where
  | f1Ops : CorpusCompiles f1OpsAst f1OpsProto
  | f1Src : CorpusCompiles f1SrcAst f1SrcProto

theorem corpus_programTV : ∀ s p, CorpusCompiles s p → ProgramTV s p
  | _, _, .f1Ops => f1Ops_tv
  | _, _, .f1Src => f1Src_tv

/-- The translation-validation obligations for the corpus. -/
theorem corpus_compileTV : CompileTV CorpusCompiles := CompileTV.of_programTV corpus_programTV

/-- **Layer B on the corpus** (B1 exit): `compile_refinement_Statement` for
the host `luac`'s outputs on the validated programs. -/
theorem compile_refinement_corpus : compile_refinement_Statement CorpusCompiles :=
  compile_refinement_of_tv corpus_compileTV

end Lua.Compile

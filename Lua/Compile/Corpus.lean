import Lua.Compile.TV
import Lua.Ast.Exec
import Lua.Programs.Validation
import Lua.Programs.Supported
import Lua.Programs.F1OpsAst
import Lua.Programs.F1SrcAst
import Lua.Programs.WhileAst
import Lua.Programs.F1bBitsAst
import Lua.Programs.F1Src

/-!
# Layer B on a corpus: `compile_refinement` for the host `luac`'s outputs

`CorpusCompiles` is the finite compiler relation "`p` is the host
`luac -s` output for `s`", listing the validated pairs: each source AST is
generated from the `.lua` file by `scripts/gen_ast.py` (a parser for all of
Lua 5.4) and each `Proto` from the committed `.luac` chunk by
`scripts/gen_proto.py` (check.sh stage 1 keeps both in sync with their
inputs).

Per program, the expected output is the ELF's on the Sail model
(`c/tests/*.expected`). `AstSupported` and `Supported` are decided by the
kernel, `LuaSem` is derived by the interpreter (`luaRun_sound`), `BcSem` by
the stepper (`bcSem_of_run`), both evaluated by `decide +kernel`;
determinism of both semantics gives the `↔`.

* `c/tests/while.lua`: `while` loops, `break`, and `goto continue` to a
  label at the end of the loop body;
* `c/tests/f1_ops.lua`: numeric `for`, `//`/`%`, wraparound, `and`/`or`,
  `not`, comparisons, `while` (uses a multi-name `local`);
* `c/tests/f1_src.lua`: `if`/`elseif`/`else`, `repeat … until` over the
  body's locals, `break` out of `while`/`for`/`repeat` (also from inside an
  `if`), shadowing, `local` with missing and extra values;
* `c/tests/f1b_bits.lua`: the integer bitwise operators `& | ~ << >>` and
  unary `~`, with `luaV_shiftl`'s edge cases.

Every `print(…)` is a call of the global `print`, looked up in `_ENV`.
`print_print.lua` passes `print` itself as an argument, whose rendering is
an address in the binary; it is outside `AstSupported`.
-/

namespace Lua.Compile

open Lua.Bytecode Lua.Ast Lua.Vm Lua.Programs

/-! ## `c/tests/while.lua` -/

/-- `c/tests/while.expected`. -/
def whileOut : String := "55\n2500\n36\n"

theorem while_astSupported : AstSupported whileAst := by decide +kernel

theorem while_luaSem : LuaSem binaryHost whileAst whileOut :=
  luaRun_sound (fuel := 1000) (by decide +kernel)

/-- **Translation validation of `while.lua`**: the source and the binary's
output agree on both semantics. -/
theorem while_tv_pair : LuaSem binaryHost whileAst whileOut ∧ BcSem binaryHost whileProto whileOut :=
  ⟨while_luaSem, while_bcSem⟩

theorem while_tv : ProgramTV whileAst whileProto :=
  .of_outputs while_astSupported while_supported while_tv_pair.1 while_tv_pair.2

/-! ## `c/tests/f1_ops.lua` -/

/-- `c/tests/f1_ops.expected`. -/
def f1OpsOut : String :=
  "385\n10\n7\n4\n1\n-3\t-2\t-4\t1\t-7\t-7\n-9223372036854775808\t-2\t-9223372036854775808\n-9223372036854775808\t0\n5\t6\ttrue\tfalse\ttrue\ttrue\tfalse\n8\ttrue\tfalse\ttrue\tfalse\n7\t2187\ttrue\tfalse\n"

theorem f1Ops_astSupported : AstSupported f1OpsAst := by decide +kernel

theorem f1Ops_luaSem : LuaSem binaryHost f1OpsAst f1OpsOut :=
  luaRun_sound (fuel := 1000) (by decide +kernel)

/-- **Translation validation of `f1_ops.lua`**. -/
theorem f1Ops_tv_pair : LuaSem binaryHost f1OpsAst f1OpsOut ∧ BcSem binaryHost f1OpsProto f1OpsOut :=
  ⟨f1Ops_luaSem, f1Ops_bcSem⟩

theorem f1Ops_tv : ProgramTV f1OpsAst f1OpsProto :=
  .of_outputs f1Ops_astSupported f1Ops_supported f1Ops_tv_pair.1 f1Ops_tv_pair.2

/-! ## `c/tests/f1_src.lua` -/

/-- `c/tests/f1_src.expected`. -/
def f1SrcOut : String :=
  "1\t2\tnil\tnil\n3\n38\n4\n10\t8\n4\n4\n19\ntrue\n3\n3\t2\t7\tnil\n"

theorem f1Src_astSupported : AstSupported f1SrcAst := by decide +kernel

theorem f1Src_supported : Supported f1SrcProto := by decide +kernel

theorem f1Src_luaSem : LuaSem binaryHost f1SrcAst f1SrcOut :=
  luaRun_sound (fuel := 1000) (by decide +kernel)

theorem f1Src_bcSem : BcSem binaryHost f1SrcProto f1SrcOut :=
  bcSem_of_run (n := 4000) (by decide +kernel)

/-- **Translation validation of `f1_src.lua`**. -/
theorem f1Src_tv_pair : LuaSem binaryHost f1SrcAst f1SrcOut ∧ BcSem binaryHost f1SrcProto f1SrcOut :=
  ⟨f1Src_luaSem, f1Src_bcSem⟩

theorem f1Src_tv : ProgramTV f1SrcAst f1SrcProto :=
  .of_outputs f1Src_astSupported f1Src_supported f1Src_tv_pair.1 f1Src_tv_pair.2

/-! ## `c/tests/f1b_bits.lua` -/

/-- `c/tests/f1b_bits.expected`. -/
def f1bOut : String :=
  "2640\t24570\t21930\t-23131\t-1\n90\t23386\t42405\t9223372036854775807\n9223372036854775807\t1\t-9223372036854775808\t1445\t370080\n0\t0\t0\t2891\t185040\t0\t0\n96\t0\t0\t224\t0\t2\t9223372036854775804\n72624976668147841\t129\t72624976668147712\n833130\ttrue\ttrue\n"

theorem f1b_astSupported : AstSupported f1bAst := by decide +kernel

theorem f1b_luaSem : LuaSem binaryHost f1bAst f1bOut :=
  luaRun_sound (fuel := 1000) (by decide +kernel)

/-- **Translation validation of `f1b_bits.lua`**. -/
theorem f1b_tv_pair : LuaSem binaryHost f1bAst f1bOut ∧ BcSem binaryHost f1bProto f1bOut :=
  ⟨f1b_luaSem, f1b_bcSem⟩

theorem f1b_tv : ProgramTV f1bAst f1bProto :=
  .of_outputs f1b_astSupported f1b_supported f1b_tv_pair.1 f1b_tv_pair.2

/-! ## The corpus relation -/

/-- The host `luac -s`'s output on the validated corpus. -/
inductive CorpusCompiles : Chunk → Proto → Prop where
  | while_ : CorpusCompiles whileAst whileProto
  | f1Ops : CorpusCompiles f1OpsAst f1OpsProto
  | f1Src : CorpusCompiles f1SrcAst f1SrcProto
  | f1b : CorpusCompiles f1bAst f1bProto

theorem corpus_programTV : ∀ s p, CorpusCompiles s p → ProgramTV s p
  | _, _, .while_ => while_tv
  | _, _, .f1Ops => f1Ops_tv
  | _, _, .f1Src => f1Src_tv
  | _, _, .f1b => f1b_tv

/-- The translation-validation obligations for the corpus. -/
theorem corpus_compileTV : CompileTV CorpusCompiles := CompileTV.of_programTV corpus_programTV

/-- **Layer B on the corpus** (B1 exit): `compile_refinement_Statement` for
the host `luac`'s outputs on the validated programs. -/
theorem compile_refinement_corpus : compile_refinement_Statement CorpusCompiles :=
  compile_refinement_of_tv corpus_compileTV

end Lua.Compile

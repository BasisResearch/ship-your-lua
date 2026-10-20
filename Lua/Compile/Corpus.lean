import Lua.Compile.TV
import Lua.Ast.Exec
import Lua.Programs.Validation
import Lua.Programs.Supported
import Lua.Programs.F1OpsAst
import Lua.Programs.F1SrcAst
import Lua.Programs.WhileAst
import Lua.Programs.F1bBitsAst
import Lua.Programs.F1Src
import Lua.Programs.Escape
import Lua.Programs.EscStrfltAst
import Lua.Programs.EscForstrAst
import Lua.Programs.EscUnmfltAst
import Lua.Programs.F3Float
import Lua.Programs.F3FloatAst
import Lua.Programs.F3Floop
import Lua.Programs.F3FloopAst
import Lua.Programs.PowFold
import Lua.Programs.PowFoldAst
import Lua.Compile.Consts

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
  unary `~`, with `luaV_shiftl`'s edge cases;
* `c/tests/stuck/s_{strflt,forstr,unmflt}.lua`: string coercion to floats
  (`"1.5" + 1`, `-"1.5"`) and a coerced `for` limit (`for i = 1, "2"`), the
  former escapes (FLOAT-DESIGN.md S1/S2; outputs from the ELF on the Sail
  model, `abstractions/ledger/f1-lane-5.md`);
* `c/tests/f3_float.lua`, `c/tests/f3_floop.lua`: float numerals, `/` and
  `^` (FLOAT-DESIGN.md S3), with the folds `luac` makes checked against the
  model (`corpus_kAccounted`) and the parser's numerals against
  `luaO_str2num` (`corpus_lexOk`). `c/tests/fold/powfold.lua`, a `^` folded
  with the host's `pow`, is the counterexample outside `AstSupported`
  (`powFold_counterexample`).

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

/-! ## The former escapes: floats from string coercion -/

theorem escStrflt_astSupported : AstSupported escStrfltAst := by decide +kernel
theorem escForstr_astSupported : AstSupported escForstrAst := by decide +kernel
theorem escUnmflt_astSupported : AstSupported escUnmfltAst := by decide +kernel

theorem escStrflt_luaSem : LuaSem binaryHost escStrfltAst "2.5\n" :=
  luaRun_sound (fuel := 100) (by decide +kernel)
theorem escForstr_luaSem : LuaSem binaryHost escForstrAst "1\n2\n" :=
  luaRun_sound (fuel := 100) (by decide +kernel)
theorem escUnmflt_luaSem : LuaSem binaryHost escUnmfltAst "-1.5\n" :=
  luaRun_sound (fuel := 100) (by decide +kernel)

/-- **Translation validation of `"1.5" + 1`**: `2.5` on both semantics. -/
theorem escStrflt_tv : ProgramTV escStrfltAst escStrfltProto :=
  .of_outputs escStrflt_astSupported escStrflt_supported escStrflt_luaSem escStrflt_bcSem
theorem escForstr_tv : ProgramTV escForstrAst escForstrProto :=
  .of_outputs escForstr_astSupported escForstr_supported escForstr_luaSem escForstr_bcSem
theorem escUnmflt_tv : ProgramTV escUnmfltAst escUnmfltProto :=
  .of_outputs escUnmflt_astSupported escUnmflt_supported escUnmflt_luaSem escUnmflt_bcSem

/-! ## Floats: numerals, `/` and `^` (FLOAT-DESIGN.md S3) -/

/-- `c/tests/f3_float.expected`. -/
def f3FloatOut : String :=
  "1.5\t0.25\t3.0\t1e+15\t0.0025\t16.0\t0.5\tinf\t9.2233720368548e+18\n6.0\t1.5\t3.5\t0.33333333333333\tinf\t-inf\t0.0\t3.3333333333333\n9.0\t1.1066819197003\t0.5\t8.0\t0.33333333333333\t2.25\t2.25\t9.0\n-0.0\t-0.0\t-inf\tnan\t-nan\tnan\n0.3\tfalse\ttrue\t3.0\t0.5\tinf\t-4.0\n"

/-- `c/tests/f3_floop.expected`. -/
def f3FloopOut : String :=
  "1.875\n0.5\t0.25\t0.70710678118655\t2.0\n1.5\t2.25\t1.2247448713916\t0.66666666666667\n0.001\ttrue\n"

theorem f3Float_astSupported : AstSupported f3FloatAst := by decide +kernel
theorem f3Floop_astSupported : AstSupported f3FloopAst := by decide +kernel

theorem f3Float_supported : Supported f3FloatProto := by decide +kernel
theorem f3Floop_supported : Supported f3FloopProto := by decide +kernel

theorem f3Float_luaSem : LuaSem binaryHost f3FloatAst f3FloatOut :=
  luaRun_sound (fuel := 100) (by decide +kernel)
theorem f3Floop_luaSem : LuaSem binaryHost f3FloopAst f3FloopOut :=
  luaRun_sound (fuel := 100) (by decide +kernel)

theorem f3Float_bcSem : BcSem binaryHost f3FloatProto f3FloatOut :=
  bcSem_of_run (n := 200) (by decide +kernel)
theorem f3Floop_bcSem : BcSem binaryHost f3FloopProto f3FloopOut :=
  bcSem_of_run (n := 400) (by decide +kernel)

/-- **Translation validation of `f3_float.lua`**: float numerals (decimal,
hex, overflowing to `inf`, an integer numeral too large for an integer),
`/` (folded `7 / 2`, `1 / 3`; unfolded division by zero), `^` at run time
and folded with the exponent `2`, `-0.0` and NaN signs, folded `//`, `%`. -/
theorem f3Float_tv : ProgramTV f3FloatAst f3FloatProto :=
  .of_outputs f3Float_astSupported f3Float_supported f3Float_luaSem f3Float_bcSem

/-- **Translation validation of `f3_floop.lua`**: float `for` loops, `/` and
`^` on loop values, a float `while` condition. -/
theorem f3Floop_tv : ProgramTV f3FloopAst f3FloopProto :=
  .of_outputs f3Floop_astSupported f3Floop_supported f3Floop_luaSem f3Floop_bcSem

/-! ## Numerals and folded constants -/

/-- **The parser's numerals are `luaO_str2num`'s** on every corpus program
(and on the counterexample below). -/
theorem corpus_lexOk :
    [whileAstNumerals, f1OpsAstNumerals, f1SrcAstNumerals, f1bAstNumerals,
      escStrfltAstNumerals, escForstrAstNumerals, escUnmfltAstNumerals,
      f3FloatAstNumerals, f3FloopAstNumerals, powFoldAstNumerals].all LexOk = true := by
  decide +kernel

/-- **Every float constant `luac` put in a corpus chunk is the model's**: a
float numeral or a fold computed by `Lua.Num` (`KAccounted`). -/
theorem corpus_kAccounted :
    [(whileAst, whileProto), (f1OpsAst, f1OpsProto), (f1SrcAst, f1SrcProto),
      (f1bAst, f1bProto), (escStrfltAst, escStrfltProto), (escForstrAst, escForstrProto),
      (escUnmfltAst, escUnmfltProto), (f3FloatAst, f3FloatProto),
      (f3FloopAst, f3FloopProto)].all (fun sp => KAccounted sp.1 sp.2) = true := by
  decide +kernel

/-! ## The counterexample: `^` folded with the host's `pow`

`c/tests/fold/powfold.lua` compares a folded `0.5 ^ -0.5` with the same
`^` at run time. Host `luac` folds it with glibc's `pow` to
`0x3ff6a09e667f3bcd` (`K[3]`); the ELF's `^` is newlib's, `0x3ff6a09e667f3bcc`
(1 ulp apart; of 33,092 pairs of short decimal operands, 3,127 differ:
`abstractions/ledger/b-s3.md`). The ELF on the Sail model prints `false`
(`c/tests/fold/powfold.expected`), the source semantics `true`: no
translation validation holds, so `AstSupported` excludes a `^` that `luac`
may fold (`powOk`). -/

/-- `luac`'s folded constant is not the model's fold. -/
theorem powFold_kfold : KAccounted powFoldAst powFoldProto = false := by decide +kernel

/-- The source semantics: `0.5 ^ -0.5 == a ^ b` is `true`. -/
theorem powFold_luaSem : LuaSem binaryHost powFoldAst "true\n" :=
  luaRun_sound (fuel := 100) (by decide +kernel)

/-- The bytecode semantics of `luac`'s chunk: `false`, as the ELF prints. -/
theorem powFold_bcSem : BcSem binaryHost powFoldProto "false\n" :=
  bcSem_of_run (n := 100) (by decide +kernel)

/-- **The counterexample**: source and bytecode disagree on `powfold.lua`. -/
theorem powFold_counterexample :
    ¬ ∀ out, LuaSem binaryHost powFoldAst out ↔ BcSem binaryHost powFoldProto out := fun h =>
  absurd (BcSem.deterministic ((h _).1 powFold_luaSem) powFold_bcSem) (by decide)

/-- `powfold.lua` is outside `AstSupported` (`powOk`). -/
theorem powFold_not_astSupported : ¬ AstSupported powFoldAst := by decide +kernel

/-! ## The corpus relation -/

/-- The host `luac -s`'s output on the validated corpus. -/
inductive CorpusCompiles : Chunk → Proto → Prop where
  | while_ : CorpusCompiles whileAst whileProto
  | f1Ops : CorpusCompiles f1OpsAst f1OpsProto
  | f1Src : CorpusCompiles f1SrcAst f1SrcProto
  | f1b : CorpusCompiles f1bAst f1bProto
  | escStrflt : CorpusCompiles escStrfltAst escStrfltProto
  | escForstr : CorpusCompiles escForstrAst escForstrProto
  | escUnmflt : CorpusCompiles escUnmfltAst escUnmfltProto
  | f3Float : CorpusCompiles f3FloatAst f3FloatProto
  | f3Floop : CorpusCompiles f3FloopAst f3FloopProto

theorem corpus_programTV : ∀ s p, CorpusCompiles s p → ProgramTV s p
  | _, _, .while_ => while_tv
  | _, _, .f1Ops => f1Ops_tv
  | _, _, .f1Src => f1Src_tv
  | _, _, .f1b => f1b_tv
  | _, _, .escStrflt => escStrflt_tv
  | _, _, .escForstr => escForstr_tv
  | _, _, .escUnmflt => escUnmflt_tv
  | _, _, .f3Float => f3Float_tv
  | _, _, .f3Floop => f3Floop_tv

/-- The translation-validation obligations for the corpus. -/
theorem corpus_compileTV : CompileTV CorpusCompiles := CompileTV.of_programTV corpus_programTV

/-- **Layer B on the corpus** (B1 exit): `compile_refinement_Statement` for
the host `luac`'s outputs on the validated programs. -/
theorem compile_refinement_corpus : compile_refinement_Statement CorpusCompiles :=
  compile_refinement_of_tv corpus_compileTV

end Lua.Compile

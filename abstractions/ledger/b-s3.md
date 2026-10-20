# Lane B-S3: Layer B with float numerals, `/` and `^` (FLOAT-DESIGN.md S3)

Base: main `e4b68d8`. CPU and peak memory are one `lake env lean <file>`
each (`/usr/bin/time -v`, `LEAN_NUM_THREADS=4`).

## Result

| target | status | where |
|---|---|---|
| float numerals in `LuaSem` | **one rulebook arm** | `rules`: `.numeral (.float b) ↦ Const.toValue? (.float b)` (the value `LOADK` loads), `Lua/Ast/Semantics.lean` |
| `/`, `^` in `LuaSem` | already `Value.arith` (lane float-s1) | `binOp` |
| `AstSupported` with numerals, `/`, `^` | **decidable**, extended | `supE`, `binOk`, `powOk`, `mayFold` |
| a `^` `luac` may fold | **excluded** (`powOk`) | counterexample below |
| the parser's numerals are `luaO_str2num`'s | **proved** on the corpus | `corpus_lexOk` over the generated `<name>Numerals` (`gen_ast.py`), `LexOk` (`Lua/Compile/Consts.lean`) |
| `luac`'s float constants are the model's | **proved** on the corpus | `corpus_kAccounted`, `KAccounted`/`foldK` (`constfolding` on `Value.arith`) |
| corpus TV | **proved** | `f3Float_tv`, `f3Floop_tv`; `corpus_compileTV`, `compile_refinement_corpus` (9 programs) |
| the host-`pow` fold | **machine-checked counterexample** | `powFold_counterexample`, `powFold_kfold`, `powFold_not_astSupported` |

Axioms: all `[propext, Classical.choice, Quot.sound]`;
`powFold_not_astSupported` `[propext]` (check.sh stage 6). `scripts/check.sh`:
all stages OK; `abstractions/gate.py`: ok.

## The exclusion (FLOAT-DESIGN.md §5 R5)

`luac` (`lcode.c` `constfolding` → `luaO_rawarith` → `luai_numpow`) folds a
`^` of numeric constants with the build host's libm `pow` (glibc); the
ELF's `^` and `Lua.Num.numpow` are newlib's fdlibm.

* Host probe: 33,092 pairs of short decimal operands (`x, y` from
  integers −20…49, tenths, quarters and a few others; `y ≠ 2`), Python's
  `math.pow` (glibc) against `Lua.Num.numpow` in Lean: **3,127 differ**,
  each by 1 ulp (1,578 low, 1,549 high).
* `c/tests/fold/powfold.lua`: `local a, b = 0.5, -0.5; print(0.5 ^ -0.5 == a ^ b)`.
  `luac -s` folds the left side to `K[3] = 0x3ff6a09e667f3bcd`; newlib gives
  `0x3ff6a09e667f3bcc`. The ELF on Sail prints `false`
  (`powfold.expected`); host `lua` prints `true`; `LuaSem` gives `true`
  (`powFold_luaSem`), `BcSem` `false` (`powFold_bcSem`).
* The condition `powOk`: a `^` is in F1 unless both operands `mayFold`
  (numerals, through parentheses, unary `-`/`~`, folding operators and
  `<const>` locals: an over-approximation of `tonumeral` after
  `constfolding`), except with the exponent the numeral `2`
  (`luai_numpow`'s `a*a` on both sides; `-2 ^ 2` in `f3_float.lua` is
  folded to `LOADF -4`, accounted for).
* Random fold probe (scratch, seeded): 400 nested constant expressions over
  `+ - * / // %`, unary `-` and `^ 2` (291 distinct float constants): **0**
  not the model's. 400 `x ^ y` of constant numerals (211 float constants):
  **20** not the model's. `/` folds agree with IEEE as expected;
  `constfolding` refuses `0/0`, `1/0`, `0.0/1`, `-0.0` (zero and NaN
  results), which run at run time (`f3_float.lua` line 4–6).

## Corpus additions

| program | content | ELF on Sail | steps |
|---|---|---|---|
| `c/tests/f3_float.lua` | float numerals (decimal, hex `0x1p4`, `0x.8`, `1e400` = `inf`, `9223372036854775808` as float), `/` folded and not, division by zero, `^` at run time and `^ 2` folded, `-0.0`, `0/0` (`nan`), `-(0/0)` (`-nan`), `1 % 0.0`, `0.1 + 0.2`, `//`, `%` | PASS vs `BcSem`/`LuaSem`; host differs on NaN signs only | 466,263 |
| `c/tests/f3_floop.lua` | float `for` with step `0.25`, `x ^ 2`, `x ^ 0.5`, `1 / x`, float `while` | PASS (= host) | 296,762 |
| `c/tests/fold/powfold.lua` | the counterexample (outside `AstSupported`) | `false` (host `true`) | 197,554 |

Differential runs: `c/tests/difftest.sh` (ELF on the Sail Lean emulator)
gives the `.expected` files; `bcSem_of_run` + `decide +kernel` derives the
same outputs from the `luac -s` chunks, and `luaRun_sound` from the ASTs.

## Numbers

| file | lines (added) | CPU (user) | peak |
|---|---|---|---|
| `Lua/Compile/Consts.lean` | 129 (new) | 0.5 s | 0.82 GB |
| `Lua/Ast/Semantics.lean` | +55 −13 | — | — |
| `Lua/Compile/Corpus.lean` | +105 −1 | 26.7 s (base 12.5 s) | 3.15 GB (base 3.13 GB) |
| `scripts/gen_ast.py` | +15 | — | — |

## Obstacles

* A generated file's doc comment opens a nested Lean comment if its path
  contains `/-` (a scratch path `/tmp/claude-2000/-data…` did); the corpus
  paths do not.
* The lexer check ties the tree to `str2number` through the generated
  numeral table, not by a traversal of the tree; the table is the same
  parse's.

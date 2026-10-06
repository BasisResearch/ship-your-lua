# Lane float-s1: floats in `δ` (FLOAT-DESIGN.md S1, S1b, S2, S3-minimal)

Base: main `6f31b36`. Lines are non-blank, non-comment lines (base → now).
Builds: `lake build Lua` after the semantics change, 11 min wall, 3.8 GB
peak (`/usr/bin/time`); `scripts/check.sh`: all stages OK.

## Result

| target | status | where |
|---|---|---|
| `Value.flt (x : Float.Model) (neg : Bool)` (sign bit kept: `-nan`) | defined | `Lua/Bytecode/Semantics.lean` |
| `δ` over `Lua.Num`: `fastArith` (`luaO_rawarith`), string metamethods over `str2number`, `LTnum`/`LEnum`, `luaV_equalobj` (`Value.rawEq`), F2I, `tostringbuff` for `print`/`..` | defined | `Semantics.lean`, `Lua/Num/Arith.lean` (+135) |
| three-way `opArith`; `forprepK` (`forlimit` coercion, float loop), `forloopK` (float loop) | defined | `Semantics.lean` |
| `LOADF`, `DIV`, `DIVK`, `POW`, `POWK` kernels; moved into F1 (`Float` fragment removed: no opcode left) | defined | `Semantics.lean`, `Lua/Fragment.lean` |
| `^`: newlib 4.5.0 fdlibm `pow` transcribed (not a `Host` field: a field would thread `Host` through every kernel; one implementation exists) | defined, 18 `decide` facts | `Lua/Num/Pow.lean` (252), `PowFacts.lean` |
| `Supported` loop check `loopsOk` | defined | `Fragment.lean` |
| metatheory (`kstep_iff`, `footprint`, `certain_answers`, `opKernel_wf`, `body_fault`, `stuck_cases`, corpus `Supported`/`BcSem`) | **rebuilt** | — |
| `loop_inv`, `forloop_regs`, `Fault.Escape` exact (only `FORLOOP`), `noEscape_of_supported` | **proved** | `Lua/StuckCases.lean` (+271) |
| escapes as `BcSem` outputs `2.5`, `1 2`, `-1.5` | **proved** | `Lua/Programs/Escape.lean` |
| `ValRepr.flt`; `SimArmOn`, `SimArm.split`; 31 arms proved off their float paths; `FloatArms` (36 fields) | **proved / named premises** | `Lua/Vm/Sim/{Rel,StepK,Fold}.lean`, `Kit/*`, `gen_lua_arm.py` |
| `vm_refinement_of_open' : OpenArms → FloatArms → ErrorSimRest → vm_refinement_Statement luaLayout` (no `NoEscape`) | **proved** | `Lua/Vm/Sim/StuckErr.lean` |
| Layer B: `LuaSem` operators and `for` over the same value operations; escapes in the corpus (`esc*_tv`) | **proved** | `Lua/Ast/Semantics.lean` (−45), `Lua/Compile/Corpus.lean` |

Open (S3): float numerals, `/`, `^` in `AstSupported`. Machine side: `FloatArms`.

## Tests (ELF on Sail)

* `pow`: 1,570 vectors, bit-exact (`c/tests/float/run_pow.sh`); signalling-NaN
  operands differ (not values: `isSNaN`).
* Semantics end to end (`c/tests/float/run_sem.sh`, `gen_sem.py` seed
  20261006): 22 programs, 3,586 printed lines, Lean `run` = ELF byte for byte;
  21 error programs: ELF exits 2, Lean stuck at the expected instruction.
  Host `lua` differs on 409 lines, all NaN sign. Sail: ~51 CPU-min.

## Notes

* `abstractions/gate.py` dates a case by the first commit adding `theorem
  <name>` (or its blame, if earlier): restating existing kit cases with the
  float premise had re-dated them as new.
* `gen_proto.py` literals beyond ~5,000 instructions hit the recursion limit
  when elaborated (the tests split programs).

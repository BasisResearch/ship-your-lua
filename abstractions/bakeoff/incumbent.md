# Bake-off contender: `incumbent` (abstraction "none")

The current style: every rule's case is written by hand in each metatheory
file. Both clusters were implemented, and each is measured on its own.

Cost is counted in non-blank, non-comment Lean lines.
- **Proof** lines are theorem and lemma bodies, counted with `abstractions/census.py`'s `decls`, HEAD against the working tree.
- **Spec** lines are definitions, inductive rules and table entries. They are counted from the diff with comments stripped.
- **Shared** spec is the string layer in `Lua/Bytecode/Semantics.lean`, which both layers use. It is counted once and reported separately.
- **Generated** lines are the output of `scripts/gen_proto.py` and `scripts/gen_ast.py`.

## Phase 1: SETUP

| item | value |
|---|---|
| lines | 0 |
| wall time | 0 |
| failed builds | 0 |

## Phase 2: REFACTOR

There is nothing to re-seat. The originals were re-measured with `abstractions/census.py` at HEAD `79b6082`.

| target | files | proof lines (census) |
|---|---|---|
| R1 | `Lua/FragmentSound.lean` + `Lua/Bytecode/Exec.lean` | 596 + 261 = **857** |
| R2 | `Lua/Ast/Determinism.lean` + `Lua/Ast/Exec.lean` | 216 + 294 = **510** |

Both match the figures in SUITE.md. The wall time was about 1 min (one census run), with 0 failed builds.

After the held-out phase, the same files measure:
- R1: 670 + 322 = 992 (+135);
- R2: 273 + 331 = 604 (+94).

## Phase 3: HELD-OUT (H1–H5 in both clusters)

### Semantics implemented

**Shared layer** (`Lua/Bytecode/Semantics.lean`, "Strings" section):
- `intBytes` and `Value.concatBytes?`: `tostring` of a string or an integer (`%lld`).
- `strLt` and `strLe`: `l_strcmp` in the C locale, which is byte-lexicographic.
- `str2int`: `l_str2int` over the whole string.
  - Accepts leading and trailing C-locale spaces and a `+` or `-` sign.
  - Hex digits wrap on overflow.
  - A decimal value that overflows is rejected. `l_str2d` would read it as a float, which is outside the slice.
  - An embedded NUL fails.
- `Value.arithInt?`, `strArith` (at least one operand is a string and both convert to integers) and `unmInt`.

**Bytecode** (`Step`):
- `lenStr`, `concat` and `cmpStr`.
- `arithMM`: an arithmetic instruction whose operands are not both integers falls through to `pc+1`.
- `mmbinStr`: `MMBIN`/`MMBINI`/`MMBINK` with the string metatable. The operation comes from the TM event in `C` (`tmArith`), `k` swaps the operands, and the result goes to `R[A]` of the instruction at `pc-1`.
- `unmStr`: `UNM` of a string calls `luaT_trybinTM(rb, rb, TM_UNM)` directly.
- `LOADK` of `Const.str` already had a rule. Only `Supported` had to admit it.

**CONCAT's range write set.** The rule writes `R[A]`. Everything above `A` is `Clobbered`, exactly as for `CALL`:
- `keepMask` of a `CONCAT` is `rmask 0 A`, and its edge writes `rmask A 1`;
- `CStep` lets those registers hold anything;
- `cbcSem_iff` and `bcSemFrom_iff` still hold, with the `DefInit.step` `kept` case extended to `CONCAT`.

**Source** (`Eval`):
- `string`, `concat`, `len`, `cmpStr` (`< <= > >=`) and `arithStr` (`+ - * // %`), plus `negStr`.
- `BinOp.strArith` and `BinOp.strCmp`.
- Interpreter cases and `AstSupported` (`supE` admits `.string`; `inF1` admits `..` and `#`).

### Validation

| cluster | theorem | proof lines | generated lines |
|---|---|---|---|
| bytecode | `f4Strlite_bcSem` (`Lua/Programs/Validation.lean`) and `f4Strlite_supported` (`Lua/Programs/Supported.lean`) | 4 | 116 (`Lua/Programs/F4Strlite.lean`) |
| source | `f4Strlite_astSupported` and `f4Strlite_luaSem` (`Lua/Compile/Corpus.lean`) | 3 (+6 for `f4Strlite_tv` and the corpus entry) | 18 (`Lua/Programs/F4StrliteAst.lean`) |

Notes on the validation:
- The expected output is `c/tests/f4_strlite.expected`, the ELF's output on Sail. Every check is `decide +kernel`.
- On top of what was asked, `f4_strlite` joins `CorpusCompiles`, so `compile_refinement_corpus` covers it. That costs 3 spec lines (`f4StrliteOut` and the constructor) and the 6 proof lines above.

### Per-H cost, bytecode cluster

The spec here counts only lines specific to the bytecode side: `Step`, `step?`, `Supported`'s tables, `Clobbered` and the helpers. The shared layer is listed separately.

| case | shared spec | bytecode spec | proof: `Step.sim`/`DefInit` (`FragmentSound`) | proof: `step?_sound`/`_complete` (`Exec`) | proof total |
|---|---|---|---|---|---|
| H1 `LOADK` str | 0 | 1 | 0 | 0 | 0 |
| H2 `CONCAT` | 5 | 14 | 21 (arm 7, `DefInit.step` clobber 14) | 6 | 27 |
| H3 `LEN` | 0 | 11 | 6 | 4 | 10 |
| H4 `LT`/`LE` str | 6 | 11 | 9 | 13 | 22 |
| H5 `MMBIN*`/`UNM` | 38 | 50 | 38 | 38 | 76 |
| **total** | **49** | **87** | **74** | **61** | **135** |

### Per-H cost, source cluster

| case | source spec (rules, interpreter, `AstSupported`) | proof: determinism | proof: `luaRun_sound` (`execSound` and the eval lemmas) | proof total |
|---|---|---|---|---|
| H1 literal | 3 | 1 | 0 (one arm changed) | 1 |
| H2 `..` | 7 | 8 | 8 | 16 |
| H3 `#` | 3 | 1 | 3 | 4 |
| H4 string order | 12 | 16 | 4 | 20 |
| H5 string arithmetic | 19 | 31 | 22 | 53 |
| **total** | **44** | **57** | **37** | **94** |

The source cluster reuses the same 49 shared spec lines.

The split within a file is attributed by hand for the arms that `census` cannot separate: `Eval.det`'s nested arms and `step?_sound`'s `case MMBIN | MMBINI | MMBINK`. The per-file totals are exact.

### Lines added and deleted, per file

These are raw `git diff --numstat` counts, including comments.

| file | + | − | cluster |
|---|---|---|---|
| `Lua/Bytecode/Semantics.lean` | 169 | 2 | shared + bytecode |
| `Lua/Bytecode/Exec.lean` | 116 | 43 | bytecode |
| `Lua/Fragment.lean` | 37 | 19 | bytecode |
| `Lua/FragmentSound.lean` | 96 | 19 | bytecode |
| `Lua/Programs/Validation.lean` | 11 | 0 | bytecode |
| `Lua/Programs/Supported.lean` | 3 | 0 | bytecode |
| `Lua/Programs/F4Strlite.lean` (generated, new) | 254 | 0 | bytecode |
| `Lua/Ast/Semantics.lean` | 48 | 8 | source |
| `Lua/Ast/Exec.lean` | 68 | 14 | source |
| `Lua/Ast/Determinism.lean` | 63 | 2 | source |
| `Lua/Compile/Corpus.lean` | 26 | 1 | source |
| `Lua/Programs/F4StrliteAst.lean` (generated, new) | 44 | 0 | source |
| `Lua.lean`, `scripts/check.sh` | 10 | 1 | both |

### Wall time and failed builds

The phase ran from 05:17 to 05:44 UTC, about 27 minutes. That includes about 6 minutes waiting for free memory. The two clusters were interleaved, so the split below is approximate:

| cluster | wall time | build attempts | failed builds |
|---|---|---|---|
| shared layer | ~4 min | — | — |
| bytecode | ~13 min | 4 | 1 |
| source | ~6 min | 2 | 0 |
| full `lake build Lua` | ~1 min | 1 | 0 |

The failed bytecode build had three errors, none of them in the semantics:
- two `rename_i` mismatches in `step?_sound`'s `LT`/`LE` string arms;
- one `assumption` pick in `strArith_isStr`.

### Acceptance

- The `#print axioms` of `step?_sound`, `step?_complete`, `Step.deterministic`, `BcSem.deterministic`, `Supported.defInit`, `DefInit.step`, `bcSemFrom_iff`, `cbcSem_iff`, `luaRun_sound`, `LuaSem.deterministic`, `compile_refinement_corpus`, `f4Strlite_bcSem`, `f4Strlite_luaSem` and `f4Strlite_tv` is ⊆ {propext, Classical.choice, Quot.sound}.
- `lake build Lua` is green.
- `scripts/check.sh --static-only` is green except stage 3c. Stage 3c fails on `bc-rule-fanout`, as expected: the last quarter of cases averages 5.4 lines against 2.4 in the first quarter.
- The existing kernel checks against the ELF outputs still pass: `while`, `f1_ops`, `f1b_bits`, `print_print` and `f1_src`.

## Summary

| cluster | setup | refactor size (vs original) | held-out spec | held-out proof | wall time | failed builds |
|---|---|---|---|---|---|---|
| bytecode | 0 | 857 (= original, R1) | 87 (+49 shared) | 135 (+4 validation) | ~13 min (+4 shared) | 1 |
| source | 0 | 510 (= original, R2) | 44 (+49 shared) | 94 (+9 validation) | ~6 min | 0 |

## Findings

1. **SUITE.md is wrong about `UNM`.** It says `UNM` goes through `MMBIN`. `luac` emits no `MMBIN` after `UNM` (`f4_strlite` listing, pc 68), and `lvm.c`'s `OP_UNM` calls `luaT_trybinTM(rb, rb, ra, TM_UNM)` itself. I modelled it as a direct rule (`unmStr`).
2. **The operation of an `MMBIN*` comes from its own `C` field** (the TM event), not from the arithmetic opcode. Only its destination comes from the instruction before it. The bitwise events have no string metamethods, so `"3"&1` is stuck, which matches the host `lua`.
3. **`CONCAT`'s clobber set is every register above `A`, not only `A+1..A+B-1`.** `OP_CONCAT` runs `checkGC(L, L->top)` with `top = ra + 1`, and an atomic GC step clears the stack above `top` (`traversethread`). The incumbent expresses this with the `CALL` machinery (`Clobbered`, `keepMask`). It costs a second, copied 14-line `kept` case in `DefInit.step`, which is the incumbent's duplication signal.
4. **Arithmetic opcodes gained an edge.** Every arithmetic and bitwise opcode now has the fall-through edge `(pc+1, ∅)`, and `MMBIN*` changed from "never executed" (`some []`) to a real edge that writes `R[pi.a]`. That changed `edgesOf_arith` and the `arith` arm's edge membership for all 21 arithmetic opcodes.
5. **H5 dominates both clusters.** It is 56% of bytecode proof and 56% of source proof.
   - The source side pays the quadratic inversion cost: rules with a variable operator (`cmpStr`, `arithStr`) add a line to every existing binary-operator arm of `Eval.det` (eq, ne, and/or ×4, cmp, arith, concat). They also need three disjointness lemmas.
   - H2 (`concat`, whose operator is fixed) is cheap by comparison, because `cases` eliminates the other arms automatically.
6. **H1 on the bytecode side was nearly free.** `Const.toValue?` already mapped strings, so only `edgesOf`'s `LOADK` filter changed (1 line, 0 proof).
7. **Out of scope, as SUITE.md says.** A decimal string that overflows an integer (`"9223372036854775808"+0`) is a float in real Lua. `str2int` rejects it, so such a program is stuck.

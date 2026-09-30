# Bake-off contender B-rulebook (C4, source cluster `ast-construct-fanout`)

The abstraction: `LuaSem` is the graph of one non-recursive **rulebook**.

- **The rulebook** (`Lua/Ast/Semantics.lean`, `rules`) gives one program per
  construct in a free "call" monad (`Lua.Rulebook.Prog`: `ret | call c k | fail`).
  - The premises of a construct are its calls. Its side conditions are
    ordinary Lean `if`/`match`, so the branches are exclusive by construction.
- **The judgments are one call type** (`Call`: `eval`, `stat`, `list`,
  `blockFrom` (goto), `block`, `forIter`). The dependent answer type
  `Call.Res` is `Value` for `eval` and `Env × String × Sig` otherwise.
- **The relation** `Sem rb c r := Runs rb (rb c) r` is the least relation
  resolving the calls (`Lua/Ast/Rulebook.lean`).
- **The interpreter** `solve rb fuel c` is generic.
- **The generic theorems** (proved once, for ANY rulebook):
  - `sem_iff_solve : Sem rb c r ↔ ∃ n, solve rb n c = some r`;
  - `Sem.det`.
- **`LuaSem`'s public shape is unchanged**: `LuaSem H c out := ∃ ρ', Sem
  (rules H) (.block [] "" c) (ρ', out, .normal)`.
  - `luaRun`, `luaRun_sound`, `LuaSem.deterministic`,
    `compile_refinement_corpus` and every Corpus TV fact build unchanged.
  - The kernel `decide +kernel` checks against the ELF outputs still pass
    (while, f1_ops, f1_src, f1b_bits).

Counting: non-blank, non-comment Lean lines. Lines inside `theorem`/`lemma`
are PROOF; everything else is SPEC. Counter: the scratch `count.py`, the same
rule as `abstractions/census.py`. The originals reproduce SUITE.md's numbers
(Exec 294 proof, Determinism 216 proof).

## Phase 1: SETUP (05:18–05:21, commit c072e1e)

| file | +/− | spec | proof |
|---|---|---|---|
| `Lua/Ast/Rulebook.lean` (new, generic, no Lua) | +187 / −0 | 39 | 74 |

- **Proof breakdown.**
  - 52 lines are the core: `handle_mono`, `handle_sound`,
    `solve_succ/mono/sound`, `Runs.complete`, `sem_iff_solve`, `Sem.det`.
  - 22 lines are simp read-back lemmas (`runs_bind`, `runs_call`, …). They
    are used only for derived rule lemmas, which nothing needs yet.
- **Failed builds:** 1. The theorems first recursed on `Prog` with a varying
  implicit `α`, and structural recursion failed; I switched to `induction`.

## Phase 2: REFACTOR R2 (05:21–05:26, commit e1b9092)

| file | +/− | spec before → after | proof before → after |
|---|---|---|---|
| `Lua/Ast/Semantics.lean` | +178 / −120 | 259 → 295 (inductives → rulebook, +36) | 0 → 0 |
| `Lua/Ast/Exec.lean` | +25 / −513 | 172 → 9 (hand interpreter deleted) | 294 → 14 |
| `Lua/Ast/Determinism.lean` | +7 / −240 | 11 → 4 | 216 → 6 |

- **Compression of R2's proofs:** 510 → 20 proof lines (−96%).
  - With the generic setup counted as well: 510 → 94.
  - `execSound`, `Eval.det`, `ExecS.det`, `ExecL.det`, `ExecBF.det`,
    `ExecB.det` and `ForIter.det` no longer exist. The gate now reports
    `ast-construct-fanout: 0 cases`.
- **What remains:**
  - `luaSem_iff_run` (L-A1 for `LuaSem`, 11 lines);
  - `luaRun_sound` (a thin wrapper);
  - `LuaSem.deterministic` (5 lines, from `Sem.det`).
- **Whole source cluster, spec + proof:** 952 → 441 lines (Semantics +
  Exec + Determinism, with Rulebook added).
- **Failed builds:** 1. `scoped` is a keyword, and a namespace `open` was
  wrong.

## Phase 3: HELD-OUT H1–H5 (05:26–05:40, commit 019d6d9; about 5 min of it waiting for memory)

Each case's rulebook or primitive entries are spec. Interpreter soundness and
determinism for each case cost **0 proof lines**: the generic theorem covers
them, and there is no separate interpreter case to write.

| case | spec lines (new/changed) | proof lines | where |
|---|---|---|---|
| H1 string literal | 2 | 0 | `rules` arm `.eval _ (.string s)`; `supE` admits `.string` |
| H2 `..` (str/int, `tostring` `%d`) | 10 | 0 | `concatBytes`, `binOp` `.concat` arm, `BinOp.inF1` |
| H3 `#` on strings | 2 | 0 | `unOp` `.len`, `UnOp.inF1` |
| H4 string `< <= > >=` (`l_strcmp`, C locale) | 14 | 0 | `bytesLt`, `BinOp.strCmp`, `binOp` string branch |
| H5 arithmetic on integer-valued strings | 35 | 0 | `isSpace`, `digitVal`, `str2int` (= `l_str2int`: spaces, sign, decimal with overflow rejected, hex wrapping), `arithInt`, `BinOp.coerces` (`+ - * // %` only, not bitwise), `binOp` coercion branch, unary `-` |
| **total** | **63** | **0** | Semantics.lean +98/−14 in all, docs included |

**Validation of `c/tests/f4_strlite.lua`** (`Lua/Programs/F4StrliteSrc.lean`):

- `f4Strlite_astSupported` (`decide +kernel`);
- `f4Strlite_luaSem : LuaSem binaryHost f4StrliteAst f4StrliteOut`
  (`luaRun_sound (fuel := 1000)` + `decide +kernel`), where the output is
  exactly `c/tests/f4_strlite.expected`;
- cost: 9 spec lines + 3 proof lines;
- GENERATED: `Lua/Programs/F4StrliteAst.lean`, 18 lines, from
  `scripts/gen_ast.py`, registered in check.sh stage 1;
- it passed on the first build that got past the definitions.

Other changes:

- **`check.sh`:** the stage-6 list drops `execSound` and adds
  `sem_iff_solve`, `Sem.det`, `luaSem_iff_run`, `f4Strlite_astSupported` and
  `f4Strlite_luaSem`. The expected count goes from 77 to 81.
- **Failed builds:** 2. A `Value.concatBytes` dot name was in the wrong
  namespace, and a precedence slip.

## Gate

`scripts/check.sh` passes every stage except 3c. Stage 3c fails on
`bc-rule-fanout`, as expected; `ast-construct-fanout` now has 0 cases.

Axioms:

| theorem | axioms |
|---|---|
| `sem_iff_solve`, `Sem.det` | `[propext]` |
| `luaRun_sound`, `LuaSem.deterministic`, `luaSem_iff_run`, `f4Strlite_luaSem` | `[propext, Classical.choice, Quot.sound]` |
| `f4Strlite_astSupported` | `[propext, Quot.sound]` |

## Summary

| setup | refactor size (vs original) | held-out spec | held-out proof | wall time | failed builds |
|---|---|---|---|---|---|
| 113 lines (39 spec + 74 proof) | R2 proofs 20 vs 510 (94 vs 510 with setup); cluster spec+proof 441 vs 952 | 63 (+9 validation, +18 generated) | 0 (+3 validation) | ~22 min (setup 3, refactor 5, held-out 14 incl. ~5 waiting on memory) | 4 (1 / 1 / 2) |

## Findings

- **Derived rule lemmas need `Call.Res` to be `@[reducible]`.**
  - Otherwise the `α` index of `Runs` is `(Call.stat ..).Res`, not
    `Outcome`, and `simp`/`rw` with `runs_bind` do not fire.
  - With it, classic rules are one-liners, checked in scratch, e.g.
    `whileF`: `unfold Sem; simp [rules, eval]; exact ⟨v, hv, by simp [hf]⟩`.
  - None is committed, because no consumer needs them.
- **Fuel semantics changed without cost.** Fuel now bounds the nesting depth
  of calls, not interpreter recursion. `fuel := 1000` still suffices for
  every corpus program, and kernel time for Corpus is about as before
  (~1.5 min for the whole rebuild).
- **H5 needed a careful definition of "coerces".** It follows `lstrlib.c`'s
  `tonum`, which uses `len + 1`, so strings with embedded zeros are
  rejected. A string that converts to a float (for example `"3.0"` or a
  decimal overflow) has no rule. Bitwise operators do not coerce.
  - `str2int` was sanity-checked by `#eval` on 12 edge cases against
    `lobject.c`'s behaviour.
- **What the abstraction does not buy.** The trusted spec is now a monadic
  program, not inference rules: +36 spec lines against the inductives. The
  rulebook cannot express non-determinism without a `choose` node.

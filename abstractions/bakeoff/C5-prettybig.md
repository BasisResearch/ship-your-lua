# C5-prettybig: pretty-big-step `LuaSem` with one abort rule (source cluster, control for C4)

Branch `worktree-agent-aadbd02614b79eadb`, from `main` at 79b6082.

**Abstraction.** This follows Charguéraud's pretty-big-step semantics (ESOP 2013), as proposed in `fanout/R1-3.md` #4 and `fanout/R1-4.md` #3.

- `LuaSem` stays an inductive relation, under the same name, over a term type. Only its form changed, so the relation is new and there is no separate equivalence proof.
- **Term types.** `Ext` is a statement, list or block, or one of 9 intermediate forms. `EExt` is an expression or one of 3 intermediate forms.
- **Entry rules.** Each construct has ONE entry rule. It evaluates the first sub-term and hands the outcome to an intermediate form.
- **Intermediate rules** are indexed by a constructor of that outcome, not by a guard:
  - `Truthy` for `branch`, which serves `while`, `if`, `until`, `and` and `or`;
  - `Option` for `forIter` (the count) and `blockAt` (the goto target);
  - `Sig` for `then_`.
- **One abort rule**, `Exec.abort : e.abort? = some sg → Exec ρ o e ρ o sg`, propagates every abrupt completion. `then_ inLoop sg k` is the only form with an `abort?`, and a loop body's `break` is caught by `Sig.passUp`. It absorbs `whileX`, `repeatX`, `ExecL.stop` and the abrupt half of `ForIter.last`.
- **`abort_det`** is proved once, in 3 lines.
- **Primitive operators** are partial functions (`binVal`, `unVal`), as `op.arith`/`op.cmp` already partly were. `and` and `or` go through `branch` (`BinOp.next`).
- **`Exec` is ONE inductive** (28 rules), not 5 mutual ones. Determinism is ONE induction, and interpreter soundness is ONE fuel induction with one arm per rule.
- The kernel checks against the ELF outputs (the Corpus TV facts, `compile_refinement_corpus`) pass unchanged, at the same fuel of 1000.

Cost counts non-blank, non-comment lines. PROOF is `census.py`'s `decls` (theorem bodies), and SPEC/other is the rest of the file (`scratchpad/c5/cen.py` wraps both).

## Phase 1+2: SETUP + REFACTOR (05:16 → 05:44 UTC, 28 min, including ~8 min of reading)

The abstraction *is* the rewrite of `LuaSem`, so setup and refactor were one step and one commit (1f824f2).

| file | +/− (git numstat) | before: total / proof / arms | after: total / proof / arms |
|---|---|---|---|
| `Lua/Ast/Semantics.lean` | +202 −104 | 259 / 0 / – | 308 / 0 / – |
| `Lua/Ast/Determinism.lean` | +97 −219 | 227 / **216** / 125 | 105 / **96** / 59 |
| `Lua/Ast/Exec.lean` | +162 −452 | 466 / **294** / 67 | 193 / **104** / 9 |
| **total** | | 952 / 510 / 192 | 606 / 200 / 68 |

**SETUP**, the abstraction itself (inside `Semantics.lean`/`Determinism.lean`):

- About 40 spec lines: `Truthy`, `Value.truthy`, `EExt`, `BinOp.next`, `Ext` (14 lines), `Sig.passUp`, `Ext.abort?`, `elseExt`, `forNext`, and the `abort` rule.
- 3 proof lines: `abort_det`.

**REFACTOR (R2)**:

- Proofs: 216 + 294 = **510 → 96 + 104 = 200** proof lines (**−61%**). Case arms fell from 192 to 68.
  - `ExecS/ExecL/ExecBF/ExecB/ForIter.det` (5 mutual theorems) became one `Exec.det`, with 21 arms: `abort` (via `abort_det`), one shared arm for the 8 premise-free rules, and 19 arms that each read "`cases h₂` leaves one rule plus an impossible `abort`".
  - `execSound` is 1–3 lines per rule.
- Spec: `Semantics.lean` +49 (the intermediate forms). The interpreter's definitions shrank from 172 to 89, because `run` is now one function over `Ext` rather than 5 mutual ones.

**Failed builds.** There were 3 `lake build` errors:

1. `Value.truthy` landed in the wrong namespace.
2. `until` is a keyword, so it could not name a rule.
3. An implicit type on a helper lemma.

There were also 4 failing single-file `lake env lean` checks: `nomatch` against a helper lemma, and a binder issue in the `execSound` recursion.

**Kept names.** These are unchanged: `LuaSem`, `LuaSem.deterministic`, `luaRun_sound`, `execSound`, `Eval.det`, `EvalList.det`, `Exec.Same`, `AstSupported`, `compile_refinement_corpus` and all Corpus TV facts. `ExecS`/`ExecB`/`Eval` stay as abbreviations for the new relation at `.stat`/`.block`/`.exp`.

## Phase 3: HELD-OUT H1–H5 (05:44 → 05:50 UTC, 6 min; 0 failed builds)

Commit e32af18.

| case | spec lines (new/changed) | proof lines (new) | what |
|---|---|---|---|
| H1 literals | 3 (`EvalX.string`, `evalE` case, `supE`) | 0 (3 existing lines extended by one alternative: `EvalX.det`, `evalE_sound`) | |
| H2 `..` | 11 (`intBytes`, `Value.concatBytes?`, `binVal` case, `BinOp.inF1`) | 0 | |
| H3 `#` | 2 (`unVal` case, `UnOp.inF1`) | 0 | |
| H4 string `<`,`<=`,`>`,`>=` | 12 (`bytesLt`, `BinOp.strCmp`, `binVal` case) | 0 | |
| H5 integer-string arithmetic | 38 (`isSpace`, `decDigit?`, `hexDigit?`, `readDigits`, `str2int` = `l_str2int`, `Value.toInt?`, `BinOp.coerces`, the `binVal` arithmetic path, `unVal .neg`) | 0 | |
| validation | 17 (`Lua/Compile/F4Strlite.lean`: expected output, 2 kernel `example`s of edge cases) | 3 (`f4Strlite_astSupported`, `f4Strlite_luaSem`, both `decide +kernel`) | |
| generated | 18 (`Lua/Programs/F4StrliteAst.lean`, `gen_ast.py`) | – | |

- **Totals.** Spec ≈ 66, proof 0 new (3 existing lines extended), validation 3. File diffs:
  - `Semantics.lean` +96 −12;
  - `Exec.lean` +4 −3;
  - `Determinism.lean` +1 −1;
  - new `Lua/Compile/F4Strlite.lean` (45 lines);
  - `Lua/Programs/F4StrliteAst.lean` (44 lines, generated);
  - `Lua.lean` +2;
  - `scripts/check.sh` +5 (stage 1 drift entry, stage 6 axioms for `abort_det`, `Exec.det`, `f4Strlite_luaSem`, `f4Strlite_astSupported`).
- **Validation.** `f4Strlite_luaSem : LuaSem binaryHost f4StrliteAst f4StrliteOut`, with exactly `c/tests/f4_strlite.expected`, and `f4Strlite_astSupported`. Both are kernel-checked at fuel 1000. A deliberately wrong output, and `str2int "1.5" = some 1`, are both rejected by `decide +kernel`.
- **Edge cases** (checked against Lua's rules):
  - `" 0x10 "` → 16;
  - `"-9223372036854775808"` → minint;
  - `"9223372036854775808"`, `"1.5"`, `"0x"` and `"1 2"` → no integer;
  - no rule for `"1.5"+1`, `"3"&1`, `"1"<2`, `"1"//0`, or `-12 .. true`.

## Summary

| contender | setup (spec / proof) | refactor size vs original (R2 proof lines) | held-out spec | held-out proof | wall time | failed builds |
|---|---|---|---|---|---|---|
| C5-prettybig | ~40 / 3 | **200 vs 510 (−61%)**; arms 68 vs 192 | 66 (+17 validation, +18 generated) | 0 new (+3 validation) | 34 min (28 setup+refactor, 6 held-out) | 3 `lake build` (+4 single-file checks), all in setup/refactor; 0 in held-out |

Axioms of `abort_det`, `Exec.det`, `EvalX.det`, `LuaSem.deterministic`, `luaRun_sound`, `execSound`, `compile_refinement_corpus`, `f4Strlite_luaSem` and `f4Strlite_astSupported`: `[propext, Quot.sound]`.

## Notes and surprises

- **Most of the held-out saving is not the abort rule.** H1–H5 are expressions with no abrupt behaviour, so the abort rule does nothing for them. The saving comes from putting primitive operators in *functions* (`binVal`/`unVal`) behind one `rhs` rule, and from `and`/`or` sharing the `Truthy`-indexed `branch`. Nothing in the rule structure grows with H2–H5: determinism and interpreter soundness need no new arm.
  - The incumbent style could have had the same benefit by factoring its operators into a function. For the C4 comparison, credit the abort rule and one-rule-per-term with the **R2** gain: 5 mutual det theorems with guard cross-inversions became one linear induction.
- **Faithfulness.** The previous `ForIter` (count `n`, `last` when `n = 0 ∨ abrupt`) is recovered with `forIter … (some n)` and `forNext`, with no guard. The goto-catch of blocks needs no abort side condition: `blockAt` is indexed by `Option` of `sg.target all` and has its own `done`/`jump` rules. The only "propagating" form is `then_`, so `isPropagating` became the single `Ext.abort?` function with 2 cases.
- **`cases` on computed indices works.** Intermediate forms carry computed classifiers, such as `v.truthy` and `forCount i l st`. In `Exec.det`, the first premise's determinism substitutes the value, so the second derivation's index becomes syntactically equal. No `cases` on a non-constructor index was needed.
- **One irreducible per-arm residue:** `| abort ha => nomatch ha` in each of the 20 non-abort `Exec.det` arms. The generic abort rule unifies with every term, so each non-abort arm must dismiss it. `nomatch` does this by reduction of `Ext.abort?`. The arm is still per construct, but one token long.
- **Fuel.** Each loop iteration now costs 4 fuel instead of 1, from the intermediate forms. The corpus's `fuel := 1000` was still enough, so no change was needed.
- **No law turned out false.** One subtlety: `Ext.abort?` must match on the `Sig` *before* the `inLoop` Boolean (`Sig.passUp`). Otherwise `abort? (.then_ l .normal k)` does not reduce for a variable `l`, and `nomatch` fails.
- **Gate.** `scripts/check.sh` stage 3c (the abstraction gate) fails as expected. `ast-construct-fanout` fell from 187 cases to 8. Every other stage is green (`check.sh` with 3c made non-fatal: "all stages OK"; stage 6 now expects 81 axiom reports).

# Lane float-sf2: the remaining `SoftFloatSpec` fields on the `SfRef` route

The base is main `9f5ab04`. The six fields `floatsidf`, `floatdidf`, `fixdfdi`,
`eqdf2`, `ledf2` and `gedf2` have left `SoftFloatSpec`. Each one is now a
theorem `Lua.Vm.Fn.<R>.spec_proved` under the field's exact hypotheses.
`SoftFloatSpec` has no fields left. It stays, empty, because
`FloatArms.soft` still names it. All eight routines are in `gen_lua_at.py`'s
`FPROVED`, and the regenerated call sites take no premise.

## What is proved

| routine | (b2): reference = `F64` | (b1): lifted `F` = reference | spec theorem |
|---|---|---|---|
| `__ledf2`, `__gedf2` | `SfRef.cmp_eq` (`_FP_CMP_D` = `F64.compare`) | `Ledf2.F_eq_ref`, `Gedf2.F_eq_ref` | `Ledf2.spec_proved`, `Gedf2.spec_proved` |
| `__eqdf2` | `SfRef.eqv_eq` (`_FP_CMP_EQ_D` = `F64.eq`) | `Eqdf2.F_eq_ref` | `Eqdf2.spec_proved` |
| `__fixdfdi` | `SfRef.toInt_eq` (`_FP_TO_INT`) | `Fixdfdi.G_eq` | `Fixdfdi.spec_proved` |
| `__floatdidf` | `SfRef.ofInt_eq` (`_FP_FROM_INT`) | `Floatdidf.F_eq_sfref` | `Floatdidf.spec_proved` |
| `__floatsidf` | `SfRef.ofInt_eq` | `Floatsidf.F_eq_sfref` (canonical `int`) | `Floatsidf.spec_proved` |

Axioms of all ten theorems: `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` stage 6 lists them. There are no `sorry`, `axiom`,
`native_decide` or `bv_decide` and no raised limits.

## The route

- **Comparisons: `compare_key`, no rounding.**
  - The references `cmpFields`/`eqFields` (`Lua/Num/SfRefCmp.lean`)
    transcribe soft-fp's `_FP_CMP`/`_FP_CMP_EQ` branch for branch.
  - (b2) goes through the sign-magnitude key `±(e·2^52 + f)`:
    `cmpFields_key` (soft-fp's chain is the key order) and `compare_key`
    (`F64.compare`'s lexicographic `(ce, cm)` order is the key order,
    `lex_mag`).
  - The cost is 96 lines and 7 s of CPU.
- **The chamber generator `sfc_chambers F r [refs]`** (`Lua/Vm/Fn/SfRefCmp.lean`).
  - This is the abstraction that both round-5 winners named, built here for
    two-operand routines. A command macro emits 11 chamber lemmas: a NaN
    operand (2), zero operands by the other's sign (5), and both nonzero by
    both signs (4). It also emits the cover `G_eq` and `F_eq_ref`.
  - A chamber (`sfc_chamber`) unpacks the operands (`P`, `argA_P`/`argE_P`/`argF_P`).
  - It then decides the reference's branches once under the chamber's
    facts, explores the DAG (`sfc_go`), and closes each closed-word leaf by
    `decide`.
  - **Cost of the generator**: about 95 lines (the macro and the chamber
    tactic), plus about 95 lines of comparison lens (guards, `P`).
  - **Per routine** it is about 12 lines: the `sfc_chambers` call and
    `spec_proved`. Compare about 400 lines of restated chamber statements
    per routine in B-SFREF.
- **Conversions** (`Lua/Num/SfRefInt.lean`, `Lua/Vm/Fn/SfRefInt.lean`).
  - `toIntFields` is `_FP_TO_INT` (truncate, saturate by the sign).
    `fromNat` is `_FP_FROM_INT`: count the leading zeros, then either shift
    exactly or apply the sticky shift `rto`, then `roundPack`.
  - (b2) `fromNat_eq` reuses B-SFREF's laws unchanged: `roundPack_eq`,
    `round_scale` (the exact path) and `round_rto` (W1, the sticky path).
  - `__fixdfdi` (b1): four exponent chambers in one tactic (`sfi_chamber`).
  - `__floatdidf` (b1) has a stage lemma per machine site:
    - `g_2a8`: `_FP_ROUND` and the pack;
    - `g_308`: the sticky shift, by `nf_sticky`/`nf_srs`;
    - `g_2a0`: the left shift;
    - `g_248`: the exact pack, through the shared `exact_pack`.

    The entry forwards the frame reloads (`frame_addr32`), the magnitude
    (`abs_nf`) and `__clzdi2` (`nf_clz`).
  - `__floatsidf` (b1) uses the same entry on a canonical `int`
    (`canon_range`, `sign32_nf`, `mag32_nf`). It always takes the exact
    pack (`exact_pack`).

## Numbers

Lines are non-blank, non-comment lines. CPU and memory are for one
`lake env lean <file>` with its imports built, measured under `/usr/bin/time`.

| file | lines | CPU (user s) | wall s | peak |
|---|---|---|---|---|
| `Lua/Num/SfRefCmp.lean` (b2 comparisons) | 96 | 7.4 | 3.9 | 0.80 GB |
| `Lua/Num/SfRefInt.lean` (b2 conversions) | 148 | 1.5 | 1.2 | 0.80 GB |
| `Lua/Vm/Fn/SfRefCmp.lean` (lens, generator, 3 routines) | 217 | 206.6 | 19.8 | 2.68 GB |
| `Lua/Vm/Fn/SfRefInt.lean` (3 routines) | 431 | 17.4 | 6.8 | 2.21 GB |
| **total** | **892** | 233 | | |

- **Heartbeats.** The files were re-elaborated with `maxHeartbeats`
  lowered. At 100k only `Ledf2`'s and `Gedf2`'s generated `ch_00` fail
  (same-sign chambers, 14 leaves). At 150k nothing fails. In
  `SfRefInt.lean` everything is under 100k; only `g_2a8` needs more than
  50k.
- **Build and check.** `lake build Lua` passes, as does
  `scripts/check.sh` (all stages, including stage 6).
- **Obstacle found and recorded.** `SfLens.sf_nf`'s `nf_mod_lit`
  (discharged by `omega`) loops to `maxRecDepth` inside an `if` branch
  whose condition contradicts the path's facts, because simp's `ite`
  congruence puts the condition in context. So:
  - the comparison and conversion normal forms (`sfc_nf`, `sfi_nf`) decide
    the guards first and do not call `sf_nf` on undecided goals;
  - `__fixdfdi`'s saturation chamber splits the sign first.

## Validation

These are theorems, which is stronger than vectors. The routines' Sail
vectors (`c/tests/float/`, `abstractions/ledger/float-s0a.md`) and the
`SpecTest.lean` evaluations still pass unchanged. No new definition enters
the semantics: the references are proof devices, each equal to the `F64`
specification by (b2). So no new differential test was needed.

# Bake-off contender A2-section: section-typed transfer functions (bytecode)

This is abstraction R1-2 #2, with the round-2 kill-port correction (C2), applied to the `bc-rule-fanout` cluster. It is the cheap-setup rival to contender A, which uses full kernel terms.

**Cost measure.** Costs are non-blank, non-comment Lean lines. Each line is classed by the declaration it belongs to:

- spec: `def`, `structure`, `inductive`, `macro`;
- proof: `theorem`.

Generated lines are counted separately. The counting script is `scratchpad/a2/loc.py`, which reads the same way as `census.py`.

## The abstraction

`Lua/Bytecode/Section.lean` is generic; it does not mention Lua. It defines:

- `View α R := (r : Nat) → R.testBit r = true → α`: a section of the register file over the mask `R`.
- `restrict`: the restriction map from register files to views.
- `Edge {tgt, defs, kills}`: an edge with its target, the registers it defines and the registers it kills.
- `Outcome α eo`: an index `Fin (eo.getD []).length` into the instruction's edge table, a section over that edge's defs, and output. An instruction whose table is `none` has no outcome at all.
- `Xfer α R eo := View α R → Option (Outcome α eo)`: a transfer function.

Its laws are all proved without induction:

- `restrict_congr`: the footprint law.
- `Outcome.patch_agree`: the frame law.
- `testBit_edgeMask`: `edgeMask m e = (m ∪ defs) \ kills`, which is what the definite-initialisation (DI) analysis uses.

**Semantics.** `Step` has one constructor: fetch, decode, then `xfer p H pc w o (restrict (readsOf w o) s.regs) = some out`, giving `s.patch out`. `step?` is the same term mapped over `Option`.

**Tables.** `readsOf` and `edgesOf` stay tables. They moved to `Semantics.lean` and are now keyed by operand shape first. Typing checks them:

- a view access needs a proof that the register is in `readsOf` (`by rd`);
- an outcome needs a proof that its edge index is in `edgesOf` (`by edge_ok`).

Only proofs depend on the table's value, never data. So there are no casts in the computation, and `decide +kernel` evaluates `run` exactly as before.

**Kill ports.**

- `keepMask` and `Clobbered` are gone.
- A `CALL` edge kills registers `[A+C-1, 256)`.
- A `CONCAT` edge kills `[A+1, 256)`.
- `CStep` havocs the kills of the edge that was taken.
- The DI sweep uses `edgeMask`.

## Phase 1: SETUP (05:16–05:28, including reading the code)

| file | spec | proof | failed builds |
|---|---|---|---|
| `Lua/Bytecode/Section.lean` (new) | 28 | 19 | 0 |

## Phase 2: REFACTOR (05:28–05:41, plus a discipline fix at 05:48)

All required names are still proved:

- `step?_sound`, `step?_complete`, `Step.deterministic`, `BcSem.deterministic`;
- `bcSemFrom_iff`, `cbcSem_iff`, `Supported.defInit`, `reachable_defInit`;
- `condJump_ne_none`, `condJump_lt`;
- `while_bcSem`, `f1Ops_bcSem`, `f1b_bcSem`, `printPrint_bcSem`;
- every `*_supported`.

Two statements changed shape, and both are named structures (discipline R7):

- `Step.sim` now ends in `EdgeSim l m s₁' s₂'`.
- `DefInit.step` now ends in `StepPostSome`.

Two theorems are new:

- `xfer_sim` is L-B1 at the outcome level: `restrict_congr` followed by `▸`.
- `DefInit.fire` is the DI invariant for one outcome.

| file | original spec / proof | now spec / proof | git +/− (vs 79b6082, whole round) |
|---|---|---|---|
| `Lua/FragmentSound.lean` | 53 / **596** | 55 / **350** | +113 / −360 |
| `Lua/Bytecode/Exec.lean` | 115 / **261** | 22 / **67** | +10 / −301 |
| `Lua/Bytecode/Semantics.lean` | 184 / 0 | 275 / 8 (after refactor) | +271 / −137 (refactor) |
| `Lua/Fragment.lean` | 157 / 4 | 99 / 4 (after refactor) | +9 / −86 (refactor) |

**R1 compression: 857 proof lines become 417 (−51%).**

- No per-rule arm remains. The gate now reports `bc-rule-fanout: 2 cases — ok`; the 2 cases are the `split` bullets of `step?_sound`.
- The old code had about 205 lines of `Step.sim` arms and about 190 lines of `step?_sound`/`step?_complete` arms. They are replaced by:
  - `xfer_sim` (14 lines) and `Step.sim` (6);
  - `step?_sound` (9) and `step?_complete` (3).
- Most of the remaining 350 lines of `FragmentSound.lean` are the DI fixpoint-certificate machinery (sweep, fold stability, `mapM`). That part is generic and did not change.

**Where the spec grew, and the `testBit` friction.**

- Spec lines in `Semantics.lean` + `Exec.lean` + `Fragment.lean` went from 456 to 396: +91 in `Semantics.lean`, −93 in `Exec.lean`, −58 in `Fragment.lean`.
- The `xfer` arms are the rules. Measured at the end of the round, including H1–H5, they carry **81 proof obligations on 56 lines**:
  - `by rd` (register in the read mask);
  - `by edge_ok` (edge index in the table);
  - the `subst he` / `subst hce` proofs in the helpers.
- They also need 2 tactic macros (7 lines) and `match h :` names for the table discriminants.
- Lean's `match` does not generalize a discriminant that is hidden inside `edgesOf`, so the table cannot refine the expected type. Proofs have to go through the named `h`. That is the friction in practice: each proof is a single token, but the tactics had to be tuned. On the first attempt `simp [edgesOf, *]` looped on `edgesOf`'s equation lemmas; `unfold` followed by `simp only [*]` fixed it.

**Failed attempts.**

- 3 `lake build`s failed:
  1. `sweep` and `fixpoint` no longer take `p`;
  2. wrong binder count in the `CStep` case;
  3. a `Prop` structure cannot have an `Edge` field (fixed by making it a one-constructor inductive).
- About 5 `lake env lean` elaborations of `Semantics.lean` failed, all while tuning the macros.

## Phase 3: HELD-OUT (05:42–05:47; build and gate checks until 05:51)

Every H case is just its `xfer` arm plus table entries. There is no per-case theorem. Stepper soundness and completeness, the footprint/DI simulation, and determinism all hold for the new rules with **0 new proof lines**. The only per-case proof content is the `by rd`/`by edge_ok` tokens inside the spec.

| case | spec lines added (`Semantics` + `Fragment`) | proof lines | proof tokens inside spec |
|---|---|---|---|
| H1 `LOADK` of a string | 2 + 0 (−1) | 0 | 1 |
| H2 `CONCAT` (defs `{A}`, kills `[A+1,256)`) | 12 + 3 (−1) | 0 | 2 |
| H3 `LEN` of a string | 6 + 2 (−3) | 0 | 2 |
| H4 string `LT`/`LE` (`l_strcmp`, C locale) | 10 + 0 | 0 | 0 |
| H5 string arithmetic (`l_str2int`, `MMBIN*`, fall-through edge, `UNM`) | 69 + 1 (−10), plus fix-ups | 0 | 9 (+2 in `arithOut`) |
| **total, net** (`loc.py`: `Semantics` 275→360 spec, `Fragment` 99→102) | **+88 spec** | **0** | ≈16 |

**Validation.** Both theorems are new, and both were kernel-checked by `decide +kernel` on the first build attempt:

- `f4Strlite_bcSem : BcSem binaryHost f4StrliteProto "<c/tests/f4_strlite.expected>"` (`Lua/Programs/Validation.lean`): 4 proof lines.
- `f4Strlite_supported` (`Lua/Programs/Supported.lean`): 1 line.

**Generated.** `Lua/Programs/F4Strlite.lean` has 254 lines. It is added to `check.sh`'s drift list.

**Failed builds in this phase: 0.**

**Axioms.**

- `propext`, `Classical.choice`, `Quot.sound`: `xfer_sim`, `Step.sim`, `DefInit.fire`, `DefInit.step`, `step?_sound`, `step?_complete`, both determinism theorems, `Supported.defInit`, `bcSemFrom_iff`, `cbcSem_iff`, `f4Strlite_bcSem`.
- `propext`, `Quot.sound`: `restrict_congr`, `patch_agree`.
- `propext` only: `f4Strlite_supported`.

**`scripts/check.sh`.** Every stage passes except 3c. Stage 3c fails on `ast-construct-fanout` only, which is expected; `bc-rule-fanout` is ok. Stages 4, 5, 5b and 6 were run with 3c made non-fatal; stage 6 now expects 81 reports.

## Summary

| setup | refactor size (vs original) | held-out spec | held-out proof | wall time | failed builds |
|---|---|---|---|---|---|
| 28 spec + 19 proof | R1 proofs 417 vs 857 (−51%); spec −60 net; 0 per-rule arms | +88 spec (≈16 proof tokens inside it) | 0 metatheory lines + 5 validation lines | ≈35 min (05:16–05:51) | 3 |

## Findings

1. **H2's write set in SUITE.md is too small.** After `luaV_concat`, `OP_CONCAT` runs `checkGC(L, L->top)` with `top = ra + 1` (`vendor/lua-5.4.7/src/lvm.c:1580-1586`). In the atomic phase, `traversethread` sets every slot from `top` to `stack_last` to nil (`lgc.c`).
   - So registers *above* `A+B-1` can be clobbered too, which confirms R2-2's [check].
   - With kill ports the fix costs one token: `CONCAT` kills `[A+1, 256)`.
   - `f4_strlite` is still `Supported`, because `luac` never keeps a live local above a concatenation's base.
   - The SUITE's range-only write set would make `cbcSem_iff` unfaithful for `CONCAT`.
2. **`Step` became undefined where `edgesOf` is `none`.** In the section-typed form an outcome can only name an edge of the table. For example, a conditional test with no following `JMP` no longer steps; the old `Step` skipped to `pc+2`.
   - This absorbs L-B1's "edges exist" precondition into the semantics.
   - It changes nothing on `Supported` programs. All four old kernel validations and `f4_strlite` still agree with the ELF.
3. **SUITE.md's H5 wording is slightly wrong.**
   - String arithmetic gives an integer only when `luaO_str2num` itself gives one, i.e. `l_str2int` succeeds. `"10.0"+1` is the float `11.0`. It is not `luaV_tointegerns`.
   - `UNM` of a string calls `luaT_trybinTM(..., TM_UNM)` inside the `UNM` arm (`lvm.c:1540-1553`), not through a following `MMBIN`.
   - H5 as implemented: an arithmetic opcode whose operands are not both integers falls through to `MMBIN*` on a second edge that defines nothing. `MMBIN*` defines `R[A]` of the previous instruction (`prevInstr`) through `strArith` (`TM_ADD`/`SUB`/`MUL`/`MOD`/`IDIV`, at least one string operand, both converted by `l_str2int`).
4. **The typing does not make the tables faithful.** It checks that a rule reads only `readsOf` and writes only the defs of an `edgesOf` edge. A def mask that is wrong but too small would simply make `Step` write less. Faithfulness of the tables still rests on the kernel comparisons with the ELF. Kills are also chosen by hand, as finding 1 shows.
5. **Cost profile against contender A.**
   - The setup is 47 lines.
   - Metatheory is free per rule.
   - The whole price is paid in spec, about 1.4 proof tokens per rule line.
   - Nothing is derived: `readsOf`, `edgesOf` and `regTop` are still written by hand for every new opcode. H5 alone touched all three tables.

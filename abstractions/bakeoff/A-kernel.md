# Bake-off contender A-kernel (cluster `bc-rule-fanout`)

Abstraction: candidates C1+C2+C3 of `abstractions/ROUND-1.md` §3. Each
opcode is one term, a `Kernel` (`Lua/Bytecode/Kernel.lean`). A kernel has
static read ports, and edges that each carry a target, def ports and a kill
range. Its body maps the read values to the chosen edge index, the def
values and the printed values. The values are computed through the shared
primitive `δ` (`Lua/Bytecode/Semantics.lean`). Registers hold
`Option Value`: ⊥ is a stale value, and reading ⊥ is stuck.

- **`Step`** has one rule (`KStep.run`): fetch the instruction, then run its
  kernel. `step?` is the same term run in `Option` (`kstep`).
- **`reads`, `edges`, `regTop`** are folds of the kernel.
- **The opcode table** (`opKernel`) is built from combinators named after the
  `lvm.c` macros: `opArith`, `docondjump`, `setR`/`move`, `mmbin`, plus one
  small kernel each for `TESTSET`, `FORPREP`, `FORLOOP`, `CALL` and
  `CONCAT`.

Generic theorems, proved once in `Lua/Bytecode/Kernel.lean`:

| law | theorem |
|---|---|
| L-B2 | `kstep_iff` (`KStep ↔ kstep = some`), `KStep.det` |
| L-B1 with kills | `footprint`. Both states are stuck, or both step along the same edge (`StepMatch`), agree on what survives the kill ports plus the def ports, and change nothing outside the def and kill ports |
| certain answers | `Cert.step`, `Cert.star`, `certain_answers`. A run where every kill port that is not a def port holds anything (`HStep`) is matched by the ⊥-semantics run with the same output |

`keepMask`, `Clobbered`/`CStep` and the CALL special case are gone. `CALL`
kills `[A+C-1, maxstacksize)`, and `CONCAT` kills `[A+1, A+B-1]` (H2's write
set is the whole range: def `A`, kill the rest). The analysis is
`st[t] ⊆ (st[pc] \ kill) ∪ def`.

Lines are non-blank, non-comment Lean lines (census.py's convention; the
originals measure 596 + 261 as in SUITE.md). "Proof" means the lines of
theorem/lemma declarations, and "spec" means everything else.

## Phase 1: SETUP (05:16–05:38, 22 min, including about 9 min of reading and design)

| file | added | deleted | spec | proof |
|---|---|---|---|---|
| `Lua/Bytecode/Kernel.lean` (new) | 319 | 0 | 81 | 116 |

Failed builds: 0 `lake build`; 0 failing single-file checks.

## Phase 2: REFACTOR (05:38–05:50, 12 min)

| file | added | deleted | spec before → after | proof before → after |
|---|---|---|---|---|
| `Lua/Bytecode/Semantics.lean` | 255 | 202 | 192 → 229 | 0 → 0 |
| `Lua/Bytecode/Exec.lean` | 24 | 333 | 121 → 22 | 261 → 58 |
| `Lua/Fragment.lean` | 65 | 126 | 163 → 102 | 4 → 4 |
| `Lua/FragmentSound.lean` | 161 | 583 | 72 → 42 | 596 → 266 |
| `scripts/check.sh` | 4 | 2 | — | — |

**Compression of R1.**

| | original | re-seated | with the setup proofs |
|---|---|---|---|
| proof lines (FragmentSound + Exec) | 596 + 261 = 857 | 266 + 58 = 324 (−62%) | 324 + 116 = 440 (−49%) |
| per-rule proof arms (census) | 75 | **0** | 0 |

About 190 of the remaining 266 FragmentSound lines are the fixpoint
machinery (`LLe`, `foldl_stable`, `sweep_stable`, `fixpoint_spec`,
`mapM_range_some`, `Supported.defInit`). It is unchanged in substance and
has no per-opcode content. The rest is the bridge from the analysis masks to
the generic `Cert` (`DefInit.cert`, about 20 lines) and the corollaries.

Spec across the four files: 548 before, 395 after, and 476 with
`Kernel.lean`'s spec. The kernel table replaces the 27 `Step` constructors,
the `step?` arms, `edgesOf`, `reads`, `regTop` and `keepMask`.

All names are kept, and all are proved:

- `step?_sound`, `step?_complete`, `Step.deterministic`,
  `BcSem.deterministic`, `Final.not_step`;
- `Supported.defInit`, `DefInit.step`, `bcSemFrom_iff`, `cbcSem_iff`,
  `reachable_defInit`;
- `while_bcSem`, `f1Ops_bcSem`, `f1b_bcSem`, `printPrint_bcSem`, and every
  `*_supported` / `readsStale_unsupported`;
- the Corpus TV facts.

`CBcSem` is redefined as "havoc every kill port" (`HStep`), which includes
the old clobbering of registers at or above a call's results.
`condJump_ne_none` and `condJump_lt` are dropped (there is no `condJump`),
and `DefInitAt.pc_lt`/`DefInit.pc_lt` subsume them. The check.sh stage-6
list follows: it drops those two and adds `kstep_iff`, `footprint`,
`certain_answers` and `DefInit.cert`.

Failed builds: 0 `lake build`. 3 single-file `lake env lean` checks errored:
- `Semantics.lean`, once: `idiv` resolved to `BinOp.idiv`, and a
  multi-line structure instance did not parse;
- `FragmentSound.lean`, twice: an `if` that `simp` did not reduce, and
  implicit entry states that unified the wrong way.

## Phase 3: HELD-OUT (05:50–05:58, 8 min)

| case | spec lines | proof lines | what |
|---|---|---|---|
| H1 string literals | 0 | 0 | `LOADK`'s kernel already takes any non-float constant, and `Supported` is a fold of the kernel, so strings are admitted with no new line |
| H2 `CONCAT` | 11 | 0 | `Prim.concat` + one δ case, `Value.toStr?` (`%lld`), `concatK` (def `A`, kill `A+1..A+B-1`), a table entry |
| H3 `LEN` | 3 | 0 | `Prim.len`, one δ case, a table entry |
| H4 string order | 7 | 0 | `lexLt` (`l_strcmp` in the C locale), two δ cases |
| H5 string arithmetic | 56 | 0 | about 33 lines are `luaO_str2num`'s integer part (`str2int`, `digits`, `digitVal`, `isSpace`) and `Value.toInt?`. The other 23: `BinOp.ofTM`, `BinOp.strMeta`, `Prim.tm` + its δ case, `UNM` on strings, `opArith`'s fall-through edge to `MMBIN*`, `mmbin`/`flip`, and three table entries (`MMBIN`, `MMBINI`, `MMBINK`) |
| validation | 2 | 4 | `f4Strlite_bcSem`: `BcSem binaryHost f4StrliteProto "<expected>"` by `bcSem_of_run` + `decide +kernel`; `f4Strlite_supported` by `decide +kernel` |
| generated | 116 | 0 | `Lua/Programs/F4Strlite.lean` (`scripts/gen_proto.py`), registered in check.sh |

Every held-out case costs 0 lines of stepper soundness, completeness,
footprint or definite-initialisation proof: all of them are the generic
theorems. "`Supported`'s tables" for a case means its kernel entry.

| file | added | deleted |
|---|---|---|
| `Lua/Bytecode/Semantics.lean` | 122 | 3 |
| `Lua/Fragment.lean` | 6 | 5 |
| `Lua/Programs/Validation.lean` | 9 | 0 |
| `Lua/Programs/Supported.lean` | 4 | 0 |
| `Lua/Programs/F4Strlite.lean` (generated) | 254 | 0 |
| `Lua.lean`, `scripts/check.sh` | 6 | 2 |

Failed builds: 0 `lake build`. One full `check.sh` run failed stage 6 on the
axiom-report count (77 was hard-coded; it is now 81).

## Acceptance

`scripts/check.sh` passes every stage except 3c. In 3c, `bc-rule-fanout`
now has 0 cases; `ast-construct-fanout` still fails, as expected. Stage 6:
every listed theorem uses only axioms in {propext, Classical.choice,
Quot.sound}. There is no sorry, axiom, native_decide or raised limit.

## Summary

| setup | refactor size (vs original) | held-out spec | held-out proof | wall time | failed builds |
|---|---|---|---|---|---|
| 81 spec + 116 proof | 324 proof vs 857 (−62%); 440 with setup (−49%); 0 per-rule arms (was 75) | 79 (+116 generated) | 4 (validation only; 0 per case) | 42 min | 0 `lake build` (3 failing single-file checks, 1 check.sh count fix) |

## Findings

- **No law turned out false.** L-B1 with kills, L-B2 and certain answers are
  each proved once, with no opcode case split anywhere in the metatheory.
- **Certain answers needed one precise point:** when a register is both a
  def port and a kill port, the def wins (`writeDefs` runs after the kill
  filter), and `HStep` havocs only kill ports that are not def ports.
  Otherwise the stability condition `(M pc ∖ kill) ∪ def` is unsound.
- **Reads are per kernel, not per edge.** `FORLOOP`'s exit edge does not read
  `R[A]` in `lvm.c`, but its kernel's static read ports include it, so on
  exit the ⊥-semantics is stuck if `R[A]` is ⊥. This is invisible on
  `Supported` programs (the old `reads` mask already included `R[A]`). A
  per-edge read set would make it exact, at the cost of a less static term.
- **Edges must exist statically.** A conditional test whose next instruction
  cannot give a jump target now has no kernel (it is stuck), even on the
  skip path. This only affects malformed bytecode, which `Supported` already
  rejected.
- **`BcSem` now starts from all-⊥ registers** instead of all-nil.
  `bcSemFrom_iff` shows the two agree on supported programs.
- **The kill range of `CALL` is bounded by `maxstacksize`** (the frame). The
  old `Clobbered` was unbounded. Registers above the frame are never touched
  by supported programs, so `cbcSem_iff` loses nothing.
- **H1 was free.** In the incumbent the cost of H1 lived only in `Supported`'s
  hand table (`edgesOf` rejected string constants). Once the table is a
  fold of the kernel, that exclusion has nowhere to live.
- **H5's cost is value-level.** Most of H5 is `luaO_str2num`'s integer parser.
  The rest is one `MMBIN*` combinator, whose destination port is the
  previous instruction's `A`: a static port read from `pc - 1`, which the
  kernel term expresses without trouble. The three-valued δ that R2-3/R2-6
  asked for was not needed. "Both integers or fall through" is decided by
  the `opArith` combinator, and δ keeps `none` for errors.
- **The old constructor names are not kept as lemmas.** Nothing downstream
  inverted `Step` constructors (the TV facts use `BcSem.deterministic` only).

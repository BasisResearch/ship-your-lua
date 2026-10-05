# Round-4 A1 bake-off, axis B: contender B-SEGLOCAL (segment-local discharge)

The base is main `6defac8` (which includes BASE-S). The branch is
`worktree-agent-a93a0f796c7e17316`; this file's commit is the head.

## Summary row

| setup | callees | held-out hand lines (per case) | generated | CPU (user s) | peak mem | largest decl heartbeats | refactor `sim_MODK` (before → after) | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 709 Lean (`At` 596, `AtArm` 111, `AtAttr` 2) + 604 Python (`gen_lua_at.py`) | 88 (`divdi3_sum` 42, `idivC_eq`/`idiv_m1` 46) | **IDIV 53**, **FORPREP 64** (file lines, imports and opens included) | 1,533 (`Lua/Vm/At/{Modk,Idiv,Forprep}.lean`: 99 at-lemmas, call lemmas and fin lemmas) | generated 363; arms 27; library 9 | 3.7 GB (`At/Forprep`) | arm decls ≤ 37.9k; generated decls ≤ 197.8k (`FORPREP.fin_1`) | 31 + DivLib's split (≈ 60) → **57**, every path one declaration, no `armBody_split` | ≈ 12 `lake build`, ≈ 45 `lake env lean` | ≈ 3 h 35 min |

Lines are non-blank, non-comment lines, with `/- … -/` blocks and `--` lines
dropped (`tmpat/loc.py`, not committed). CPU and memory are one `lake env
lean <file>` per module (`/usr/bin/time`). Heartbeats are per declaration,
elaborated synchronously (`Elab.async false`), in `maxHeartbeats` units: the
default budget is 200k.

## What is proved

The full build passes: `lake build Lua.Vm.Sim.Kit`, and `scripts/check.sh`
(see "Gate" below). All the new theorems are in check.sh's stage-6 list.

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Sim.At.sim_IDIV` | `Lua/Vm/Sim/Kit/AtIdiv.lean` | `SimArm .IDIV` (held out) |
| `Lua.Vm.Sim.At.sim_FORPREP` | `Lua/Vm/Sim/Kit/AtForprep.lean` | `SimArm .FORPREP` (held out) |
| `Lua.Vm.Sim.At.sim_MODK` | `Lua/Vm/Sim/Kit/AtModk.lean` | `SimArm .MODK` (refactor; the kit's `Kit.sim_MODK` is kept) |
| `Lua.Vm.Sim.Kit.divdi3_sum` | `Lua/Vm/Sim/Kit/Divdi3.lean` | `__divdi3`'s summary: `a0 = m.sdiv n` for `n ≠ 0`, at the four sign paths |
| `Lua.Vm.Sim.Kit.idivC_eq`, `idiv_m1` | `Lua/Vm/Sim/Kit/IdivEq.lean` | `luaV_idiv` in `lvm.c`'s order: the C quotient, minus one when the signs differ and the remainder is nonzero |
| `Rgn.sep`, `AtFin.close`, `AtStep.seq` | `Lua/Vm/Sim/Kit/At.lean` | the regions are disjoint (once, from `Ranges`); the close from a fin row; composition |
| 99 at-lemmas | `Lua/Vm/At/*.lean` (generated) | e.g. `FORPREP.call_8001e200`: `luaV_tointeger` from its entry row to its return row |

The axioms are `[propext, Classical.choice, Quot.sound]` for every one of
them. No path that the kernel excludes is assumed. The stuck cases (`n = 0`,
step 0, non-integer operands) are refuted from `hk`. The machine-only paths
(the float helpers, the error exits) are never entered, because the kernel's
case has no `Step` there.

## The route

1. **Location-list rows (`At.lean`).**
   - The arm context is `Cx` (`p c s w ins`), with its facts in `Cx.Ok`.
   - A `Loc` is what a register holds, as a function of `Cx`:
     - a fetch-head register;
     - an affine address over the pointers and the instruction fields
       (atom-indexed slot labels: `base + 16·a + 48` is data);
     - a slot's or `K[C]`'s tag or payload in the *entry* memory;
     - an entry-memory cell;
     - the arithmetic the arms and helpers do (`add`, `sub`, `xor`, `srem`,
       `sdiv`, `udiv`, `umod`, `snez`).
   - The path's memory is a store log `Ent` over the entry memory. A spill
     cell (`sp+16`) and an out-parameter (`sp+40`) are just log entries: a
     later load reads the stored location back.
   - `At X pc L M c` is `SegSt` with pins `Loc.den X _` and memory
     `Log.den X M`. `AtStep` is a run between two rows.
2. **Generated at-lemmas (`scripts/gen_lua_at.py`).**
   - **The walk.** The generator walks each arm's paths over the generated
     segments with a symbolic `Loc` state:
     - loads are resolved against the log by region;
     - a branch is pruned when its operands are known;
     - a path ends at the head, or is dropped at an unsummarised or
       non-returning call.
   - **What it emits.**
     - One at-lemma per (segment, entry row), proved in its own declaration
       by `at_seg`, which runs the following inside that declaration:
       - the segment's bus conditions by `kit_disch`;
       - its guards from the at-lemma's guard *about locations* (`at_guard`);
       - its loads forwarded through the log (`atFwd` + `at_sep` with
         `Rgn.sep`);
       - the post-row by `at_pins`/`at_eq`, and the post-memory by `at_mem`.
     - One `call_<ret>` lemma per summarised call (`at_call`). Its frame is
       the row; it has no `HFrame` statement and no `divFrame`. Dead `s6`,
       `s10` and `t0` are pinned by `SegSt.pin22`/`pin26`/`pin5`.
     - One `fin` lemma per arrival at the head (`AtFin`: the pins, the frame
       and the stored slots).
3. **The arm (`AtArm.lean`).** Each path is the kit's M1 setup (forward
   kernel evaluation, unchanged), then `at_go NS`:
   - **`at_run`.** This chains at-lemmas by `At.run`. Candidates are found
     by name (pc, and the row's `ra` for calls) and filtered by the row/log
     names, so they meet syntactically.
     - Hypotheses are closed by `at_hyp`: `omega` for bounds, and `at_vals`
       for guards. `at_vals` is one `simp` over the path's value facts, with
       no memory.
     - The polarity is picked by which guard closes.
   - **`at_close`.** The fin lemma for the row, then `AtFin.close`.

## Lines and costs per case

| case | hand lines | declarations (heartbeats) | notes |
|---|---|---|---|
| IDIV | 53 (setup macro 9, 6 path lemmas, `sim_IDIV` 3) | zero 6.4k, m1 16.3k, same-sign 28.3k, different-sign (both helpers) 28.4k, fall 18.8k | both helper returns are generated rows; no split |
| FORPREP | 64 (`neg_step` 3, `FpQ`/setup 18, `msb_of_*` 5, 5 paths × 4, `sim_FORPREP` 10) | up-skip 29.7k, up-run 37.0k, down-skip 35.9k, down-run 37.9k, zero 14.9k | the KIT-2 lane could not fit one FORPREP path in 200k; here the largest is 37.9k |
| MODK refactor | 57 (with a 17-line fall path; the kit used `kitk_fall`) | zero 4.5k, m1 14.5k, rz 24.3k, same 30.6k, corr 28.6k, fall 15.7k | the kit's `modk_m1` was 196k and its general path ≈ 205k, which forced `armBody_split` |

**Generated cost.** The at-lemmas cost 7–58k heartbeats each. The sums per
arm are 800k (MODK), 790k (IDIV) and 1,168k (FORPREP). The **fin lemmas are
the costliest declarations**:
- 69–92k for MODK and IDIV;
- 108–198k for FORPREP (four slot and C-frame stores in the log).

Their frame proofs run `omega` over the negated `Slots`/`Scratch`/`CFrame`
implications once per store. This is where the budget bites next (see below).

R2-2's falsifier:
- (i) The standalone MODK seg4 at-lemma costs 86.8k (predicted under 60k).
- (ii) Using it costs **0.14k** (predicted under 10k).

The idea passes on (ii), the claim that matters.

## CPU and memory per module

| module | user s | wall s | peak RSS |
|---|---|---|---|
| `Kit/At` | 6.9 | 6.3 | 2.0 GB |
| `Kit/AtArm` | 1.6 | 2.0 | 1.9 GB |
| `Kit/Divdi3` | 6.8 | 7.2 | 2.0 GB |
| `Kit/IdivEq` | 0.5 | 0.7 | 0.8 GB |
| `At/Modk` (generated) | 107.8 | 27.6 | 3.3 GB |
| `At/Idiv` (generated) | 104.5 | 25.3 | 3.2 GB |
| `At/Forprep` (generated) | 150.5 | 40.6 | 3.7 GB |
| `Kit/AtModk` | 8.7 | 3.3 | 2.1 GB |
| `Kit/AtIdiv` | 7.1 | 3.1 | 2.1 GB |
| `Kit/AtForprep` | 11.5 | 4.0 | 2.2 GB |
| (before) `Kit/Modk` | 72.9 | 26.3 | 2.8 GB |

For MODK, the segment work moves from the arm (73 s, with near-budget
declarations) to the generated file (108 s, every declaration at most 92k).
The total CPU is higher, but no declaration is near the budget.

## What the route could not express

- **The close's frame is the costly declaration.** The `AtFin` frame and
  keep proofs reuse `kit_disch`'s `omega` with every region fact in context.
  `FORPREP.fin_1` uses 197.8k of the 200k budget.
  - The fix is to prove a store's region membership once and apply `Rgn.sep`
    against the excluded regions (as `at_sep` does for loads), or to split
    the fin lemma by field.
  - Not done. A longer arm (CALL, VARARGPREP) will need it.
- **`simp` would not forward loads.** `simp` with `ld1_wm8` did not fire on
  the generated terms, whereas `rw` with the same lemma did. The cause was
  not found.
  - The forwarder (`atFwd`) therefore finds each load in the goal at the
    `Expr` level and rewrites it by `MVarId.rewrite` with an explicitly
    instantiated lemma.
- **Paths that the generator cannot evaluate.** These are dropped and listed
  in each generated file's header:
  - the float helpers (`__floatdidf`, `fmod`, `__eqdf2`), never reached on F1
    values;
  - the error exits (`luaG_runerror`/`luaG_forerror`, via `auipc`);
  - Python's evaluator also stops on a slot load past a store at *another*
    field (`R[A]` against `R[B]`, a possible alias). None of the three arms
    has one.
- **Joins.** A segment after a join is emitted once per distinct entry row:
  - MODK `f7cc` 4×, IDIV `f74c` 3×, FORPREP `f878` 2×;
  - no location is generalised.
- **Hygiene pitfalls.** These cost iterations:
  - `rcases … with rfl` inside a macro binds a hypothesis named `rfl`;
  - a tactic run during `exact`'s elaboration sees unassigned metavariables;
  - the closers now run after `refine`.
- **Not reused.** The kit's `kit_run` polarity search, `ArmPre`/`AtRet`/
  `divFrame` and `HFrame` statements at splits are unused on this route.
  `HFrame` survives only inside the helper summaries.

## Forecast

- **VARARGPREP.**
  - **The obstacle.** `luaT_adjustvarargs` moves `func`, so the close is a
    re-witness with new pointers, not `AtFin.close` with the same `w`.
  - **The copy loop.** The row language has no loop rule. The copy loop
    (4 stores, stride 0 at `L->top`) needs a comprehension log entry, which
    is M-loop's, not this route's.
  - **Estimate.**
    - The at-lemmas for the straight parts: generated.
    - The arm, once a loop summary and a re-witness exist: about 40 lines.
- **CALL print.**
  - **Out of reach.** The callee chain (`luaD_precall` → `luaB_print` →
    stdio, 81 functions) is beyond what the generator's call table can hold.
  - **What the route offers.** A call lemma is cheap once a summary exists:
    `at_call` needs only the summary's term. The log also represents the
    callee's footprint on the stack and `L` as entries.
  - **The dominant cost.** The summary itself (thousands of lines, stdio
    step tables, A0.2).
  - **Estimate.** The arm itself, about 60 lines.
- **RETURN.**
  - **What is generated.** The return chain to the HTIF exit is a `Final`
    clause, not a `SimArm`. The at-lemmas cover its segments up to
    `luaD_poscall`.
  - **What is missing.** Its nil-fill loops (×2) again need a loop
    summary.
  - **Estimate.** About 30 lines over a poscall summary.

## Gate

The full `scripts/check.sh` was run with stage 3c removed. Every other
stage passes, including:
- stage 1, which now includes `gen_lua_at.py --check`;
- stage 3b (`discipline: OK (12 rules)`);
- stage 5 (`lake build Lua Vsa VsaIris`);
- stage 5b;
- stage 6 (all axiom reports standard, the new theorems included).

Stage 3c (the abstraction gate, exempt by the brief) fails:

    a1-kit-arm: 35 cases — FAIL (first-quarter mean 3.2 lines, last-quarter mean 8.4)

This contender's path lemmas (`modk_*`, `idiv_*`, …) fall in the cluster's
selector.

## Files

- **Library:**
  - `Lua/Vm/Sim/Kit/At.lean`;
  - `Lua/Vm/Sim/Kit/AtArm.lean`;
  - `Lua/Vm/Sim/Kit/AtAttr.lean`;
  - `Lua/Vm/Sim/Kit/Summaries.lean`.
- **Generator:** `scripts/gen_lua_at.py`.
- **Generated:** `Lua/Vm/At/{Modk,Idiv,Forprep}.lean`.
- **Callees:** `Lua/Vm/Sim/Kit/Divdi3.lean`, `Lua/Vm/Sim/Kit/IdivEq.lean`.
- **Arms:** `Lua/Vm/Sim/Kit/{AtModk,AtIdiv,AtForprep}.lean`, indexed by
  `Lua/Vm/Sim/Kit.lean`.

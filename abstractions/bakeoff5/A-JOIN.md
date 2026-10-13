# Round-5 bake-off, axis A: contender A-JOIN

Base: main `754321c` (round 5 §1–5). Branch `worktree-agent-a477dd8e35837a950`.

The design is ROUND-5 §3's converged one:
- comparison atoms keyed by the unordered pair of model values;
- forks split on the Boolean the machine reads;
- idioms evaluated on the four answers;
- cut points at the machine's joins, proved once;
- per-operand views;
- one `sgnBound` shared by FORLOOP and FORPREP.

There is no symmetry group and no feasibility filter.

**Results:**
- **SUB** is closed under `SoftFloatSpec`.
- **FORPREP**'s float loop is closed. Its coerced classes are a named premise.
- **LT** is closed except its `luaV_flttointeger` paths, which are a named premise.
- **FORLOOP** drops from 29 to 11 lines and from 56.7–59.1k to 37.1k heartbeats.

## Summary row

| setup | held-out hand lines (per case) | generated | CPU | peak | largest decl | refactor before → after | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 562 hand lines: Lean 432 (`AtJoin` 348, `AtJoinRow` 13, kit edits +71/−32), generators +130/−11 | SUB 14 · FORPREP 15 (+3 open premise) · LT 19 (+4 open premise); mean 16.0 | 2,515 new lines (`At/Sub` 815, `At/ForprepF` 724, `At/LtF` 976), `At/Forloop` +77/−92, 15 `Segs` modules ±291 (pin lists), 6 one-line drifts | arms 3.9–7.4 s each; at-lemma modules 50–164 s each; 454 s user over the 10 new or changed modules | 3.6 GB (`At/LtF`) | hand: `sim_LT_flt` 101.7k; generated: `ForprepF.fin_frame` ≈134k (measured on the same tactic before the split) | FORLOOP 29 → 11 lines, 56.7–59.1k → 37.1k heartbeats, file CPU 4.4 → 3.9 s | 21 `lake build` (20 module, 1 full-build OOM at 12 GB); ≈15 scratch `lake env lean` | ≈ 1 h 40 min to the last proof; ≈ 2 h 30 min with the measurements and the build |

**How lines were counted.**
- A hand line is not blank and not a comment. `--` comments and `/- … -/` blocks, docstrings included, are dropped.
- Per case: the declarations of the case. That is the arm theorem plus its class predicates and the named premise. Imports, `open` and `namespace` lines are not counted.
- The per-file totals are FORLOOP 19, SUB 22, FORPREP 26 and LT 31.
- Generator lines are Python lines that are not blank and not a `#` comment (`git diff 754321c`).

**Per-declaration heartbeats** (`abstractions/bakeoff5/ajoin/Measure.lean`, `Elab.async false`, in thousands of `maxHeartbeats` units):

| declaration | k |
|---|---|
| `sim_FORLOOP_flt` | 37.1 |
| `sim_SUB_flt` | 86.5 |
| `fp_flt3` | 58.3 |
| `sim_LT_flt` | 101.7 |

Per-module CPU and peak are in `abstractions/bakeoff5/ajoin/measure.out`. The scripts are `measure.sh` and `build.sh`.

**Build and gate.**
- **The full build** (`lake build Lua Vsa VsaIris`, 1,888 jobs) completed. A one-shot build under the 12 GB cap was killed (SIGTERM, out of memory: lake compiles independent modules in parallel). `build.sh` therefore first builds the stale modules one at a time in import order (22 min wall, 0 failures), then runs the full build, which confirms with nothing left to compile (`build.out`).
- **`scripts/check.sh --static-only`:** stages 1–3b OK; 3c FAILs as intended: `a1-float-arm`, 15 cases, first quarter 2.7, last quarter 12.7.
- **Stage 6**, run apart from the same `Axioms.lean`: 408 reports, every axiom in {propext, Classical.choice, Quot.sound} (`axioms.out`). Stage 5b (OS traces) was not run; nothing it reads changed.

## What is proved

All of the following are under `SoftFloatSpec`, with axioms ⊆ {propext, Classical.choice, Quot.sound}, as `scripts/check.sh` stage 6 checks.

| theorem | file | statement |
|---|---|---|
| `sim_FORLOOP_flt` | `Lua/Vm/Sim/Kit/AtFltForloop.lean` | `SimArmOn .FORLOOP FltStep` (refactor) |
| `sim_SUB_flt` | `Lua/Vm/Sim/Kit/AtFltSub.lean` | `SimArmOn .SUB FltBC` (`FloatArms.SUB`) |
| `fp_flt3` | `Lua/Vm/Sim/Kit/AtFltForprep.lean` | `ArmBody .FORPREP FpFlt3` (three floats) |
| `sim_FORPREP_flt` | same file | `FpCoerce_Statement → SimArmOn .FORPREP ForCoerce` |
| `sim_LT_flt` | `Lua/Vm/Sim/Kit/AtFltLt.lean` | `LtF2I_Statement → SimArmOn .LT FltAB` |

**Open premises** (named, typed, documented, listed in PHASES.md):

- **`FpCoerce_Statement`** (`ArmBody .FORPREP FpCoerce`) covers the classes that are neither three integers nor three floats.
  - The machine calls `luaV_tonumber_` (`0x8001ab58`; `l_strton` → `strtod` on a string, a conversion on an integer) and `luaV_tointeger` on a non-integer limit.
  - On the at-route, a call node's post-log must state the exact memory, including the callee's frame stores.
  - A value-only premise cannot supply that. A level-(a) summary of the two callees can, but `l_strton`/`strtod` makes that a callee project.
- **`LtF2I_Statement`** (`ArmBody .LT LtF2I`) covers an integer outside `l_intfitsf` against a float. This is `LTintfloat`/`LTfloatint`'s `luaV_flttointeger(F2Iceil/F2Ifloor)` chain. Two things are missing:
  - **`floor`'s summary.** newlib's `s_floor.c` itself calls `__adddf3` and `__gedf2`, and `gen_lua_fn.py` lifts no routine that calls another soft-float routine.
  - **The value equation `__fixdfdi(floor x) = (floor x).toInt64`** under the range atoms. It is not an atom decision.

  The walk stops at `jal floor` (`0x8001f900`, `0x8001fb00`), and the hand side hands these classes to the premise in one `first` alternative.

## The abstraction as built

**Setup: `Lua/Vm/Sim/Kit/AtJoin.lean` (348), `AtJoinRow.lean` (13).**

Pair atoms:
- `model_cmp_swap`: `compare y x = (compare x y).map swap` at model level, from `F64.compare_swap`.
- `model_{lt,le,beq}_cmp`, `toModel_add`.
- `decForallAtom`: `decide` over the four answers of one atom.

`at_atoms` is the leaf refutation:
1. Rewrite the path's fork facts (`hf_<pc>`) and the kernel's test (`hq`) to `Float.Model.compare` terms, using the routines' `S`, `F64`'s bridge and the payload models.
2. Key every comparison by its unordered pair, oriented as the kernel's test names it first.
3. Generalise the atoms, and the `k` bit as a Boolean atom.
4. Refute with one closed `decide`.

There is no idiom lemma. The machine's `blez`, `slti 1`, `not; srli 63`, `sgtz` and `srli 63` are evaluated by that `decide` on the four answers, so `relOf` comes by evaluation.

Boolean forks, `at_step1`/`at_walk`:
- `at_run`'s chaining, except that a guard over a soft-float answer or a join (`Loc.fn`) is never closed by trial.
- The run splits on the very `Bool` the branch reads (`rcases Bool.eq_false_or_eq_true G`), and each side takes its lemma by `assumption`.
- The kernel is not split before the run.
- At each leaf, `at_leaf` splits the kernel's test (`split at hk`), refutes the infeasible side with `at_atoms` and closes the other with `at_close`.

Join cuts:
- **Generator.** `JOINS = {arm: {join pc: (register, fork pc)}}` in `gen_lua_at.py`.
  - Each side's path ends in `join_<pc>`, an `AtStep` of no machine step from the side's row to the join row. The joined register is `.fn j<k>`, with `j<k> X := if G then v_t else v_f` (`@[at_fspec]`).
  - The tail is walked and emitted once.
  - `joinPcs` names the cut points for the hand side.
- **Hand side.** `at_cut` states `tail_<pc> : ∀ c₁, Steps c c₁ → At X pc row log c₁ → goal` once and proves it by the run and the leaves from the join row. A side that reaches the join ends in `exact tail_<pc> _ acc h0`.
- **Sites.** FORLOOP `0x8001e194` (`a5`), FORPREP `0x8001c1b8` (`a4`).

`sgnBound R st a b := if lt 0 st then R a b else R b a`:
- `forloop_sgnBound` and `forprep_sgnBound` are `rfl`.
- `sgnBound_eq_true` folds `simp`'s nested Prop-`if` into one Boolean, so the leaf splits it once.
- `sgnBound_atoms` is the skeleton on its two atoms.

Per-operand views:
- `ValRepr.numView` sorts a register into float (model and sign), integer (payload) or no number, with a uniform third component so one `rcases` pattern serves all three.
- Tactics: `num_reg`, `num_regf` (an integer split by the kernel's own `l_intfitsf`), `flt_reg_q`/`flt_reg_s`/`flt_reg`/`flt_reg2`, and `at_tags` (tag guards from whatever view facts are in context, `fits_geu`/`fits_ltu` for `intfitsf`).

**Kit changes forced by the held-out cases:**
- **`at_fin` (`Kit/At.lean`)** handled at most 2 stored slots, and `at_new` (`AtArm`) at most 3. FORPREP's float loop stores 4.
  - Both were generalised: `repeat' apply And.intro`, six alternatives.
  - A fin with more than 2 slots is split by the generator into `fin_frame`/`fin_keep` declarations (`at_fin_with`). The one-declaration form was ≈255k heartbeats, over budget; the frame part alone is ≈134k.
  - `at_fin` is now `at_fin_frame`/`at_fin_keep`/`at_fin_slots`/`at_fin_bound`, with no duplicated text.
- **`WinFrame` (`Kit/AtCond.lean`)** now admits C-frame stores. A float path spills to `luaV_execute`'s frame (`sd sp+16`), and `updatetrap`'s reload had demanded that frame unchanged.
- **`gen_lua_arms.py`:**
  - SUB, FORPREP and LT join `FLOAT_ARMS`.
  - A soft-float call node's arguments (`a0`, `a1` for a binary routine) are kept live into the `jal`.
  - 15 `Segs` modules regenerate with extra pins. `Lua/Vm/Sim/Arms/Sub.lean` (the frozen `gen_lua_arm.py` route) regenerates with one argument more.
- **`gen_lua_at.py`:** `sgtz`, the pseudo-arms `OP_FORPREP_F`/`OP_LT_F` over the real arm's segments (`SEG_OP`), and `FCALLS` for `__floatdidf` and `__subdf3`.

## What the route could not express

1. **Joins across operand classes with different logs.**
   - SUB's machine joins at `0x8001e528` (`s4`) and `0x8001e52c` (`a1`) per operand. That is exactly the per-operand coercion view.
   - But the sides differ in `__floatdidf`'s frame clobber (`Ent.clob`), and `JOINS` takes binary forks with equal logs.
   - So SUB's three float paths each keep their own `__subdf3` call lemma. This is 86.5k heartbeats; the `(flt, flt)` class runs twice, once from each side of `FltBC`.
   - The fix is a join log, a `clob` whose content is `if class then k else id`, plus `memPatch_self`. It is not built.
2. **Callee premises.**
   - The at-route states exact memory, so a callee outside the pilot needs a summary with its frame, not a value premise.
   - This blocks `luaV_tonumber_`/`luaV_tointeger` (FORPREP) and `floor` (LT; and 13 more fields).
3. **Value equations inside a leaf.**
   - The f2i chain's `__fixdfdi` result is an integer the machine compares with `i`.
   - Relating it to the kernel's `toInt64` needs a range-conditional lemma, which an atom `decide` cannot give.
   - L5-chain's "three more atoms" holds for the forks, not for the final value.
4. **"One closed `decide` per arm"** became one per refuted leaf.
   - FORLOOP has 2 machine leaves after the cut × 1 refuted kernel side.
   - SUB has none; it has no fork on a soft-float answer.
   - LT has one per fork leaf, with the `k` bit as a second Boolean atom.
   - A per-arm table (`sgnBound_tab`) would need the machine's decision function stated by hand; the per-leaf form needs nothing.
5. **Tactic hazards met:**
   - `case'` matches tag suffixes, so `case' inr` hit an inner `rcases` goal. Fixed by named holes `?fa`/`?fb`.
   - The rcases pattern `_` clears a hypothesis, which dropped the view's tag facts. Fixed by naming them.
   - The kernel's list `match` needs two registers inverted together (`flt_reg2`).

## Forecast for the other 33 `FloatArms` fields

The arm side now costs about 10–20 lines per field. What blocks the rest is callee summaries.

| group | fields | forecast |
|---|---|---|
| GEI-like | LEI, GTI | ≈ 10 lines each with `num_regf` off and the immediate; GTI's swapped `__gedf2(x, imm) > 0` is one oriented atom, free |
| UNM | UNM | inline sign flip, no call: ≈ 8 lines, no atoms |
| `op_arithf` with `__adddf3`/`__subdf3` | ADD, ADDK, SUBK | ADD is SUB's 14 lines, made a 3-line instance once the class block is factored into one `op_arithf` macro. K forms need a `K[C]` view (`num_reg` over `kval`, ≈ 10 setup lines) |
| needs a new level-(a) summary | MUL, MULK (`__muldf3`), DIV, DIVK (`__divdf3`), POW, POWK (`pow`), MOD, MODK (`fmod` + `nummod`'s sign fix, 2 atoms `{0,m}`, `{0,b}`, decided by the leaf) | arm side ≈ 15 lines each; blocked on `gen_lua_fn.py` lifting `__muldf3`/`__divdf3` (limb arithmetic through `__muldi3`/`__udivdi3`) and libm |
| f2i chain | BAND, BOR, BXOR, SHL, SHR, BANDK, BORK, BXORK, BNOT, SHRI, SHLI, IDIV, IDIVK (13), LE's f2i paths | blocked on `floor`'s summary and the `__fixdfdi` range value equation, as `LtF2I_Statement`. With both, the forks are 3 atoms per chain and the walk/leaf machinery applies unchanged |
| LE | LE | LT's 19 lines with `leNum`; the same open f2i premise |
| callee semantics | EQ, EQK | `luaV_equalobj`'s float case (F2Ieq through `floor`): blocked like the f2i chain |
| FORPREP coerced | (FORPREP) | blocked on `luaV_tonumber_`/`luaV_tointeger` summaries |

**Heartbeats.** The per-arm cost is the walk once, plus per machine leaf a leaf refutation of about 2–3k. The budget forecast from §1.3 (15k per outcome) no longer applies: LT's 24 float paths cost 101.7k across 6 classes, and FORLOOP-like arms are 37–58k.

## Commits

- `4e9ec5e` Boolean forks, join cuts, pair atoms; FORLOOP float refactored
- `f0d5880` SUB with a float operand by per-operand views
- `3983c28` FORPREP's float loop on three floats (join at `0x8001c1b8`)
- `42f4381` LT with a float operand (f2i paths open), FORPREP float arm (coerced classes open)
- `0301d4f` the join cut proved once (`at_cut`), `sgnBound` folds the kernel's test
- (final) report, `check.sh` stage-6 entries, PHASES row, measurements

# Round-5 bake-off, axis A: contender A-TREE (answer trees, the control)

Base: main `eb982c0`. Branch `worktree-agent-ae439782cb7f12a75`; this file's
commit is the head. Round 1's form of the float-arm abstraction
(`fanout/R5-R1-3.md` §A, `R5-R1-4.md` §B–C), built to measure round 2's
objection (suffix replay under a 4-way split).

Lines are non-blank, non-comment lines. CPU and peak are one
`lake env lean <file>` per module (imports built), `/usr/bin/time`, under a
12 GB scope. Heartbeats are per declaration, in `maxHeartbeats` units (limit
200k), read from the `at_tree.log` counters (`IO.getNumHeartbeats`).

## Summary row

| setup | held-out lines (per case) | generated | CPU (user s) | peak | largest decl | refactor before → after | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 298 Lean (`AtTree` 294, `AtTreeAttr` 4) + 39 Python (`gen_lua_at.py`, `gen_lua_arms.py`) + 2 kit fixes (`WinFrame` over `Win`, `at_fin` for > 2 stored slots) | **SUB 5** (proved); **LT 18** (9 proof + 9 split/defs; proved except the f2i classes, premise `LtF2i_Statement`); **FORPREP —** (not proved: obstruction below) | `At/Sub` 694, `At/LtFlt` 833; 17 segment modules re-emitted (+341/−309, call arguments carried to the `jal`) | arms: Sub 4.5, Lt 8.4, Forloop 7.8, `AtTree` 4.2; generated: `At/Sub` 114.6, `At/LtFlt` 170.7 | 3.7 GB (`At/LtFlt`); arms 2.3 GB | `sim_LT_fit` **153.5k**; `sim_FORLOOP_flt` 139.8k; `sim_SUB_flt` 86.0k | `sim_FORLOOP_flt` **29 → 9** lines, **59.1k → 139.8k** heartbeats | ≈ 25 (single-file), 3 module builds, 13 OOM-killed full builds | ≈ 2 h |

## What is proved

All under `SoftFloatSpec` (the existing level-(b) premise); axioms
`[propext, Classical.choice, Quot.sound]` (check.sh stage 6 list extended).

| theorem | file | statement |
|---|---|---|
| `sim_SUB_flt` | `Lua/Vm/Sim/Kit/AtFltSub.lean` | `SimArmOn .SUB FltBC` — the `FloatArms.SUB` field, complete |
| `sim_LT_fit` | `Lua/Vm/Sim/Kit/AtFltLt.lean` | `SimArmOn .LT LtFit`: `FltAB` with every integer operand within `±2^53` |
| `sim_LT_flt` | same | `SoftFloatSpec → LtF2i_Statement → SimArmOn .LT FltAB` |
| `sim_FORLOOP_flt` | `Lua/Vm/Sim/Kit/AtFltForloop.lean` | refactored onto the tree, same statement |
| `SimArmOn.of_split` | `Lua/Vm/Sim/Kit/AtTree.lean` | an arm's family from its parts on and off `R` |

Open, named: `LtF2i_Statement` (LT with an integer outside `±2^53` against a
float: `luaV_flttointeger`'s chain). PHASES.md row added.

## The route (`Lua/Vm/Sim/Kit/AtTree.lean`)

1. **Per-class views** (`at_view [r₀, …]`): each read register is split into
   `flt | int | other` (`Value.cls3`); the operand predicate `hT` and the
   kernel (`hk`, by constructor cases for `other` where the kernel matches on
   constructors) refute classes; each surviving float is read as
   `F64.toModel` of its slot's payload (`htg_k` its tag), integers as their
   payload, `other` as two tag inequalities. The kernel is restated over
   bits (`tree_view`: `model_add`, `model_lt`, `model_ofI`, …;
   `tree_kernel`: `δ`, `fastArith`, `ltIntFloat`, `intfitsf_view`, …).
2. **Answer tree** (`at_tree NS`): walk the generated at-lemmas; at a fork
   whose guard (after the call sites' specs) still mentions
   `F64.compare a b`, split it **four ways** (`ho_k`, and its swap
   `ho_k'`); a guard on the instruction's `k` is a 2-way atom. Guards close
   by evaluation on the closed answers (`at_thyp`: one simp, then
   `decide +kernel`). At the fetch head the kernel is evaluated under the
   leaf's atoms and the arm closes (`at_tleaf`).
3. **Feasibility filter**: none was needed. Every case's machine and kernel
   compare the same pairs (up to swap, which `ho_k'` covers), so no
   infeasible atom combination reached a leaf where the two sides disagree.
   No filter was implemented.

Per arm the proof is `kit_setup; at_view [...]; at_tree NS` plus the arm's
own facts (FORLOOP's jump target, LT's `kit_nj` and the `LtNoFit` split).

## Measurement: round 2's objection (suffix replay) holds

FORLOOP, 4 kernel outcomes, 2 machine forks, 2 atoms (`compare(step, 0)`,
`compare(limit, idx)`):

| | float-m0 (`at_go` per kernel outcome) | A-TREE (4-way per atom) |
|---|---|---|
| hand lines | 29 | 9 |
| runs to the fetch head (leaves) | 4 | **16** |
| total heartbeats | 59.1k | **139.8k** |
| view / register reads | 6.6k (`kit_reg` ×3 + refute) | 15.0k (`at_view`) |
| closes | 10.8k | **51.8k** (16 × 3.2k) |
| segment steps taken | 34.0k (incl. rejects) | 21.3k |
| wrong-polarity rejects | 10.3k | 13.3k (9) |
| fork detection (guard simp) | — | 18.9k |

- The prefix runs once (no prefix replay), but every suffix after a fork
  is replayed for each of the 4 answers, where the machine reads one
  Boolean: `compare(step,0)` ∈ {lt, eq, none} all take `blez`'s side. The
  leaf count is 4^atoms; the closes alone are 5× the incumbent's.
- LT (`sim_LT_fit`): 3 classes × 4 answers × 2 values of `k` = **24
  leaves**, 153.5k heartbeats (closes 33.6k, fork detection 39.0k, steps
  34.5k, rejects 21.2k): one declaration, 77% of the budget, with the f2i
  classes not even included.
- SUB (no comparison atom): 5 classes, 5 leaves, 86.0k. The view is what
  pays here (classes are split before the run, so the shared prefix
  `d964…d994` runs 5×).

Lines fell sharply (FORLOOP 29 → 9, SUB 5, LT 9 for its proved part); the
cost moved into heartbeats, which grow with 4^atoms × 2^bools × classes.

## What the route could not express

1. **LT's `luaV_flttointeger` chain** (`LtF2i_Statement`). Its paths call
   libm `floor` (no level-(a) summary: needs a premise providing a call node
   with its frame, ≥ 112 bytes, beyond `at_fnSp`'s 48), load `-2^63`,
   `2^63`, `1.0` from `.rodata` by `auipc`+`ld` (the at-lemma generator
   stops at an address built from `auipc`), and compare `__fixdfdi`'s result
   with the integer, which needs `Fixdfdi.S x = (F64.toModel x).toInt64` for
   `-2^63 ≤ x < 2^63` (not proved). Its atoms (`compare(f, -2^63)`,
   `compare(f, 2^63)`, `compare(B, floor B)`) would add 4^3 leaves per class
   (forecast below).
2. **FORPREP** (`ForCoerce`), not proved. Machine-checked obstruction:
   the generated at-lemmas of its float loop (`OP_FORPREP_FLT`, the
   all-float path; generator entry reverted, output kept out of the tree)
   fail in `fin` (`ForprepFlt.lean:1066`, 4 stored slots over a log of 12
   entries with three reloaded spills): `whnf` timeout at 200k heartbeats in
   `at_fin`'s memory-frame simp. (`at_fin` also could not split more than two
   stored slots: fixed, `repeat' refine And.intro`.) The coerced classes
   further need `luaV_tonumber_` (3 sites) and `luaV_tointeger` on a
   non-integer limit as call nodes with out-parameter stores (`sp+32/40/48`),
   which `call_effect` has no shape for.
3. **Generic Boolean atoms.** Only `F64.compare` and `ins.k` are atoms; an
   integer guard (`l_intfitsf`) had to become a class refinement by a named
   split (`LtNoFit`, `SimArmOn.of_split`) and a view lemma
   (`intfitsf_view`).
4. **Infrastructure the held-out cases forced** (not tree-specific):
   call nodes' argument registers carried through a pass-through segment
   (`gen_lua_arms.py` `FLOAT_NARGS`), `sgtz`/`sext.w` of an answer in the
   at-walk, `WinFrame` over `Win` (LT spills `R[B]` to `sp+16`, which the
   jump-target read must cross), aliases for a second at-lemma module of an
   arm (`ALIAS`, `LtFlt`).

## Forecast for the other 33 `FloatArms` fields

Lines: the route makes an arm `kit_setup; at_view; at_tree` (5–9 lines),
provided the generator emits its float paths. Heartbeats decide:

| shape (§1.3) | fields | atoms per leaf path | leaves (classes × 4^a × 2^k) | forecast |
|---|---|---|---|---|
| GEI-like | LEI, GTI, UNM | 1 compare (+k) | 8 | ≤ 60k: fits |
| ADD-like | ADD, ADDK, SUBK (+MUL, MULK, IDIV, IDIVK, MOD with callees) | 0 | 4–5 | 80–90k like SUB; MUL/DIV/IDIV/MOD need `__muldf3`/`__divdf3`/`floor`/`fmod` call nodes (no level-(a) summary) |
| all-float | DIV, DIVK, POW, POWK | 0–1 | 4–8 | blocked on `__divdf3`/`pow` summaries |
| f2i family | BAND/BOR/BXOR, SHL/SHR, BANDK…, BNOT, SHRI/SHLI, LT/LE f2i | 3–4 per operand | 4^4 × classes ≈ 256–1024 | **over 200k** per declaration at ≈ 1.4k/leaf (LT: 33.6k/24); needs a per-class split into separate declarations and still exceeds per class |
| FORPREP | — | 2–3 | 16–64 | blocked (obstruction 2) |
| EQ, EQK | callee | — | — | float semantics inside `luaV_equalobj` |

So 13 fields (the f2i family and LT/LE) exceed the budget under a 4-way
split; a Boolean split on the bit the machine reads (A-JOIN) would give
2^atoms instead.

## Gate

- `lake build Lua Vsa VsaIris`: OK (1924 jobs). Under the 12 GB scope the
  default parallelism was OOM-killed (13 tries); `LEAN_NUM_THREADS=4` builds.
  The frozen kit route's `Lua/Vm/Sim/Arms/Sub.lean` was re-emitted by
  `gen_lua_arm.py` (SUB's segments carry two more registers).
- `scripts/check.sh`: all stages OK, 3c included (`a1-float-arm: 14 cases —
  ok (first 2.7, last 5.0)`; one open named premise, `LtF2i_Statement`).
- Axioms of `sim_SUB_flt`, `sim_LT_fit`, `sim_LT_flt`, `sim_FORLOOP_flt`,
  `SimArmOn.of_split`: `[propext, Classical.choice, Quot.sound]`.

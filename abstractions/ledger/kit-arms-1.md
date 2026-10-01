# Kit lane 1: the arithmetic and bitwise family

Route: the kit (`Lua/Vm/Sim/Kit`, CLAUDE.md's A1 row). Targets, in priority
order: MULK, MODK, IDIV, IDIVK, UNM, SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK.

**Status: stopped by the gate after MODK.** `abstractions/gate.py`'s cluster
`a1-kit-arm` reached 9 cases and failed: the first-quarter mean is 6.0 lines,
and the last-quarter mean is 5.0, not a third cheaper. The lane rule is to
stop and report, so IDIV … BXORK are not attempted (see "Gate" below).

Lines are non-blank, non-comment lines; docstrings and `/- … -/` blocks are
dropped. Hand lines are the per-path `ArmBody`/`ArmPre` lemmas plus `sim_X`,
as the gate counts them. Build numbers are `lake env lean <file>` alone,
under the 30 GB cap (user CPU, wall, peak RSS).

## Arms

| arm | file | hand lines (per declaration) | total hand | user CPU | wall | peak |
|---|---|---|---|---|---|---|
| MULK | `Kit/Mulk.lean` | `mulk_int` 10, `sim_MULK` 2 | 12 | 17.3 s | 15.5 s | 2.2 GB |
| MODK | `Kit/Modk.lean` | `modk_zero` 2, `modk_m1` 2, `modk_call` 6, `modk_rz` 3, `modk_same` 4, `modk_corr` 4, `sim_MODK` 2 | 23 | 76.4 s | 80.3 s | 2.8 GB |

Both are built, and their axioms are {propext, Classical.choice, Quot.sound}
(stage 6 lists `sim_MULK`, `sim_MODK`, `sim_div`, `armBody_split`,
`sim_arithK`, `Ranges.k_getElem_wm8`).

## Setup

| item | file | lines | CPU |
|---|---|---|---|
| `K[C]` operands: `BothIntK`, `sim_arithK`, `Core.kptr_ld`, `Ranges.k_{getElem,bytesT1,bytesT8}_wm8`, `kitk_rd` (runner normaliser and `kit_side_pre`), `kitk_ints`, `kitk_fall` | `Kit/K.lean` | 96 | 1.9 s |
| division arms: `DivPath`, `sim_div`, `kit_div_{zero,m1,close}`, the split at a helper's return (`AtRet`, `ArmPre`, `ArmPost`, `armBody_split`, `kit_div_{pre,post}`), `imod_m1` | `Kit/DivLib.lean` | ≈ 150 | 2.9 s |
| `bgeu_one`, `srem_neg_one`, moved out of `Kit/Mod.lean` (net 0) | `Kit/DivBits.lean` | 20 | 1.3 s |
| `kit_side_pre` hook (a normaliser before `kit_side`'s closers; default: none) | `Kit/Run.lean` | +10 | — |
| `bitwiseRK` (BANDK/BORK/BXORK need an integer `K[C]`) | `Lua/Bytecode/Semantics.lean` | +11 | — |
| generator: the 12 ops in `SIM_OPS`; helpers `__divdi3` and `__umoddi3` (its sign fix-ups); `jr t0` as a return in the liveness | `scripts/gen_lua_arms.py` | +16 (Python) | — |
| `__umoddi3` code pins | `scripts/gen_lua_code.py` | +2 (Python) | — |

Generated: `Lua/Vm/Arms` and `Lua/Vm/Code` changed by about +10,250 −3,900
(the 12 arms' segments now carry the fetch-head pins, and the new helper
segments `Segs/{Hdivdi3,Humoddi3}`).

## What cost the most

- **The heartbeat budget.** With `savestate`'s two stores in front of every
  read, a whole general `OP_MODK` path (the run to `__moddi3`, the call, the
  correction, the close) needs about 205,000 heartbeats. `OP_MOD`'s needs
  about 179,000, measured with `IO.getNumHeartbeats` around each step.
  - The run to the call node alone is about 122,000.
  - The fix is the split at the helper's return (`armBody_split`): one
    `ArmPre` per arm, shared by its general paths, and one short `ArmPost`
    per path. Each half is well under budget, and no limit was raised.
- **`K[C]` reads through stores.** Giving `omega` the disjunctive facts that
  separate the constant array from `savestate`'s words (two more
  disjunctions, beside `ci_sep` and `L_sep`) made every failing `omega` cost
  four times as much.
  - Without them, `kit_guard`'s fallback unified a store chain with the entry
    memory: 557,000 heartbeats for one segment.
  - The fix: `Ranges.k_*_wm8` derive the separation from `Ranges.k_out` once,
    as lemmas. `kitk_rd` applies them before any closer runs (the new
    `kit_side_pre` hook) and after each segment (`kit_norm`).
- Failed iterations: about 30 `lake env lean` runs with errors (MODK about
  25), and 0 failed `lake build`. Wall time is about 3 h, most of it on
  MODK's budget.

## Gate

```
a1-kit-arm: 9 cases — FAIL (first-quarter mean 6.0 lines, last-quarter mean 5.0: not a third cheaper)
    sim_MULK 2, mulk_int 10 | modk_zero 2, modk_m1 2, sim_MODK 2, modk_rz 3, modk_same 4, modk_corr 4, modk_call 6
```

The cluster's selector was widened to this lane's prefixes (`mulk_`, `modk_`,
…). The previous selector matched only `add_`, `mul_`, `mod_` and `eq_`, so
it counted only the `sim_*` declarations of new arms.

The gate sorts cases by commit time, then by line count. So within one
commit, the costliest declaration comes last. Here that is `modk_call`, with
a 4-line statement of the frame at `__moddi3`'s return.

The per-path proofs are 1 to 2 lines after the statement. The cost that does
not fall is the statements: a path condition per path, and the `ArmPre`
frame per arm.

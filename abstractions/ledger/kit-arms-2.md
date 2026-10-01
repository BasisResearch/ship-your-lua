# Kit arms, lane KIT-2 (control and compare family)

Base `9cf3939`. Lines are non-blank, non-comment lines; per-declaration counts
are `abstractions/census.py`'s (the gate's). CPU and peak memory are one
`lake env lean` of the module alone (user s / peak RSS).

## Per arm

| arm | status | hand lines (path lemmas + `sim_X`) | arm-local helpers | build CPU | peak |
|---|---|---|---|---|---|
| LT | integers and stuck cases proved; two strings a premise (`sim_LT_of_str`) | 7 (`lt_int` 3, `lt_stuck` 2, `sim_LT_of_str` 2) | — | 15.7 s | 2.2 GB |
| LE | as LT (`sim_LE_of_str`) | 7 (`le_int` 3, `le_stuck` 2, `sim_LE_of_str` 2) | — | 15.5 s | 2.2 GB |
| EQK | proved but two long strings (`sim_EQK_of_long`) | 21 (`eqk_short` 16, `sim_EQK_of_long` 5) | `Core.kptr_ld` 4 | 9.9 s | 2.2 GB |
| LOADNIL | **proved** (`sim_LOADNIL`) | 47 (`loadnil_loop` 25, `sim_LOADNIL` 22) | `ofNat_bne` 6, `field_b_shl` 8, `insert_addr` 2 | 7.0 s | 2.2 GB |
| FORPREP | not landed (see below) | — | — | — | — |
| EQ long strings | not started (gate stop) | — | — | — | — |

## Setup

| file | lines | what |
|---|---|---|
| `Kit/Cond.lean` | 91 | `kit_cond` (both `docondjump` exits once), `kit_nj`, `kit_trap`, `bne_ite`/`bne_ite_prop`, `kit_order_int`/`kit_order_stuck`, `sim_order` |
| `Kit/Multi.lean` | 122 | `Core.bleachF` (close with C-frame writes), `Core.stack_of` (several registers written), insert read-through lemmas, `SegSt.pin5`/`mem_eq`, the global `kit_val` slot-address rule, `nilMem`, `writeDefs_range`, `foldr_range_top` |
| `Kit/Tointeger.lean` | 61 | callee: `toint_sum` (`luaV_tointeger` on an integer), 8.1 s |
| `Kit/Run.lean` | +18 | `imm_neg_add` in `kit_disch` (negative 12-bit immediates: callee frames); `kit_bv` returns when the normaliser closes the guard |
| `Sim/Rel.lean` | +3 | `Ranges.k_top` (the constants below the C stack: `VmRegionsAt.k_hi` + `cstack_room`) |
| `scripts/gen_lua_arms.py` | +12 (Python) | `SIM_OPS += FORPREP LOADNIL EQK LT LE`, helper `luaV_tointeger`, `SUMMARISED += luaV_tointeger, __hidden___udivdi3` |

Generated: `Lua/Vm/Arms` +8,072 −2,598 (the five arms' segments with the
fetch-head pins, `HluaV_tointeger`); `gen_lua_arm.py --check` passes.
`lake build Lua.Vm.Sim.Kit` from scratch of the kit modules: 2 min 34 s wall
(three lanes building), peak 2.96 GB.

## Gate

`abstractions/clusters.tsv` `a1-kit-arm` now selects every kit path lemma
(`(add|mul|mod|eq|eqk|lt|le|loadnil|forprep)_…`, `sim_X`, `sim_X_of_…`); the
round-3 regex saw none of this lane's cases. After EQK and LOADNIL it fails:

```
a1-kit-arm: 10 cases — FAIL (first-quarter mean 2.0 lines, last-quarter mean 23.5)
  2 le_stuck, 2 sim_LE_of_str, 2 lt_stuck, 2 sim_LT_of_str, 3 le_int, 3 lt_int,
  5 sim_EQK_of_long, 16 eqk_short, 22 sim_LOADNIL, 25 loadnil_loop
```

The lane stopped there, as instructed. The rising cost tracks two missing
kit rules, not repetition:

* **a loop rule.** `loadnil_loop` (25) is the third hand measure induction
  over generated segments (`muldi3_loop`, `udiv_norm`/`udiv_div`); CLAUDE.md's
  loop row (`loopFromBody`) has no kit counterpart.
* **a call-node mid-state.** EQK's 16 lines are mostly the `equalobj_sum`
  frame and context (`EqCtx`) written at the call; FORPREP needs the same
  twice.

## FORPREP: the obstruction

The integer path is `savestate`, three tag tests, `R[A+3] := init`, the spill
`sd a5,16(sp)`, `luaV_tointeger(&R[A+1], sp+40, mode)` (`toint_sum`, proved),
the `blt`/`bge` on the limit, `__udivdi3` (`udivdi3_sum`, with `t0` pinned by
`SegSt.pin5`) and the count store. Run as one `ArmBody` lemma it exceeds the
default 200,000 heartbeats (measured: the run to the `luaV_tointeger` entry
alone is between 100,000 and 200,000; adding the call and the
`FpMem` facts on the concrete memory times out at `whnf`). The budget is not
raised (law 1). Profile: `omega` inside `kit_disch` dominates (10.5 s of
tactic time for 6 segments; 2–4 `omega` runs per side condition through
`Nat.mod_eq_of_lt`), then type checking of the large concrete memory terms
(7.5 s).

The construction that fits: split at the `luaV_tointeger` call with an
abstract mid-state memory (a named structure: the spill, `R[A+1]`'s tag and
payload, `R[A+3]`, the frame against the entry memory outside
`R[A+3]`/`Scratch`/`CFrame`), then one lemma per exit (up/down × run/skip)
over the abstract memory. The draft (stage 1 statement `fp_pre`, `FpInts`,
`fpFrame`, `FpMem`) was not landed.

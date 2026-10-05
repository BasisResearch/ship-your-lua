# Round-4 A1 bake-off, axis B: contender B-INC (the kit as it is)

B-INC proves the held-out arms of axis B on today's kit. Hand splits use
`armBody_split` with a hand-stated mid-state, as MODK does. Call frames are as
in `Kit/Modk.lean`, and the closers are the existing ones. There is no region
log and no generated cut. The base is `09ef132`.

## Summary row

| setup | callees | held-out hand lines (IDIV / FORPREP) | generated | CPU (user s) | peak mem | largest decl heartbeats | refactor `sim_MODK` (before → after) | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 37 (`Kit/Split.lean` 33, `Kit/DivLib.lean` +4) | 82 (`__divdi3` 43; `luaV_idiv` restated, `idivC_eq`, 39) | **84 / 263** | 0 | 50.9 / 47.4 (+6.3 callee, +1.6 setup) | 2.61 GB | **205k** (`idiv_m1'`, measured synchronously; it passes the 200k budget in the build) | 31 → 31 lines (23 gate lines; per-declaration heartbeats unchanged); library split 20 → 24 lines | 0 `lake build`, ≈ 22 `lake env lean` error iterations | ≈ 60 min (+15 min measuring) |

Lines are non-blank, non-comment lines. `/- … -/` blocks (docstrings
included) and `--` lines are dropped. They are counted by
`scratchpad/binc/loc.py`, with imports, `open` and `namespace` lines
included. CPU and memory are from one `lake env lean <module>` under
`/usr/bin/time -v` and a 16 GB scope.

## What is proved

`scripts/check.sh` passes every stage but 3c (3c is expected to fail; see
"Gate"). It includes the full `lake build Lua Vsa VsaIris` and the stage-6
axioms. Every new theorem depends on `[propext, Classical.choice, Quot.sound]`.

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Sim.Kit.sim_IDIV` | `Lua/Vm/Sim/Kit/Idiv.lean` | `SimArm .IDIV` (= `sim_IDIV_Statement`) |
| `Lua.Vm.Sim.Kit.sim_FORPREP` | `Lua/Vm/Sim/Kit/Forprep.lean` | `SimArm .FORPREP` |
| `Lua.Vm.Sim.Kit.divdi3_sum` | `Lua/Vm/Sim/Kit/Divdi3.lean` | `__divdi3`'s summary: `a0 = m.sdiv n` at `ra`, frame kept (4 sign paths, nested `udivdi3_sum`) |
| `Lua.Vm.Sim.Kit.idivC_eq`, `idiv_m1` | `Lua/Vm/Sim/Kit/IdivEq.lean` | `idiv` in `lvm.c`'s order: `sdiv`, less one if the signs differ and `srem ≠ 0`; `n = -1` gives `0 - m` |
| `Lua.Vm.Sim.Kit.armBody_splitS`, `ArmPreS.then`, `SegSt.pinAny` | `Kit/DivLib.lean`, `Kit/Split.lean` | the split at any state `S`; two splits chained; a dropped register pinned at its value |
| `Lua.Vm.Sim.Kit.fp_close`, `fpMem_of` | `Kit/Forprep.lean` | FORPREP's close over an abstract mid-state memory (`FpMem`) |
| `Lua.Vm.Sim.Kit.sim_MODK` | `Kit/Modk.lean` | unchanged; now on `armBody_splitS` |

**Excluded paths are discharged.**
- IDIV:
  - `n = 0` has no `Step` (`idiv` is `none`);
  - the float and metamethod tags fall through by `kit_arith_fall` (`ValRepr.ne_float`).
- FORPREP: `fp_stuck` refutes the kernel step when `step = 0` or when any of
  `R[A]`, `R[A+1]`, `R[A+2]` is not an integer (`forprepK`'s body is
  `none`).
  - This also covers the machine's float limit (`luaV_tointeger` returning 0)
    and the `luaV_tonumber_`/`__gedf2` paths. Under these premises the
    kernel has no step.
- Every machine path that remains is run to the head.

## The route, per case

**IDIV** has seven declarations and a hand-stated split state:
- **The paths.** They are `sim_div`'s: zero, minus one, and the general case
  split by `P = (x.msb = y.msb)` and `Q = (x.srem y = 0)`.
- **Zero and minus one.** These are `kit_div_zero` and `kit_div_m1`, 2 lines
  each.
- **The general case** is split at `__divdi3`'s return `0x8001f740`.
  - `idiv_call` (13 lines) runs the arm to the call.
  - It adds the `t0` and `s10` pins that `__divdi3`'s segments carry
    (`pin5`, `pinAny`).
  - It calls `divdi3_sum` and repins to `IdivRet`.
- **`IdivRet`** is a 10-line hand statement of the pins and `saveMem`.
  - `AtRet`/`divFrame` cannot be reused: `s10` is dead after the call (the
    generated post-state drops it). So no `HFrame` value is a function of the
    arm state.
- **The posts.**
  - `idiv_pos` runs `xor`/`bltz`, then the store.
  - `idiv_exact` and `idiv_corr` also call `__moddi3` (`moddi3_sum`, frame
    read off the pins) and `snez`/`sub` (`snez_val`).
  - Each is a 6–7-line `armBody_splitS` instance on the `idiv_post` macro
    (14 lines).

**FORPREP** has two hand splits with an abstract memory:
- **`fp_entry`** (6 lines) runs the entry to `0x8001e1d8` (`FpEntry`, 12
  lines of pins).
  - That is three guarded loads through `savestate`: `R[A]`'s tag,
    `R[A+2]`'s tag, and `step ≠ 0`.
- **`fp_up` / `fp_down`** (`fp_mid`, 11 lines) run from there to
  `luaV_tointeger`'s entry.
  - The state is `FpCall r`: the memory is an abstract `m` with a named-field
    `FpMem` (frame outside `R[A+3]`'s slot ∪ `Scratch` ∪ the C frame,
    `R[A+3] = init`, the spill).
  - It is established once by `fpMem_of` (15 lines) from the concrete store
    chain `sb; sd 16(sp); sd`.
- **Four posts**, 3 lines each: up/down × run/skip.
  - `fp_post` (19 lines) evaluates the kernel (`forCount`, `toInt_sign`),
    calls `toint_sum` (its `TiCtx`), and runs.
  - The run paths then call `udivdi3_sum` (`fp_udiv`), with `-step` for
    down (`neg_step`).
  - They close with `fp_close` (37 lines, once): `Core.bleachF` +
    `Core.stack_of` over `FpMem`.
  - The post-call reads go through the abstract `m`: the spill by
    `FpMem.spill'`, the limit by the out-parameter's store and
    `FpMem.slot_eq`.
- **The assembly.** `fp_stuck` (13 lines) and `sim_FORPREP` (16 lines) split
  the cases.

### FORPREP's 263 lines by role

| role | lines |
|---|---|
| hand mid-state statements (`FpInts`, `FpPath`, `FpEntry`, `FpMem`, `fpFrame`, `FpCall`) | 38 |
| memory lemmas over the abstract state (`fpMem_of`, `FpMem.slot_eq`, `FpMem.spill'`, `fp_close`) | 67 |
| comparison / sign / `forCount` restatements (`slt_toInt`, `sge_toInt`, `toInt_sign`, `neg_step`) | 13 |
| path macros (`fp_setup`, `fp_mid`, `fp_rd`, `fp_post`, `fp_frame`, `fp_close_run`, `fp_close_skip`, `fp_udiv`, normaliser rules) | 71 |
| path theorems and assembly (`fp_entry`, `fp_up`, `fp_down`, 4 posts, `fp_stuck`, `sim_FORPREP`) | 53 |
| imports / opens / namespace | 21 |

For IDIV (84 lines): the `IdivRet` statement is 10, the paths and
`sim_IDIV` 43, and the macros 19 (`idiv_post`, `idiv_mod`).

## Measurements

**CPU and memory** (`lake env lean`, one module at a time):

| module | user s | wall s | peak RSS |
|---|---|---|---|
| `Kit/Idiv` | 50.9 | 22.1 | 2.61 GB |
| `Kit/Forprep` | 47.4 | 23.7 | 2.61 GB |
| `Kit/Divdi3` | 6.3 | 6.6 | 1.97 GB |
| `Kit/IdivEq` | 0.8 | 1.2 | 1.85 GB |
| `Kit/Split` | 0.8 | 1.2 | 1.85 GB |
| `Kit/DivLib` | 1.5 | 1.9 | 1.88 GB |
| `Kit/Modk` (after) | 52.6 | 18.2 | 2.78 GB |

**Heartbeats per declaration**, in thousands.
- They are measured by `IO.getNumHeartbeats` around each command, with
  `Elab.async false`. This was done in uncommitted copies
  (`scratchpad/binc/HB_*.lean`, `hbify.py`).
- In synchronous mode the count includes the statement's elaboration. It
  overstates the asynchronous proof task that the 200k budget limits:
  `idiv_m1'` counts 205k here but builds under the default budget.

| IDIV | k | FORPREP | k | MODK (after = before) | k |
|---|---|---|---|---|---|
| `idiv_zero` | 6 | `fp_entry` | 90 | `modk_zero` | 4 |
| `idiv_m1'` | **205** | `fp_up` | 66 | `modk_m1` | **190** |
| `idiv_call` | 131 | `fp_down` | 59 | `modk_call` | 144 |
| `idiv_pos` | 47 | `fp_up_run` | **147** | `modk_rz` | 47 |
| `idiv_exact` | 63 | `fp_up_skip` | 67 | `modk_same` | 57 |
| `idiv_corr` | 63 | `fp_down_run` | 109 | `modk_corr` | 62 |
| `sim_IDIV` (with `kit_arith_fall`) | 163 | `fp_down_skip` | 64 | `sim_MODK` (with `kitk_fall`) | 166 |
| `divdi3_sum` | 107 | `fp_stuck` / `fp_close` / `fpMem_of` | 8 / 1 / 2 | | |

**Failed builds and wall time.**
- `lake build` failed 0 times.
- `lake env lean` error iterations:
  - FORPREP: 11, plus 11 clean or exploratory runs (`trace_state`/`sorry`
    probes, removed);
  - IDIV: 4;
  - `IdivEq`: 3;
  - `Split`: 3;
  - `Divdi3`: 1.
- Wall time:
  - IDIV, from the kit read to `sim_IDIV` proved: about 22 minutes;
  - FORPREP: about 25 minutes;
  - refactor and full check: about 13 minutes.

**Refactor of `sim_MODK`.** On B-INC there is nothing to remove.
- `ArmPre`/`ArmPost` became `abbrev`s of the general `ArmPreS`/`ArmPostS`
  at `AtRet`. `armBody_split` became `armBody_splitS`: the library went
  from 20 to 24 lines and `Modk.lean` is unchanged at 31.
- MODK's structure is still set by the budget. `modk_call` is 144k and the
  path cannot be one declaration (§1b.3: ≈ 201k).
- `divFrame` is still a hand frame.

## Gate

```
a1-kit-arm: 28 cases — FAIL (first-quarter mean 3.3 lines, last-quarter mean 8.1: not a third cheaper)
```

The cluster's selector misses most of this branch's declarations:
- `idiv_m1'` is skipped because of the prime;
- the `fp_*` lemmas are skipped because the selector wants `forprep_`.

It counts `idiv_call` 13, `idiv_pos` 6, `idiv_exact`/`idiv_corr` 7 and
`sim_FORPREP` 16. Counted by the route's own lines, the per-arm cost rises:
- MODK: 23;
- IDIV: 84 (43 in paths);
- FORPREP: 263 (53 in path theorems).

## What the route could not express

Each item gives the evidence in the code.

1. **A split state is a hand statement per arm, and it does not transfer
   between arms.**
   - IDIV could not reuse `AtRet`/`divFrame`. `__divdi3`'s segments pin
     `s10`, but the arm's generated post-state at the call has dropped it
     (it is dead after the return, `seg_8001f734_8001f740`).
   - So the frame at the return holds an arbitrary value (`SegSt.pinAny`,
     from `RegsOk`). It cannot be a function of the arm state, which is what
     `ArmPre`'s `F` needs. Hence `IdivRet` (10 lines) without `HFrame`, and
     `armBody_splitS`.
   - FORPREP's split costs 38 lines of state and 67 of memory lemmas. That is
     L4-split′'s "statement cost", measured: 40% of the arm.
2. **The budget dictates splits even on paths with no call.**
   - `idiv_m1'` (the `n = -1` path, no helper) is the largest declaration:
     205k measured synchronously, inside the 200k task budget by a few
     percent.
   - It has five guarded loads through `savestate`. `modk_m1` is 190k.
   - One more load on such a path breaks the budget, and there is no call
     return to cut at. The cut would need yet another hand state at an
     arbitrary segment boundary.
   - FORPREP fits only because the second split makes the memory abstract.
     Each post-call read (spill, limit) is then a `FpMem` field rather than a
     store-chain peel.
3. **The kit's closers depend on syntactic forms that the hand states must
   reproduce.**
   - A folded `raAddr` defeats `slot_arith`, so a pin read by `kit_val`
     needed `simp only [raAddr] at h0`.
   - `omega` cannot relate `ins.a` to `ins.toNat / 2^7 % 2^8`, so the frame
     facts needed the field unfolded by hand (`fp_frame`).
   - `kit_bv` cannot bridge `¬ i < l` (the kernel's `forCount`) and the
     machine's `bge` (`≥b`). `sge_toInt` is stated as `!decide (x < y)` to
     match.
   - The kernel's `-(st + 1) + 1` against the machine's `0 - st` needed
     `neg_step`.
   - `IdivRet` states `s3`/`s4` as `slotVal` because the post segments read
     them.
4. **`try` does not branch on a path.** `try (obtain … := h0.call …)` is
   "recovered" by elaboration error recovery and poisons the state. So a call
   on some paths only must be a separate macro, chosen per path (`idiv_mod`,
   `fp_udiv`).
5. **Dead pins at helper entries.** Helper segments carry callee-saved
   registers that the caller's segments dropped: `s10` for `__divdi3`, and
   `t0` for `__udivdi3` (`pin5`). The kit must invent their values. That is
   sound (`RegsOk`), but the frame stops being the arm state's function.

## Forecast

- **VARARGPREP: 250–350 hand lines on B-INC.**
  - The callee, `luaT_adjustvarargs`, needs:
    - a summary with the slot-copy loop as a hand measure induction (about
      40 lines, like `loadnil_loop`);
    - a nil-fill of the source tags;
    - a store to `L->top`.
  - The close is a re-witness of `VmRel` at a new `func`, not `bleach`. That
    is relation work outside the kit.
  - The arm needs a hand mid-state with abstract memory in `FpMem`'s style:
    the copied window, then the old window's tags nil.
  - Each copy iteration's `ld`/`sd` through the growing chain is a budget
    risk, so the loop body must be stated over an abstract memory too.
- **CALL print: not reachable on this route.**
  - The chain is about 81 functions (93 back edges) through `luaD_precall`,
    `luaB_print` and the stdio chain. B-INC's tools (hand loop inductions,
    hand mid-states) scale per function.
  - It needs the stdio step tables (PHASES A0.2) and a runtime-shape summary
    with a footprint post-condition. The arm itself, once that exists, is
    about 60–80 lines plus a hand split at `luaD_precall`'s return.
- **RETURN: about 150–250 hand lines plus summaries.**
  - It is the `Final` clause.
  - `luaD_poscall` has two loops (nil fill and slot copy), each a hand
    induction of 25–40 lines.
  - The exit to HTIF is a `TohostSite`.
  - The paths with a `k` bit (`luaF_close`) are outside F1.
  - On B-INC every loop exit and every call return that crosses the budget
    is another hand-stated state. FORPREP's ratio (40% of the arm in state
    statements and their memory lemmas) is the expected cost.

## Files and commits

- New:
  - `Lua/Vm/Sim/Kit/{Split,Divdi3,IdivEq,Idiv,Forprep}.lean`;
  - `abstractions/bakeoff4/B-INC.md`.
- Changed:
  - `Lua/Vm/Sim/Kit/DivLib.lean`: the general split, with `ArmPre`/`ArmPost`
    as its instances;
  - `Lua/Vm/Sim/Kit/Modk.lean`: `armBody_splitS`;
  - `Lua/Vm/Sim/Kit.lean`: imports;
  - `scripts/check.sh`: stage-6 axioms for the new theorems.
- PHASES.md is not edited, to avoid conflicts between contenders. The
  coordinator updates the `sim_IDIV_Statement` and `SimArm .FORPREP` rows on
  adoption.

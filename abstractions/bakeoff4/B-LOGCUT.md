# Round-4 A1 bake-off, axis B: contender B-LOGCUT (region log + generated cuts)

Base `09ef132`; branch `worktree-agent-a93a0f796c7e17316`. Held out: `SimArm .FORPREP`
and `SimArm .IDIV`. Refactor: `sim_MODK`. Both held-out cases are **complete**, with
no premise; `sim_MODK` is re-proved on the route.

## Summary row

| setup | callees | held-out hand lines (per case) | generated | CPU | peak mem | largest decl heartbeats | refactor (before → after) | failed builds | wall |
|---|---|---|---|---|---|---|---|---|---|
| 938 Lean (library) + 22 (`log_frame_slot`) + 46 Python (generator) | 107 (`__divdi3` 25, `luaV_tointeger` in log form 45, `idivC_eq`/`idiv_m1` 37) | IDIV **88** (65 in declarations + 23 in family macros); FORPREP **153** (74 + 79); FORPREP's operand family 25 | `cuts.tsv` 348 lines; no new segments | 13.6 s library, 9.0 s callees; IDIV 26.2 s, FORPREP 25.3 s, MODK 35.7 s (user) | 2.49 GB | own route: 110k (`divdi3_sum`), arm paths ≤ 86k (`modk_corr`); inherited kit fall-through 188k (`sim_MODK`), 184k (`sim_IDIV`) | MODK 23 → 14 lines (and no `ArmPre`/`divFrame` statement); 76.4 → 35.7 s CPU | ≈ 15 `lake build`, ≈ 75 `lake env lean` | 1 h 52 min (18:12–20:04) |

Lines are non-blank, non-comment lines: `--` lines and `/- … -/` blocks
(docstrings included) are dropped. CPU and peak memory are `/usr/bin/time -v`
of `lake env lean <module>` alone, under a 16 GB cap. Heartbeats are in the
unit of `maxHeartbeats` (thousands), per declaration, measured with
synchronous elaboration (`Elab.async false`) around each command.

## What is proved

All axioms are `[propext, Classical.choice, Quot.sound]` (`#print axioms`; the
names below are in `scripts/check.sh` stage 6).

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Sim.Kit.sim_IDIV` | `Lua/Vm/Sim/Kit/Idiv.lean` | `SimArm .IDIV` (= `sim_IDIV_Statement`) |
| `Lua.Vm.Sim.Kit.sim_FORPREP` | `Lua/Vm/Sim/Kit/Forprep.lean` | `SimArm .FORPREP` |
| `Lua.Vm.Sim.Kit.sim_MODK` | `Lua/Vm/Sim/Kit/Modk.lean` | `SimArm .MODK` (refactor) |
| `Lua.Vm.Sim.Kit.divdi3_sum` | `Lua/Vm/Sim/Kit/Divdi3.lean` | `__divdi3`'s call-node summary: `a0 = m.sdiv n` |
| `Lua.Vm.Sim.Kit.call_8001ade8` | `Lua/Vm/Sim/Kit/ForprepLib.lean` | `luaV_tointeger(&R[A+1], sp+40)` with the post memory as the log |
| `Lua.Bytecode.idivC_eq`, `idiv_m1` | `Lua/Vm/Sim/Kit/IdivEq.lean` | `luaV_idiv` in `lvm.c`'s order (C quotient, sign-fix by `m % n ≠ 0`); the `n = -1` exit |
| `Lua.Vm.Sim.Log.Regions.of_ranges`, `disj_sound`, `log_frame_scratch`, `log_frame_F` | `Lua/Vm/Sim/Kit/Log.lean` | the region facts once from `Ranges`; the forwarder; the frames of a log |
| `IdivRet.reach`, `IdivJoin.reach`, `FpFork.reach`, `FpUp.reach`, `FpDn.reach` | `Idiv.lean`, `Forprep.lean` | the generated cut states' reach theorems |

The kernel's excluded paths are discharged, not assumed: `n // 0`
(`idiv_zero`), an operand not an integer or a zero step (`forprep_notint`,
`forprep_zero`), and the non-integer fall-throughs (`kit_arith_fall`).

## The route

### M-log: the region log (`Kit/Log.lean`, `Kit/LogRun.lean`, `Kit/LogArms.lean`)

* **Regions, once per arm.** `Rgn` = register slots, `K`, `ci->u.l.savedpc`,
  `L->top`, `luaV_execute`'s frame, the callee frames below `sp`, and `ciR`
  (the `CallInfo`, read only: `ci->top`). `Regions.of_ranges` proves, once from
  `Ranges`, that the pairs `sepPair` lists are disjoint, and that every region
  is in RAM above `tohost`, below `2^32` and 8-aligned. This is `Ranges.lift`:
  the no-wrap facts per region. `ciR` is not separated from `K` (no `Ranges`
  fact), so `sepPair` leaves that pair out.
* **Atom-indexed slot labels.** An arm's table is `tbl ops`: five standard
  atoms, then its operand atoms (`opsK`: `R[A]`, `R[B]`, `K[C]`; `opsR`:
  `R[A]`, `R[B]`, `R[C]`; `opsF`: `R[A]…R[A+3]` as one atom of span 64). A
  location is `(atom, k)` with numerals, so `R[A+3]` against `R[A+1]` is
  `k = 48` against `k = 16` in one atom: the forwarder `disj` decides it by
  evaluation.
* **Loads.** `log_simp` folds every store at a lifted address into the log
  (`log_fold1`/`log_fold8`, by `rfl`) and forwards every read
  (`rd1_skip`/`rd8_skip` with `disj … = true` by `rfl`, `rd1_hit`/`rd8_hit`).
  A bus check at a lifted address is `True` (`la_lo`, `la_hi`, `la_ht`,
  `la_win`, `la_al`; the side condition `k + n ≤ span` by evaluation).
* **The branch is picked by evaluating its guard.** `log_run` evaluates the
  `_t` guard with `log_side` (one `simp only` over `log_simp` and the arm's
  `hl_*` facts, then `decide`). A wrong polarity fails fast, as a closed
  `false = true`. The side closer runs no `omega`.

### M-call: summaries keyed by entry pc

* The runner applies `Lua.Vm.Sim.Kit.call_<pc>` at that pc, however the pc is
  reached: by a `jal`, a fall-through (`__divdi3` into `__udivdi3`) or a tail
  `j` (`__divdi3`'s negative/negative case). The return address `r` is a
  parameter, so `ret` and `jr t0` returns are the same rule.
* **The frame is the live registers.** The summary's frame (`HFrame`) is found
  by register name. A register it names that the caller does not pin is
  dead (`IDIV`'s `s10` at `__divdi3`). It is pinned to its present value
  (`RegsOk`: every GPR present) by `pinMissing`.
* **Caller-frame cells.** `luaV_tointeger` is keyed in log form
  (`call_8001ade8`). Its post memory is the caller's log plus three entries:
  `*p` at `sp+40`, and the callee's saves of `ra` and `s1` below `sp`. FORPREP's
  spill `sp+16` (written before the call) and the limit at `sp+40` are then
  read back after the call by the forwarder, with no frame statement.

### M-cut: cut states from generated data (`Kit/LogCut.lean`, `scripts/gen_lua_arms.py`)

* **The generator emits the cut points.** It writes `Lua/Vm/Arms/cuts.tsv`
  (`arm_cuts`): per SIM arm, the call returns (`ret`), the starts of the
  branch segments (`fork`), and the segment starts with two or more
  predecessors in the arm (`join`).
* **`log_cut NAME : T at pc [abstract r] := by tac`.** `tac` is a prefix of a
  path ending in `log_cut_here`. The cut is the state the run reaches,
  composed from the segments' posts. It keeps only the pins the generated
  segments at `pc` read (the generator's live set), abstracted over
  `p c s w ins`. The command:
  * defines it `@[irreducible]`, with `NAME.reach : T NAME`, `NAME.out` and
    `NAME.intro`, all from one run under the default budget;
  * refuses a `pc` that is not in `cuts.tsv`.
* **The kernel's output names a join.** `IDIV`'s four paths meet at the store
  `0x8001f74c` with different results in `s10`. `IdivJoin` abstracts `s10`;
  each path's leg ends with `IdivK … v`, `idiv x y = some v`. The store and
  the close are proved once for every `v` (`idiv_from`).
  * A path whose facts rewrote a live pin (the `n = -1` path knows `s4 = -1`)
    meets the join by proving the pin equal from its facts (`log_eq` inside
    `log_pins_of`).
* **Combinators:** `ArmReach`, `ArmLeg`, `ArmFrom` (and `…V` for joins).
  `ArmReach.leg`, `.body`, `.join` and `ArmReachV.body` compose them into
  `ArmBody`.

### The arms

* **MODK (refactor):** five one-line paths (`logk_div pc (kernel)`), no split.
  The general paths run through `__moddi3` in one declaration (≤ 86k).
* **IDIV:**
  * `IdivRet` is a `ret` cut at `__divdi3`'s return. It is shared by the
    three general paths, and the `bltz` fork follows it.
  * `IdivJoin` is the `join` cut, named by the kernel's output.
  * Each path is a short leg: `idiv_exact`, `idiv_corr`, `idiv_neg1`.
  * `idiv_from` closes once.
* **FORPREP:**
  * `FpFork` is the `fork` cut before `bgez s6`, shared by the four paths.
  * `FpUp` and `FpDn` are `ret` cuts at `luaV_tointeger`'s two returns.
  * The four paths are three-line `ArmFrom`s from those cuts.
  * The closes write `R[A+3]` (and `R[A+1]` for the run paths) through
    `Core.bleachF` + `Core.stack_of`. The slot frame is `log_frame_slot`, one
    Boolean check over the log.

## Measurements

### Hand lines

| row | file | lines |
|---|---|---|
| setup | `Kit/LogAttr.lean` (the simp set) | 2 |
| setup | `Kit/Log.lean` (regions, atoms, log, forwarder, reads, folds, bus checks, frames, guard normal forms) | 364 |
| setup | `Kit/LogRun.lean` (`log_run`, `log_side`, `log_norm`, `log_eq`, `log_conv`, `log_facts`, `log_pins_of`, call keys, `pinMissing`) | 234 |
| setup | `Kit/LogArms.lean` (`opsK`, `opsR` families, `log_setup`) | 82 |
| setup | `Kit/LogCut.lean` (cut combinators, `log_cut`, `log_cut_here`, `log_join`) | 188 |
| setup | `Kit/LogDiv.lean` (division paths: `logk_div`, `logr_div`, `log_val`, `log_close1`) | 68 |
| setup | `Kit/ForprepLib.lean`: `okSl`/`log_frame_slot` | 22 |
| setup, generator | `scripts/gen_lua_arms.py` (`arm_cuts`, `JAL_END`) | 46 (Python) |
| callee | `Kit/Divdi3.lean` (`divdi3_sum`, four sign cases in one `log_run`) | 25 |
| callee | `Kit/ForprepLib.lean`: `call_8001ade8` (+ `sp_m80`, `la_sp`, `la_cs`) | 45 |
| callee | `Kit/IdivEq.lean` (`idivC_eq`, `idiv_m1`: `δ` in `lvm.c`'s order) | 37 |
| arm | `Kit/Idiv.lean`: `IdivRet` 5, `IdivJoin` 8, `idiv_exact` 8, `idiv_corr` 8, `idiv_neg1` 8, `idiv_from` 16, `idiv_zero` 2, `sim_IDIV` 10 | 65 |
| arm glue | `Kit/Idiv.lean`: `logr_setup` 12, `logr_leg` 5, `idiv_k` 4, `IdivK` 2 | 23 |
| arm | `Kit/Forprep.lean`: `FpFork` 7, `FpUp` 10, `FpDn` 10, four paths 3 each, `forprep_notint` 10, `forprep_zero` 8, `sim_FORPREP` 17 | 74 |
| arm glue | `Kit/Forprep.lean`: `fp_base` 10, `fp_log` 10, `fp_from` 20, `fp_skip` 9, `fp_run` 15, `fp_stuck_setup` 7, four 2-line lemmas | 79 |
| arm family | `Kit/ForprepLib.lean`: `FpInts`, `FpPath`, `opsF` lifts | 25 |
| refactor | `Kit/Modk.lean` 22 (14 in declarations; before: 31, 23 in declarations, plus `DivLib`'s split machinery, which MODK no longer uses) | 14 |

**Ablation: the log and keyed calls without cuts.** Each path is then one
declaration from the arm's entry (earlier commits `b417268` and `4cedb5a`).
* IDIV is **16** lines in its declarations, with the shared `logr_div` macro
  (13) in `LogDiv.lean`. Its paths cost 6 / 64 / 73 / 94 / 94k heartbeats,
  sum 330k; the module 35.7 s.
* FORPREP is **114** lines. Its paths cost 88 / 122 / 94 / 120k, sum 424k;
  the module 43.4 s.
* With cuts, IDIV's sum is 235k (largest 60k) and its CPU 26.2 s. FORPREP's
  sum is 320k (largest 70k) and its CPU 25.3 s.

So the cuts trade statement lines for CPU and per-declaration headroom:
* IDIV: +49 lines;
* FORPREP: +39 lines;
* −27 % to −29 % CPU on both.

### Heartbeats (thousands, per declaration)

| declaration | hb | | declaration | hb |
|---|---|---|---|---|
| `IdivRet` (entry → `__divdi3` return) | 60.1 | | `FpFork` (entry → fork) | 39.9 |
| `IdivJoin` (same-sign leg, derives the join) | 18.8 | | `FpUp` (fork → `luaV_tointeger` return) | 34.8 |
| `idiv_exact` / `idiv_corr` (legs through `__moddi3`) | 38.3 / 38.5 | | `FpDn` | 37.5 |
| `idiv_neg1` (entry → join) | 55.3 | | `forprep_upskip` / `uprun` | 35.2 / 70.4 |
| `idiv_from` (join → head, once) | 18.3 | | `forprep_downskip` / `downrun` | 38.4 / 63.3 |
| `idiv_zero` | 5.5 | | `forprep_notint` / `forprep_zero` | 5.6 / 5.8 |
| `sim_IDIV` (its `kit_arith_fall` fall-through) | **184.1** | | `sim_FORPREP` | 0.8 |
| `modk_m1` / `rz` / `same` / `corr` | 61.7 / 70.6 / 79.7 / 86.4 | | `divdi3_sum` (4 cases) | 110.4 |
| `sim_MODK` (its `kitk_fall` fall-through) | **188.5** | | `Regions.of_ranges` | 31.9 |

MODK's general path was ≈ 205k on the kit and had to be split at
`__moddi3`'s return; here it is one declaration of 71–86k. FORPREP's run to
the `luaV_tointeger` entry alone was between 100k and 200k on the kit; here
the whole longest path from the fork is 70k.

### CPU and memory (`lake env lean`, user s / wall / peak)

| module | user | wall | peak |
|---|---|---|---|
| `Kit/LogAttr` | 0.6 | 1.0 | 1.5 GB |
| `Kit/Log` | 4.8 | 3.3 | 1.9 GB |
| `Kit/LogRun` | 2.6 | 2.7 | 1.9 GB |
| `Kit/LogArms` | 1.2 | 1.4 | 1.8 GB |
| `Kit/LogCut` | 1.7 | 2.0 | 1.9 GB |
| `Kit/LogDiv` | 1.3 | 1.7 | 1.9 GB |
| `Kit/IdivEq` | 0.4 | 0.6 | 0.8 GB |
| `Kit/Divdi3` | 6.5 | 6.8 | 2.0 GB |
| `Kit/ForprepLib` | 2.1 | 2.2 | 2.0 GB |
| `Kit/Idiv` | 26.2 | 17.8 | 2.4 GB |
| `Kit/Forprep` | 25.3 | 14.4 | 2.3 GB |
| `Kit/Modk` | 35.7 | 11.5 | 2.5 GB |

### Failed builds and wall time

These are approximate, tallied from the session.

| phase | wall (from the commit times) | failed `lake build` | `lake env lean` error iterations |
|---|---|---|---|
| reading, library (log, runner), MODK refactor | 44 min (18:12–18:56) | 8 | ≈ 30 |
| `__divdi3`, `idivC_eq`, IDIV (no cuts) | 11 min | 2 | ≈ 10 |
| FORPREP (no cuts) | 16 min | 1 | ≈ 15 |
| `log_cut`, generator cuts, IDIV and FORPREP on cuts | 24 min | 4 | ≈ 20 |
| measurement, gate, report | 17 min | 0 | — |

`scripts/check.sh` passes every stage but 3c (run with stage 3c made
non-fatal: generator drift, discipline, `lake build Lua Vsa VsaIris`, the OS
traces and the stage-6 axioms all OK). Stage 3c (`a1-kit-arm`) fails: 33
cases, first-quarter mean 3.2 lines, last-quarter mean 6.8.

## What the route could not express, with evidence

1. **FORPREP's joins.**
   * `cuts.tsv` lists `0x8001e218` (the skip store, reached from both
     directions) and `0x8001f878` (the count store) as joins.
   * They are not cut: the two directions' logs differ in a dead cell.
     `luaV_tointeger` saves its return address below `sp`, and the log entry
     `⟨3, 248, ra⟩` holds `0x8001e200` going up and `0x8001f9b4` going down.
   * `log_cut` keeps the whole log. A join needs either dead-entry filtering
     (the log describes only what later loads read: R2-4 #3, "filtrate") or
     abstracting a log entry as `abstract x26` abstracts a register.
   * As it is, the two skip closes and the two count closes are each written
     twice: one `fp_skip`/`fp_run` per path.
2. **The kit's fall-through stays near the budget.** `sim_IDIV` costs 184k
   and `sim_MODK` 188k. Both are `kit_arith_fall`/`kitk_fall` (the kit's
   `omega` closers on the non-integer paths), inherited unchanged. The route
   proves the integer paths cheaply but did not re-express the fall-through
   on the log.
3. **Normal forms have to agree.**
   * A fact rewrites a guard only in the guard's normal form.
   * `BitVec.msb_xor` had to leave `log_simp`: the kernel's
     `(y ^^^ r).msb` and the guard's `bltz` must meet in one form. MODK's sign
     paths are therefore restated as `(y ^^^ x.srem y).msb = false`.
   * The full `simp` the kit runs on the kernel step unfolds `bytesT8`; the
     route replaces it with a `simp only` set.
4. **The lift is per family.**
   * The operand addresses are lifted by one lemma per operand (`opsK_A`,
     `opsR_C`, …), proved once per family.
   * A new operand shape is a new lemma: `C` without the `zext.b` mask is
     `lift_slotC`.
   * A simproc that matched the address against the table's atoms would make
     this generic; it was not built.
5. **Distinct atoms of one region are not separated.** A read of `R[B]` after
   a store to `R[A]` is not forwarded (`disj` is `false`: `A` and `B` are
   symbolic). The held-out arms never read a register slot after writing
   another one; MOVE-like arms would.
6. **What a cut still costs by hand.** Only the cut's *state* is generated.
   Its statement (`ArmReach o Q`, the path condition `Q`) and the
   implications between path conditions in `sim_X` are still written: IDIV
   +49 and FORPREP +39 lines against the no-cut variant.

## Forecast

* **VARARGPREP.**
  * The arm's loads through `savestate` and `ci` are the log's: an arm of
    about 30 lines with a `ret` cut at `luaT_adjustvarargs`'s return.
  * The callee is a slot-copy loop that writes `nextra` slots at a symbolic
    stride and moves `ci->func`. The log has no comprehension entry ("for all
    i < k"), so the loop is a hand induction whose invariant is a log of
    `k` entries (about 120 lines).
  * The close needs a re-witness of `VmRel` at the new `func`, with the slot
    atoms re-based (about 60 lines of relation lemmas).
* **CALL print.**
  * With a `call_<pc>` summary for `luaD_precall`, the arm is about 40–60
    lines: `savestate`, the `L->top` store, a `ret` cut and the close.
  * The summary is the dominant cost (thousands of lines, the stdio chain,
    PHASES A0.2). The log does not reduce it.
  * Its memory effect spans `L`, `ci`, the heap and the stack above `R[A]`,
    so its post state needs heap regions keyed to `HeapAt`'s chunks (R2-1 #2)
    and a `CallInfo` region that is writable apart from `savedpc`.
* **RETURN.**
  * It is the `Final` clause (`luaD_poscall` → the return chain → HTIF), not
    a `sim`.
  * The arm side (`ci->callstatus`, `nresults`, `L->top`) is a few `ciR`/`lR`
    reads: about 50 lines.
  * The poscall nil fill and slot copy are store loops (M-loop, not in this
    route): about 150 lines with the kit's loop pattern.

## Files

* Library:
  * `Lua/Vm/Sim/Kit/LogAttr.lean`, `Log.lean`, `LogRun.lean`;
  * `LogArms.lean`, `LogCut.lean`, `LogDiv.lean`;
  * `ForprepLib.lean` (also FORPREP's family and callee).
* Callees: `Lua/Vm/Sim/Kit/Divdi3.lean`, `IdivEq.lean`.
* Arms: `Lua/Vm/Sim/Kit/Idiv.lean`, `Forprep.lean`, `Modk.lean` (refactor).
* Generator: `scripts/gen_lua_arms.py` (`arm_cuts`) → `Lua/Vm/Arms/cuts.tsv`.
* Gate:
  * `scripts/check.sh` stage 6 lists the new theorems.
  * `PHASES.md` updates the IDIV, FORPREP and MODK rows.

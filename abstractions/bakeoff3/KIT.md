# Round-3 A1 bake-off: contender KIT (direct kit)

KIT proves the arms by hand on a small library. It has no generator for arm
proofs. The generated `SegSt` segments are reused, and the segment generator
is extended to the helpers' bodies; those lines count as generated. The base
is `3f9797f`, and the branch head is the last commit on this worktree.

## Summary row

| setup | callee proofs | per-arm hand lines (MUL / EQ / MOD) | generated lines | build CPU (s) | peak mem | refactor `sim_ADD` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 495 Lean (+30 base Lean, +198 Python) | 524 | 19 / 100 (partial) / 160 | +8,588 −825 | 249 (Kit modules) + 46 (helper segments) | 2.9 GB | **17** lines (incumbent: 233 generated + ~134-line `arith` template) | ~10 `lake build`, ~110 `lake env lean` iterations | ≈ 2 h 45 min |

Lines are non-blank, non-comment lines: lines inside `/- … -/` blocks
(docstrings included) and `--` lines are dropped.

## What is proved

All of these are built (`lake build Lua.Vm.Sim.Kit`, and the full default
`lake build`). Their axioms are {propext, Classical.choice, Quot.sound}; stage 6
of `scripts/check.sh` now lists them (141 reports).

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Sim.Kit.sim_ADD` | `Lua/Vm/Sim/Kit/Add.lean` | `SimArm .ADD` (refactor case) |
| `Lua.Vm.Sim.Kit.sim_MUL` | `Lua/Vm/Sim/Kit/Mul.lean` | `SimArm .MUL` |
| `Lua.Vm.Sim.Kit.sim_MOD` | `Lua/Vm/Sim/Kit/Mod.lean` | `SimArm .MOD` = `sim_MOD_Statement` |
| `Lua.Vm.Sim.Kit.eq_short` | `Lua/Vm/Sim/Kit/Eq.lean` | `OP_EQ`'s run unless `R[A]` and `R[B]` are both long strings |
| `Lua.Vm.Sim.Kit.sim_EQ_of_long` | `Lua/Vm/Sim/Kit/Eq.lean` | `SimArm .EQ` from the long/long path (the one open premise) |
| `muldi3_sum`, `udivdi3_sum`, `moddi3_sum` | `Kit/{Muldi3,Udivdi3,Moddi3}.lean` | the helper summaries at the Lua ELF's addresses |
| `equalobj_sum` | `Kit/Equalobj.lean` | `luaV_equalobj`'s summary: `a0 = (v1 = v2)` for represented F1 values, not both long strings |
| `imodC_eq` | `Kit/ModEq.lean` | `imod` restated in `lvm.c`'s branch order: C remainder plus the sign fix-up |

**Held-out results:** MUL and MOD are complete. EQ is complete except for one
path, two long strings, which is blocked by the relation (see the obstruction
below).

## The route

- **M1, forward evaluation** (`kit_setup`). `kstep_iff` and one `simp` over
  the kernel term compute the successor. There is no `step_*` inversion. One
  δ entry is restated in `lvm.c`'s order: `imodC_eq`, plus `bgeu_one` and
  `srem_neg_one` for the `n ∈ {0, -1}` exit.
  - `n % 0` is the kernel's stuck case. `mod_zero` is one `simp` that closes
    `hk` to `False`; no machine run is needed.
- **M2, tag lemmas over the tightened `ValRepr`.** These are the base's
  `int_of_tag`/`not_int`/`ne_float`, plus `tag_mem`, `tag_det`, `tag_eq`
  (via `tagOf`), `eq_of_tag` and `eq_iff_payload` (`Kit/Equalobj.lean`).
  The last one is where `ι` and `TStringRepr.inj` give short-string pointer
  equality.
  - Guards are discharged generically. `kit_guard` applies a guard lemma per
    tag hypothesis. `kit_bv` runs one `simp` with every value fact in
    context, after an arm-local normaliser (`kit_bv_norm`).
- **M3, one close** (`Core.bleach`). The final memory agrees with the entry
  memory outside slots ∪ `Scratch`, and the new register file is represented.
  - Its shapes are `bleach_store` (one slot via `SlotStore`, after scratch
    stores), `bleach_same`, and the tactic `kit_frame`, which proves the
    frame for any chain of `writeMap8`/`insert` stores.
- **M5, call nodes** (`SegSt.call`). A call node runs the helper's summary, a
  `Triple` from the entry pins to the return address.
  - The frame is a pin list (`HFrame`, or `KFrame` for `luaV_equalobj`). The
    generator carries it through the helper's segments by a liveness
    fixpoint. The arm side carries it across the `jal` because a
    summarised call's successor is its return address.
  - `__moddi3` returns through `t0` and calls `__udivdi3`, a nested call node
    returning inside `__moddi3`.
  - `luaV_equalobj` is classified after F1 pruning. It is loop-free; its
    jump table on the variant is read from `.rodata` (`eq_jump`, one
    `decide +kernel`).
- **Runner** (`kit_run`, `Kit/Run.lean`). It runs the generated segments
  starting at the current pc. It finds each segment by its name, fills the
  values with `_` and the side conditions with `kit_side`, and finds the pins
  by register name (`pins_of`).
  - A branch's two polarities are pre-checked on their guard alone
    (`guardsHold`) before the segment is elaborated.
  - It stops at the head, at a stop pc, or at a computed pc (a `ret`, a
    `jr` through a table).
  - This is the M1–M5 composition: the arm proof writes no segment arguments
    and no pin indices.
- **Tablebase tails.** These are not separate lemmas. The `mv s11,s3` tails
  (`0x8001e43c`, `0x8001c1e4`, …) cost zero lines per arm, because
  `kit_arith_fall` covers the whole fall-through to `MMBIN` of every
  `op_arith` arm. It is used by ADD, MUL and MOD and is keyed by the kernel
  value `⟨pc+1, regs, out⟩`.

## Lines

| row | file | lines |
|---|---|---|
| setup | `Kit/Run.lean` (runner, pins, guards) | 290 |
| setup | `Kit/Close.lean` (skeleton, M1, M3, arm tactics) | 205 |
| setup, base | `Rel.lean` +19 (`Ranges`: `ci_sep`, `L_sep`, `ci_top`, `L_top`, `slots_top`, `L_al`, `ci_al`, `L_sep_ci`; `Ranges.scratch_out`), `Entry.lean` ±4, `Runtime.lean` +7 | 30 |
| setup, generator | `scripts/gen_lua_arms.py` +195 (helpers, liveness, `SUMMARISED`), `gen_lua_boot_witness.py` +3 | 198 (Python) |
| callee | `Kit/Muldi3.lean` (loop by measure `a1`) | 66 |
| callee | `Kit/Udivdi3.lean` (normalise loop, divide loop, summary) | 158 |
| callee | `Kit/Moddi3.lean` (4 sign paths in one `all_goals`) | 38 |
| callee | `Kit/Equalobj.lean` (3 machine paths, jump table, M2 tag lemmas ≈ 70) | 262 |
| arm | `Kit/Add.lean` | 17 |
| arm | `Kit/Mul.lean` | 19 |
| arm | `Kit/Mod.lean` 108 + `Kit/ModEq.lean` 52 (`imodC_eq`) | 160 |
| arm | `Kit/Eq.lean` (skip/jump paths, `eq_short`) | 100 |

The callee proofs reuse ship-your-interpreter's arithmetic lemmas by name
from the already-copied `Vsa/Sim/{Muldi3Spec,DivLoops,DivSpec}.lean`:
`invmul_bv`, `ret_tgt`, `shr_lt`, `shl_double`, `or_a3_toNat`, `a2_half`,
and the `bgeu`/`bltu`/`blez` bridges. Their machine parts are not reused: the
WHILE-address step lemmas are replaced by the generated helper segments at
the Lua addresses, so no relocation argument is needed.

**Generated.**
- 5,967 lines of helper segments and site batteries:
  - `Lua/Vm/Arms/{Segs,Sites}/H__muldi3`, `Hhidden___udivdi3`, `Hmoddi3`,
    `HluaV_equalobj`.
- The MUL/MOD/EQ arm segments regenerated with the fetch-head pins (`SIM_OPS`).
- In total `Lua/Vm/Arms` changed by +8,588 −825. There is no drift in the
  incumbent's generated arms (`gen_lua_arm.py --check` passes).

## CPU and memory

Each module was checked alone with `lake env lean` (user CPU s / wall s /
peak RSS):

| module | user s | wall s | peak |
|---|---|---|---|
| `Kit/Run` | 4.8 | 5.5 | 1.9 GB |
| `Kit/Close` | 3.1 | 4.2 | 1.9 GB |
| `Kit/Muldi3` | 8.9 | 9.7 | 1.9 GB |
| `Kit/Udivdi3` | 15.6 | 11.9 | 2.0 GB |
| `Kit/Moddi3` | 10.5 | 11.8 | 2.0 GB |
| `Kit/ModEq` | 0.9 | 1.1 | 0.8 GB |
| `Kit/Equalobj` | 45.1 | 19.8 | 2.4 GB |
| `Kit/Add` | 14.5 | 9.4 | 2.1 GB |
| `Kit/Mul` | 16.1 | 9.5 | 2.1 GB |
| `Kit/Mod` | 104.7 | 44.3 | 2.9 GB |
| `Kit/Eq` | 24.8 | 14.2 | 2.2 GB |
| helper segments + sites (4 + 4 modules) | 46.4 | 24.4 | 2.0 GB |

- `lake build Lua.Vm.Sim.Kit` from the regenerated segments took 84 s wall
  and peaked at 2.9 GB RSS.
- `sim_ADD` costs 14.5 s user. The incumbent's generated `Arms/Add.lean`
  costs 19 s per module (BASE.md table).

## Failed builds and wall time

The counts are approximate; they were tallied from the session log.

| phase | wall | failed `lake build` | `lake env lean` error iterations |
|---|---|---|---|
| library + `sim_ADD` + generator (helpers, `SIM_OPS`) | 35 min | 4 | ≈ 35 |
| `__muldi3` + `sim_MUL` | 18 min | 0 | ≈ 15 |
| `__udivdi3`, `__moddi3`, `imodC_eq`, `sim_MOD` | 43 min | 2 | ≈ 30 |
| `luaV_equalobj` + EQ | 64 min | 1 | ≈ 30 |
| re-check, budget regression, gate | 10 min | 3 | — |

## What the route could not express, with evidence

1. **EQ with two long strings: the relation is too weak, not the kit.**
   - `ValRepr.str` gives `TStringRepr w.mo x s`, which says only what the
     *complement* memory holds at `x`.
   - Nothing places the string object outside `Win`. `Core.frame` ties
     `c.σ.mem` to `w.mo` only outside `Win`.
   - So a `VmRel` state may hold two equal long strings at different
     pointers, one of them inside the register slots or the C frame. There
     `c.σ.mem`'s bytes differ from `w.mo`'s.
   - `luaS_eqlngstr` → `memcmp` reads `c.σ.mem` and answers *unequal*, while
     `δ .eq` (content equality) answers *equal*. The machine then takes the
     other `docondjump` edge, so `sim_EQ_Statement` is not provable against
     this `VmRel`.
   - Fix (relation widening, d1): `ValRepr.str` (or `Complement`) must state
     that a register's string object lies outside `Win`, e.g. in the heap
     below `symHeapEnd`, apart from the Lua stack and the `Scratch` words.
     The boot witness and CONCAT would supply it.
   - The proved part is stated as `sim_EQ_of_long`: `SimArm .EQ` follows from
     that path alone.
   - Even after the fix, the path needs a `memcmp` summary: two loops,
     word-wise then byte-wise. That would be a further callee row, estimated
     at about 150 lines.
2. **The per-declaration heartbeat budget.**
   - Tactic search (`kit_run`) is elaboration-heavy. `OP_MOD` had to be
     split into five path lemmas (`mod_zero`, `mod_m1`, `mod_rz`, `mod_same`,
     `mod_corr`) plus `kit_arith_fall`. `Kit/Mod.lean` sits near the default
     200,000 heartbeats.
   - Evidence: adding one disjunctive `Ranges` fact (`L_sep_ci`) to the common
     `kit_setup` doubled `omega`'s case splits. It pushed `mod_rz`, `mod_same`
     and `mod_corr` over the budget (`(deterministic) timeout at whnf`).
   - The fact is now added only where EQ needs it. The limit was never raised.
3. **Rewriting inside pins.**
   - Pin values have type `RegisterType R`. `simp at h` could not unfold a
     folded `abbrev` there (`eqMem`), nor match `slot_addr`. The first was
     worked around by making `eqMem` a macro.
   - For the second, `pins_of` falls back to `pin_eq … (by kit_val)` when the
     pin value and the expected value differ in normal form.
4. **Relation facts the arms needed**, added to the base:
   - `VmRegionsAt.L_sep_stack`, `L_al` and `ci_al`. These are new boot-witness
     obligations; `gen_lua_boot_witness.py --check` finds that they hold at
     both traced entries.
   - Numeric `Ranges` fields replacing the ∀-form `scratch_out`: `omega`
     cannot instantiate a ∀, and every `savestate` store needs the
     separations.
   - Without `L_sep_stack`, `L->top`'s store could hit a register slot. In
     that case MOD and EQ are not provable at all: this was a soundness gap in
     the base's plausibility argument.

## Forecast for the remaining arms

- **CALL print.** This is not reachable by this route alone. `luaD_precall` →
  `luaB_print` → stdio is about 81 functions and needs the stdio step tables
  (PHASES A0.2). The callee also writes `L`/`ci`/`G`, the heap and slots above
  `R[A]`: the L-C3′ *runtime* shape. A call node needs a footprint
  post-condition plus relation widening (`func` relocation, `LuaStateAt.next`).
  Estimate: arm ≈ 60 lines once a runtime summary exists; that summary is
  the dominant cost (thousands of lines).
- **VARARGPREP.** `luaT_adjustvarargs` is a runtime-shape callee that moves
  `func`. The close is not `bleach` with the same `w`: it needs a re-witness
  with a new `func`. Estimate: 40–60 lines for the arm, plus a summary of
  about 64 instructions with a slot-copy loop.
- **FORPREP.** `luaV_tointeger`/`luaV_tonumber_` write an out-parameter at
  `sp+40`, in `luaV_execute`'s own frame. `bleach` requires exactness outside
  slots ∪ `Scratch`, so it needs a variant that allows frame writes except
  `0(sp)`, about 15 lines. The float paths are excluded only by the
  FORPREP/kernel invariant. Estimate: 80 lines plus two small call nodes.
- **LOADNIL.** This is an inline loop; `kit_run` does not iterate. It needs a
  loop lemma in the `muldi3_loop` pattern (measure and invariant over the
  slots written), about 40 lines, plus a multi-slot close (an `upd` fold over
  `bleach`, about 20 lines once).
- **RETURN.** It is the `Final` clause, not a `sim`. Its return-chain callees
  (`luaD_poscall`, the exit to HTIF) are runtime/noreturn shapes, outside
  KIT's pure call node.

# Lane F1-F3: the K bitwise arms and the shifts on the join route

Base: main `c658715`. Route: CLAUDE.md's float-arm row (round 5's A-JOIN), with lane F2's shape macros.

How the numbers are taken (as lane F2):
- **Hand lines** are the non-blank, non-comment lines of the arm's declarations, without `import`, `open`, `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports built. **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k/100k/150k/200k under which the file builds. The limit is never raised, and the default is 200k.

## Gate fix (first)

The `a1-float-arm` cluster selected its cases by a name regex. That regex missed `lt_f2iL`/`R`, `le_f2iL`/`R`, the f2i combiners and the `bitwise_flt_arm` arms.

The cluster now selects by location, with the new kind `located` (`abstractions/gate.py`, `clusters.tsv`). It takes every theorem and every top-level user-command invocation in `Lua/Vm/Sim/Kit/AtFlt[A-Z]*.lean`, whatever its name, and skips comment blocks.

| when | cases | first quarter | last quarter | status |
|---|---|---|---|---|
| before (name regex) | 8 | 3.0 | 3.0 | not judged (< 12 cases) |
| after the fix, at `c658715` | 17 | 3.0 | 1.5 | ok |
| end of lane | 24 | 3.0 | 1.7 | ok |

## Result

| `FloatArms` field | status | theorem (file) | hand lines | generated (at-lemmas) | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| BANDK | **proved** (soft, `FloorSpec`) | `sim_BANDK_flt` (`Kit/AtFltBandk.lean`) | 3 | `At/BandkF` 603 | 5.8 s | 2.38 GB | ≤ 150k |
| BORK | **proved** (soft, `FloorSpec`) | `sim_BORK_flt` | 3 | `At/BorkF` 595 | 3.9 s | 2.38 GB | ≤ 50k |
| BXORK | **proved** (soft, `FloorSpec`) | `sim_BXORK_flt` | 3 | `At/BxorkF` 595 | 4.4 s | 2.37 GB | ≤ 50k |
| SHRI | **proved** (soft, `FloorSpec`) | `sim_SHRI_flt` (`shift_flt_arm`: 2 class declarations) | 1 | `At/ShriF` 766 | 9.6 s | 2.42 GB | ≤ 100k |
| SHLI | **proved** (soft, `FloorSpec`) | `sim_SHLI_flt` (2 class declarations) | 1 | `At/ShliF` 766 | 17.6 s | 2.40 GB | ≤ 150k |
| SHL | **proved** (soft, `FloorSpec`) | `sim_SHL_flt` (`shift2_flt_arm`: 16 class declarations) | 1 | `At/ShlF` 2,423 | 122.5 s | 3.22 GB | ≤ 150k |
| SHR | **proved** (soft, `FloorSpec`) | `sim_SHR_flt` (16 class declarations) | 1 | `At/ShrF` 2,431 | 144.8 s | 3.26 GB | ≤ 200k |
| EQ | open | — | — | — | — | — | — |
| EQK | open | — | — | — | — | — | — |

Seven fields left `FloatArms`, so it now has 16 fields: 14 arm fields plus `soft` and `floor`.

**Setup** (library and generator):

| file | hand lines | what |
|---|---|---|
| `Kit/AtFrame.lean` (new) | 21 | `at_fwd`, `at_fwd_k` (forward the loads, read `0(sp)` as `k`, forward again), as `at_eq_ext`/`at_side_ext` rules |
| `Kit/At.lean` | +4 | `proveBy` runs without error recovery and rejects a proof with a synthetic `sorry` |
| `Kit/AtJoinInt.lean` (new) | 12 | `at_jbitk` (`op_bitwiseK`'s set-up before `at_walk`) |
| `Kit/AtJoinShift.lean` (new) | 265 | listed below |
| `Kit/AtJoin.lean` | +≈ 30 | listed below |
| `scripts/gen_lua_at.py` | +17 python | `OP_{BANDK,BORK,BXORK}_F`, `OP_{SHL,SHR,SHLI,SHRI}_F` rows, seeds, `AtFrame` import |
| `scripts/gen_lua_arms.py` | +3 python | the shifts in `FLOAT_ARMS`, so `s10` stays live across the float calls; regenerates `Segs/G22,G23,G75–G77` and `At/Shl,Shr` |
| `abstractions/gate.py`, `clusters.tsv` | +36 python | the `located` cluster kind |

`Kit/AtJoinShift.lean` contains:
- `shiftl_m`, `shiftr_m`, `shiftr_K`: the kernel's shift on the machine's tests, as `bsel`, which `split` and `simp` cannot see into;
- the residual-atom rules `slt_negfix*`, `slt_i64*`, `slt_negi64*`, `ult_c*`, `uge_c63`, and `BitVec.zero_sub`;
- `at_kfork`, `at_new`/`at_new_ext` for a shifted store;
- `F2IC`, `armBody_f2ic`, `at_jshiftI`, `at_jshift2(f)`;
- the commands `shift_flt_arm` and `shift2_flt_arm`.

`Kit/AtJoin.lean` gains:
- a fallback in `at_step1`: after the soft-float forks, a guard the context does not decide is a fork;
- the hooks `at_leaf_first` (tried before the refutation) and `at_leaf_ext` (in the close branch).

## How the route was extended

1. **BANDK/BORK/BXORK: F2's obstruction isolated.**
   - The side conditions of `at_seg seg_8001d730_8001d768` were not the failing obligation.
   - The failing obligation was the pin `x14 = K[C] &&& i`: a load whose address is itself a load (`ld 0(sp)`) through `floor`'s frame.
   - `atFwd` tried the outer load first. `at_sep` then ran `omega` under `<;>` with error recovery on, so `proveBy` "succeeded" with an admitted goal and a logged error. That logged error is the `omega` failure F2 saw.
   - Fix, generic:
     - `proveBy` runs without recovery, so the attempt fails cleanly. No green module used the old path, because a recovered error always fails the module.
     - `at_fwd_k` forwards the loads, rewrites `0(sp)` to `k`, then forwards again.
2. **Shifts: residual atoms.**
   - The machine tests the amount (`bltz`, `blt 63`, `blt -63`, or `bltu`/`bgeu` on `C`). The kernel's `luaV_shiftl` is restated on exactly those tests.
   - When the amount is a converted float, a test of `__fixdfdi`'s value becomes the model's `toInt64` under the range atom (`slt_fixL`/`R`, `slt_negfix*`). The kernel's test of `f2iVal` takes the same `decide` form (`slt_i64*`), so both sides read one residual atom.
   - The kernel's selections are `bsel`. They are left unsplit, so `at_leaf` does not multiply leaves.
   - On the closing side, `at_kfork` rewrites them by the path's fork facts. The range comes from the kernel's own `F2Ieq` fact.
3. **Leaf cost.**
   - Each arm is split into one declaration per `F2Ieq` outcome, and for SHL/SHR also per the other operand's class and outcome.
   - `at_leaf_first` closes a shift leaf before trying a refutation. The expensive failure is the refutation of a satisfiable leaf. A close on a wrong side fails fast, at the `fin` lemma's key or pc.
   - SHL's `b0_11` declaration went from 200–300k heartbeats to under 150k.
4. **Two smaller fixes.**
   - `exact .int` at default transparency unfolded `Aff.den`/`BitVec` arithmetic until `maxRecDepth`. The shifts' `at_new` matches at reducible transparency and unfolds the affine immediate first.
   - The kernel's `simp` turns `0 - y` into `-y`, so `BitVec.zero_sub` is applied to both sides.

## Open, with the obstruction

**EQ, EQK** (`FloatArms.EQ`, `.EQK`):
- `OP_EQ` calls `luaV_equalobj` (`jal 0x8001b780`). Its float paths are:
  - the same variant through the `ttypetag` jump table: target `0x8001b90c`, `__eqdf2`;
  - mixed integer and float at `0x8001b810`: the `F2Ieq` chain `floor`/`__eqdf2`/`__gedf2`/`__ledf2`/`__fixdfdi` at `0x8001b9b4` or `0x8001ba68`.
- The route cannot reach them, for three reasons:
  1. `gen_lua_arms.py`'s `HELPERS` entry for `luaV_equalobj` has `0x8001b810` as a stop, and `0x8001b90c` is not a root. So no segments exist for these paths. Adding them changes the liveness of the segments `equalobj_sum` (the kit-route proof of `EQ`) is built on.
  2. `gen_lua_at.py` treats `luaV_equalobj` only as a call node with a hand summary for two long strings (`lngeq_sum`). Its walker stops at a `ret`/`jr` (`Stop("return")`), so it cannot walk a callee inline, nor a jump-table `jr` whose target is a `.rodata` word.
  3. The callee-context route (`FNS`, `Kit/AtFn.lean`) has no soft-float call nodes or pair atoms.
- What is needed is a float summary of `luaV_equalobj` as a call node: `a0` equals `eqNum` of the two values, with the frame as a `clob`. That requires (1) and (2), or float support in (3).
- The two fields stay `FloatArms` premises (PHASES row).

## Builds

- Every module was built one `lake build` at a time while iterating, under a 12–14 GB cap.
- The full `lake build Lua Vsa VsaIris` ran with `LEAN_NUM_THREADS=4` under 30 GB: exit 0, 9 min 43 s wall, 4.79 GB peak.
- `gen_lua_at.py --check` and `gen_lua_arms.py --check` are clean, and `scripts/check.sh --static-only` is OK.
- The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`. They are listed in check.sh stage 6.

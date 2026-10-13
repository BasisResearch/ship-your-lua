# Lane F1-F4: `EQ`, `EQK` with a float operand, through `luaV_equalobj`'s float summary

Base: main `357b178`. Route: the join route for the arms (CLAUDE.md's float-arm row), the callee-context rows for the callee (`Kit/AtFn.lean`, `gen_lua_at.py --fn`).

How the numbers are taken (as lanes F2, F3):
- **Hand lines** are the non-blank, non-comment lines, without `import`, `open`, `namespace`, `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports built. **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k/100k/150k/200k under which the file builds. The limit is never raised.

## Result

| `FloatArms` field | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| EQ | **proved** (`FloorSpec`) | `At.sim_EQ_flt` (`Kit/AtFltEq.lean`) | arm 77 (shared with EQK: `EqfTest`, `flt_pair`, the shared tail `at_eqf_tail`) | `At/EqF` 115 | 4.6 s (arm file) | 2.39 GB | ≤ 50k |
| EQK | **proved** (`FloorSpec`) | `At.sim_EQK_flt` (`Kit/AtFltEq.lean`) | (above) | `At/EqkF` 109 | | | |

`FloatArms` loses `EQ` and `EQK`: 14 fields, 12 of them arms, plus `soft` and `floor`.

The callee and the call node:

| piece | file | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|
| `luaV_equalobj`'s float summary `equalobj_flt_sum`, the classes `eqo_ff`/`eqo_if`/`eqo_fi`, `eqfMem` | `Kit/EqualobjF.lean` | 205 | `AtF/EqobjFF` 207, `AtF/EqobjIF` 654, `AtF/EqobjFI` 654 | 12.4 s (AtF: 12.6, 52.8, 69.5 s) | 2.46 GB (AtF ≤ 2.52 GB) | ≤ 100k (AtF ≤ 50k) |
| the call node at a row `eqf_at`, `at_eqf`/`at_eqkf`, `vOf`/`kvOf` | `Kit/AtEqF.lean` | 76 | `At/EqF` 115, `At/EqkF` 109 | 1.5 s (At: 31.2, 10.6 s) | 2.31 GB (At ≤ 2.88 GB) | ≤ 50k (`At/EqF` ≤ 100k) |
| a float against another type: `eqo_diff_gen` (`eqo_diff` its corollary) | `Kit/Equalobj.lean` | +35 / −0 net | | | | |

**Setup** (library and generators, counted once):

| file | lines | what |
|---|---|---|
| `Kit/AtFnFlt.lean` (new) | 65 | `fat_fcall` (a soft-float summary at a callee row, dead `s6`/`s10` pinned), `fat_fnsp`, `fat_rod`, `fat_walk` (fork splitting on the `Bool` of a guard no fact decides) |
| `Kit/AtFn.lean` | +≈ 45 | `fw{1,2,4,8}_patch`, `memPatch` in `fat_mem`, `ground_toNat` (an `auipc` address as a literal, a pre-simproc of `fat_rd`), `fat_side` on `auipc` addresses |
| `scripts/gen_lua_at.py` | +≈ 140 python | `--fn` specs with `float=True` (`FCALLS` call nodes, a framed routine's `Fm` as a `memPatch` log entry, `FOPAQUE`, `noncomputable section`); the `eqf` specs; `OP_EQ_F`, `OP_EQK_F`; the `eqf` location; a `clob` with a content function |
| `scripts/gen_lua_arms.py` | +11 python | `luaV_equalobj`: root `0x8001b90c`, no stop; `CALLEE_READS` for `floor`, `__eqdf2`, `__gedf2`, `__ledf2`, `__fixdfdi` |

## The three gaps of lane F3, closed

1. **Segments.** `0x8001b810` is no longer a stop, and the jump table's `LUA_VNUMFLT` target `0x8001b90c` is a root. That gives 33 new segments in `Segs/HluaV_equalobj.lean`.
   - The existing summary's liveness first moved: the soft-float helpers keep `s6`/`s10` (`[22, 26]`), and that liveness flowed back to `luaV_equalobj`'s entry, which `eqPre` (`KFrame`) does not pin.
   - Fixed by `CALLEE_READS` for the five routines: a call reads only its arguments. The summaries' `HFrame` is pinned at the call itself (`SegSt.pin22`/`pin26`).
   - Of the existing segments, three carry three more pins, and `seg_8001b7b8_8001b7c8` is split at the new leader `0x8001b7bc`.
   - `equalobj_sum`, `eqo_long` and the EQ/EQK proofs build unchanged.
2. **The walk across the jump table.** The callee route already followed a `jr` to a literal target. The table's word for tag 19 is a root fact (`cells`). The `auipc` address it is read at is evaluated to a literal by `ground_toNat`, before `ground_bv` folds the `+++`.
3. **Soft-float call nodes on the callee route, once and generically.** `float=True` in an `FNS` spec reuses the arm route's `FCALLS` table.
   - Leaf routines keep the memory.
   - `floor`'s 112-byte frame is a `memPatch` entry, read past by `fw*_patch`.
   - Forks on the routines' answers are split by `fat_walk`, which has no per-callee code.

## Per-leaf decision

`eqf_res` (in `pins_of`'s `kit_val` hook) proves each leaf's 0/1 equal to `eqNum`. It rewrites the fork facts by the routines' `spec_proved` lemmas, the `bnez`/`bltz`/`bgez` idioms, `F64`'s model bridges, `floor`'s model (`floor_model`), and `__fixdfdi`'s value under the range fact (`fix_of_model`). The kernel's mixed case is restated as `f2iOk a && decide (f2iVal a = b)` (`eqNum_fi`/`eqNum_if`).
- This is not the pair-atom `decide` of `at_atoms`. On the callee route each leaf's answer is a value equation, not a refutation over compare atoms. Rewriting by the facts closes all 9 leaves (FF: 1, IF: 4, FI: 4).

## Open

Nothing new.

## Integration with lane F1-F5

Lane F1-F5 discharged `FloorSpec` (`PREMISE_PROOF`: `floorSpec_proved`). On merging, the callee route uses it too:
- `emit_fcall` passes `PREMISE_PROOF[mod]` to a framed routine's `sum` and imports its `FPROVED` module, so the `eqf` specs' context loses `hfl : FloorSpec`.
- `eqf_res`'s `floor_model`, `eqo_{ff,if,fi}`, `equalobj_flt_sum`, `eqf_at`, `at_eqf`/`at_eqkf` and `sim_EQ_flt`/`sim_EQK_flt` take no `FloorSpec`. `armTable` uses `At.sim_EQ_flt` and `At.sim_EQK_flt` directly.
- `FloatArms` keeps `soft`, `DIV`, `DIVK`, `POW`, `POWK`, `MOD`, `IDIV`, `MODK`, `IDIVK` and `FORPREP`.

## Builds

- Single modules were built one `lake build` at a time under a 12 GB cap. The full `lake build Lua Vsa VsaIris` (2051 jobs) ran with `LEAN_NUM_THREADS=4` under 30 GB and completed with exit 0.
- `gen_lua_at.py --check` and `gen_lua_arms.py --check` are clean. `check_discipline.py` is OK. `abstractions/gate.py` is OK (`a1-float-arm`: 32 cases, first quarter 3.0, last quarter 4.1).
- The axioms of `sim_EQ_flt`, `sim_EQK_flt`, `equalobj_flt_sum`, `armTable` and `vm_refinement_of_open'` are `[propext, Classical.choice, Quot.sound]`. They are listed in check.sh stage 6.

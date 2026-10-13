# Lane F1-F2: float arms on the join route (round 5's A-JOIN)

Base: main `9f5ab04`. Route: CLAUDE.md's A1 float row (A-JOIN, adopted in round 5).

How the numbers are taken:
- **Hand lines** are non-blank, non-comment lines of the arm's declarations, without `import`, `open`, `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` (imports built), and **peak** is its maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k/100k/150k/200k under which the file builds. The limit is never raised; the default is 200k.

## Result

| `FloatArms` field | status | theorem (file) | hand lines | generated (at-lemmas) | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| LEI | **proved** (soft) | `sim_LEI_flt` (`Kit/AtFltLei.lean`) | 3 | `At/Lei` 279 | 1.9 s | 2.24 GB | ≤ 50k |
| GTI | **proved** (soft) | `sim_GTI_flt` (`Kit/AtFltGti.lean`) | 3 | `At/Gti` 279 | 1.9 s | 2.24 GB | ≤ 50k |
| ADD | **proved** (soft) | `sim_ADD_flt` (`Kit/AtFltAdd.lean`) | 3 | `At/Add` 809 | 6.0 s | 2.30 GB | ≤ 100k |
| (SUB, refactor) | proved, 14 → 3 lines | `sim_SUB_flt` | 3 | — | 5.7 s | 2.30 GB | ≤ 100k |
| ADDK | **proved** (soft) | `sim_ADDK_flt` | 3 | `At/Addk` 833 | 5.4 s | 2.31 GB | ≤ 100k |
| SUBK | **proved** (soft) | `sim_SUBK_flt` | 3 | `At/Subk` 855 | 5.4 s | 2.30 GB | ≤ 100k |
| UNM | **proved** (no premise) | `sim_UNM_flt` | 3 | `At/UnmF` 103 | 1.3 s | 2.27 GB | ≤ 50k |
| (LT, refactor) | proved, 19 → 3 lines | `sim_LT_flt` | 4 | — | 10.8 s | 2.30 GB | ≤ 150k |
| LE | **proved** (soft) | `sim_LE_flt` (`Kit/AtFltLe.lean`) | 4 | `At/LeF` 2,441 | 7.2 s | 2.31 GB | ≤ 150k |
| LT f2i (`LtF2I_Statement`) | **discharged** (soft, `FloorSpec`) | `lt_flt_f2i` (`Kit/AtFltF2I.lean`) | 8 | `At/LtF` 275 → 2,402 | 37.2 s (with LE's) | 3.33 GB | ≤ 200k |
| LE f2i (`LeF2I_Statement`) | **discharged** (soft, `FloorSpec`) | `le_flt_f2i` | 8 | (in `At/LeF`) | (above) | (above) | ≤ 200k |
| BNOT | **proved** (soft, `FloorSpec`) | `sim_BNOT_flt` | 3 | `At/BnotF` 421 | 2.0 s | 2.29 GB | ≤ 50k |
| BAND | **proved** (soft, `FloorSpec`) | `sim_BAND_flt` (6 class declarations) | 1 | `At/BandF` 1,613 | 30.1 s | 2.66 GB | ≤ 200k |
| BOR | **proved** (soft, `FloorSpec`) | `sim_BOR_flt` | 1 | `At/BorF` 1,613 | 35.0 s | 2.67 GB | ≤ 200k |
| BXOR | **proved** (soft, `FloorSpec`) | `sim_BXOR_flt` | 1 | `At/BxorF` 1,613 | 30.4 s | 2.66 GB | ≤ 200k |

Fields that left `FloatArms`: LEI, GTI, ADD, ADDK, SUBK, UNM, LT, LE, BNOT, BAND, BOR and BXOR (12). The new field `floor : FloorSpec` was added. `FloatArms` now has 23 fields: 21 arm fields plus `soft` and `floor`.

**Setup** (library and generator; hand lines as above):

| file | hand lines | what |
|---|---|---|
| `Kit/AtJoinOps.lean` | 78 | the per-kernel-shape set-ups before `at_walk`: `at_jorderI` (`op_orderI`), `at_jarith` (`op_arith`), `at_jarithK` (`op_arithK`, `flt_k_q`, `num_k`), `at_jorder` (`op_order`, `FltF2I`), `luai_numunm`'s store rule |
| `Kit/AtJoinF2I.lean` | 221 | the f2i chain: `slt_fixR`/`slt_fixL` (a value equation as a conditional under its range atom), the kernel's chain restated over the atoms (`ltIntFloat_f2i`, …, `flttointeger_eq`, `rawArith_bit_*`), `at_fact`, the stored integer (`at_new_ext`), `at_jf2i`, `at_junary`, `at_jbit`, `RegCls`/`armBody_cls`/`sim_on_or`, `bitwise_flt_arm` |
| `Kit/FltNeg.lean` | 37 | `F64.neg_eq_xor`, `F64.toModel_neg` (NaN included), `ValRepr.flt_neg` |
| `Kit/FltValLt.lean`, `Fn/Floor.lean` | 150 + 20 | ported unchanged from A-INC (branch `worktree-agent-af308d3f0fd62a0df`): `fixdfdi_model`, `.rodata` constants, `FloorSpec` |
| `Kit/AtJoin.lean` | +≈ 90 | `at_atoms`: `at_atom_simp`, the immediate through `__floatsidf`, residual Boolean atoms, facts reverted with their atoms, the structural `Decidable` (`atomDec`, `at_atom_decide`), Prop facts only; `at_step1` never re-splits a fork; `at_leaf` splits an `if` kernel result (`split_res_hq`) |
| `Kit/AtFloat.lean`, `Kit/At.lean`, `Kit/AtFAttr.lean` | +29, +1, +5 | A-INC's `at_ground`, `at_fnSp` (112 bytes), 15 row variants; the `at_atom_simp` attribute |
| `scripts/gen_lua_at.py`, `gen_lua_arms.py` | +66/−11 python | the arms' `FLOAT_ARMS`/`SEG_OP`/`FLOAT_SEED` rows; `Fixdfdi`/`Floor` call nodes (`PREMISED`), `auipc`, symbolic `sext.w` (A-INC), `xori` |

## How the route was extended

1. **Kernel-shape set-ups (law 3).** SUB's 14 lines are now `at_jarith`, and ADD is SUB with `model_add_comm` in the store rule, because the compiler calls `__adddf3(c, b)`. The K forms use the same macro over `K[C]`'s view (`kitk_const`, `flt_k_q`, `num_k`). LEI/GTI use `at_jorderI`, LE uses LT's set-up (`at_jorder`), and UNM/BNOT use `at_junary`. Every arm is a 1–4-line instance.
2. **Value equations in the leaf** (A-JOIN obstacle 3). `__fixdfdi`'s result compared with an integer is rewritten to `if minIntF ≤ g then decide (i < g.toInt64) else <opaque>`. This gives a conditional over a pair atom, and the decision does the rest. The integer compares become residual Boolean atoms. A stored converted integer uses `fixdfdi_model`, whose side condition is a path fact proved by the leaf's own decision (`at_fact`).
3. **Leaf cost.** One `Decidable` instance over 9 binders exceeded the instance search. The fix is an instance built by structure plus kernel evaluation, with each fact reverted under the atoms it reads, so that a false fact prunes the enumeration. On LT's f2i class this took the leaves from 866k to 71k heartbeats.
4. **Heavy arms.** BAND as one declaration is ≈ 300k heartbeats. It is split into one declaration per (float operand, class of the other) (`armBody_cls`, `sim_on_or`), generated by the command `bitwise_flt_arm` (1 hand line per arm). Each class declaration is ≤ 200k, but the largest are in the 150–200k bracket.

## Gate

`python3 abstractions/gate.py` reports `a1-float-arm: 8 cases — ok (first 3.0, last 3.0; not judged below 12 cases)`. It was run after each arm and was never red.

The gate's theorem regex does not see every case:
- `lt_f2iL`/`R` and `le_f2iL`/`R` are each a 3-line instance.
- `sim_BAND_flt`, `sim_BOR_flt` and `sim_BXOR_flt` come from the `bitwise_flt_arm` command, one line each.

Counted by hand, the lane has 19 cases, all at 1–4 lines. That is the automation floor (≤ 5), so the cluster cannot fail on cost.

## Open, with the obstruction

- **BANDK, BORK, BXORK**: the generated at-lemmas do not build.
  - `gen_lua_at.py` emitted `BandkF` etc., and `lake build Lua.Vm.At.BandkF` fails.
  - The failure is `at_seg Lua.Vm.Arms.seg_8001d730_8001d768` (`omega could not prove the goal`). The segment re-reads the constant array pointer `ld 0(sp)` through `floor`'s 112-byte frame (`memPatch … (sp - 112) 112`) and loads `K[C]`.
  - A standalone `bytesT8_memPatch_out` + `kptr_at` rewrite proves the address side condition (`hlo_5` form). The obligation that fails inside `at_seg` was not isolated: the `kit_disch` errors are logged at the `at_seg` call.
  - The arm side (`at_jbitk`: `kitb_const`, then `rawArith_bit_fi`) was written and removed with the modules. These fields stay in `FloatArms`.
- **SHL, SHR, SHLI, SHRI**: not attempted on the hand side.
  - The machine branches on the converted amount (`msb`, `< 64`) before shifting.
  - Those branches are facts about `__fixdfdi`'s value, not pair atoms. `at_fact` would have to decide them, and the store needs `shiftlC_*` under them.
  - The modules were generated (`ShlF`, …) and then dropped.
- **Blocked on summaries** (skipped as instructed):
  - MUL, MULK (`__muldf3`);
  - DIV, DIVK (`__divdf3`);
  - POW, POWK (`pow`);
  - MOD, MODK (`fmod`);
  - IDIV, IDIVK (`__divdf3` and `floor`);
  - EQ, EQK (`luaV_equalobj`'s float case: a callee summary);
  - FORPREP's coerced classes (`luaV_tonumber_`).
- **Joins over unequal write logs** (SUB's per-operand rejoins) were not built: the macro made it unnecessary for lines. SUB, ADD, ADDK and SUBK still walk their three operand classes separately (≤ 100k each).
- **`FloorSpec`** stays a named premise (`FloatArms.floor`, PHASES).

## Builds

- Every module was built one `lake build` at a time, in import order, under a 12 GB cap (`seqbuild.sh` pattern from A-JOIN's `build.sh`); the run through `Lua.Vm.Sim.Fold` ended with 0 failures.
- Generators: `gen_lua_at.py`, `gen_lua_arms.py` and `gen_lua_arm.py` pass `--check`.
- `scripts/check.sh --static-only` is OK.
- Axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`. They are listed in check.sh stage 6.

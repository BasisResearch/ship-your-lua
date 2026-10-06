# F1 arms, lane F1-1 (IDIVK, UNM, SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK)

Base `df460c9`, on the round-4 route (at-lemmas, `abstractions/ROUND-4.md`
§7).

How the numbers were measured:
* **Hand lines** are counted by `abstractions/census.py`, the gate's measure: non-blank, non-comment proof lines per declaration, local macros excluded.
* **File lines** are non-blank, non-`--` lines.
* **CPU and peak memory** come from one `lake env lean` of the module alone (user seconds, peak RSS).
* **Heartbeats** are per declaration, elaborated synchronously (`Elab.async false`), in `maxHeartbeats` units. The default budget is 200k.

## Per arm

Every arm below is **proved**, except UNM's string path (`UnmStr_Statement`).

| arm | hand lines (census) | arm file | generated | CPU arm / gen | peak arm / gen | largest decl (arm; generated) |
|---|---|---|---|---|---|---|
| IDIVK (`At.sim_IDIVK`) | 13 (5 paths × 2, `sim` 3) | 32 | 524 | 5.9 / 42.7 s | 2.06 / 2.40 GB | 29.0k; `fin_1` 93.5k |
| UNM (`At.sim_UNM_of_str`) | 5 | 35 | 80 | 5.1 / 7.2 s | 2.03 / 2.14 GB | `unm_stuck` 51.8k; `fin` 53.7k |
| SHL (`At.sim_SHL`) | 11 | 27 | 402 | 6.2 / 25.4 s | 2.08 / 2.23 GB | 27.3k; 52.9k |
| SHR (`At.sim_SHR`) | 11 | 27 | 404 | 7.0 / 25.7 s | 2.07 / 2.23 GB | 29.5k; 52.9k |
| SHLI (`At.sim_SHLI`) | 11 | 27 | 318 | 4.4 / 21.3 s | 2.04 / 2.22 GB | 18.5k; 52.9k |
| SHRI (`At.sim_SHRI`) | 11 | 28 | 322 | 4.3 / 21.5 s | 2.04 / 2.23 GB | 17.6k; 52.9k |
| BANDK (`At.sim_BANDK`) | 4 | 20 | 125 | 1.9 / 11.3 s | 2.03 / 2.17 GB | 10.6k; 54.2k |
| BORK (`At.sim_BORK`) | 4 | 20 | 122 | 1.9 / 11.1 s | 2.03 / 2.15 GB | 10.5k; 54.2k |
| BXORK (`At.sim_BXORK`) | 4 | 20 | 122 | 1.8 / 11.0 s | 2.03 / 2.17 GB | 10.5k; 54.2k |
| refactor: IDIV | 53 → 13 | 31 | (unchanged) | 5.8 s | 2.09 GB | 29.7k |
| refactor: MODK | 57 → 16 | 34 | (unchanged) | 7.0 s | 2.06 GB | 32.2k |

Gate after the last arm:

```
a1-kit-arm: 42 cases — ok (first 1.9, last 1.8)
```

## Setup (the factoring, then the shift and bitwise shapes)

* **`Kit/AtOps.lean`** (219 file lines, 14 census).
  * It states the arm-side hand-off once per kernel shape:
    * `at_fall`, `at_fallK`, `at_fall1`: the `opArith` fall-through, for two registers, `K[C]`, and one register;
    * `at_div_m1`, `at_div_gen`: the division arms (`DivPath`);
    * `sim_unary`, with `at_unary_int`/`at_unary_stuck`: one-register `setR`;
    * `TagB`, `at_int1`, `sim_tagB`;
    * `kitb_const`, `at_bitk`, `at_bitk_fall`: `bitwiseRK`, where `K[C]` has no tag test and the kernel operand order is turned to the machine's by `and_comm`/`or_comm`/`xor_comm`.
  * After the gate stop, IDIVK, UNM, IDIV and MODK were moved onto it, which removed the copied `*_fall`/`*_m1` proofs.
* **`Kit/Shift.lean`** (166 lines).
  * It restates `luaV_shiftl`/`luaV_shiftr` per machine branch, in four families: `shiftlC_*`, `shiftrC_*`, `shiftrK_*` and `sc_eq`.
  * Each family has four cases: `big`, `run`, `neg_big`, `neg_run`.
  * The facts over the field `C` are three `decide +kernel` lemmas over `c < 256`.
  * These lemmas follow the `imodC_eq`/`idivC_eq` naming. Their first names (`shl_big`, …) fell inside the gate's arm-path selector.
* **`Kit/AtShift.lean`** (105 lines).
  * It holds the path predicates and the arm combinator: `ShPath`, `Sh1`–`Sh4`, the guard and amount abbreviations, `sim_shift`, `at_shift`.
  * Two closers are extended by `macro_rules` for the affine amount `C`: `at_hyp` and `at_new`.
* **`Kit/At.lean`** (+43/−8, additive):
  * new `Loc` constructors `and`, `or`, `sll`, `srl`, `addw`, `subw`, with their denotations;
  * `at_eq`:
    * it applies congruence under `extractLsb` (`congrN` with no closing by `rfl`);
    * a binary operation on two loads goes to the operand congruence instead of failing;
    * a folded `Aff.den` is unfolded;
  * `at_pins` elaborates a pin's fact before `pin_eq`. Elaborated against an `addiw` row value inline, the unifier loops (`maximum recursion depth`);
  * a segment side condition through an in-segment `ld 0(sp)` gets `kptr_at` first.
* **`scripts/gen_lua_at.py`** (+33/−8):
  * `ARMS` gains the nine arms;
  * new instructions `and`, `or`, `sll`, `srl`, `subw`, `negw`, `addiw`;
  * float-path pruning, for this lane's arms only (`PRUNE_ARMS`). A tag is never `LUA_VNUMFLT`, and the not-taken guard is closed from `ValRepr.ne_float`;
  * MODK, IDIV and FORPREP's generated files are byte-identical to the base.

## UNM's string path

How `lvm.c`'s `OP_UNM` handles each value:
* an integer is negated inline (`0x8001eb1c`);
* a float is negated by its sign bit (`0x8001d8dc`), which no F1 value reaches;
* anything else calls `luaT_trybinTM(L, rb, rb, ra, TM_UNM)` (`0x8001ec2c`).

The kernel `δ .unm` steps on an integer, and on a string with `str2int s = some _`. The machine reaches that value only through:

`luaT_trybinTM` → the string metatable's `__unm` (`lstrlib.c` `arith_unm`) → `trymt`/`tonum` → `lua_arith`.

That path is the named premise `UnmStr_Statement := ArmBody .UNM RegStr` (PHASES row). It is to be supplied with the `MMBIN`/`CALL` runtime summaries. The other values are the kernel's stuck case (`unm_stuck`), proved.

## Obstacles and risks

* **`FORPREP.fin_1` is over the budget when elaborated synchronously.**
  * It measures 200.4k (deterministic timeout at `whnf`) with `Elab.async false`. That holds both on the base `At.lean` and with this lane's. The round-4 report gave it 197.8k.
  * The normal `lake build` passes.
  * This is the round-4 carried risk, the frame proofs of the close. It is not a regression here.
* **The scratch tooling was shared.** Another session overwrote a scratch script during the measurement, so the measurements were rerun with a private copy.

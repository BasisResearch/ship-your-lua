# F1 arms, lane F1-1 (IDIVK, UNM, SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK)

Base `df460c9`, on the round-4 route (at-lemmas, `abstractions/ROUND-4.md`
§7). Hand lines are `abstractions/census.py`'s (non-blank, non-comment proof
lines per declaration, the gate's measure; local macros excluded). File lines
are non-blank, non-`--` lines. CPU and peak memory are one `lake env lean`
of the module alone (user s, peak RSS). Heartbeats are per declaration,
elaborated synchronously (`Elab.async false`), in `maxHeartbeats` units (the
default budget is 200k).

## Per arm

| arm | status | hand lines (census) | arm file | generated | CPU arm / generated | peak arm / generated | largest decl (arm; generated) |
|---|---|---|---|---|---|---|---|
| IDIVK | **proved** (`At.sim_IDIVK`) | 36 (zero 2, m1 8, same 2, diff 3, fall 18, `sim_IDIVK` 3) + the 9-line `idivk_gen` macro | 66 | 524 (`Lua/Vm/At/Idivk.lean`, 33 lemmas) | 8.6 s / 45.4 s | 2.06 / 2.40 GB | `idivk_same` 28.7k; `fin_1` 93.5k |
| UNM | **proved but the string path** (`At.sim_UNM_of_str`, premise `UnmStr_Statement`) | 25 (`unm_int` 11, `unm_stuck` 7, `sim_UNM_of_str` 7) | 58 | 80 (`Lua/Vm/At/Unm.lean`, 4 lemmas) | 3.4 s / 8.2 s | 2.04 / 2.14 GB | `unm_stuck` 29.4k; `fin` 53.6k |
| SHL, SHR, SHLI, SHRI, BANDK, BORK, BXORK | not started: the gate stop (below) | — | — | — | — | — | — |

## Setup

* `scripts/gen_lua_at.py`: `ARMS += OP_IDIVK, OP_UNM`; float-path pruning for
  this lane's arms (`PRUNE_ARMS`: a tag compared with `LUA_VNUMFLT` is never
  equal, the not-taken guard is closed from `ValRepr.ne_float`; the earlier
  arms' generated files are unchanged).
* No library change: IDIVK is IDIV's route with `kitk_ints`/`dvK`; UNM uses the
  existing `Loc.sub (lit 0)` for `neg`.

## UNM's string path

`lvm.c` `OP_UNM`: an integer is negated inline (`0x8001eb1c`), a float by
the sign bit (`0x8001d8dc`, no F1 value), anything else calls
`luaT_trybinTM(L, rb, rb, ra, TM_UNM)` (`0x8001ec2c`). The kernel `δ .unm`
steps on an integer and on a string with `str2int s = some _`; the machine
reaches that value only through `luaT_trybinTM` → the string metatable's
`__unm` (`lstrlib.c` `arith_unm` → `trymt`/`tonum` → `lua_arith`), a runtime
call. That path is the named premise `UnmStr_Statement := ArmBody .UNM UnmStr`
(PHASES row), to be supplied with the `MMBIN`/`CALL` runtime summaries. Every
other value (nil, booleans, builtins) is the kernel's stuck case
(`unm_stuck`), proved.

## Gate: STOP after UNM

```
a1-kit-arm: 9 cases — FAIL (first-quarter mean 2.0 lines, last-quarter mean 9.0: not a third cheaper)
     2.0 idivk_zero, 2.0 idivk_same, 3.0 idivk_diff, 3.0 sim_IDIVK, 8.0 idivk_m1, 18.0 idivk_fall,
     7.0 unm_stuck, 7.0 sim_UNM_of_str, 11.0 unm_int
```

The lane stopped there, as instructed (the remaining seven arms not started).
What the numbers say:

* **The cost is the arm-side setup, not the segments.** Every machine path
  is generated and costs at most 93.5k heartbeats in its own declaration; the
  hand lines are the kernel's forward evaluation and case split (M1), per
  kernel shape: `kit_setup`, `kit_bound`, `kit_reg`, `split at hk`,
  `pair_eq`, `simp … at hk; subst hk`, written per path.
* **Duplication.** `idivk_fall` (18 lines) is the third copy of
  `modk_fall`/`idiv_fall` (the `op_arith(K)` fall-through on at-lemmas), and
  `idivk_m1` the third of `modk_m1`/`idiv_m1`. A generic
  "`opArith`/`setR` kernel → at-lemmas" path tactic (setup, operand values,
  the kernel's exit chosen by tags, `at_go`) would make each path a one-line
  instance; the remaining seven arms are all `opArith` (shifts, `bitwiseRK`)
  and would be its instances.
* **Gate artefact (also).** Ties within one commit are ordered by cost
  (`cases.sort()` on `(time, cost, name)`), so a commit's cheap macro cases
  fill the first quarter.

## What the remaining arms need (surveyed, not built)

* **BANDK/BORK/BXORK** (`0x8001d710`, `0x8001d6b8`, `0x8001d660`): the
  `R[B]` tag test, `ld 0(sp)` + `K[C]`'s payload with no tag test, `and`/`or`/
  `xor`; the fall-through is `mv s11,s3` (`0x8001c9cc`). Needs `Loc.and`,
  `Loc.or` and the generator's `and`/`or`; the kernel side needs a
  `bitwiseRK` setup (`kval = some (.int y)`; `Core.kconst` gives the payload).
* **SHL/SHR** (`0x8001d5f0`, `0x8001d57c`) and **SHLI/SHRI** (`0x8001dd30`,
  `0x8001dd8c`): `luaV_shiftl` inlined as `bltz`/`blt` (`bltu`/`bgeu` on `C`
  for SHRI) to `sll`/`srl` or 0, with `negw`, `addiw`, `subw`. Needs
  `Loc.sll`/`srl`/`negw`/`addw`/`subw`, `at_eq` congruence under
  `extractLsb`/`sign_extend` (the shift amount is `extractLsb y 5 0`), an
  unsigned-comparison closer in `at_vals`, and `shiftl`/`shiftr` restated per
  machine branch (four cases per opcode, as `idivC_eq`).

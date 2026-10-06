# Lane F1-2: LE, EQK, LEN, GETTABUP, LT on the location-list route

Base: main `df460c9`. Route: CLAUDE.md's A1 row (round 4: at-lemmas,
`Kit/{At,AtArm}.lean`, `scripts/gen_lua_at.py`). Lines are non-blank,
non-comment lines (`--` lines and `/- … -/` blocks, docstrings included,
dropped); for an existing file, the lines this lane adds. CPU and peak
memory are one `lake env lean <file>` each (`/usr/bin/time -v`); heartbeats
are per declaration, elaborated synchronously (`Elab.async false`), in
`maxHeartbeats` units (default budget 200k).

## Result

| target | status | theorem |
|---|---|---|
| `SimArm .LE`, no premise | **proved** | `Lua.Vm.Sim.At.sim_LE` (`Kit/AtStr.lean`) |
| `SimArm .EQK`, no premise | **proved** | `Lua.Vm.Sim.At.sim_EQK` (`Kit/AtStr.lean`) |
| `SimArm .LEN` (string length) | **proved** | `Lua.Vm.Sim.At.sim_LEN` (`Kit/AtStr.lean`) |
| `SimArm .GETTABUP` (`_ENV.print`) | **open: obstruction** | see below |
| `LT` on the at-lemmas, `lt_str_take` under 150k | **done**: 14k (was 200.3k) | `Lua.Vm.Sim.At.sim_LT`; the kit's `Kit/LtStr.lean` retired |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists them).

## Setup (shared by every compare arm and every call node)

| piece | file | lines |
|---|---|---|
| `docondjump` on the route: `trap_ld`/`trap_sx` (`updatetrap`), `jmp_at` (`donextjump`, `jmpPc`), `kraw_eq` through the hook; `ScrFrame`/`WinFrame` and `at_scr`/`at_win` | `Kit/AtCond.lean` | 82 |
| the hooks `at_eq_ext` (`at_eq`, tried first) and `at_pc_ext` (`at_close`); `at_pins` one goal per pin (a projection `⟨r, v⟩.1` let the elaborator unify the pins' values at default transparency: `maxRecDepth` on the jump pin), `at_seg` pins and memory as goals of their own; `Loc.fn` (a value over the context a log may hold) | `Kit/At.lean`, `Kit/AtArm.lean` | 27 |
| the rules (`at_eq_cond`, shape-directed: a failed `exact` unified through `sign_extend` and cost 137k on one pin) | `Kit/AtCond.lean` | 27 |
| generator: `lw`, `lui`, `sext.w`, `andi`, the `k` bit, the jump target, facts substituted into both-symbolic compares, `CALLS`/`OBSERVED` (a call node fused with its observing segment), X-dependent locations (`XLOCS`), per-arm imports | `scripts/gen_lua_at.py` | 141 py |
| generator: `EXTRA_ARMS` (an arm outside the census F1 list emitted in modules of its own, so the address-chunked F1 modules do not move), `luaV_objlen` helper | `scripts/gen_lua_arms.py` | 40 py |
| `luaV_objlen` code pins | `scripts/gen_lua_code.py` | 2 py |
| `ArmBody.byTest`, `StrTest`, string-tag lemmas, the string guards' `at_hyp` rule, `at_str_path` | `Kit/AtStr.lean` | 64 |

## Per arm

| arm | hand lines (arm) | callee lines | generated lines | CPU (user) / peak | largest declaration (heartbeats) |
|---|---|---|---|---|---|
| LE | 7 (`le_str_take` 3, `le_str_skip` 3, `sim_LE` 1) | `LsObs` and its proofs: `Lstrcmp` +79, `Lex` +42 (`lexLt` order), `LstrcmpPro` +3, `Word`/`Strcmp` +4; the call node `lstr_sum` + `at_lstr` + `obs_le` 52 (shared with LT) | `At/Le.lean` 228 | arm 8.0 s / 2.17 GB (`AtStr`, all four arms); at-lemmas 62.5 s / 2.96 GB | arm `le_str_take` 14k; generated `fin` 92k, the jump segment 86k, `call_8001e29c` 74k |
| LT | 7 (`lt_str_take` 3, `lt_str_skip` 3, `sim_LT` 1) | as LE (`obs_lt`) | `At/Lt.lean` 228 | at-lemmas 61.6 s / 2.97 GB | arm `lt_str_take` **14k** (kit: 200.3k); generated `fin` 92k |
| EQK | 41 (`at_eqk_path` 18, `EqkTest`+cases 10, the `bne_ite_prop` rule 4, take/skip/sim 5) | exact return memory: `Lngstr` +25 (`RetSave`, `writeMap8_idem`), `EqLong` +16 (`eqo_long_ex`); the call node `lngeq_sum` + `at_eqk` 39 | `At/Eqk.lean` 118 | at-lemmas 11.9 s / 2.23 GB | arm `eqk_long_take` 12k; generated jump segment 29k |
| LEN | 24 (`StrB` 2, `len_str` 12, `len_stuck` 8, `sim_LEN` 2) | `Kit/Objlen.lean` 127 (`objlen_sum`, short and long strings, exact memory `olMem`); the call node `len_sum` + `at_objlen` 39 | `At/Len.lean` 65; segments `Segs/XLEN` 390, `Segs/HluaV_objlen` 976, sites 1,620, code pins 1,363 | at-lemmas 16.0 s / 2.42 GB; `Objlen` 15.5 s / 2.10 GB; segments ≤ 7.8 s / 1.97 GB | `objlen_long` 109k; generated `fin` 105k |

The kit's held-out LT took 111 hand lines (round 4, S-SCAN); on the route
LT is 7 lines over the shared setup. FORPREP's `fin_1`, the costliest
generated declaration before this lane (197.8k), measures 190k after the
library changes.

## GETTABUP: the obstruction

`OP_GETTABUP` at `0x8001cf84` reads `cl` at `8(sp)`, `cl->upvals[B]`,
`upval->v`, the `TValue`'s tag (`69`, a table), then `luaH_getshortstr(t,
key)` (`0x8001808c`): the main position `node + 24·(key->hash &
(2^lsizenode - 1))`, then `gnext` offsets until a node with key tag `68`
and key pointer `key`, or `absentkey`. Three facts are missing:

1. **The walk.** `VmEntryData.env_print_ptr` gives `TableHasShortKeyPtr m
   env x (.builtin .print)`: *some* node `i < 2^lsizenode` holds the key
   pointer `x`. It does not say that the chain from `x`'s main position
   reaches node `i` past nodes with other keys, which is what the machine
   needs; a memory where `print`'s node is off its main position's chain
   satisfies the field and makes `luaH_getshortstr` return `absentkey`
   (then `luaV_finishget`, not F1). The boot check (`printPtrCheck`,
   `Lua/Vm/Boot/Check.lean`) and `VmEntryData` need a walk field (the
   string table's `StrChain`, `Lua/Vm/Runtime.lean`, is the model), and the
   two boot witnesses re-checked.
2. **The closure in the relation.** `RelPtrs`/`Core` hold `k` at `0(sp)`
   (`Core.kptr`) but no `cl` at `8(sp)`, and `Complement` holds no
   `cl->upvals[0]`, `UpVal.v`, `_ENV`'s `TValue` or the table header and
   nodes (`VmEntryData` has them: `cl_upval0`, `uv_v`, `env_tag`,
   `env_val`). `vmRel_entry` would establish them and every close keep the
   `8(sp)` word.
3. **The callee.** A `luaH_getshortstr` summary over the chain
   (`seg_loop`), and generator locations for pointer-chased loads
   (`Loc.fn`).

None of these is an arm-local proof; (1) and (2) widen the A0 entry facts
and the relation shared by every arm.

## Builds and iterations

About 14 `lake build` runs of single modules and the `Lua.Vm.Sim.Kit`
index, and about 70 `lake env lean` runs with errors (the jump pin's
`maxRecDepth` and its 199k first cost took about 20 of them).

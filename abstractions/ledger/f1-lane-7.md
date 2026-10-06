# Lane F1-7: GETTABUP (`_ENV.print`) on the location-list route

Base: main `75aa247`. Route: CLAUDE.md's A1 row (round 4: at-lemmas,
`Kit/{At,AtArm}.lean`, `scripts/gen_lua_at.py`; loops by `seg_loop`). Lines
are non-blank, non-comment lines (`--` lines and `/- … -/` blocks, docstrings
included, dropped); for an existing file, the lines this lane adds. CPU and
peak memory are one `lake env lean <file>` each (`/usr/bin/time -v`);
heartbeats are per declaration, elaborated synchronously (`Elab.async
false`), in `maxHeartbeats` units (default budget 200k).

## Result

| target | status | theorem |
|---|---|---|
| `SimArm .GETTABUP` (`_ENV.print`), every kernel path | **proved** | `Lua.Vm.Sim.At.sim_GETTABUP` (`Kit/AtGettabup.lean`); `OpenArms` 7 → 6 fields, `armTable`'s case |
| (1) the hash-chain walk at the entry | **proved, checked** | `VmEntryData.env_get` (`EnvGetAt`, `shrWalk`), `envGetCheck_sound`; both boot witnesses re-checked (`entryOk`), the generator checks it natively (`check_env_get`) |
| (2) the closure and `_ENV` in the relation | **proved** | `Core.clptr`, `Complement.env` (`EnvMem … (HeapRead p w)`); `vmRel_entry`, `Kit.varargSim` and every arm re-established |
| (3) `luaH_getshortstr` | **proved** | `Kit.getshortstr_sum` (the loop `Kit.gs_loop` by `seg_loop`), the call node `At.gss_at` |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists them). The kernel's excluded paths (`B ≠ 0`, `K[C]`
not `"print"`) have no `Step` (`hk` refuted); the machine's other paths
(`_ENV` not a table, an empty slot: `luaV_finishget`) are refuted by
`EnvMem.tag`/`EnvMem.ptag` as guards of the at-lemmas, and `absentkey`
(`0x800180ec`) by the walk's success (`EnvMem.found`).

## Setup (shared)

| piece | file | lines |
|---|---|---|
| `nodeNext`, `shrWalk` (over a reader: view, `rdLE`, total), `shrWalk_mem`/`mono`/`congr`, `EnvSlot`, `HeapApart`, `EnvGetAt`, `VmEntryData.env_get` | `Lua/Vm/Repr.lean` | 104 |
| `envSlotOf`, `envGetCheck` + soundness, `entryCheck` (`printPtrCheck`/`envGetCheck` over `v.minus VarargDirty`) | `Lua/Vm/Boot/Check.lean` | 46 |
| the native walk and places | `scripts/gen_lua_boot_witness.py` | 40 py |
| `totR`, `Env.*` (the pointers as total reads), `EnvMem`, `mono`, `agree`/`EnvAgree`, `congr`, `EnvGetAt.envMem` (and `rdLE_spec` moved here from `Entry.lean`) | `Lua/Vm/Sim/Env.lean` | 206 |
| `HeapRead`, `Complement.env`, `Core.clptr`, `clptr_of`/`clptr_of'` | `Lua/Vm/Sim/Rel.lean` | 21 |
| `heapRead_of_apart`, `envMem_of_entry`, `relParts`' env input, `EntryHead`/`entry_head` (the prologue's first segment split out of `entry_at`) | `Lua/Vm/Sim/Entry.lean` | 118 (most moved) |
| the close lemmas keep `8(sp)`: `CFrame` from `16(sp)`, `bleachF`, `bleach`, `update`, `vclose` | `Multi`, `Kit/Close`, `Close`, `Kit/Varargprep`, `Vararg` | 33 |
| atoms `cl`/`uv`/`tv`/`tab`/`pn`, `Loc.cell1`, hook `at_side_ext`; hook `at_new_ext` | `Kit/At.lean`, `Kit/AtArm.lean` | 18 |
| `HeapRead.ld*`, `env_*_at`, `env_*_m`, `kval_str`, `Core.envMem`, `gss_at`, `at_env`, `at_logwin`, the `at_eq_ext`/`at_side_ext` rules | `Kit/AtEnv.lean` | 132 |
| generator: `ENV_ARMS`/`ENV_LOADS` (pointer loads to atoms, `B = 0`), the `luaH_getshortstr` call node | `scripts/gen_lua_at.py` | 34 py |
| generator: `luaH_getshortstr` helper (`absentkey` a stop), `OP_GETTABUP` in `SIM_OPS` | `scripts/gen_lua_arms.py` | 5 py |

## Per arm

| arm | hand lines (arm) | callee lines | generated lines | CPU (user) / peak | largest declaration (heartbeats) |
|---|---|---|---|---|---|
| GETTABUP | 35 in `Kit/AtGettabup.lean`: `sim_GETTABUP` 14 (gate count), the arm's `at_hyp`/`at_new_ext` rules 9 | `getshortstr_sum` + `gs_loop` + the mask, `gnext` and guard lemmas: `Kit/Getshortstr.lean` 217 | `At/Gettabup.lean` 171 (8 lemmas); segments `Segs/HluaH_getshortstr` 810, sites 889; `G20`/`G51` +501 (GETTABUP's segments with the fetch-head registers) | arm 1.3 s / 2.1 GB; at-lemmas 19.7 s / 2.3 GB; summary 6.6 s / 2.0 GB | arm 6.3k; `gs_loop` 74.8k, `getshortstr_sum` 13.9k; generated `fin` 69.2k, `at_8001cf84_8001cfd0_n` 60.3k, `call_8001e81c` 29.2k |

The first version of `sim_GETTABUP` (21 lines, the `_ENV` facts derived in
the arm) made `abstractions/gate.py` fail on `a1-kit-arm` (last-quarter
mean 3.1 > the floor 3); factoring them into the library (`Core.envMem`,
`kval_str`, the `env_*_m` lemmas used by the arm's rules) brought it to 14
lines and the gate back to ok (last-quarter mean 2.7).

## Budgets

| declaration | before | after |
|---|---|---|
| `entry_at` (`vmRel_entry`) | 200.4k measured with the lane's relation change (≈184k reported at main) | **29.5k**: the first segment split out (`entry_head`, 17.8k), the pin bounds by `List.length` instead of `simp` (each `pinsHold_get … (by simp)` on the second segment's pin list cost ≈15k), the dead `kArr` facts dropped |
| `FORPREP.fin_1` (narrowed `CFrame`) | 190k | 190.1k |
| `varargSim` | — | 79.0k |
| `entry_fresh` | — | 6.6k |

## Builds and iterations

About 20 `lake build` runs (single modules; three full `lake build Lua`,
one `lake build Lua Vsa VsaIris`) and about 25 `lake env lean` runs.

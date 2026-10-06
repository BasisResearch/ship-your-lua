# F1 lane 5: `StuckSim` — the stuck states, the escapes, the error paths

Base `e3ff9b9`. Lines are non-blank, non-comment lines (`/- … -/` blocks and
`--` lines dropped). CPU and peak memory are one `lake env lean <file>` of the
module alone (`/usr/bin/time`, user s / peak RSS). Heartbeats are per
declaration, measured by lowering `maxHeartbeats` per theorem until it fails
(`set_option maxHeartbeats K in`, in a scratch copy, never raised): "≤ K" means
it elaborates in K.

## Result

**`StuckSim` is false**, and so is `vm_refinement_Statement luaLayout`. The
kernel is stuck wherever F1 has no value for the result, and at three families
of such states Lua 5.4.7 (string coercion on: `LUA_NOCVTS2N` unset) continues:

| program (`c/tests/stuck/`) | `BcSem` stuck at | Lua 5.4.7 | ELF on the Sail model |
|---|---|---|---|
| `s_strflt.lua` `local x = "1.5" + 1; print(x)` | `MMBINI` (`δ (.tm .add)` on `"1.5"`, `1`) | `lstrlib.c` `arith` → `lua_arith`: `2.5` | prints `2.5`, exit 0 (192,534 steps) |
| `s_forstr.lua` `for i = 1, "2" do print(i) end` | `FORPREP` (limit `"2"`) | `forlimit` → `luaV_tointeger` coerces the string | prints `1`, `2`, exit 0 (186,147 steps) |
| `s_unmflt.lua` `local s = "1.5"; print(-s)` | `UNM` (`"1.5"`) | `arith_unm`: `-1.5` | prints `-1.5`, exit 0 (191,970 steps) |

Machine-checked half (`Lua/Programs/Escape.lean`): each program is
`Supported` and has no `BcSem` output (`esc*_supported`, `esc*_noBcSem` by
`stuckRun` + `decide +kernel`), `escStrflt_escapes` exhibits the reachable
`StuckAt` with a `Fault.Escape`, and `esc*_obstruction` derives from
`vm_refinement_Statement luaLayout` that the ELF loaded with the program never
halts with code 0. Empirical half: `c/tests/difftest.sh c/tests/stuck/*.lua`
(host `lua` and the ELF on the Sail model agree; the three exit 0). The seven
`e_*.lua` probes there (one per error kind: `n//0`, `n%0`, arithmetic on nil,
`'for' step is zero`, mixed order, a call of nil, `#` of a boolean) exit 2 on
the ELF (1 on the host `lua`).

## What is proved

| theorem | file | statement |
|---|---|---|
| `stuck_cases` | `Lua/StuckCases.lean` | a reachable, non-final, stuck state of a `Supported` program is a `StuckAt p s w o K vs φ`: the kernel exists, the read ports are defined, the body fails at the fault `φ` (`Fault.Fails`), `o ∈ φ.ops` |
| `reach_regs`, `Kernel.Wf`, `opKernel_wf` | `Lua/StuckCases.lean` | the definite-initialisation mask's registers hold values at reachable states (from one well-formedness lemma per combinator) |
| `body_fault` | `Lua/StuckCases.lean` | a kernel body fails only at a `Fault`: `δ` (`n%0`/`n//0`, `MMBIN*`, `UNM`, `BNOT`, `LEN`, the order tests), `CONCAT`, `FORPREP`, `FORLOOP`, `CALL` |
| `stuckRun_sound`, `noBcSem_of_stuckRun` | `Lua/StuckCases.lean` | a computed run to a stuck state is a `RunsStuck`; no `BcSem` output |
| `esc{Strflt,Forstr,Unmflt}_{supported,noBcSem,obstruction}`, `escStrflt_escapes` | `Lua/Programs/Escape.lean` | the obstruction above |
| `foldSim_of_arms`, `foldRel_entry` | `Lua/Vm/Sim/Fold.lean` | the fold's clauses for one program (now shared by `vmSim_of_arms`) |
| `stuckSimNE_of_error`, `vmSimNE_of_arms`, `vm_refinement_ne_of_open` | `Lua/Vm/Sim/Stuck.lean` | `ErrorSim → StuckSimNE`; Layer A under `NoEscape` from `OpenArms`, `FinalSim`, `ErrorSim` |
| `At.{idiv,mod,idivk,modk,forprep}_err` | `Lua/Vm/Sim/Kit/AtErr.lean` | `ArmErr`: from the arm's entry the machine reaches `luaG_runerror`'s entry (`n//0`, `n%0`, `'for' step is zero`) |
| `runerrorSim`, `stuckOut_of_armErr`, `vm_refinement_ne_of_rest` | `Lua/Vm/Sim/StuckErr.lean` | `ThrowFrom symLuaGRunerror → ErrorSimAt .runerror`; Layer A under `NoEscape` from `OpenArms`, `FinalSim`, `ErrorSimRest` |

Axioms of each: `[propext, Classical.choice, Quot.sound]` (check.sh stage 6).

## What is open

* `ThrowFrom symLuaGRunerror`: `luaG_runerror` (`luaO_pushvfstring`,
  `luaG_addinfo`, string creation and the heap) → `luaG_errormsg` →
  `luaD_throw` → `longjmp` → `luaD_rawrunprotected` returns → `lua_pcallk`
  (`luaD_seterrorobj`, `luaD_shrinkstack`) → `main`'s `fprintf(stderr, …)`
  (newlib `vfprintf`) → `exit(2)` → `_exit`'s `tohost` store. About 3,900
  Sail steps on the probes (fetch head to exit). Shares string creation with
  `CONCAT` (lane F1-2) and the exit with `FinalSim` (lane F1-4).
* The other eight sites of `ErrorSimRest`: their arms reach the error through
  a helper that can also return (`luaT_trybinTM` for `opinterror`,
  `tointerror`, `strarith`; `luaV_objlen`, `luaT_callorderTM[i]`,
  `luaV_concat`, `luaV_tonumber_`, `luaD_precall`), so each needs that
  helper's summary on the failing arguments (keyed by entry pc, as
  `ThrowFrom`), and the arm paths for `MMBIN*`, `LEN`, `CONCAT`, `CALL`,
  `BNOT` are on arms that are not yet on the at-lemma route.
* `NoEscape` (the corrected Layer A's hypothesis). Removing it needs floats in
  `δ`, the numeral recogniser `l_str2d`, the coerced `for` limit, and
  `FORLOOP` on a non-integer internal register (or `Supported` rejecting writes
  to a loop's internal registers).

## Per part

| part | hand lines | generated lines | CPU | peak | largest declaration |
|---|---|---|---|---|---|
| the enumeration (`Lua/StuckCases.lean`) | 550 | — | 4.1 s | 0.8 GB | `opKernel_wf`, `body_fault`, `stuck_cases` ≤ 12.5k |
| the obstruction (`Lua/Programs/Escape.lean`) | 65 | 3 `Proto`s (54, `gen_proto.py`) | 1.5 s | 1.8 GB | `escStrflt_escapes` ≤ 12.5k |
| the stuck clause and Layer A without escapes (`Stuck.lean`, `Fold.lean` +28 −15) | 60 + 13 | — | 1.3 s | 2.2 GB | ≤ 12.5k |
| error paths (`Kit/AtErr.lean`) | 90 (5 cases: 2 lines each; the rest setup) | at-lemmas into `luaG_runerror`: `Idiv` +38, `Idivk` +38, `Modk` +39, `Forprep` +28, new `Mod` 622 | 6.5 s (`At/Mod.lean` 97 s, 3.2 GB) | 2.1 GB | each `*_err` ≤ 12.5k |
| `runerror` site (`StuckErr.lean`) | 168 | `LayoutErr.lean` 13 | 2.2 s | 2.2 GB | `runerrorSim` ≤ 12.5k |
| generators (`gen_lua_at.py` +22, `gen_lua_layout.py` +30), `At.lean` (`errEntryPcs`, `at_run` stop) +8 | 60 | — | — | — | — |

## Route

* The enumeration is read off the kernel table: one `Kernel.Wf` lemma and one
  failure lemma per `lvm.c` combinator (`setR`, `opArith`, `mmbin`,
  `docondjump`, `forprepK`, `forloopK`, `callK`, `concatK`), and `opKernel_wf`
  / `body_fault` dispatch the table by combinator. `Fault.Fails` is the
  kernel's own computation (`(forprepK 0 0).body vs = none`, `δ f …`), not a
  restatement.
* The error paths are on the at-lemma route with no new kind of lemma:
  `gen_lua_at.py` follows a path into an error exit (`ERRS`) as it follows one
  to the fetch head (`auipc`, the message address, is an opaque row value),
  `at_run` stops at the exit's entry, and `at_err` closes with the row's pc.
  There is no kernel run (`kit_setup_err`): the path's facts are the
  machine's tags and payloads, from the stuck state's read values through
  `Core.stack`/`Core.kconst` (`divR_q`, `divK_q`, `forprep_q`). The exit's own
  behaviour is one obligation keyed by its entry pc (`ThrowFrom f`).
* The error entries are generated (`Lua/Vm/LayoutErr.lean`, a third output of
  `gen_lua_layout.py`, so that nothing below `Layout.lean` rebuilds).

## Obstacles

* **`StuckSim` and `vm_refinement_Statement luaLayout` are false** (above).
  Kept as stated; the corrected route is `vm_refinement_ne_Statement` under
  `NoEscape`. Which of (floats in `δ`; a `Supported` that rejects string
  constants feeding arithmetic; `NoEscape` as a per-program premise) is wanted
  is a design decision for the coordinator.
* `ThrowFrom` needs the error formatting: `luaO_pushvfstring` creates strings
  (`luaS_newlstr`, the string table, `malloc`), the same infrastructure as
  `CONCAT`; and `main`'s `fprintf(stderr)` is newlib's `vfprintf`. Neither
  exists at Lua addresses yet.
* `FoldSim.stuckOut` needs only the exit code (`StuckOut`), not the output, so
  no stderr/console summary is needed beyond termination.

## Gate

`abstractions/gate.py`: ok (`a1-kit-arm` 47 cases, first quarter 1.9 lines,
last 2.0). The first version of `Kit/AtErr.lean` (4–7 lines per case, the
setup inline) failed the gate (last quarter 3.2); the cases were then factored
into per-shape hand-offs (`div_err`, `divk_err`, `fp_err`), as `Kit/AtOps.lean`
does. `scripts/check.sh`: see the lane report.

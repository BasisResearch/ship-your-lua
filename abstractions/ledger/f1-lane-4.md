# F1 lane 4: `FinalSim`

Base `e3ff9b9`. Lines are non-blank, non-comment lines (`/- … -/` blocks and
`--` lines dropped). CPU and peak memory are one `lake env lean <file>` of the
module alone (`/usr/bin/time`, user s / peak RSS). Heartbeats are per
declaration, measured by lowering the budget for the whole file
(`lake env lean -DmaxHeartbeats=K`, never raised): "(a, b]" means it fails at
`a` and elaborates at `b`.

## What is proved

| theorem | file | statement |
|---|---|---|
| `Ret.vmRel_final` | `Lua/Vm/Sim/Kit/RetFinal.lean` | `vmRel_final_Statement`: from `VmRel` at a `Final` state (any `RETURN`/`RETURN0`/`RETURN1`), `Halts c s.out 0` |
| `finalSim` | `Lua/Vm/Sim/Fold.lean` | `FinalSim` |
| `vm_refinement_of_open'` | `Lua/Vm/Sim/Fold.lean` | `OpenArms → StuckSim → vm_refinement_Statement luaLayout` |
| `Ret.ret_RETURN` (`ret_p1`–`ret_p4`), `ret_RETURN0`, `ret_RETURN1` | `Kit/RetArm.lean` | the arm, every path, to the return into `ccall` (`AtCcall`) |
| `Ret.fclose_sum` | `Kit/RetClose.lean` | `luaF_close` with nothing open, the call-node summary |
| `Ret.poscall_sum` | `Kit/RetPoscall.lean` | `luaD_poscall` (no hooks, `wanted = 0`), the call-node summary |
| `Ret.ret_fresh`, `Ret.ret_tail` | `Kit/RetTail.lean` | `CIST_FRESH` and the epilogue (the saved words); the poscall call site to `ccall` |
| `Ret.ret_chain` (`ret_chain1`, `ret_chain2`), `chainMem` | `Kit/RetChain.lean` | `ccall` → `luaD_rawrunprotected` → `luaD_pcall` → `lua_pcallk` → `main` → `_start` → `exit` |
| `Ret.exit_run`, `exit_halt`, `exitOk_of_quiet` | `Kit/Exit.lean` | `exit(0)` with no handlers halts with code 0; the `tohost` store |
| `SavedAt.congr`, `Core.saved_of`, `callers_congr`, `exitOk_entry` | `Rel.lean`, `Entry.lean` | the new relation fields are region facts |

Axioms of each: `[propext, Classical.choice, Quot.sound]` (check.sh stage 6).

## Per part

| part | hand lines | generated lines | CPU | peak | largest declaration |
|---|---|---|---|---|---|
| relation fields, diff additions (`Core.saved`, `Complement.{callers, callerL, exit}`, `ExitOk`; `Rel` +105, `Entry` +86, `Vararg` +18, the six closes +29) | 238 | — | — | — | `entry_at` ≤ 200k (unchanged budget) |
| boot contract, diff additions (`CStackAt.s0/saved`, `RuntimeReadyAt.callerL`, `StdioBoot.atexit`; `Runtime` +15, `Assemble` +9, `Check` +2, generator +22) | 48 | `RuntimeData` +16; witnesses regenerated | witnesses ≈ 5 min | 3.3 GB | `rtOk` (`decide +kernel`) |
| generators, diff additions (`gen_lua_arms.py` HELPERS/SIM_OPS +40, `gen_lua_code.py` +5, `gen_lua_layout.py` +3) | 48 | segments, sites, code pins: +21,285 / −710 (14 helper modules, the `RETURN*` segments with the fetch-head pins) | `Lua.Vm.Arms` 48 s wall | — | generated |
| `RetMem` (`RAgree`, `RetDirty`, `kit_split`, `kit_hyp`, `HeadReads`) | 218 | — | 2.1 s | 1.9 GB | ≤ 25k |
| `luaF_close` (`RetClose`) | 135 | — | 11.0 s | 2.0 GB | `fc1` (100k, 150k] |
| `luaD_poscall` (`RetPoscall`) | 64 | — | 6.9 s | 2.0 GB | `poscall_sum` (100k, 150k] |
| tail (`RetTail`) | 172 | — | 7.8 s | 2.0 GB | `ret_fresh` (50k, 100k] |
| arms (`RetArm`) | 221 | — | 23.4 s | 2.1 GB | `ret_p3` (100k, 150k]; `ret_p2` (50k, 100k]; the rest ≤ 50k |
| C chain (`RetChain`) | 149 | — | 10.1 s | 2.1 GB | `ret_chain1`, `ret_chain2` ≤ 100k (one declaration was (150k, 200k]: split) |
| `exit` (`Exit`) | 91 | — | 4.3 s | 1.9 GB | ≤ 25k |
| the clause (`RetFinal`) | 51 | — | 0.9 s | 1.9 GB | ≤ 25k |

## Route

* **The saved words are a region fact.** `Core.saved : SavedAt c.σ.mem w`:
  only the prologue writes `72…175(sp)` (objdump of `luaV_execute`: every
  other store to its frame is at `0(sp)` … `56(sp)`). Every close keeps it by
  `Core.saved_of` from its own frame hypothesis. The one change to an existing
  abstraction is `CFrame` narrowed from `[sp+8, sp+176)` to `[sp+8, sp+72)`;
  every at-lemma's frame proof went through unchanged.
* **The values are the boot's.** The callers' `s1 … s11` at the entry are the
  same in both traced programs (`RuntimeData.calleeSavedEntry`, generated), and
  `s0 = a0 = L`; the caller frames' copies of `L` (`callerLSlots`) are checked
  too, so the chain's stores through a reloaded `L` land in the `lua_State`.
* **Memory along the return is abstract.** Agreement with the head memory off
  the words the run writes (`RAgree`, `RetDirty`): the run's state is
  `∃ M, RAgree w m0 M ∧ SegSt …` between phases, so no declaration carries a
  store chain longer than its own phase.
* **Every path is run.** A branch the relation does not decide (`B = 0`, `k`,
  `L->top < ci->top`, `C`) is split on its generated guard (`kit_split`), and
  `kit_run` takes each polarity by the case hypothesis (`kit_hyp`, a
  syntactic match: `assumption` hit the recursion limit on the BitVec terms).
  No instruction field is decoded by hand.
* **The end is `ExitOk`.** `exit(0)` after a `print` runs newlib's
  `stdio_exit_handler` = `_fwalk_sglue(_impure_data, _fclose_r, __sglue)`:
  `__sflush_r`, htif `_close`, `_free_r` of the stdout buffer. `VmRel` says
  nothing about stdio after a print, and `CALL` is open. So the relation
  carries `Complement.exit : ExitOk p w` ("`exit(0)` from this complement
  halts with code 0, printing nothing"), proved where no handler is installed
  (`exitOk_entry`, at the entry and after `VARARGPREP`). The arm that installs
  the handler (`CALL print`) must re-establish it; `FinalSim` itself is proved.

## Obstacles

* **Not decidable by the generated route as it stood.** The at-lemma generator
  (`gen_lua_at.py`) ends paths at the fetch head; the return leaves
  `luaV_execute`. The kit route (`kit_run` over generated segments, one
  declaration per phase, as lane F1-3's `VARARGPREP`) was used instead, with
  two new tactics (`kit_split`, `kit_hyp`) and the `RAgree` memory.
* **`ret_chain` in one declaration needed (150k, 200k]** (five returns and four
  stores): split at the return into `luaD_pcall` (`AtPcall`).
* **What `OpenArms.CALL` now owes.** Its post-state complement must satisfy
  `ExitOk`: the `exit` run through `stdio_exit_handler` over the stdout state
  the `print` leaves (the A0.2 stdio tables, `_free_r` on the allocator step
  tables). This is the post-print half of the old `FinalSim` obstruction, now
  attached to the arm that changes stdio.

## Gate

`scripts/check.sh` (all stages, including the full `lake build Lua Vsa VsaIris`
and stage-6 axioms): OK (the full build 8 min 12 s wall from a warm cache of the base; check.sh 1 min 6 s after it). `abstractions/gate.py`: ok
(`a1-kit-arm` 42 cases, first 1.9, last 1.8).

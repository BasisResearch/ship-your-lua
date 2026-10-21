# Lane F1-26: error unwind cut at `fprintf`; `exit(2)` proved

Route: the existing callee-context generator (`gen_lua_at.py`), generated
segments (`gen_lua_arms.py`), and the shared error tail (`ErrTail.lean`).
The lane supplies `exit_run_err`, `errExit_stuck`, and
`unwind_of : UnwindRest → Unwind_Statement`; it does not discharge
`ErrorSimRest`.

## Result

| Target | Status | Location |
|---|---|---|
| Close written, unbuffered `stderr` | Proved: `fclose_errW` | `Kit/ExitErr.lean`, generated `AtF/FcloseErrW.lean` |
| Close untouched/empty-write `stdout` | Proved: `fclose_out9`, `fclose_outF` | `Kit/ExitErr.lean`, generated `AtF/FcloseOut{9,F}.lean` |
| `stdio_exit_handler` after an error | Proved for all three stdout phases: `exit_handler_err9`, `exit_handler_errF`, `exit_handler_errU` | One `err_walk` over generated `AtF/ExitHandlerE{9,F,U}.lean` |
| `exit(2)` | Proved: `exit_run_err`, ending with `exit_halt2` | `Kit/ExitErr.lean` |
| `main` after error `fprintf` | Proved: `errExit_stuck` | `Kit/Unwind.lean`, generated `Arms/Segs/Hmain.lean` |
| Full unwind | Conditional: `unwind_of` | `Kit/Unwind.lean` |

The seams are named contracts `FprintfPre`/`ErrPrintAt` and
`ErrExitIn`/`ErrExitAt`. `ErrorSimRest.unwind` now carries `UnwindRest`:
`PcallErr_Statement` and `FprintfErr_Statement`.

## Remaining obligations

* `PcallErr_Statement`: unwind through `luaD_pcall`, close protected state,
  move the error object, shrink the Lua stack and CallInfo chain, return
  through `lua_pcallk`, and obtain the string for `fprintf`.
* `FprintfErr_Statement`: `_vfprintf_r` for `"lua: %s\n"`, stdio setup,
  the unbuffered `__sfvwrite_r` path and `_write(2)`, leaving `ErrExitIn`.
* The other `ErrorSimRest` fields remain the formatting heads, the per-site
  heads, and the floating zero-step FORPREP path.

The pcall proof still needs an allocator shrink summary, a free summary
retaining the resulting heap and other live payloads, and invariant facts
for the base CallInfo, successor CallInfo and stderr. These are proof
obligations, not decisions requiring user permission. `FRet` already
provides the allocator heap/frame needed for the stronger free summary.

## Review and validation

The takeover audit found and removed an import cycle introduced by the
lane index: `Kit → Unwind → ErrTail → Fold → Kit`. `StuckErr` imports
`Unwind` directly, after `Fold` is available. The two new entry witnesses
are named records (`ErrPrintData`, `ErrExitData`), with `Nonempty` as their
propositional boundary, avoiding anonymous witness/projection towers. They
carry data and proofs, so the records live in `Type`; their predicates are
in `Prop`. The refactored consumers build and retain the same axiom set.

* `scripts/abs_inventory.sh` was run before proof work.
* `python3 scripts/check_discipline.py`: passed (17 rules).
* `python3 abstractions/gate.py`: passed.
* Generated fclose and exit-handler variants match `gen_lua_at.py --check`.
* `lake build Lua.Vm.Sim.Kit.Unwind Lua.Vm.Sim.StuckErr`: passed after
  the import fix (2521 dependency jobs, incremental).
* All eleven stage-6 additions, from `fclose_errW` through `unwind_of`,
  report only `[propext, Classical.choice, Quot.sound]`.
* The complete integration gate is run on main before landing.

No heartbeat or recursion limit was raised. Lean validation uses a systemd
scope with `MemoryMax=12G` and one CPU core; one build at a time in this
worktree. The initial virtual-address cap was replaced with this resident
memory cap after Lean failed to create a thread. No results from that
failed build count as validation.

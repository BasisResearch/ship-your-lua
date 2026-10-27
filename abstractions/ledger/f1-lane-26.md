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

The pcall proof still needs an allocator shrink summary, invariant facts
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

## Heap-retaining free summary (sol-1)

The existing `FQ` kept the return PC, SP and s0/s1/s2/s3. It discarded
`FRet.heap` (including the resulting top/break/chunks/bins, the surviving
ledger and `top ≤ top0`), `FRet.pres` and `FRet.frame`; `MRegs.ra` was not
part of the segment return pins. `FRet.heap_named` now consumes the heap's
anonymous witnesses once. `FQHeap` carries the named heap witness, image,
presence and frame through `free_body` and `LocalRun.reach`.

`FreeRHeap_Statement` returns a named `FreeRData` witness and `FreeRPost`:

* `HeapAt` of the actual return memory's zero fill, with top no greater
  than at entry;
* every entry chunk in use whose payload base differs from `p` retains
  that base and at least its entry capacity in a resulting chunk in use;
* every byte of those surviving payloads is unchanged, at presence level;
* the existing global/arena/stack frame, now also framing surviving payloads.

`freeSurvivors_ledger` identifies the filtered Lua chunks with the existing
ported ledger. `live_of_ledger` reads its base/capacity guarantee from the
resulting `PHeapAt`. `heap_agree` lands the heap image in the actual return
memory and is shared with malloc. The freed block is excluded from the
ledger; neither its liveness nor its payload bytes are promised.
`FreeRPost.inUse` transports surviving payload membership, and
`freeR_of_heap` derives the unchanged `FreeR_Statement`.

No allocator instruction proof, generator or Unwind entry/post field changed.
`FreeRunAll` adds only the named return-heap witness and its extractor. The pending Unwind file was read in lane-f1-26;
it depends on that lane's `ExitErr` and generated variants, and is not copied
into this earlier worktree. Its named witnesses already satisfy R6/R7.

### Exact remaining premises

* `PcallErr_Statement`: from `Supported`, `Reach`, `Core`, `ErrMsgMem`,
  `sp ≤ X.w.sp`, `ThrowPost`, and the status-2 `SegSt` at `0x8000b4c0`,
  prove finite steps to `ErrPrintAt`. This still requires the close-protected
  run (`luaD_rawrunprotected(closepaux)`/`luaF_close`), `luaD_seterrorobj`,
  `luaD_shrinkstack`/`luaD_reallocstack` with a non-NULL `_realloc_r` shrink
  summary that retains the resulting heap and other allocations, the
  `luaE_shrinkCI` loop (using `freeRHeap_proved`), `lua_pcallk` and
  `lua_tolstring(L, -1, NULL)`. Base CallInfo, successor CallInfo and stderr
  facts must be established/transported by the invariant; they are not
  supplied by a free summary.
* `FprintfErr_Statement`: from `ErrPrintAt` (its `FprintfPre` carries the
  heap, message `StrZ`, main's saved RA, no atexit, `StdoutIn` with empty
  pending bytes, initialized stderr when appropriate, `_REENT->_stderr`,
  locale and rodata), prove finite steps through `fprintf(stderr,
  "lua: %s\n", msg)`/`_vfprintf_r` to `ErrExitAt` with `ErrExitIn`.
  The missing summary covers optional `__sinit`, stderr setup and the
  unbuffered `__sprint_r`/`__sfvwrite_r`/`__swrite`/`_write(2)` path.
  The pending lane's trace uses `__SRW`, so it does not use `__sbprintf`.
* `unwind_of` still requires both fields of `UnwindRest`. The formatting
  heads, other site heads and FORPREP floating zero-step premise remain
  as before. No `ErrorSimRest` or pcall premise is discharged by this change.

### Validation of this extension

Validated on 2026-10-21 using `bash /tmp/sol1-validate-free.sh` (exit 0).
It invokes the MAIN `scripts/lean-capped.sh` for each `lake env lean`,
with explicit output paths under this worktree's private `.lake/build`.
All processes were awaited; no `lake build` or dependency-cache writes
were used. The inherited systemd scope has a 12 GB cap, each invocation
checks available memory, and only one Lean process runs at a time.
The manager had released the old orphan lock and restored missing private
cache artifacts before this validation; no missing modules were reported.

* `Kit/Malloc`, `Kit/AllocHeap`, `VsaIris/Vsa/FreeRunAll` and
  `Kit/AllocProof` all compile. The log is `/tmp/sol1-free-validation.log`.
* The ten-name audit passes: `AllocProof.freeRHeap_proved`,
  `AllocProof.freeR_proved`, `AllocProof.mallocR_proved`,
  `AllocProof.fq_of_ret`, `AllocProof.heap_agree`,
  `AllocHeap.freeSurvivors_ledger`, `AllocHeap.live_of_ledger`,
  `FreeRPost.inUse`, `freeR_of_heap` and `VsaIris.VsaHeap.FRet.heap_named`.
  Every report is a subset of `[propext, Classical.choice, Quot.sound]`.
  These names are registered in check.sh stage 6.
* `python3 scripts/check_discipline.py`: passed (17 rules, 1603 files).
* `python3 abstractions/gate.py`: passed.
* The forbidden-token checker from check.sh stage 3: passed.
* `python3 scripts/syi/gen_alloc_steps.py --check`: passed.
* `bash -n scripts/check.sh` and `git diff --check`: passed.

The ledger induction now normalizes the induction hypothesis to the same
filter/map form as the goal. The return records use explicit field layout,
and the surviving-ledger cast exposes `H` before transport. Payload bounds
use direct inequalities and the existing `homega` approach of generalizing
`heapEnd`, avoiding large-literal normalization in the full call context.
No Lean budget was raised. Full integration through check.sh remains the
manager's landing gate; the unwind premises above remain open.

## `_write(2)` console boundary (sol-1)

`Kit.write_stderr_sum` and `Os.stderr_write_refines` supply the real fd=2
machine/OS boundary through the shared `write_console_sum`, generated
`Hwrite` segments, `write_loop`, `write_putc`, `wrMem` and `wrRet`.
The contract requires an initialized fd table (`fs_ready ≠ 0`,
`fds[2].kind = FD_STDERR`), the explicit stack/buffer bounds, return
alignment and real `SegSt` entry. The OS bridge additionally requires
present buffer bytes, a live abstract process with fd 2 bound to stderr,
entry `ConsoleAt`, and the signed ABI return-address bound.
See `os-stdout.md` for exact premises and validation.

The resumed descriptor-address side-condition fix is validated: capped
`lake build Lua.Vm.Sim.Kit.Write Lua.Os.ConsoleWrite` and the existing
consumer `lake build Lua.Vm.Sim.Kit.Swrite` pass. The 15-name audit includes
both machine instances and both OS bridges; every axiom set is standard-only.
Exact wrapper commands and logs are recorded in `os-stdout.md`.

This closes neither `FprintfErr_Statement` nor global `HtifPrint_Statement`.
The remaining fprintf chain is optional `__sinit`, stderr setup,
`fprintf`/`_vfprintf_r`, unbuffered `__sprint_r`/`__sfvwrite_r`, and
`__swrite`/`_write_r`, including their memory and caller invariants.
Before the first print, `_write` must also run its lazy fs initialization;
unbuffered stderr setup does not call `_fstat`.
The pcall and other error-head obligations above remain unchanged.

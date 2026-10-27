# OS console write boundaries

Route: `Lua.Os.console_write_refines` in `Lua/Os/ConsoleWrite.lean`
consumes `Lua.Vm.Sim.Kit.write_console_sum`. The existing generated `_write`
segments accept either fd in their register parameters; the bounds/kind
proofs specialize their guards to 1/kind 2 or 2/kind 3. No generator change
or new instruction proof is needed. `write_loop` needs only `WrFrame`;
`seg_loop` and `write_putc`/`segSt_putc` remain the single byte loop and seam.
`write_sum` keeps its existing API and semantics. `write_stderr_sum` is the
fd=2 instance of the common summary, for arbitrary length including zero.

`ConsoleWriteResult` (instances `StdoutWriteResult` and `StderrWriteResult`) records actual `Steps`, `HtifCallAt`, `ReturnsTo`,
`HtifRetAt`, the complete-write `TCB.Os.OsStep`, `ConsoleAt`, and the exact
`wrRet` frame. `ConsoleAt` is the console field of `HtifRepr` by definition.
The abstract successor changes only the streams through
`Streams.doWrite stream bs`; the byte list is arbitrary, including empty
and non-ASCII byte lists. HTIF's console observation is one character per
byte, as in `HtifRepr`.

## Exact premises

- Stdout: the unchanged `WrCtx m sp buf bs.length r`.
- Stderr: `WrConsoleCtx m 2 sp buf bs.length r`, namely return alignment
  `r.toNat % 4 = 0`; `symFds + symFdsSize + 96 ≤ sp ≤ 2^32`;
  `sp % 8 = 0`; `tohostAddr + 16 ≤ buf`; `buf + bs.length + 96 ≤ sp`;
  `bytesT4 m symFsReady ≠ 0`; and `bytesT4 m (symFds + 48) = 3`.
  These keep the buffer below the 96-byte stack frame and the descriptor
  table below the saved RA store. The initialized table is a premise;
  lazy `fs_init` is not proved by this boundary.
- `r.toNat < 2^63`, required by the existing `ReturnsTo` ABI decoder.
- `BytesAt m buf bs`, because the ABI decoder demands present bytes while
  the machine summary uses total reads.
- `lookupFd st 1 = some (.stream .stdout)` for stdout, or
  `lookupFd st 2 = some (.stream .stderr)` for stderr; `st.proc.exited = none`.
- The real `SegSt` entry at `_write`, with `wrPre` (stdout) or `wrConsolePre 2` (stderr) registers, `ArmPay m o`
  and its machine invariant, plus entry `ConsoleAt c st`.

No premise assumes the conclusion or a whole OS implementation.
`HtifPrint_Statement` and `HtifFs_Statement` remain open: boot-only `R`
vacuity, the remaining calls (including stdin/fstat), persistent
representation and frame preservation, and filesystem resource limits
remain separate obligations. `FprintfErr_Statement` remains open: this
result supplies its `_write(2)` boundary, while optional `__sinit`, stderr
setup, `fprintf`/`_vfprintf_r`, unbuffered `__sprint_r`/`__sfvwrite_r` and
`__swrite`/`_write_r` still need their runs and caller invariants. An error
before the first print also needs `_write`’s lazy initialization: unbuffered
`__smakebuf_r` returns without calling `_fstat`.

## Validation

Validated on 2026-10-27 in sol-1. Every Lean command uses the MAIN wrapper
`/data/home/kirancodes/Documents/code/ship-your-lua/scripts/lean-capped.sh`,
with the inherited 12 GB scope, a private `.lake/build`, and an available
memory check above 25 GB. Builds run sequentially and are awaited completely.

* `<wrapper> lake build Lua.Vm.Sim.Kit.Write Lua.Os.ConsoleWrite`: passed
  (484 jobs); log `/tmp/sol-1-write-build.log`.
* `<wrapper> lake build Lua.Vm.Sim.Kit.Swrite`: passed (488 jobs), checking
  the existing `write_sum` consumer; log `/tmp/sol-1-swrite-build.log`.
* `<wrapper> lake env lean /tmp/sol-1-write-axioms.lean`: passed; all 15
  reports use only `propext`, `Classical.choice`, `Quot.sound` (the fd and
  address facts use only `propext`). Log `/tmp/sol-1-write-axioms.log`.

The resumed prefix fix supplies `wrKindAddr_eq` to the address side-condition
closer before generic arithmetic normalization can lose its shape. The
generated segment guards, machine semantics, and preconditions are unchanged.
Full integration through `scripts/check.sh` is the manager's landing gate.

Import registration remains `Lua.lean`. Stage 6 of `scripts/check.sh` now
also audits `WrCtx.console`, the descriptor guards/address fact,
`write_console_sum`, `write_stderr_sum`, `console_write_refines` and
`stderr_write_refines`.

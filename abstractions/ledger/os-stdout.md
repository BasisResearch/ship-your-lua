# OS stdout boundary

Route: `Lua.Os.stdout_write_refines` in `Lua/Os/ConsoleWrite.lean` consumes
`Lua.Vm.Sim.Kit.write_sum`. The existing generated `_write` segments,
`seg_loop` and `segSt_putc` supply the machine execution; this bridge adds
no instruction proofs or generated files.

`StdoutWriteResult` records actual `Steps`, `HtifCallAt`, `ReturnsTo`,
`HtifRetAt`, the complete-write `TCB.Os.OsStep`, `ConsoleAt`, and the exact
`wrRet` frame. `ConsoleAt` is the console field of `HtifRepr` by definition.
The abstract successor changes only the streams through
`Streams.doWrite .stdout bs`; the byte list is arbitrary, including empty
and non-ASCII byte lists. HTIF's console observation is one character per
byte, as in `HtifRepr`.

## Exact premises

- `WrCtx m sp buf bs.length r`: aligned return address and stack, stack and
  buffer bounds, initialised descriptor table (`fs_ready ≠ 0`), and the
  stdout descriptor's kind.
- `r.toNat < 2^63`, required by the existing `ReturnsTo` ABI decoder.
- `BytesAt m buf bs`, because the ABI decoder demands present bytes while
  the machine summary uses total reads.
- `lookupFd st 1 = some (.stream .stdout)` and `st.proc.exited = none`.
- The real `SegSt` entry at `_write`, with `wrPre` registers, `ArmPay m o`
  and its machine invariant, plus entry `ConsoleAt c st`.

No premise assumes the conclusion or a whole OS implementation.
`HtifPrint_Statement` and `HtifFs_Statement` remain open: boot-only `R`
vacuity, the remaining calls (including stderr/stdin/fstat), persistent
representation and frame preservation, and filesystem resource limits
remain separate obligations.

## Validation

All Lean commands run from the assigned worktree through the main repo's
`scripts/lean-capped.sh`, inheriting its 12 GB scope and CPU affinity;
`.lake/build` is private; shared dependency caches are reused.

- `lake build Lua.Os.ConsoleWrite Lua.Os.HtifTraces`: passed (485 jobs).
- `lake env lean /tmp/sol2-os-axioms.lean` (importing
  `Lua.Os.ConsoleWrite`): all three theorems report exactly
  `[propext, Classical.choice, Quot.sound]`.
- `python3 scripts/check_discipline.py`: passed (17 rules).
- `python3 abstractions/gate.py`: passed.
- `scripts/check.sh` stage 3's forbidden-token scan: passed.
- `bash -n scripts/check.sh` and `git diff --check`: passed.

The manager owns the full `scripts/check.sh` run and landing review.

Import registration: `Lua.lean`. Axiom registration: `scripts/check.sh`
stage 6 lists `osStep_write_full`, `bytesAt_of_BytesAt`, and
`stdout_write_refines`.

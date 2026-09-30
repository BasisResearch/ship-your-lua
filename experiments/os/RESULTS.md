# OS-spec traces of the Lua image's `htif.c`

The method and tools are ship-your-ocaml's (`tcb/validation/`, copied; its
`RESULTS.md` there is about ship-your-ocaml's `htif.c`). Call scripts are
run on a back end, each call's return is recorded, and `tcbcheck` checks
every trace against `TCB.Os.next` (sound by `TCB.Os.checkTrace_sound`).

The back end here is this repository's `c/src/htif.c`, unchanged,
compiled natively. `tcb/validation/driver.c`'s MEMFS branch includes
`../../c/src/htif.c` (with `-DHOST_MIRROR`), calls its functions, and
resets its file system between scripts. The MEMFS branch passes paths
unchanged, so `htif.c`'s root is the script's `/`.
`experiments/os/htif_shim.h` (a pre-include) supplies the only thing the
Lua ELF does not have: `opendir`/`readdir`/`closedir`, which report
`unsupported`, so the checker skips the rest of that trace.

Reproduce: `experiments/os/run.sh` (about 4 s; `--quick` is the gate subset,
`scripts/check.sh` stage 5b, which pins the verdicts below). Outputs go to
`experiments/os/out/` (not committed). Measured 2026-09-30, Linux
7.0.0-1012-aws, ext4, glibc 2.43.

## Linux control

The generated scripts (`tcb/validation/gen.py`, 6,490 scripts, 101,621
calls) on the Linux host: **6,398 accepted, 0 rejected, 92 special**. This
is the same result as ship-your-ocaml's RESULTS.md, before and after
DEVIATION 10 (`osReaddir`, `tcb/TCB/Os/Syscall.lean`).

## `htif.c`, generated scripts: 5,275 accepted, 0 rejected, 79 special, 1,136 unsupported

| verdict | traces | what |
|---|---|---|
| accepted | 5,275 | every call allowed by `next` (90,268 calls run) |
| special | 79 | a call the spec leaves unconstrained, where `htif.c` returns what Linux does: `open` with `O_RDONLY\|O_TRUNC` on a directory (`EISDIR`); `lseek` `SEEK_END` on a directory (`EINVAL`); `lseek` on the console (`ESPIPE`) |
| unsupported | 1,136 | the trace reaches `opendir` |
| rejected | 0 | |

The quick subset (329 scripts): 264 accepted, 0 rejected, 4 special, 61
unsupported.

## `htif.c`, console scripts: 25 accepted, 0 rejected, 1 special

`experiments/os/console.scripts` has one script per behaviour of fds 0-2,
of unknown descriptors and of the clock (the generated families barely
reach them). The scripts c06-c19 also have kernel-checked counterparts in
`Lua/Os/HtifTraces.lean`: facts about `next`, `accepts_*` for what
`htif.c` returns now, and `rejects_*` for what the console-only `htif.c`
returned before (H1-H5 below).

| script | call | `htif.c` |
|---|---|---|
| c01, c02, c03 | `write` to fd 1 or 2 | all bytes to the HTIF console |
| c04, c05 | `read` fd 0 | end of input (the spec's stdin is empty) |
| c06, c07 | `read` fd 1, `write` fd 0 | `EBADF` |
| c08, c09, c10, c24 | `fstat` fd 0-2 | `S_IFCHR`, `st_nlink = 1` |
| c11 (special) | `lseek 1 0 0` | `ESPIPE`; unconstrained on a stream |
| c12 | `lseek` with a bad `whence` | `EINVAL` |
| c13-c16 | `close` of fd 0-2, then use | success, then `EBADF` |
| c17-c21 | a descriptor it never issued | `EBADF` |
| c22, c23 | `open "/a"` without and with `O_CREAT` | `ENOENT`; `num 3` |
| c25 | `close 1`, then `open` | the new file gets fd 1 (smallest free) |
| c26 | `clock` twice | `num 0` both times (`TCB.Os.Clock.frozen`) |

## The deviations of the console-only `htif.c`, and their fixes

Before the in-image file system, the generated scripts gave 0 accepted,
874 rejected, 5,616 unsupported, and the console scripts 7/16/1. Each
deviation is fixed in the current `htif.c`:

| id | console-only `htif.c` | now |
|---|---|---|
| H1 | `fstat` on fd 0-2: `st_nlink = 0` | `st_nlink = 1` |
| H2 | `read` fd 1 is end of input, `write` fd 0 prints | `EBADF` |
| H3 | any descriptor it never issued acts as the console (ship-your-ocaml's M1) | one descriptor table; `EBADF` outside it |
| H4 | `close` does not close | it does; the number is reused |
| H5 | a bad `whence` gives `ESPIPE` | `EINVAL` |
| H6 | `open` with `O_CREAT` gives `ENOENT` | files and directories, the spec's path resolution (M2, M3), link count 0 after `unlink` (M4) |

The file system's design is shared with ship-your-ocaml, which adopted this
`htif.c` (branch `f5-htif` `39e79b2`). While running it there, they found
DEVIATION 10 in the spec's `osReaddir`, now in `tcb/` here too.

## What this means for the obligations

`Lua.Os.HtifFs_Statement` (`Lua/Os/Htif.lean`) covers every call of the
twelve functions, and the traces reject none of them. So it is plausibly
true, with two caveats recorded there.
* `htif.c`'s limits (64 files and directories, 32 descriptors, the heap)
  give `EMFILE`/`ENOSPC`, which the spec does not allow. A proof needs a
  resource bound in its scope.
* As stated, the relation `R` may hold at boot only, which makes the
  statement vacuous until the frame obligation of `OsState` in the
  semantics is added (PHASES.md, OS).

`Lua.Os.HtifPrint_Statement` is the console calls of a `print`-only
program: `write` to fds 1-2, `read` from fd 0, and `fstat` of fds 0-2. The
traces accept these (c01-c05, c08-c10, c24).

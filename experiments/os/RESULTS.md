# OS-spec traces of the Lua image's `htif.c`

The method and tools are ship-your-ocaml's (`tcb/validation/`, copied
verbatim; its `RESULTS.md` there is about ship-your-ocaml's `htif.c`). Call
scripts are run on a back end, each call's return is recorded, and
`tcbcheck` checks every trace against `TCB.Os.next` (sound by
`TCB.Os.checkTrace_sound`).

The back end here is this repository's `c/src/htif.c`, unchanged, compiled
natively: `tcb/validation/driver.c`'s MEMFS branch includes
`../../c/src/htif.c`, and `experiments/os/htif_shim.h` (a pre-include)
supplies what our console-only `htif.c` lacks. The functions the Lua ELF
does not link (`_stat`, `_unlink`, `rename`, `opendir`/`readdir`/`closedir`,
`_gettimeofday`) report `unsupported`, and the checker skips the rest of
that trace.

Reproduce: `experiments/os/run.sh` (about 4 s; `--quick` is the gate subset,
`scripts/check.sh` stage 5b). Outputs go to `experiments/os/out/` (not
committed). Measured 2026-09-29, Linux 7.0.0-1012-aws, ext4, glibc 2.43.

## Linux control

The generated scripts (`tcb/validation/gen.py`, 6,490 scripts, 101,621
calls) on the Linux host: **6,398 accepted, 0 rejected, 92 special**. This is
the same result as ship-your-ocaml's RESULTS.md: the copied spec, checker
and generator behave the same here.

## `htif.c`, generated scripts: 0 accepted, 874 rejected, 5,616 unsupported

5,616 traces reach a call the ELF does not have (every fixture starts with
`mkdir`). Of the rest, no trace is accepted:

| class | rejections | `htif.c` returns | the spec says |
|---|---|---|---|
| `open` with `O_CREAT` | 263 | `ENOENT` (`_open` always fails) | success, a new descriptor |
| `read` on a descriptor it never issued | 207 | `bytes ""` (end of input) | `EBADF` |
| `write` on a descriptor it never issued | 257 | the byte count (HTIF output) | `EBADF` |
| `lseek` on a descriptor it never issued | 102 | `ESPIPE` | `EBADF` |
| `close` on a descriptor it never issued | 36 | success | `EBADF` |
| `fstat` on a descriptor it never issued | 9 | a regular file of size 0, `st_nlink` 0 | `EBADF` |

## `htif.c`, console scripts: 7 accepted, 16 rejected, 1 special

`experiments/os/console.scripts` has one script per behaviour of fds 0-2 and
of unknown descriptors (the generated families barely reach them). The
scripts from c06 on also have kernel-checked counterparts in
`Lua/Os/HtifTraces.lean` (`accepts_*`, `rejects_*`: facts about `next`).

**Conforms.**

| script | call | `htif.c` |
|---|---|---|
| c01, c02, c03 | `write` to fd 1 or 2 | all bytes to the HTIF console |
| c04, c05 | `read` fd 0 | end of input (the spec's stdin is empty) |
| c13 | `close 1` | success |
| c22 | `open` without `O_CREAT` | `ENOENT` (the file system is empty) |
| c11 (special) | `lseek 1 0 0` | `ESPIPE`; the spec leaves `lseek` on a stream unconstrained |

**Deviates.**

| id | scripts | `htif.c` | the spec says |
|---|---|---|---|
| H1 | c08, c09, c10, c24 | `fstat` on fd 0-2: `S_IFCHR`, `st_nlink = 0` (the struct is `memset` to 0) | `st_nlink = 1` (`rejects_fstat_stdout_nlink0`). newlib calls `_fstat(1)` before the first `print`, so every printing program hits this |
| H2 | c06, c07 | `read` on fd 1 returns end of input; `write` on fd 0 prints | `EBADF` both (`rejects_read_stdout`, `rejects_write_stdin`) |
| H3 | c17-c21 | any descriptor it never issued acts as the console | `EBADF` (`rejects_write_unknown_fd`, `rejects_close_unknown_fd`); ship-your-ocaml's M1 |
| H4 | c14, c15, c16 | `close` does not close: later `write`/`close`/`fstat` on that fd succeed | `EBADF` (`rejects_write_after_close`) |
| H5 | c12 | `lseek` with a bad `whence` returns `ESPIPE` | `EINVAL` (`rejects_lseek_bad_whence`) |
| H6 | c23 | `open` with `O_CREAT` returns `ENOENT` | success: there is no file system |

Not in the ELF (reported `unsupported`): `stat`, `unlink`, `rename`,
`mkdir`, `rmdir`, `opendir`, `readdir`, `closedir`, and the clock (no
`_gettimeofday`; the Lua build has no `os` library).

## What this means for the obligations

`Lua.Os.HtifFs_Statement` (`Lua/Os/Htif.lean`), every call of the six
functions, is false of the current `htif.c`: H1-H6 each give a counterexample
once the representation relation reaches that call. It needs an `htif.c` with
a descriptor table that returns `EBADF` for descriptors it did not issue,
`st_nlink = 1` for the console, and an in-image file system for `open`.

`Lua.Os.HtifPrint_Statement`, the calls a `print`-only program makes that the
spec constrains (`write` to fds 1-2, `read` from fd 0), is what the traces
accept (c01-c05). Its scope excludes `_fstat(1)` because of H1.

import TCB

/-!
# What the OS spec says on the console traces of `htif.c`

The trace validation (`experiments/os/RESULTS.md`) runs `c/src/htif.c`,
compiled natively, on call scripts and checks the recorded returns with
`tcbcheck`. This file restates the console part of that result as
kernel-checked facts about the spec (`TCB.Os.next` from the initial state:
fds 0-2 the console streams, no input). `accepts_*`: the current
`htif.c`'s return is allowed. `rejects_*`: the return of the console-only
`htif.c` this repository had before its in-image file system (deviations
H1-H5 in RESULTS.md) is not allowed; each is paired with the `accepts_*`
fact for what `htif.c` returns now.

They are facts about `next` only. That `htif.c` returns what the scripts
recorded is the native run, not a proof about the ELF; the machine-level
obligation is `Lua.Os.HtifFs_Statement` / `HtifPrint_Statement`
(`Lua/Os/Htif.lean`). Calls with paths (`open`) are not here: the kernel
does not reduce `String.splitOn` in path resolution (`tcb/TCB/Os/Examples.lean`).
-/

namespace Lua.Os.HtifTraces

open TCB.Os TCB.Os.Fs

/-- c01: `write 1 "hello" 5 => num 5` (all of it) is allowed. -/
theorem accepts_write_stdout :
    (next OsState.init (.write 1 [104, 101, 108, 108, 111] 5) (.num 5)).length = 1 := by
  decide +kernel

/-- c02: `write 2 "oops\n" 5 => num 5` is allowed. -/
theorem accepts_write_stderr :
    (next OsState.init (.write 2 [111, 111, 112, 115, 10] 5) (.num 5)).length = 1 := by
  decide +kernel

/-- c04: `read 0 16 => bytes ""` (end of input) is allowed, and it is the
only allowed return with no input. -/
theorem accepts_read_stdin_eof :
    (next OsState.init (.read 0 16) (.bytes [])).length = 1 := by decide +kernel

/-- c06: the console-only `htif.c` returned end of input for a read of
stdout; the spec says `EBADF` (CakeML: stdout is not readable). -/
theorem rejects_read_stdout : next OsState.init (.read 1 4) (.bytes []) = [] := by decide +kernel

/-- c07: the console-only `htif.c` wrote to the console for fd 0; the spec
says `EBADF`. -/
theorem rejects_write_stdin : next OsState.init (.write 0 [120] 1) (.num 1) = [] := by
  decide +kernel

/-- c09: the console-only `htif.c`'s `_fstat(1)` left `st_nlink = 0`
(`memset`); the spec says 1. newlib calls `_fstat(1)` before the first
`print` (`__swhatbuf_r`). -/
theorem rejects_fstat_stdout_nlink0 :
    next OsState.init (.fstat 1) (.stats ⟨.chr, 0, 0⟩) = [] := by decide +kernel

/-- c09: the console's link count is 1, what `htif.c` returns now. -/
theorem accepts_fstat_stdout :
    (next OsState.init (.fstat 1) (.stats ⟨.chr, 0, 1⟩)).length = 1 := by decide +kernel

/-- c12: the console-only `htif.c`'s `_lseek` failed with `ESPIPE` for a
bad `whence`; the spec says `EINVAL`. -/
theorem rejects_lseek_bad_whence : next OsState.init (.lseek 0 0 7) (.err .ESPIPE) = [] := by
  decide +kernel

/-- c14: after `close 1` succeeded, the console-only `htif.c` still wrote
to fd 1; the spec says `EBADF`. -/
theorem rejects_write_after_close :
    ∀ s ∈ next OsState.init (.close 1) .none, next s (.write 1 [120] 1) (.num 1) = [] := by
  decide +kernel

/-- c17: the console-only `htif.c` treated a descriptor it never issued as
the console; the spec says `EBADF` (ship-your-ocaml's deviation M1). -/
theorem rejects_write_unknown_fd : next OsState.init (.write 3 [120] 1) (.num 1) = [] := by
  decide +kernel

/-- c19: the console-only `htif.c`'s `_close` succeeded on any
descriptor; the spec says `EBADF`. -/
theorem rejects_close_unknown_fd : next OsState.init (.close 3) .none = [] := by decide +kernel

/-! What `htif.c` returns now on c06, c07, c12, c14, c17, c19, and the
frozen clock (c26), each allowed. -/

theorem accepts_read_stdout_ebadf :
    (next OsState.init (.read 1 4) (.err .EBADF)).length = 1 := by decide +kernel

theorem accepts_write_stdin_ebadf :
    (next OsState.init (.write 0 [120] 1) (.err .EBADF)).length = 1 := by decide +kernel

theorem accepts_lseek_bad_whence_einval :
    (next OsState.init (.lseek 0 0 7) (.err .EINVAL)).length = 1 := by decide +kernel

theorem accepts_write_after_close_ebadf :
    ∀ s ∈ next OsState.init (.close 1) .none, (next s (.write 1 [120] 1) (.err .EBADF)).length = 1 := by
  decide +kernel

theorem accepts_write_unknown_fd_ebadf :
    (next OsState.init (.write 3 [120] 1) (.err .EBADF)).length = 1 := by decide +kernel

theorem accepts_close_unknown_fd_ebadf :
    (next OsState.init (.close 3) (.err .EBADF)).length = 1 := by decide +kernel

/-- c26: the frozen clock (`TCB.Os.Clock.frozen`) reads 0, twice. -/
theorem accepts_clock_frozen :
    ∀ s ∈ next OsState.init .clock (.num 0), (next s .clock (.num 0)).length = 1 := by
  decide +kernel

end Lua.Os.HtifTraces

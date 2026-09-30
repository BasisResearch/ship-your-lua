import TCB.Os.Syscall

/-!
# Sanity facts about the specification, kernel-checked

Small closed instances of `next`, decided by the kernel: they pin down that
the spec says what its sources say on a few cases the rest of the
development relies on.
-/

namespace TCB.Os.Examples

open Fs

/-- Closing a descriptor that is not open fails with `EBADF`, and only
that. -/
example : (next OsState.init (.close 7) (.err .EBADF)).length = 1 := by decide +kernel
example : next OsState.init (.close 7) .none = [] := by decide +kernel

/-- The console: a write to fd 1 may write any prefix, and the console
shows exactly what was written. -/
example : ((next OsState.init (.write 1 [104, 105] 2) (.num 1)).map (·.streams.console)) = [[104]] := by
  decide +kernel

/-- `exit` ends the process: no call is allowed afterwards. -/
example : ∀ s ∈ next OsState.init (.exit 3) .none, next s (.close 1) .none = [] := by decide +kernel

/-- The clock is monotone. -/
example : next { OsState.init with clock := ⟨5⟩ } .clock (.num 4) = [] := by decide +kernel
example : (next { OsState.init with clock := ⟨5⟩ } .clock (.num 5)).length = 1 := by decide +kernel

/- Facts that involve path resolution (e.g. `mkdir "/d"` then `mkdir "/d"`
can only fail with `EEXIST`) are true by evaluation but not decidable by the
kernel, which does not reduce `String.splitOn`; they are covered by the
trace validation (`tcb/validation/`) instead. -/

end TCB.Os.Examples

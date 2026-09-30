import TCB
import Vsa.Machine

/-!
# The OS boundary on bare metal: `htif.c` against the trusted OS spec

Adapted from ship-your-ocaml's `OCaml/Os.lean` (commit `b6ffcf9`, see
ATTRIBUTION.md): the part that depends only on `Vsa.Machine` and `TCB`.

`tcb/TCB/Os` is the OS interface (a port of SibylFS for files and of
CakeML's basis model for console streams): `OsStep st call ret st'`. On
Linux it is trusted: it describes the kernel. On this bare-metal build
the "kernel" is `c/src/htif.c`, code inside the ELF, so the spec is a
proof obligation instead: `HtifFsImplements`.

The statement is about the machine: whenever the ELF enters one of its
system-call functions in a state whose in-image file system represents the
abstract state `st` (the relation `R`, over the machine's memory), the
function returns after finitely many steps with a result the spec allows,
and the new memory represents the new abstract state.

Two changes from ship-your-ocaml's statement (both needed for the Lua
instance, `Lua/Os/Htif.lean`):

1. `retOf` reads the result from the entry *and* the return configuration.
   A `read` returns bytes in the buffer, and `fstat` a `struct stat`, whose
   address is an argument register at the entry; the RISC-V ABI does not
   preserve it to the return. ship-your-ocaml's `retOf c'` is the case that
   ignores the entry.
2. A call the spec leaves unconstrained in `st` (`OsSpecial`, SibylFS's
   special states, e.g. `lseek` on a console stream) may return anything and
   leave any represented state. ship-your-ocaml's statement demands an
   `OsStep` there, which `next` never provides (it filters special results
   out), so no implementation could meet it on such a call.
-/

namespace Lua.Os

open Vsa.Machine

/-- The calling convention of the ELF's system-call functions: the call
decoded at a function's entry, and the result read at its return. -/
structure CallConv where
  /-- `some call` iff `c` is at the entry of a system-call function with
  arguments that decode to `call` -/
  callAt : Config → Option TCB.Os.Call
  /-- `c'` is the return point of the call entered at `c` (the return
  address reached with the callee's stack frame popped) -/
  returnsTo : Config → Config → Prop
  /-- the result as the C library sees it (return value, `errno`, the
  bytes written to an out-parameter), read at the return `c'` of the call
  entered at `c` -/
  retOf : Config → Config → TCB.Os.Ret

/-- **The in-image file system implements the OS spec (statement).** -/
def HtifFsImplements (cc : CallConv) (R : Config → TCB.Os.OsState → Prop) : Prop :=
  ∀ c st call, R c st → cc.callAt c = some call →
    ∃ c' st', Steps c c' ∧ cc.returnsTo c c' ∧
      (TCB.Os.OsSpecial st call ∨ TCB.Os.OsStep st call (cc.retOf c c') st') ∧ R c' st'

end Lua.Os

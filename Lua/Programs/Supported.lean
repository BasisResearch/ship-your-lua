import Lua.Fragment
import Lua.Programs.While
import Lua.Programs.PrintPrint
import Lua.Programs.F1Ops

/-! Kernel-checked `Supported` for the validation programs, and a negative
example that reads a register before writing it. -/

namespace Lua.Programs

open Lua.Bytecode

theorem while_supported : Supported whileProto := by decide +kernel

theorem f1Ops_supported : Supported f1OpsProto := by decide +kernel

theorem printPrint_supported : Supported printPrintProto := by decide +kernel

/-- `MOVE 0 1` reads register 1, which nothing wrote: rejected by `defInit`. -/
def readsStale : Proto :=
  .mk 0 true 2 [0x00010000#32, 0x01010046#32] [] [⟨true, 0, 0⟩] []

theorem readsStale_unsupported : ¬ Supported readsStale := by decide +kernel

end Lua.Programs

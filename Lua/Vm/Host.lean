import Lua.Bytecode.Semantics
import Lua.Vm.Layout

/-!
# The binary's `Host`

What `c/lua-riscv-htif.elf` prints for function values: `luaL_tolstring`'s
`"%s: %p"` with `lua_topointer` of a light C function, i.e. `function: 0x`
followed by the function's address in lowercase hex (newlib's `%p`).
Observed on the Sail model: `print(print)` prints `function: 0x800219b0`
(VALIDATION.md).
-/

namespace Lua.Vm

open Lua.Bytecode

/-- Lowercase hexadecimal without leading zeros. -/
def hexLower (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The rendering of builtins by the bare-metal binary. -/
def binaryHost : Host where
  showBuiltin
    | .print => "function: 0x" ++ hexLower Layout.symLuaBPrint

example : binaryHost.showBuiltin .print = "function: 0x800219b0" := by decide

end Lua.Vm

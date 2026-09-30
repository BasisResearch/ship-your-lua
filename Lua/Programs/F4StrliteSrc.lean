import Lua.Ast.Exec
import Lua.Vm.Host
import Lua.Programs.F4StrliteAst

/-!
# Held-out validation of `c/tests/f4_strlite.lua` on the source side

Strings (`abstractions/pilot/SUITE.md` H1–H5): the program is
`AstSupported`, and its `LuaSem` output is `c/tests/f4_strlite.expected`
(recorded from the ELF on Sail), derived by the rulebook's interpreter and
checked by the kernel.
-/

namespace Lua.Programs

open Lua.Ast Lua.Vm

/-- `c/tests/f4_strlite.expected`. -/
def f4StrliteOut : String :=
  "lua\t5.4\nlua 5.4\tlua7\t77\n3\t6\t0\nfalse\ttrue\ttrue\ttrue\ttrue\ttrue\n" ++
  "11\t-2\t42\t3\t1\n12345\t5\t12345\ntrue\ttrue\n"

theorem f4Strlite_astSupported : AstSupported f4StrliteAst := by decide +kernel

theorem f4Strlite_luaSem : LuaSem binaryHost f4StrliteAst f4StrliteOut :=
  luaRun_sound (fuel := 1000) (by decide +kernel)

end Lua.Programs

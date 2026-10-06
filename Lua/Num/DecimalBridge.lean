import Lua.Num.Decimal
import Lua.Bytecode.Semantics
import Lua.Ast.Semantics

/-!
# One `str2int`

`Lua.Num.str2int` (`Lua/Num/Decimal.lean`, the transcription of `l_str2int`)
is the semantics' `str2int`: the bytecode's and the source semantics' names
for it are exported from `Lua.Num` (step S1 of `abstractions/FLOAT-DESIGN.md`
swapped their former copies for it, which these theorems proved equal).
-/

namespace Lua.Num

/-- The bytecode semantics' digit scan is `digits` (it is exported from
`Lua.Num`). -/
theorem digits_bytecode : Lua.Bytecode.digits = digits := rfl

/-- The bytecode semantics' `str2int` is `str2int` (it is exported from
`Lua.Num`, FLOAT-DESIGN.md S1). -/
theorem str2int_bytecode : Lua.Bytecode.str2int = str2int := rfl

/-- The source semantics' `str2int` is `str2int` (it is exported from
`Lua.Num`, FLOAT-DESIGN.md S1). -/
theorem str2int_ast : Lua.Ast.str2int = str2int := rfl

end Lua.Num

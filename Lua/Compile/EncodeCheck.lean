import Lua.Compile.Encode

/-! Boundary regressions for the B2 emitter. The raw words below were
cross-checked against the vendored Lua 5.4.7 `lopcodes.h` macros. -/

namespace Lua.Compile.Encode

open Lua.Bytecode

/-- `CREATE_Ax`, `CREATE_ABx`, `CREATE_ABCk`, `CREATE_sJ` and `SETARG_sJ`
reference vectors, including maximal fields and a backwards jump to zero. -/
theorem c_macro_vectors :
    ([ax? .EXTRAARG 33554431, abx? .LOADK 255 131071,
      abc? .MOVE 255 255 255 true, abc? .MOVE 1 2 3 false,
      sj? (-16777215), sj? 0, sj? 16777216, sj? (-1),
      patchJump? (BitVec.ofNat 32 2147483448) 10 0].map
        (Option.map (fun w : Word => w.toNat))) =
    [some 4294967250, some 4294967171, some 4294967168, some 50462848,
      some 56, some 2147483576, some 4294967224, some 2147483448,
      some 2147482168] := by decide +kernel

/-- Each oversized field is rejected, as are both neighbours of the signed
jump range and a patch of a non-JMP word. -/
theorem overflow_checks :
    [ax? .EXTRAARG 33554432, abx? .LOADK 256 0, abx? .LOADK 0 131072,
      abc? .MOVE 256 0 0 false, abc? .MOVE 0 256 0 false,
      abc? .MOVE 0 0 256 false, sj? (-16777216), sj? 16777217,
      patchJump? (BitVec.ofNat 32 0) 0 1] = List.replicate 9 none := by
  decide +kernel

/-- Forward patches may target the current end; absent sites, unused
opcodes and out-of-range backwards destinations fail. -/
theorem patch_site_checks :
    [patchJumpAt? [BitVec.ofNat 32 2147483448] 0 1,
      patchJumpAt? [] 0 0,
      patchJumpAt? [BitVec.ofNat 32 127] 0 0,
      patchJumpAt? [BitVec.ofNat 32 2147483448] 1 0,
      (patchJump? (BitVec.ofNat 32 2147483448) 16777215 0).map List.singleton] =
    [some [BitVec.ofNat 32 2147483576], none, none, none, none] := by
  decide +kernel

end Lua.Compile.Encode

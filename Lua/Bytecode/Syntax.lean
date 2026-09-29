import Lua.Bytecode.OpCode

/-!
# Lua 5.4 bytecode: instructions, constants, prototypes

The deep embedding of what `luac` produces and `lundump.c` loads: a function
prototype (`Proto`, mirroring `struct Proto` in `lobject.h` without the
debug information that `luac -s` strips) whose code is a list of raw 32-bit
instruction words. Decoding follows `lopcodes.h` exactly:

```
iABC   C(8) | B(8) | k(1) | A(8) | Op(7)
iABx        Bx(17)     | A(8) | Op(7)
iAsBx      sBx(17)     | A(8) | Op(7)
iAx             Ax(25)        | Op(7)
isJ             sJ(25)        | Op(7)
```

with the excess-K signed encodings `sBx = Bx - OFFSET_sBx`
(`OFFSET_sBx = 2^16 - 1`), `sJ = Ax - OFFSET_sJ` (`2^24 - 1`) and
`sB = B - OFFSET_sC`, `sC = C - OFFSET_sC` (`OFFSET_sC = 127`).

Nothing here is Lua-program-specific; a program is a `Proto` value.
-/

namespace Lua.Bytecode

/-- A raw instruction word (`Instruction` is `l_uint32`). -/
abbrev Word := BitVec 32

namespace Word

/-- Field extraction: `size` bits starting at bit `pos`. -/
def field (w : Word) (pos size : Nat) : Nat := (w.toNat >>> pos) % 2 ^ size

/-- `GET_OPCODE`. -/
def opNum (w : Word) : Nat := w.field 0 7
/-- `GETARG_A`. -/
def a (w : Word) : Nat := w.field 7 8
/-- `GETARG_k`. -/
def k (w : Word) : Bool := w.field 15 1 == 1
/-- `GETARG_B`. -/
def b (w : Word) : Nat := w.field 16 8
/-- `GETARG_C`. -/
def c (w : Word) : Nat := w.field 24 8
/-- `GETARG_Bx`. -/
def bx (w : Word) : Nat := w.field 15 17
/-- `GETARG_Ax`. -/
def ax (w : Word) : Nat := w.field 7 25

/-- `OFFSET_sBx = MAXARG_Bx >> 1`. -/
def offsetSBx : Nat := 65535
/-- `OFFSET_sJ = MAXARG_sJ >> 1`. -/
def offsetSJ : Nat := 16777215
/-- `OFFSET_sC = MAXARG_C >> 1`. -/
def offsetSC : Nat := 127

/-- `GETARG_sBx`. -/
def sbx (w : Word) : Int := (w.bx : Int) - offsetSBx
/-- `GETARG_sJ`. -/
def sj (w : Word) : Int := (w.ax : Int) - offsetSJ
/-- `GETARG_sB`. -/
def sb (w : Word) : Int := (w.b : Int) - offsetSC
/-- `GETARG_sC`. -/
def sc (w : Word) : Int := (w.c : Int) - offsetSC

/-- The decoded opcode (`none` for the 45 unused 7-bit values). -/
def op? (w : Word) : Option OpCode := OpCode.ofNat? w.opNum

end Word

/-- A constant-table entry, as `lundump.c`'s `loadConstants` produces it.
Floats are kept as their IEEE-754 bit pattern (`lua_Number` is `double`);
strings as bytes (Lua strings are byte strings, not Unicode). -/
inductive Const where
  | nil
  | bool (b : Bool)
  | int (i : BitVec 64)
  | float (bits : BitVec 64)
  | str (s : List UInt8)
  deriving DecidableEq, Repr, Inhabited

/-- `Upvaldesc` without the debug name. -/
structure UpvalDesc where
  /-- the upvalue is a register of the enclosing function -/
  instack : Bool
  /-- register index, or index into the enclosing function's upvalues -/
  idx : Nat
  /-- `VDKREG`/`RDKCONST`/`RDKTOCLOSE`/`RDKCTC` -/
  kind : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A function prototype (`struct Proto` minus debug information). -/
inductive Proto where
  | mk (numparams : Nat) (isVararg : Bool) (maxstacksize : Nat)
      (code : List Word) (k : List Const) (upvalues : List UpvalDesc)
      (protos : List Proto)
  deriving Repr, Inhabited

namespace Proto

def numparams : Proto → Nat | mk n .. => n
def isVararg : Proto → Bool | mk _ v .. => v
def maxstacksize : Proto → Nat | mk _ _ m .. => m
def code : Proto → List Word | mk _ _ _ c .. => c
def k : Proto → List Const | mk _ _ _ _ k .. => k
def upvalues : Proto → List UpvalDesc | mk _ _ _ _ _ u _ => u
def protos : Proto → List Proto | mk _ _ _ _ _ _ p => p

/-- The instruction at `pc`. -/
def fetch (p : Proto) (pc : Nat) : Option Word := p.code[pc]?

/-- The constant `K[i]`. -/
def const (p : Proto) (i : Nat) : Option Const := p.k[i]?

end Proto

end Lua.Bytecode

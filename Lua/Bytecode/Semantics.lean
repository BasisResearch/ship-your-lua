import Lua.Bytecode.Syntax
import Lua.Bytecode.Kernel
import Lua.Num.Arith

/-!
# Lua 5.4 bytecode semantics `BcSem` — fragment F1

A small-step relation over VM states of one activation of the main chunk,
transcribed from `luaV_execute` (`lvm.c`, Lua 5.4.7) opcode by opcode. Each
opcode is ONE term, its `Kernel` (`Lua/Bytecode/Kernel.lean`): static read
ports, edges with def and kill ports, and a body computing values through
the shared primitive `δ`. The terms are built from combinators named after
`lvm.c`'s macros (`opArith`, `docondjump`, `setR`); `opKernel` is the table.
`Step` has one rule: fetch, then run the kernel. Registers hold `Option
Value`: ⊥ is a stale value, and reading it is stuck. F1 covers integers and
floats (`abstractions/FLOAT-DESIGN.md` §2), moves, constants, arithmetic and
bitwise operations, string coercion of numerals (`LUA_NOCVTS2N` is unset),
comparisons and conditional jumps, numeric `for` (integer and float loops,
`FORPREP`/`FORLOOP`), `RETURN*`, and calls to the builtin `print` fetched
from `_ENV`. `Lua/Bytecode/Fragment.lean` says which programs are in F1 and
ledgers every other opcode.

The numbers are the shared layer `Lua.Num` (`Lua/Num/Arith.lean`,
`Lua/Num/Decimal.lean`, `Lua/Num/Pow.lean`): integers are `BitVec 64`,
floats are core's IEEE binary64 model `Float.Model`, and every numeric
function is a transcription of the C it names (`luaO_rawarith`, `LTnum`,
`luaV_equalobj`, `luaO_str2num`, `tostringbuff`, newlib's `pow`, …).

Faithfulness conventions (each is what `lvm.c` does, cited per rule):

* `pc` is the index of the instruction being executed; `lvm.c`'s `pc` after
  `vmfetch` is our `pc + 1`, so a C `pc += n` lands on `pc + 1 + n` here.
* Arithmetic and bitwise operations on numbers store the result and SKIP the
  following `MMBIN*` (`op_arith_aux`, `op_arithf_aux`, `op_bitwise`: `pc++`):
  that fast path is `luaO_rawarith` (`fastArith`). Otherwise they fall
  through to `MMBIN*`, whose only defined case is the string library's
  arithmetic metamethods (`lstrlib.c` `arith`); every other case is a Lua
  error, so no rule applies: the state is stuck, the program has no
  behaviour, and `stuck_sim` must show the binary does not exit 0.
* A float carries, besides its `Float.Model` value, the sign bit of the
  double (`Value.flt x neg`): the model canonicalises NaN, and the sign of a
  NaN is the one bit of it Lua observes (`print(-(0/0))` writes `-nan`). Every
  float an operation computes is `Value.ofFloat` of the model's result (the
  ELF's soft-float gives the canonical positive NaN); `UNM` flips the sign,
  copies keep it.
* Conditional jumps (`docondjump`): if `cond ≠ k` skip the next instruction,
  else execute the next instruction's jump (`donextjump`: `pc += sJ + 1`).
* `//` and `%` are floor division/modulo with `luaV_idiv`/`luaV_mod`'s
  special cases (division by zero is an error; `n // -1 = -n` wrapping), and
  `luai_numidiv`/`luai_nummod` on floats.
* `print` writes `tostring` of each argument separated by `\t`, then `\n`
  (`luaB_print`). The rendering of a function value (`function: 0x…`, an
  address in the binary) is a parameter of the semantics (`Host`).

Nothing here executes Lua: `Step`, `Steps`, `Final` and `BcSem` are `Prop`s.
-/

namespace Lua.Bytecode

/-- Host (C) functions reachable in F1. -/
inductive Builtin where
  | print
  deriving DecidableEq, Repr, Inhabited

/-- Values of F1. A float is the model's value `x` and the sign bit `neg` of
the double (for a non-NaN it is `x`'s sign; for a NaN, which `Float.Model`
canonicalises, it is the sign `print` shows). -/
inductive Value where
  | nil
  | bool (b : Bool)
  | int (i : BitVec 64)
  | flt (x : Float.Model) (neg : Bool)
  | str (s : List UInt8)
  | builtin (f : Builtin)
  deriving DecidableEq, Repr, Inhabited

/-- A computed float (`setfltvalue` of an operation's result): its sign bit
is the model's (the canonical NaN is positive). -/
def Value.ofFloat (x : Float.Model) : Value := .flt x x.toBits.toBitVec.msb

/-- A number as a value. -/
def Value.ofNum : Lua.Num.Numeral → Value
  | .int i => .int i
  | .flt x => .ofFloat x

/-- A number (`ttisnumber`), without string coercion. -/
def Value.toNum? : Value → Option Lua.Num.Numeral
  | .int i => some (.int i)
  | .flt x _ => some (.flt x)
  | _ => none

/-- `lstrlib.c` `tonum` (and `l_strton`, `lvm.c:91`): a number, or a string
that `luaO_str2num` reads whole (`lua_stringtonumber(L, s) == len + 1`). -/
def Value.tonum? : Value → Option Lua.Num.Numeral
  | .int i => some (.int i)
  | .flt x _ => some (.flt x)
  | .str s => Lua.Num.str2number s
  | _ => none

/-- `tonumber` (`lvm.h:51`, `luaV_tonumber_`, `lvm.c:104`): the value as a
float; a float keeps its bits. -/
def Value.tonumber? : Value → Option Value
  | .flt x n => some (.flt x n)
  | v => v.tonum?.map fun a => .ofFloat a.toFloat

/-- `l_isfalse`: `nil` and `false` are false. -/
def Value.isFalse : Value → Bool
  | .nil => true
  | .bool b => !b
  | _ => false

/-- A signalling NaN: exponent all ones, a nonzero fraction, the quiet bit
(51) clear. `Float.Model` has one (quiet) NaN, and libm's `pow` tells the two
apart (`e_pow.c:121,128` returns 1 for `pow(qNaN, 0)`, NaN for
`pow(sNaN, 0)`), so a signalling NaN is not a value of the semantics. No
operation of the ELF makes one (soft-float returns the canonical quiet NaN)
and `luac` never emits a NaN constant. -/
def isSNaN (b : BitVec 64) : Bool :=
  (b >>> 52) &&& 0x7ff = 0x7ff && b &&& 0xfffffffffffff ≠ 0 && !b.getLsbD 51

/-- A constant as a value: a float constant is its bit pattern
(`lundump.c` `loadConstants`, `setfltvalue`), its sign bit kept; a
signalling NaN has none (`isSNaN`). -/
def Const.toValue? : Const → Option Value
  | .nil => some .nil
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .str s => some (.str s)
  | .float b =>
    if isSNaN b then none else some (.flt (Float.Model.ofBits (UInt64.ofBitVec b)) b.msb)

/-- Implementation-defined renderings the semantics must not invent: how
`tostring` shows a function value (`function: 0x…` with the C address in
the binary). Instantiated by the binary's layout in the refinement
statements. -/
structure Host where
  showBuiltin : Builtin → String

/-- Bytes to a string, one `Char` per byte (the HTIF console's convention). -/
def bytesToString (s : List UInt8) : String := String.ofList (s.map fun b => Char.ofNat b.toNat)

/-- `luaL_tolstring` on F1 values (`lauxlib.c:906-912`): an integer with
`%I` (`LUA_INTEGER_FMT`), a float with `%f`, which `luaO_pushvfstring`
renders by `tostringbuff` (`lobject.c:511-515`). -/
def Value.show (H : Host) : Value → String
  | .nil => "nil"
  | .bool true => "true"
  | .bool false => "false"
  | .int i => toString i.toInt
  | .flt x n => bytesToString (Lua.Num.tostringbuff n x)
  | .str s => bytesToString s
  | .builtin f => H.showBuiltin f

/-- The line `luaB_print` writes for these arguments. -/
def printLine (H : Host) (args : List Value) : String :=
  String.intercalate "\t" (args.map (Value.show H)) ++ "\n"

/-- The bytes of `"print"`. -/
def printKey : List UInt8 := [0x70, 0x72, 0x69, 0x6e, 0x74]

/-! ## Integer operations and numerals (`Lua.Num`) -/

-- `luaV_idiv`, `luaV_mod`, `luaV_shiftl`, `luaV_shiftr` and `l_str2int` are
-- the shared layer's (`Lua/Num/Arith.lean`, `Lua/Num/Decimal.lean`).
export Lua.Num (idiv imod shiftl shiftr isSpace digitVal digits str2int)

/-! ## The shared primitive δ -/

/-- The binary operators of `luaV_execute`'s arithmetic and bitwise arms. -/
inductive BinOp where
  | add | sub | mul | mod | idiv | band | bor | bxor | shl | shr | pow | div
  deriving DecidableEq, Repr

/-- The `lua_arith` operator (`LUA_OPADD` …, `lua.h:216`). -/
def BinOp.toOp : BinOp → Lua.Num.Op
  | .add => .add | .sub => .sub | .mul => .mul | .mod => .mod | .idiv => .idiv
  | .band => .band | .bor => .bor | .bxor => .bxor | .shl => .shl | .shr => .shr
  | .pow => .pow | .div => .div

/-- The integer operation of the integer fast path (`l_addi`, …, `luaV_mod`,
`luaV_idiv`, `luaV_shiftl`/`luaV_shiftr`); `none` is the runtime error
(`n%0`, `n//0`). `/` and `^` have none (`op_arithf`: floats only); they are
`none` here and never used (`fastArith_int`). -/
def BinOp.int : BinOp → BitVec 64 → BitVec 64 → Option (BitVec 64)
  | .add, x, y => some (x + y)
  | .sub, x, y => some (x - y)
  | .mul, x, y => some (x * y)
  | .mod, x, y => Bytecode.imod x y
  | .idiv, x, y => Bytecode.idiv x y
  | .band, x, y => some (x &&& y)
  | .bor, x, y => some (x ||| y)
  | .bxor, x, y => some (x ^^^ y)
  | .shl, x, y => some (shiftl x y)
  | .shr, x, y => some (shiftr x y)
  | .pow, _, _ => none
  | .div, _, _ => none

/-- The operator of a `TMS` event (`ltm.h`: `TM_ADD = 6` … `TM_SHR = 17`). -/
def BinOp.ofTM : Nat → Option BinOp
  | 6 => some .add | 7 => some .sub | 8 => some .mul | 9 => some .mod | 10 => some .pow
  | 11 => some .div | 12 => some .idiv
  | 13 => some .band | 14 => some .bor | 15 => some .bxor | 16 => some .shl | 17 => some .shr
  | _ => none

/-- The string library's metamethods (`lstrlib.c:330-341`,
`stringmetamethods`) cover the arithmetic operators only, not the bitwise
ones. -/
def BinOp.strMeta : BinOp → Bool
  | .add | .sub | .mul | .mod | .idiv | .pow | .div => true
  | _ => false

/-- A result of `luaO_rawarith` as a value (`none`: no result). -/
def resVal : Lua.Num.Res → Option Value
  | .val n => some (.ofNum n)
  | _ => none

/-- **`luaV_execute`'s arithmetic fast path** (`op_arith`, `op_arithK`,
`op_arithI`, `op_arithf`, `op_arithfK`, `op_bitwise`, `op_bitwiseK`,
`OP_SHRI`, `OP_SHLI`; `lvm.c:905-1011, 1440-1459`): `luaO_rawarith` on two
numbers (`Lua.Num.rawArith`); a non-number operand fails (`tonumberns`,
`tointegerns`), and the instruction falls through to `MMBIN*`. -/
def fastArith (o : BinOp) (x y : Value) : Lua.Num.Res :=
  match x.toNum?, y.toNum? with
  | some a, some b => Lua.Num.rawArith o.toOp a b
  | _, _ => .fail

/-- A concatenation operand as bytes (`luaV_concat`'s `tostring`,
`luaO_tostring`: integers with `%lld`, floats by `tostringbuff`); anything
else is an error (`luaG_concaterror`). -/
def Value.toStr? : Value → Option (List UInt8)
  | .str s => some s
  | .int i => some ((toString i.toInt).toList.map fun c => c.toNat.toUInt8)
  | .flt x n => some (Lua.Num.tostringbuff n x)
  | _ => none

/-- **Raw equality** (`luaV_equalobj`, `lvm.c:569`, without metamethods: F1
has no tables or userdata): numbers by `Lua.Num.eqNum` (`1 == 1.0`, NaN
unequal, `-0 == 0`); every other pair structurally (`ValRepr` makes the
machine's tag a function of the value, and strings compare by content). -/
def Value.rawEq : Value → Value → Bool
  | .flt a _, .flt b _ => Lua.Num.eqNum (.flt a) (.flt b)
  | .int i, .flt b _ => Lua.Num.eqNum (.int i) (.flt b)
  | .flt a _, .int j => Lua.Num.eqNum (.flt a) (.int j)
  | x, y => decide (x = y)

/-- `l_strcmp(a, b) < 0` in the "C" locale: byte-lexicographic order on
unsigned bytes, a proper prefix first. -/
def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- The primitive operations on values. -/
inductive Prim where
  /-- `op_arith`/`op_bitwise`'s integer fast path -/
  | arith (o : BinOp)
  /-- `luaT_trybinTM` with a string operand: the string metamethods -/
  | tm (o : BinOp)
  | unm | bnot | not | eq | lt | le
  /-- `luaV_objlen` -/
  | len
  /-- `luaV_concat` -/
  | concat

/-- **δ**: the value of a primitive on its operands; `none` is a runtime
error (no rule). Order tests give booleans (`luaV_lessthan`,
`luaV_lessequal`, `luaV_rawequalobj`).

* `.arith o`: the fast path's result (`fastArith`); `none` also where it
  falls through (the kernel `opArith` tells the two apart);
* `.tm o` (`MMBIN*`, `luaT_trybinTM`): the string library's metamethod
  `arith` (`lstrlib.c:288`): when `o` has one and an operand is a string,
  `tonum` both and `lua_arith` (`luaO_rawarith`); anything else is an error
  (`luaG_opinterror`, `luaG_tointerror`, `trymt`'s `luaL_error`);
* `.unm` (`OP_UNM`, `lvm.c:1540`): integers wrap, floats flip the sign
  (`luai_numunm`; a NaN's sign too), a string goes to `__unm` (`arith_unm`);
* `.bnot` (`OP_BNOT`, `lvm.c:1555`): `tointegerns`, else an error;
* `.lt`/`.le`: `LTnum`/`LEnum` on numbers, `l_strcmp` on strings, else an
  error (`luaG_ordererror`). -/
def δ : Prim → List Value → Option Value
  | .arith o, [x, y] => resVal (fastArith o x y)
  | .tm o, [x, y] =>
    if o.strMeta ∧ (x matches .str _ ∨ y matches .str _) then
      match x.tonum?, y.tonum? with
      | some a, some b => resVal (Lua.Num.rawArith o.toOp a b)
      | _, _ => none
    else none
  | .unm, [.int x] => some (.int (0 - x))
  | .unm, [.flt x n] => some (.flt (Float.Model.neg x) (!n))
  | .unm, [.str s] => (Lua.Num.str2number s).bind fun a => resVal (Lua.Num.rawArith .unm a a)
  | .bnot, [.int x] => some (.int (~~~x))
  | .bnot, [.flt x _] => (Lua.Num.flttointeger x .eq).map fun i => .int (~~~i)
  | .not, [v] => some (.bool v.isFalse)
  | .eq, [x, y] => some (.bool (x.rawEq y))
  | .lt, [.int x, .int y] => some (.bool (decide (x.toInt < y.toInt)))
  | .le, [.int x, .int y] => some (.bool (decide (x.toInt ≤ y.toInt)))
  | .len, [.str s] => some (.int (BitVec.ofNat 64 s.length))
  | .lt, [.str a, .str b] => some (.bool (lexLt a b))
  | .le, [.str a, .str b] => some (.bool (!lexLt b a))
  | .lt, [x, y] =>
    match x.toNum?, y.toNum? with
    | some a, some b => some (.bool (Lua.Num.ltNum a b))
    | _, _ => none
  | .le, [x, y] =>
    match x.toNum?, y.toNum? with
    | some a, some b => some (.bool (Lua.Num.leNum a b))
    | _, _ => none
  | .concat, vs => (vs.mapM Value.toStr?).map fun ss => .str ss.flatten
  | _, _ => none

/-- **Lua's arithmetic on two values**, as `luaV_execute` runs an
arithmetic or bitwise opcode: the fast path (`fastArith`), then, where it
fails, the `MMBIN*` metamethod (`δ (.tm o)`: the string library's); `none`
is an error. The source semantics' operators are this
(`Lua/Ast/Semantics.lean`). -/
def Value.arith (o : BinOp) (x y : Value) : Option Value :=
  match fastArith o x y with
  | .val n => some (.ofNum n)
  | .fail => δ (.tm o) [x, y]
  | .err => none

/-! ## States -/

/-- A VM state of the main chunk's activation (`VState`): the instruction
index, the register window `R[·]` (`base` onwards; `none` is ⊥, a stale
value), and everything printed so far. -/
abbrev State := VState Value

/-- The initial state at `luaV_execute`'s entry for the main closure: every
register holds a stale value (⊥). -/
def State.init : State := ⟨0, fun _ => none, ""⟩

/-- `pc + off` if it stays non-negative. -/
def jumpTo (base : Nat) (off : Int) : Option Nat :=
  if 0 ≤ (base : Int) + off then some ((base : Int) + off).toNat else none

/-- The target of the jump that follows a test at `pc` (`donextjump`: the
`JMP` at `pc + 1`, relative to `pc + 2`). -/
def nextJump (p : Proto) (pc : Nat) : Option Nat :=
  (p.fetch (pc + 1)).bind fun ni => jumpTo (pc + 2) ni.sj

/-- `forprep`'s integer case (`lvm.c`): given `init`, `limit`, `step`
(step ≠ 0), either skip the loop (`none`) or the iteration count stored in
place of the limit. Unsigned arithmetic as in C. -/
def forCount (init limit step : BitVec 64) : Option (BitVec 64) :=
  if 0 < step.toInt then
    if init.toInt > limit.toInt then none else some ((limit - init) / step)
  else
    if init.toInt < limit.toInt then none else some ((init - limit) / ((0 - (step + 1)) + 1))

/-- `LUA_MAXINTEGER`. -/
def maxInt : BitVec 64 := BitVec.ofNat 64 (2 ^ 63 - 1)
/-- `LUA_MININTEGER`. -/
def minInt : BitVec 64 := BitVec.ofNat 64 (2 ^ 63)

/-- `forlimit` (`lvm.c:178`) for an integer loop: `none` is `luaG_forerror`
(the limit is not a number or numeral); `some none`: skip the loop; `some
(some l)`: the integer limit `l`. `luaV_tointeger` (`lvm.c:153`: `l_strton`,
then `luaV_tointegerns` with `F2Iceil` for a negative step, else `F2Ifloor`);
failing that, `tonumber` and the sign of the float decides: a positive one is
too large (clip to `LUA_MAXINTEGER`, or skip a descending loop), anything
else too small (NaN included: `luai_numlt(0, NaN)` is false). The final "not
to run" test (`lvm.c:196`) is `forCount`'s. -/
def forLimit (lim : Value) (step : BitVec 64) : Option (Option (BitVec 64)) :=
  match lim.tonum?.bind (Lua.Num.Numeral.tointegerns (if step.toInt < 0 then .ceil else .floor)) with
  | some l => some (some l)
  | none =>
    match lim.tonum? with
    | none => none
    | some n =>
      if Float.Model.lt Lua.Num.zero n.toFloat then
        (if step.toInt < 0 then some none else some (some maxInt))
      else
        (if 0 < step.toInt then some none else some (some minInt))

/-! ## Kernel combinators, one per `lvm.c` macro -/

/-- An operand: a register (a read port) or a value fixed by the
instruction word (an immediate, or a constant `K[i]`). -/
inductive Opnd where
  | reg (r : Nat)
  | imm (v : Value)

/-- The read ports of some operands. -/
def Opnd.ports : List Opnd → List Nat
  | [] => []
  | .reg r :: os => r :: ports os
  | .imm _ :: os => ports os

/-- The operand values, given the values of the read ports in order. -/
def Opnd.fill : List Opnd → List Value → List Value
  | [], _ => []
  | .imm v :: os, vs => v :: fill os vs
  | .reg _ :: os, v :: vs => v :: fill os vs
  | .reg _ :: os, [] => fill os []

/-- The constant `K[i]` as an operand. -/
def kval (p : Proto) (i : Nat) : Option Value := (p.const i).bind Const.toValue?

/-- `R[a] := f(operands)`, then continue at `next`. -/
def setR (a next : Nat) (os : List Opnd) (f : List Value → Option Value) : Kernel Value where
  reads := Opnd.ports os
  edges := [{ tgt := next, defs := [a] }]
  body vs := (f (Opnd.fill os vs)).map fun v => { edge := 0, vals := [v] }

/-- `R[a] := x` (`setobj`), then continue at `next`. -/
def move (a next : Nat) (x : Opnd) : Kernel Value := setR a next [x] List.head?

/-- `R[a], …, R[a+n-1] := nil`, then continue at `next`. -/
def setNils (a n next : Nat) : Kernel Value where
  reads := []
  edges := [{ tgt := next, defs := List.range' a n }]
  body _ := some { edge := 0, vals := List.replicate n .nil }

/-- An unconditional jump to `t`. -/
def jump (t : Nat) : Kernel Value where
  reads := []
  edges := [{ tgt := t }]
  body _ := some { edge := 0 }

/-- `op_arith`/`op_arithK`/`op_arithI`/`op_arithf`/`op_arithfK`/`op_bitwise`/
`op_bitwiseK` (`lvm.c:905-1011`): where the fast path (`fastArith`) has a
result, `R[a] := x op y` and skip the following `MMBIN*` (`pc++`); where it
fails, fall through to it; `luaV_mod`/`luaV_idiv` by zero is an error. -/
def opArith (pc a : Nat) (o : BinOp) (os : List Opnd) : Kernel Value where
  reads := Opnd.ports os
  edges := [{ tgt := pc + 2, defs := [a] }, { tgt := pc + 1 }]
  body vs := match Opnd.fill os vs with
    | [x, y] =>
      match fastArith o x y with
      | .val n => some { edge := 0, vals := [.ofNum n] }
      | .fail => some { edge := 1 }
      | .err => none
    | _ => some { edge := 1 }

/-- `OP_MMBIN*` (`luaT_trybinTM`) after the arithmetic instruction at
`pc - 1` fell through: the metamethod's result goes to that instruction's
`R[A]`. -/
def mmbin (p : Proto) (pc tm : Nat) (os : List Opnd) : Option (Kernel Value) := do
  let prev ← if pc = 0 then none else p.fetch (pc - 1)
  let o ← BinOp.ofTM tm
  some (setR prev.a (pc + 1) os (δ (.tm o)))

/-- The operands of `MMBINI`/`MMBINK`, swapped if `k` (`flip`). -/
def flip (k : Bool) (x y : Opnd) : List Opnd := if k then [y, x] else [x, y]

/-- `docondjump`: if the test's truth differs from `k`, skip the jump at
`pc + 1`; otherwise take it (`donextjump`). -/
def docondjump (p : Proto) (pc : Nat) (k : Bool) (os : List Opnd)
    (test : List Value → Option Value) : Option (Kernel Value) :=
  (nextJump p pc).map fun t =>
    { reads := Opnd.ports os
      edges := [{ tgt := pc + 2 }, { tgt := t }]
      body := fun vs => (test (Opnd.fill os vs)).map fun c =>
        { edge := if (!c.isFalse) = k then 1 else 0 } }

/-! ## The opcode kernels (`luaV_execute`, `lvm.c`) -/

section
variable (p : Proto) (pc : Nat) (w : Word)

/-- `OP_TESTSET`: if `l_isfalse(R[B]) == k` skip the jump, else
`R[A] := R[B]` and take it. -/
def testsetK (t : Nat) : Kernel Value where
  reads := [w.b]
  edges := [{ tgt := pc + 2 }, { tgt := t, defs := [w.a] }]
  body
    | [v] => some (if v.isFalse = w.k then { edge := 0 } else { edge := 1, vals := [v] })
    | _ => none

/-- `OP_FORPREP` (`forprep`, `lvm.c:205`).

* **Integer loop** (`init` and `step` integers): a zero step is an error;
  `R[A+3] := init`; the limit is `forLimit`'s (a numeral string is coerced,
  a float limit is floored or ceiled, an out-of-range one clipped or the loop
  skipped); if the loop runs, the count replaces the limit (edge 0), else
  jump past the loop (edge 1).
* **Float loop** (otherwise): `tonumber` the limit, the step and `init`
  (strings coerced; failure is `luaG_forerror`), a zero step is an error;
  skip the loop (edge 3, nothing written) or make all four registers floats
  (edge 2). -/
def forprepK : Kernel Value where
  reads := [w.a, w.a + 1, w.a + 2]
  edges := [{ tgt := pc + 1, defs := [w.a + 3, w.a + 1] },
    { tgt := pc + 1 + w.bx + 1, defs := [w.a + 3] },
    { tgt := pc + 1, defs := [w.a, w.a + 1, w.a + 2, w.a + 3] },
    { tgt := pc + 1 + w.bx + 1 }]
  body
    | [.int i, l, .int st] =>
      if st = 0 then none else
      (forLimit l st).map fun
        | some lim =>
          match forCount i lim st with
          | some n => { edge := 0, vals := [.int i, .int n] }
          | none => { edge := 1, vals := [.int i] }
        | none => { edge := 1, vals := [.int i] }
    | [i, l, st] =>
      match l.tonumber?, st.tonumber?, i.tonumber? with
      | some (.flt fl nl), some (.flt fs ns), some (.flt fi ni) =>
        if Float.Model.beq fs Lua.Num.zero then none
        else if (if Float.Model.lt Lua.Num.zero fs then Float.Model.lt fl fi
                 else Float.Model.lt fi fl) then some { edge := 3 }
        else some { edge := 2, vals := [.flt fi ni, .flt fl nl, .flt fs ns, .flt fi ni] }
      | _, _, _ => none
    | _ => none

/-- `OP_FORLOOP` (`lvm.c:1784`), on the variant of the step `R[A+2]`.

* **Integer loop**: count 0 falls out; otherwise count−1, index += step,
  `R[A+3] := index`, jump back to `t` (edge 1).
* **Float loop** (`floatforloop`, `lvm.c:270`): index += step; while
  `0 < step ? index <= limit : limit <= index`, `R[A] := R[A+3] := index`
  and jump back (edge 2).

`lvm.c` reads the count and the index with `ivalue`/`fltvalue` and no tag
test; a supported program never writes these registers inside the loop
(`loopsOk`), so they hold what `FORPREP`/`FORLOOP` stored. -/
def forloopK (t : Nat) : Kernel Value where
  reads := [w.a, w.a + 1, w.a + 2]
  edges := [{ tgt := pc + 1 }, { tgt := t, defs := [w.a + 1, w.a, w.a + 3] },
    { tgt := t, defs := [w.a, w.a + 3] }]
  body
    | [i, .int n, .int st] =>
      if n = 0 then some { edge := 0 } else
      match i with
      | .int i => some { edge := 1, vals := [.int (n - 1), .int (i + st), .int (i + st)] }
      | _ => none
    | [.flt i _, .flt l _, .flt st _] =>
      let idx := Float.Model.add i st
      if (if Float.Model.lt Lua.Num.zero st then Float.Model.le idx l else Float.Model.le l idx)
      then some { edge := 2, vals := [.ofFloat idx, .ofFloat idx] }
      else some { edge := 0 }
    | _ => none

/-- `OP_CALL` of `print` with `B-1` arguments: print them, the `C-1`
results are nil, and the call clobbers the frame above them (`luaD_precall`
and `luaD_poscall` leave the stack above `L->top` stale): kill ports
`[A+C-1, maxstacksize)`. -/
def callK : Kernel Value where
  reads := List.range' w.a w.b
  edges := [{ tgt := pc + 1
              defs := List.range' w.a (w.c - 1)
              killLo := w.a + w.c - 1
              killN := p.maxstacksize - (w.a + w.c - 1) }]
  body
    | .builtin .print :: args =>
      some { edge := 0, vals := List.replicate (w.c - 1) .nil, print := some args }
    | _ => none

/-- `OP_CONCAT A B` (`luaV_concat`, `B ≥ 2`): `R[A] := R[A] .. … ..
R[A+B-1]`. It works in place, so the slots above `A` are scratch space
afterwards: kill ports. -/
def concatK : Kernel Value where
  reads := List.range' w.a w.b
  edges := [{ tgt := pc + 1, defs := [w.a], killLo := w.a + 1, killN := w.b - 1 }]
  body vs := (δ .concat vs).map fun v => { edge := 0, vals := [v] }

/-- `R[A] op x`: the arithmetic kernel of a register-register, -constant or
-immediate opcode. -/
def arithRR (o : BinOp) : Option (Kernel Value) := some (opArith pc w.a o [.reg w.b, .reg w.c])
def arithRK (o : BinOp) : Option (Kernel Value) :=
  (kval p w.c).map fun y => opArith pc w.a o [.reg w.b, .imm y]

/-- `op_bitwiseK` (`BANDK`/`BORK`/`BXORK`): `lvm.c` reads `K[C]` as
`ivalue(KC(i))` without a tag test, and only `R[B]` goes through
`tointegerns`. So the kernel exists only for an integer `K[C]`, which is
what `lcode.c`'s `codebitwise` emits (a `K` operand only for a `VKINT`
constant). A string `K[C]` would make the machine compute with the string's
pointer while `opArith` falls through to `MMBINK`. -/
def bitwiseRK (o : BinOp) : Option (Kernel Value) :=
  match kval p w.c with
  | some (.int y) => some (opArith pc w.a o [.reg w.b, .imm (.int y)])
  | _ => none

/-- The immediates `sB`, `sC` as values. -/
def immB : Opnd := .imm (.int (BitVec.ofInt 64 w.sb))
def immC : Opnd := .imm (.int (BitVec.ofInt 64 w.sc))

/-- **The kernel of each opcode** (`none`: outside the fragment, or an
operand side condition fails). -/
def opKernel : OpCode → Option (Kernel Value)
  | .MOVE => some (move w.a (pc + 1) (.reg w.b))
  | .LOADI => some (move w.a (pc + 1) (.imm (.int (BitVec.ofInt 64 w.sbx))))
  | .LOADK => (kval p w.bx).map fun v => move w.a (pc + 1) (.imm v)
  -- `cast_num(sBx)` (`__floatsidf`, exact)
  | .LOADF => some (move w.a (pc + 1) (.imm (.ofFloat (Lua.Num.ofI (BitVec.ofInt 64 w.sbx)))))
  | .LOADFALSE => some (move w.a (pc + 1) (.imm (.bool false)))
  | .LFALSESKIP => some (move w.a (pc + 2) (.imm (.bool false)))
  | .LOADTRUE => some (move w.a (pc + 1) (.imm (.bool true)))
  | .LOADNIL => some (setNils w.a (w.b + 1) (pc + 1))
  -- `_ENV.print` only: upvalue 0 of the main chunk is `_ENV`
  | .GETTABUP =>
    if w.b = 0 ∧ p.const w.c = some (.str printKey) then
      some (move w.a (pc + 1) (.imm (.builtin .print)))
    else none
  | .ADD => arithRR pc w .add
  | .SUB => arithRR pc w .sub
  | .MUL => arithRR pc w .mul
  | .MOD => arithRR pc w .mod
  | .IDIV => arithRR pc w .idiv
  | .BAND => arithRR pc w .band
  | .BOR => arithRR pc w .bor
  | .BXOR => arithRR pc w .bxor
  | .SHL => arithRR pc w .shl
  | .SHR => arithRR pc w .shr
  | .DIV => arithRR pc w .div
  | .POW => arithRR pc w .pow
  | .ADDK => arithRK p pc w .add
  | .SUBK => arithRK p pc w .sub
  | .MULK => arithRK p pc w .mul
  | .MODK => arithRK p pc w .mod
  | .IDIVK => arithRK p pc w .idiv
  | .DIVK => arithRK p pc w .div
  | .POWK => arithRK p pc w .pow
  | .BANDK => bitwiseRK p pc w .band
  | .BORK => bitwiseRK p pc w .bor
  | .BXORK => bitwiseRK p pc w .bxor
  | .ADDI => some (opArith pc w.a .add [.reg w.b, immC w])
  -- `luaV_shiftl(ib, -ic)` and `luaV_shiftl(ic, ib)`: the immediate is shifted
  | .SHRI => some (opArith pc w.a .shr [.reg w.b, immC w])
  | .SHLI => some (opArith pc w.a .shl [immC w, .reg w.b])
  | .MMBIN => mmbin p pc w.c [.reg w.a, .reg w.b]
  | .MMBINI => mmbin p pc w.c (flip w.k (.reg w.a) (immB w))
  | .MMBINK => (kval p w.b).bind fun v => mmbin p pc w.c (flip w.k (.reg w.a) (.imm v))
  | .UNM => some (setR w.a (pc + 1) [.reg w.b] (δ .unm))
  | .BNOT => some (setR w.a (pc + 1) [.reg w.b] (δ .bnot))
  | .NOT => some (setR w.a (pc + 1) [.reg w.b] (δ .not))
  | .LEN => some (setR w.a (pc + 1) [.reg w.b] (δ .len))
  | .CONCAT => if 2 ≤ w.b then some (concatK pc w) else none
  | .JMP => (jumpTo (pc + 1) w.sj).map jump
  | .EQ => docondjump p pc w.k [.reg w.a, .reg w.b] (δ .eq)
  | .EQK => (kval p w.b).bind fun v => docondjump p pc w.k [.reg w.a, .imm v] (δ .eq)
  | .EQI => docondjump p pc w.k [.reg w.a, immB w] (δ .eq)
  | .LT => docondjump p pc w.k [.reg w.a, .reg w.b] (δ .lt)
  | .LE => docondjump p pc w.k [.reg w.a, .reg w.b] (δ .le)
  | .LTI => docondjump p pc w.k [.reg w.a, immB w] (δ .lt)
  | .LEI => docondjump p pc w.k [.reg w.a, immB w] (δ .le)
  | .GTI => docondjump p pc w.k [immB w, .reg w.a] (δ .lt)
  | .GEI => docondjump p pc w.k [immB w, .reg w.a] (δ .le)
  | .TEST => docondjump p pc w.k [.reg w.a] List.head?
  | .TESTSET => (nextJump p pc).map (testsetK pc w)
  | .FORPREP => some (forprepK pc w)
  | .FORLOOP => (jumpTo (pc + 1) (-(w.bx : Int))).map (forloopK pc w)
  | .CALL => if w.b ≠ 0 ∧ w.c ≠ 0 then some (callK p pc w) else none
  -- the main chunk receives no arguments: no-op on the register window.
  -- Only as the main chunk's first instruction, with no fixed parameters
  -- (`lparser.c` `mainfunc`: `setvararg(fs, 0)`). `luaT_adjustvarargs` counts
  -- `L->top - ci->func - 1` actual arguments and moves `ci->func` past them;
  -- that is a no-op on the window only at the entry (`L->top = func + 1`),
  -- and `supportedB` rejects every edge into pc 0 (`edges`), so it runs once.
  | .VARARGPREP => if pc = 0 ∧ w.a = 0 then some (jump (pc + 1)) else none
  | _ => none

/-- The kernel of the instruction word `w` at `pc`. -/
def kernel : Option (Kernel Value) := w.op?.bind (opKernel p pc w)

end

/-- The kernel of the instruction at `pc`. -/
def kernelAt (p : Proto) (pc : Nat) : Option (Kernel Value) := (p.fetch pc).bind (kernel p pc)

/-! ## The step relation -/

section
variable (H : Host) (p : Proto)

/-- **One VM instruction**: fetch, then run the opcode's kernel
(`KStep.run`, the only rule). -/
def Step : State → State → Prop := KStep (printLine H) (kernelAt p)

/-- The main chunk returns (`RETURN`, `RETURN0`, `RETURN1`); its results are
discarded by `lua_pcall(L, 0, 0, 0)`. -/
inductive Final : State → Prop where
  | ret {s w o} : p.fetch s.pc = some w → w.op? = some o →
      (o = .RETURN ∨ o = .RETURN0 ∨ o = .RETURN1) → Final s

/-- Reflexive-transitive closure of `Step`. -/
inductive Steps : State → State → Prop where
  | refl (s : State) : Steps s s
  | head {a b c : State} : Step H p a b → Steps b c → Steps a c

/-- **`BcSem H p out`**: the main chunk `p` runs from `luaV_execute`'s
entry to its return, having printed exactly `out`. -/
def BcSem (out : String) : Prop :=
  ∃ s, Steps H p State.init s ∧ Final p s ∧ s.out = out

end

end Lua.Bytecode

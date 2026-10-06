import Lua.Bytecode.Syntax
import Lua.Bytecode.Kernel

/-!
# Lua 5.4 bytecode semantics `BcSem` — fragment F1

A small-step relation over VM states of one activation of the main chunk,
transcribed from `luaV_execute` (`lvm.c`, Lua 5.4.7) opcode by opcode. Each
opcode is ONE term, its `Kernel` (`Lua/Bytecode/Kernel.lean`): static read
ports, edges with def and kill ports, and a body computing values through
the shared primitive `δ`. The terms are built from combinators named after
`lvm.c`'s macros (`opArith`, `docondjump`, `setR`); `opKernel` is the table.
`Step` has one rule: fetch, then run the kernel. Registers hold `Option
Value`: ⊥ is a stale value, and reading it is stuck. F1 covers integers, moves, constants, integer arithmetic and bitwise
operations (F1b), comparisons and
conditional jumps, integer numeric `for` (`FORPREP`/`FORLOOP`), `RETURN*`,
and calls to the builtin `print` fetched from `_ENV`. `Lua/Bytecode/Fragment.lean`
says which programs are in F1 and ledgers every other opcode.

Faithfulness conventions (each is what `lvm.c` does, cited per rule):

* `pc` is the index of the instruction being executed; `lvm.c`'s `pc` after
  `vmfetch` is our `pc + 1`, so a C `pc += n` lands on `pc + 1 + n` here.
* Arithmetic and bitwise operations (F1b, merged into F1) on integers store
  the result and SKIP the following `MMBIN*` (`op_arith_aux`,
  `op_bitwise`: `pc++`). A non-integer operand in F1 is a runtime
  error (no floats or strings arise in F1), so no rule applies: the state is
  stuck, the program has no behaviour, and `stuck_sim` must show the binary
  does not exit 0.
* Conditional jumps (`docondjump`): if `cond ≠ k` skip the next instruction,
  else execute the next instruction's jump (`donextjump`: `pc += sJ + 1`).
* `//` and `%` are floor division/modulo with `luaV_idiv`/`luaV_mod`'s
  special cases (division by zero is an error; `n // -1 = -n` wrapping).
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

/-- Values of F1 (strings are carried for later fragments; F1 never
creates one in a register). -/
inductive Value where
  | nil
  | bool (b : Bool)
  | int (i : BitVec 64)
  | str (s : List UInt8)
  | builtin (f : Builtin)
  deriving DecidableEq, Repr, Inhabited

/-- `l_isfalse`: `nil` and `false` are false. -/
def Value.isFalse : Value → Bool
  | .nil => true
  | .bool b => !b
  | _ => false

/-- A constant as a value (`none` for floats: not in F1). -/
def Const.toValue? : Const → Option Value
  | .nil => some .nil
  | .bool b => some (.bool b)
  | .int i => some (.int i)
  | .str s => some (.str s)
  | .float _ => none

/-- Implementation-defined renderings the semantics must not invent: how
`tostring` shows a function value (`function: 0x…` with the C address in
the binary). Instantiated by the binary's layout in the refinement
statements. -/
structure Host where
  showBuiltin : Builtin → String

/-- Bytes to a string, one `Char` per byte (the HTIF console's convention). -/
def bytesToString (s : List UInt8) : String := String.ofList (s.map fun b => Char.ofNat b.toNat)

/-- `luaL_tolstring` on F1 values. -/
def Value.show (H : Host) : Value → String
  | .nil => "nil"
  | .bool true => "true"
  | .bool false => "false"
  | .int i => toString i.toInt
  | .str s => bytesToString s
  | .builtin f => H.showBuiltin f

/-- The line `luaB_print` writes for these arguments. -/
def printLine (H : Host) (args : List Value) : String :=
  String.intercalate "\t" (args.map (Value.show H)) ++ "\n"

/-- The bytes of `"print"`. -/
def printKey : List UInt8 := [0x70, 0x72, 0x69, 0x6e, 0x74]

/-! ## Integer operations (`lvm.c`, `llimits.h`) -/

/-- `luaV_idiv`: floor division; `none` is the division-by-zero error.
For `n = -1` this is `0 - m` (wrapping), which `Int.fdiv` + wrap agrees with. -/
def idiv (m n : BitVec 64) : Option (BitVec 64) :=
  if n = 0 then none else some (BitVec.ofInt 64 (Int.fdiv m.toInt n.toInt))

/-- `luaV_mod`: floor modulo; `none` is the `n%0` error. -/
def imod (m n : BitVec 64) : Option (BitVec 64) :=
  if n = 0 then none else some (BitVec.ofInt 64 (Int.fmod m.toInt n.toInt))

/-- `luaV_shiftl` (`lvm.c`): a negative `y` shifts right (logically: `intop`
works on `lua_Unsigned`), and a shift by 64 or more bits in either direction
gives 0. -/
def shiftl (x y : BitVec 64) : BitVec 64 :=
  if y.toInt < 0 then (if y.toInt ≤ -64 then 0 else x >>> (-y.toInt).toNat)
  else (if 64 ≤ y.toInt then 0 else x <<< y.toNat)

/-- `luaV_shiftr(x,y)` is `luaV_shiftl(x, intop(-, 0, y))` (`lvm.h`): the
negation wraps, so `y = minint` shifts left by `minint`, giving 0. -/
def shiftr (x y : BitVec 64) : BitVec 64 := shiftl x (0 - y)
/-! ## The shared primitive δ -/

/-- The binary operators of `luaV_execute`'s arithmetic and bitwise arms. -/
inductive BinOp where
  | add | sub | mul | mod | idiv | band | bor | bxor | shl | shr
  deriving DecidableEq, Repr

/-- The integer operation (`l_addi`, …, `luaV_mod`, `luaV_idiv`,
`luaV_shiftl`/`luaV_shiftr`); `none` is the runtime error (`n%0`, `n//0`). -/
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

/-- The operator of a `TMS` event (`ltm.h`: `TM_ADD = 6` … `TM_SHR = 17`;
`TM_POW`/`TM_DIV` are float-only). -/
def BinOp.ofTM : Nat → Option BinOp
  | 6 => some .add | 7 => some .sub | 8 => some .mul | 9 => some .mod | 12 => some .idiv
  | 13 => some .band | 14 => some .bor | 15 => some .bxor | 16 => some .shl | 17 => some .shr
  | _ => none

/-- The string library's metamethods (`lstrlib.c`, `stringmetamethods`)
cover the arithmetic operators only, not the bitwise ones. -/
def BinOp.strMeta : BinOp → Bool
  | .add | .sub | .mul | .mod | .idiv => true
  | _ => false

/-- `lisspace` in the "C" locale. -/
def isSpace (c : UInt8) : Bool := c == 32 || (9 ≤ c && c ≤ 13)

/-- A digit's value (`lisdigit`, and `lisxdigit`/`luaO_hexavalue` if `hex`). -/
def digitVal (hex : Bool) (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c.toNat - 48)
  else if hex ∧ 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if hex ∧ 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55)
  else none

/-- The leading digits of `s`: their value (accumulated from `a`), their
count (from `n`), and the rest. -/
def digits (hex : Bool) : List UInt8 → Nat → Nat → Nat × Nat × List UInt8
  | [], a, n => (a, n, [])
  | c :: cs, a, n =>
    match digitVal hex c with
    | some d => digits hex cs (a * (if hex then 16 else 10) + d) (n + 1)
    | none => (a, n, c :: cs)

/-- `luaO_str2num` of a whole Lua string, when it gives an integer
(`l_str2int`, `lobject.c`): spaces, a sign, `0x` hex digits (wrapping) or
decimal digits (rejected on overflow: `l_str2d` then makes it a float),
spaces, and nothing else (an embedded `\0` ends the C string early, so
`lua_stringtonumber` rejects it). -/
def str2int (s : List UInt8) : Option (BitVec 64) :=
  let s := s.dropWhile isSpace
  let (neg, s) := match s with
    | 45 :: t => (true, t)
    | 43 :: t => (false, t)
    | t => (false, t)
  let (hex, s) := match s with
    | 48 :: x :: t => if x == 120 || x == 88 then (true, t) else (false, s)
    | _ => (false, s)
  let (a, n, rest) := digits hex s 0 0
  if n = 0 ∨ (rest.dropWhile isSpace) ≠ [] ∨ (!hex ∧ 2 ^ 63 - 1 + (if neg then 1 else 0) < a) then
    none
  else some (if neg then 0 - BitVec.ofNat 64 a else BitVec.ofNat 64 a)

/-- An arithmetic metamethod's operand (`lstrlib.c` `tonum`), when it is an
integer: an integer, or a string converting to one. -/
def Value.toInt? : Value → Option (BitVec 64)
  | .int i => some i
  | .str s => str2int s
  | _ => none

/-- A concatenation operand as bytes (`tostring`: integers with `%lld`);
anything else is an error (`luaG_concaterror`). -/
def Value.toStr? : Value → Option (List UInt8)
  | .str s => some s
  | .int i => some ((toString i.toInt).toList.map fun c => c.toNat.toUInt8)
  | _ => none

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
`luaV_lessequal`, `luaV_rawequalobj`). -/
def δ : Prim → List Value → Option Value
  | .arith o, [.int x, .int y] => (o.int x y).map .int
  | .tm o, [x, y] =>
    if o.strMeta ∧ (x matches .str _ ∨ y matches .str _) then
      match x.toInt?, y.toInt? with
      | some a, some b => (o.int a b).map .int
      | _, _ => none
    else none
  | .unm, [.int x] => some (.int (0 - x))
  | .unm, [.str s] => (str2int s).map fun x => .int (0 - x)
  | .bnot, [.int x] => some (.int (~~~x))
  | .not, [v] => some (.bool v.isFalse)
  | .eq, [x, y] => some (.bool (decide (x = y)))
  | .lt, [.int x, .int y] => some (.bool (decide (x.toInt < y.toInt)))
  | .le, [.int x, .int y] => some (.bool (decide (x.toInt ≤ y.toInt)))
  | .len, [.str s] => some (.int (BitVec.ofNat 64 s.length))
  | .lt, [.str a, .str b] => some (.bool (lexLt a b))
  | .le, [.str a, .str b] => some (.bool (!lexLt b a))
  | .concat, vs => (vs.mapM Value.toStr?).map fun ss => .str ss.flatten
  | _, _ => none

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

/-- The constant `K[i]` as an operand (`none` for floats: not in F1). -/
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

/-- `op_arith`/`op_arithK`/`op_arithI`/`op_bitwise`/`op_bitwiseK`: on two
integers, `R[a] := x op y` and skip the following `MMBIN*` (`pc++`);
otherwise fall through to it. -/
def opArith (pc a : Nat) (o : BinOp) (os : List Opnd) : Kernel Value where
  reads := Opnd.ports os
  edges := [{ tgt := pc + 2, defs := [a] }, { tgt := pc + 1 }]
  body vs := match Opnd.fill os vs with
    | [.int x, .int y] => (δ (.arith o) [.int x, .int y]).map fun v => { edge := 0, vals := [v] }
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

/-- `OP_FORPREP` (`forprep`), integer loop: `R[A+3] := init`; if the loop
runs, the count replaces the limit, else jump past the loop. -/
def forprepK : Kernel Value where
  reads := [w.a, w.a + 1, w.a + 2]
  edges := [{ tgt := pc + 1, defs := [w.a + 3, w.a + 1] },
    { tgt := pc + 1 + w.bx + 1, defs := [w.a + 3] }]
  body
    | [.int i, .int l, .int st] =>
      if st = 0 then none else
      some (match forCount i l st with
        | some n => { edge := 0, vals := [.int i, .int n] }
        | none => { edge := 1, vals := [.int i] })
    | _ => none

/-- `OP_FORLOOP`, integer loop: count 0 falls out; otherwise count−1,
index += step, `R[A+3] := index`, jump back to `t`. -/
def forloopK (t : Nat) : Kernel Value where
  reads := [w.a, w.a + 1, w.a + 2]
  edges := [{ tgt := pc + 1 }, { tgt := t, defs := [w.a + 1, w.a, w.a + 3] }]
  body
    | [i, .int n, .int st] =>
      if n = 0 then some { edge := 0 } else
      match i with
      | .int i => some { edge := 1, vals := [.int (n - 1), .int (i + st), .int (i + st)] }
      | _ => none
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
  | .ADDK => arithRK p pc w .add
  | .SUBK => arithRK p pc w .sub
  | .MULK => arithRK p pc w .mul
  | .MODK => arithRK p pc w .mod
  | .IDIVK => arithRK p pc w .idiv
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

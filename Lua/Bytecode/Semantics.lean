import Lua.Bytecode.Syntax

/-!
# Lua 5.4 bytecode semantics `BcSem` — fragment F1

An inductive small-step relation over VM states of one activation of the main
chunk, transcribed from `luaV_execute` (`lvm.c`, Lua 5.4.7) opcode by opcode.
F1 covers integers, moves, constants, integer arithmetic and bitwise
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

/-- The integer operation of a binary opcode on integers (register-register,
register-constant, or register-immediate); `none` for opcodes that are not
F1 integer binary operations. The inner `Option` is the runtime error. The
second argument is the operand `R[C]`, `K[C]` or `sC`:

* `op_arith`/`op_arithK`/`op_arithI` (`+ - * % //`);
* `op_bitwise`/`op_bitwiseK` (`& | ~ << >>`, integers only via `tointegerns`);
* `OP_SHRI`: `luaV_shiftl(ib, -ic)`, which is `shiftr ib sC` (`-ic` of an
  `int` in `[-127, 128]` is `0 - sC` on 64 bits);
* `OP_SHLI`: `luaV_shiftl(ic, ib)`, the immediate is the value shifted
  (`sC << R[B]`). -/
def intArith : OpCode → Option (BitVec 64 → BitVec 64 → Option (BitVec 64))
  | .ADD | .ADDK | .ADDI => some fun x y => some (x + y)
  | .SUB | .SUBK => some fun x y => some (x - y)
  | .MUL | .MULK => some fun x y => some (x * y)
  | .MOD | .MODK => some imod
  | .IDIV | .IDIVK => some idiv
  | .BAND | .BANDK => some fun x y => some (x &&& y)
  | .BOR | .BORK => some fun x y => some (x ||| y)
  | .BXOR | .BXORK => some fun x y => some (x ^^^ y)
  | .SHL => some fun x y => some (shiftl x y)
  | .SHR | .SHRI => some fun x y => some (shiftr x y)
  | .SHLI => some fun x y => some (shiftl y x)
  | _ => none

/-- Operand shape of an arithmetic opcode. -/
inductive ArithShape where
  /-- `R[A] := R[B] op R[C]` -/
  | rr
  /-- `R[A] := R[B] op K[C]` -/
  | rk
  /-- `R[A] := R[B] op sC` -/
  | ri
  deriving DecidableEq

def arithShape : OpCode → Option ArithShape
  | .ADD | .SUB | .MUL | .MOD | .IDIV | .BAND | .BOR | .BXOR | .SHL | .SHR => some .rr
  | .ADDK | .SUBK | .MULK | .MODK | .IDIVK | .BANDK | .BORK | .BXORK => some .rk
  | .ADDI | .SHRI | .SHLI => some .ri
  | _ => none

/-- Integer order tests of `LT`/`LE` and the immediate forms. -/
def intCmp : OpCode → Option (BitVec 64 → BitVec 64 → Bool)
  | .LT | .LTI => some fun x y => decide (x.toInt < y.toInt)
  | .LE | .LEI => some fun x y => decide (x.toInt ≤ y.toInt)
  | .GTI => some fun x y => decide (x.toInt > y.toInt)
  | .GEI => some fun x y => decide (x.toInt ≥ y.toInt)
  | _ => none

/-! ## States -/

/-- A VM state of the main chunk's activation: the instruction index, the
register window `R[·]` (`base` onwards), and everything printed so far. -/
structure State where
  pc : Nat
  regs : Nat → Value
  out : String

namespace State

/-- `R[a] := v`. -/
def set (s : State) (a : Nat) (v : Value) : State :=
  { s with regs := fun j => if j = a then v else s.regs j }

/-- `R[a], …, R[a+n-1] := nil`. -/
def setNils (s : State) (a n : Nat) : State :=
  { s with regs := fun j => if a ≤ j ∧ j < a + n then .nil else s.regs j }

def goto (s : State) (pc : Nat) : State := { s with pc := pc }

/-- Append to the console output. -/
def emit (s : State) (str : String) : State := { s with out := s.out ++ str }

/-- `R[a], …, R[a+n-1]` as a list (call arguments). -/
def args (s : State) (a n : Nat) : List Value := (List.range n).map fun j => s.regs (a + j)

/-- The initial state at `luaV_execute`'s entry for the main closure. -/
def init : State := ⟨0, fun _ => .nil, ""⟩

end State

/-- `pc + off` if it stays non-negative. -/
def jumpTo (base : Nat) (off : Int) : Option Nat :=
  if 0 ≤ (base : Int) + off then some ((base : Int) + off).toNat else none

/-- `docondjump` at instruction `pc`: `cond ≠ k` skips the next instruction;
otherwise the next instruction's `sJ` is taken (`donextjump`). -/
def condJump (p : Proto) (pc : Nat) (cond k : Bool) : Option Nat :=
  if cond ≠ k then some (pc + 2)
  else (p.fetch (pc + 1)).bind fun ni => jumpTo (pc + 2) ni.sj

/-- `forprep`'s integer case (`lvm.c`): given `init`, `limit`, `step`
(step ≠ 0), either skip the loop (`none`) or the iteration count stored in
place of the limit. Unsigned arithmetic as in C. -/
def forCount (init limit step : BitVec 64) : Option (BitVec 64) :=
  if 0 < step.toInt then
    if init.toInt > limit.toInt then none else some ((limit - init) / step)
  else
    if init.toInt < limit.toInt then none else some ((init - limit) / ((0 - (step + 1)) + 1))

/-! ## The step relation -/

section
variable (H : Host) (p : Proto)

/-- One VM instruction of F1. Premises name the fetched word `w` and its
opcode; the conclusion is the successor state. -/
inductive Step : State → State → Prop where
  /-- `MOVE A B`: `R[A] := R[B]`. -/
  | move {s w} : p.fetch s.pc = some w → w.op? = some .MOVE →
      Step s ((s.set w.a (s.regs w.b)).goto (s.pc + 1))
  /-- `LOADI A sBx`. -/
  | loadi {s w} : p.fetch s.pc = some w → w.op? = some .LOADI →
      Step s ((s.set w.a (.int (BitVec.ofInt 64 w.sbx))).goto (s.pc + 1))
  /-- `LOADK A Bx`: `R[A] := K[Bx]`. -/
  | loadk {s w c v} : p.fetch s.pc = some w → w.op? = some .LOADK →
      p.const w.bx = some c → c.toValue? = some v →
      Step s ((s.set w.a v).goto (s.pc + 1))
  | loadfalse {s w} : p.fetch s.pc = some w → w.op? = some .LOADFALSE →
      Step s ((s.set w.a (.bool false)).goto (s.pc + 1))
  /-- `LFALSESKIP A`: `R[A] := false; pc++`. -/
  | lfalseskip {s w} : p.fetch s.pc = some w → w.op? = some .LFALSESKIP →
      Step s ((s.set w.a (.bool false)).goto (s.pc + 2))
  | loadtrue {s w} : p.fetch s.pc = some w → w.op? = some .LOADTRUE →
      Step s ((s.set w.a (.bool true)).goto (s.pc + 1))
  /-- `LOADNIL A B`: `R[A], …, R[A+B] := nil`. -/
  | loadnil {s w} : p.fetch s.pc = some w → w.op? = some .LOADNIL →
      Step s ((s.setNils w.a (w.b + 1)).goto (s.pc + 1))
  /-- `GETTABUP A 0 C` with `K[C] = "print"`: `R[A] := _ENV.print` (upvalue 0 of
  the main chunk is `_ENV`; other globals are outside F1). -/
  | gettabupPrint {s w} : p.fetch s.pc = some w → w.op? = some .GETTABUP →
      w.b = 0 → p.const w.c = some (.str printKey) →
      Step s ((s.set w.a (.builtin .print)).goto (s.pc + 1))
  /-- Integer binary operation (`op_arith`, `op_arithK`, `op_arithI`,
  `op_bitwise`, `op_bitwiseK`, `OP_SHRI`, `OP_SHLI`; see `intArith`): store
  and skip the following `MMBIN*` (`pc++`). -/
  | arith {s w o f sh x y r} : p.fetch s.pc = some w → w.op? = some o →
      intArith o = some f → arithShape o = some sh →
      s.regs w.b = .int x →
      (match sh with
        | .rr => s.regs w.c = .int y
        | .rk => p.const w.c = some (.int y)
        | .ri => y = BitVec.ofInt 64 w.sc) →
      f x y = some r →
      Step s ((s.set w.a (.int r)).goto (s.pc + 2))
  /-- `UNM A B` on an integer (wrapping negation). -/
  | unm {s w x} : p.fetch s.pc = some w → w.op? = some .UNM →
      s.regs w.b = .int x →
      Step s ((s.set w.a (.int (0 - x))).goto (s.pc + 1))
  /-- `BNOT A B` on an integer: `intop(^, ~l_castS2U(0), ib)`. No `MMBIN`
  follows a unary operator, so no skip. -/
  | bnot {s w x} : p.fetch s.pc = some w → w.op? = some .BNOT →
      s.regs w.b = .int x →
      Step s ((s.set w.a (.int (~~~x))).goto (s.pc + 1))
  /-- `NOT A B`. -/
  | not {s w} : p.fetch s.pc = some w → w.op? = some .NOT →
      Step s ((s.set w.a (.bool (s.regs w.b).isFalse)).goto (s.pc + 1))
  /-- `JMP sJ`. -/
  | jmp {s w t} : p.fetch s.pc = some w → w.op? = some .JMP →
      jumpTo (s.pc + 1) w.sj = some t → Step s (s.goto t)
  /-- `EQ A B k`: raw equality on F1 values (no floats, no metamethods). -/
  | eq {s w t} : p.fetch s.pc = some w → w.op? = some .EQ →
      condJump p s.pc (decide (s.regs w.a = s.regs w.b)) w.k = some t → Step s (s.goto t)
  /-- `EQK A B k`: raw equality with `K[B]`. -/
  | eqk {s w c v t} : p.fetch s.pc = some w → w.op? = some .EQK →
      p.const w.b = some c → c.toValue? = some v →
      condJump p s.pc (decide (s.regs w.a = v)) w.k = some t → Step s (s.goto t)
  /-- `EQI A sB k`: false unless `R[A]` is the integer `sB`. -/
  | eqi {s w t} : p.fetch s.pc = some w → w.op? = some .EQI →
      condJump p s.pc (decide (s.regs w.a = .int (BitVec.ofInt 64 w.sb))) w.k = some t →
      Step s (s.goto t)
  /-- `LT`/`LE A B k` on two integers. -/
  | cmpRR {s w o f x y t} : p.fetch s.pc = some w → w.op? = some o →
      (o = .LT ∨ o = .LE) → intCmp o = some f →
      s.regs w.a = .int x → s.regs w.b = .int y →
      condJump p s.pc (f x y) w.k = some t → Step s (s.goto t)
  /-- `LTI`/`LEI`/`GTI`/`GEI A sB k` on an integer. -/
  | cmpRI {s w o f x t} : p.fetch s.pc = some w → w.op? = some o →
      (o = .LTI ∨ o = .LEI ∨ o = .GTI ∨ o = .GEI) → intCmp o = some f →
      s.regs w.a = .int x →
      condJump p s.pc (f x (BitVec.ofInt 64 w.sb)) w.k = some t → Step s (s.goto t)
  /-- `TEST A k`. -/
  | test {s w t} : p.fetch s.pc = some w → w.op? = some .TEST →
      condJump p s.pc (!(s.regs w.a).isFalse) w.k = some t → Step s (s.goto t)
  /-- `TESTSET A B k`, skipping: `l_isfalse(R[B]) == k`. -/
  | testsetSkip {s w} : p.fetch s.pc = some w → w.op? = some .TESTSET →
      (s.regs w.b).isFalse = w.k → Step s (s.goto (s.pc + 2))
  /-- `TESTSET A B k`, taking: `R[A] := R[B]` and the next jump. -/
  | testsetJump {s w ni t} : p.fetch s.pc = some w → w.op? = some .TESTSET →
      (s.regs w.b).isFalse ≠ w.k → p.fetch (s.pc + 1) = some ni →
      jumpTo (s.pc + 2) ni.sj = some t →
      Step s ((s.set w.a (s.regs w.b)).goto t)
  /-- `FORPREP A Bx`, integer loop that runs: `R[A+3] := init`, the count
  replaces the limit. -/
  | forprepEnter {s w i l st n} : p.fetch s.pc = some w → w.op? = some .FORPREP →
      s.regs w.a = .int i → s.regs (w.a + 1) = .int l → s.regs (w.a + 2) = .int st →
      st ≠ 0 → forCount i l st = some n →
      Step s (((s.set (w.a + 3) (.int i)).set (w.a + 1) (.int n)).goto (s.pc + 1))
  /-- `FORPREP A Bx`, integer loop that is skipped: `pc += Bx + 1`. -/
  | forprepSkip {s w i l st} : p.fetch s.pc = some w → w.op? = some .FORPREP →
      s.regs w.a = .int i → s.regs (w.a + 1) = .int l → s.regs (w.a + 2) = .int st →
      st ≠ 0 → forCount i l st = none →
      Step s ((s.set (w.a + 3) (.int i)).goto (s.pc + 1 + w.bx + 1))
  /-- `FORLOOP A Bx`, another iteration: count−1, index += step, `pc -= Bx`. -/
  | forloopAgain {s w n i st t} : p.fetch s.pc = some w → w.op? = some .FORLOOP →
      s.regs (w.a + 1) = .int n → n ≠ 0 → s.regs w.a = .int i → s.regs (w.a + 2) = .int st →
      jumpTo (s.pc + 1) (-(w.bx : Int)) = some t →
      Step s ((((s.set (w.a + 1) (.int (n - 1))).set w.a (.int (i + st))).set (w.a + 3)
        (.int (i + st))).goto t)
  /-- `FORLOOP A Bx`, loop done (count 0). -/
  | forloopDone {s w} : p.fetch s.pc = some w → w.op? = some .FORLOOP →
      s.regs (w.a + 1) = .int 0 → (∃ st, s.regs (w.a + 2) = .int st) →
      Step s (s.goto (s.pc + 1))
  /-- `CALL A B C` of `print` with `B-1` arguments; its `C-1` results are nil. -/
  | callPrint {s w} : p.fetch s.pc = some w → w.op? = some .CALL →
      s.regs w.a = .builtin .print → w.b ≠ 0 → w.c ≠ 0 →
      Step s (((s.emit (printLine H (s.args (w.a + 1) (w.b - 1)))).setNils w.a (w.c - 1)).goto
          (s.pc + 1))
  /-- `VARARGPREP A`: the main chunk receives no arguments; no-op on the
  register window. -/
  | varargprep {s w} : p.fetch s.pc = some w → w.op? = some .VARARGPREP →
      Step s (s.goto (s.pc + 1))

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

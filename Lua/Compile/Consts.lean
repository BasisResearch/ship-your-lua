import Lua.Ast.Semantics

/-!
# Numerals and folded constants (Layer B, FLOAT-DESIGN.md S3)

Two checks between the source text, the parse tree and `luac`'s chunk, each
a `Bool` decided per program by `decide +kernel`:

* **`LexOk ns`**: every numeral lexeme the parser read (`scripts/gen_ast.py`
  emits `…AstNumerals` beside each AST) has, in the tree, the value
  `luaO_str2num` gives it (`Lua.Num.str2number`: `l_str2int`, else
  `l_str2d`, the ELF's correctly rounded `strtod`). This is what the lexer's
  `read_numeral` does (`llex.c`).
* **`KAccounted c p`**: every float constant of `luac`'s chunk is a value
  the model accounts for: a float numeral of the source, or what
  `lcode.c`'s `constfolding` computes ON THE MODEL (`foldK`: `luaO_rawarith`
  is `Value.arith`, the shared `Lua.Num` layer; `validop`'s division clause;
  no NaN or zero result). `luac` folds with the host's arithmetic, so a float
  constant the model does not account for is a fold where host and model
  differ: `^` folded with glibc's `pow` (`powFold_kfold`,
  `Lua/Compile/Corpus.lean`).

`foldK` is a model of `luac`'s decision to fold, not a number operation: its
values are the shared layer's.
-/

namespace Lua.Compile

open Lua.Ast
open Lua.Bytecode (Value Const Proto δ)

/-- A numeral as the value `luac` gives it. -/
def numeralValue : Numeral → Option Value
  | .int i => some (.int i)
  | .float b => Const.toValue? (.float b)

/-- `validop`'s division clause (`lcode.c`): no fold of `/`, `//`, `%` by a
numeric zero. -/
def divByZero (o : Lua.Bytecode.BinOp) (v : Value) : Bool :=
  (o == .div || o == .idiv || o == .mod) &&
    match v with
    | .int i => i == 0
    | .flt x _ => Float.Model.beq x Lua.Num.zero
    | _ => false

/-- `constfolding`'s result test: an integer, or a float neither NaN nor
zero ("to avoid problems with -0.0"). -/
def foldRes : Value → Option Value
  | .int i => some (.int i)
  | .flt x n => if x.isNaN || Float.Model.beq x Lua.Num.zero then none else some (.flt x n)
  | _ => none

/-- The value `luac` folds `e` to, computed on the model (`tonumeral` and
`constfolding`; no `<const>` locals). -/
def foldK : Exp → Option Value
  | .numeral n => numeralValue n
  | .prefixexp (.paren e) => foldK e
  | .unop .neg a => (foldK a).bind fun v => (δ .unm [v]).bind foldRes
  | .unop .bnot a => (foldK a).bind fun v => (δ .bnot [v]).bind foldRes
  | .binop op a b =>
    match op.toBc, foldK a, foldK b with
    | some o, some va, some vb =>
      if divByZero o vb then none else (Value.arith o va vb).bind foldRes
    | _, _, _ => none
  | _ => none

/-- The constants an expression may contribute: its fold and its
sub-expressions' folds. -/
def expK : Exp → List Value
  | .prefixexp (.paren a) => (foldK a).toList ++ expK a
  | .binop op a b => (foldK (.binop op a b)).toList ++ expK a ++ expK b
  | .unop op a => (foldK (.unop op a)).toList ++ expK a
  | e => (foldK e).toList

mutual
/-- The constants of an F1 statement's expressions. -/
def statK : Stat → List Value
  | .local_ _ es => expsK es
  | .assign _ es => expsK es
  | .functioncall (.call _ (.explist args)) => expsK args
  | .do_ b => blockK b
  | .while_ c b => expK c ++ blockK b
  | .repeat_ b c => blockK b ++ expK c
  | .if_ c t eifs els => expK c ++ blockK t ++ elseifsK eifs ++ optBlockK els
  | .fornum _ a b s body => expK a ++ expK b ++ optExpK s ++ blockK body
  | _ => []

def expsK : List Exp → List Value
  | [] => []
  | e :: es => expK e ++ expsK es

def optExpK : Option Exp → List Value
  | none => []
  | some e => expK e

def statsK : List Stat → List Value
  | [] => []
  | st :: ss => statK st ++ statsK ss

def blockK : Block → List Value
  | .mk ss _ => statsK ss

def elseifsK : List (Exp × Block) → List Value
  | [] => []
  | (c, b) :: r => expK c ++ blockK b ++ elseifsK r

def optBlockK : Option Block → List Value
  | none => []
  | some b => blockK b
end

/-- **Every float constant of `p` is accounted for by the model**: a float
numeral of `c` or a fold `foldK` computes. -/
def KAccounted (c : Chunk) (p : Proto) : Bool :=
  let vs := blockK c
  p.k.all fun
    | .float b => (Const.toValue? (.float b)).any (vs.contains ·)
    | _ => true

/-- **The parser's numerals are `luaO_str2num`'s** (`llex.c`
`read_numeral`): each lexeme's value in the tree is `Lua.Num.str2number` of
its text. -/
def LexOk (ns : List (List UInt8 × Numeral)) : Bool :=
  ns.all fun
    | (t, .int i) => Lua.Num.str2number t == some (.int i)
    | (t, .float b) =>
      Lua.Num.str2number t == some (.flt (Float.Model.ofBits (UInt64.ofBitVec b)))

end Lua.Compile

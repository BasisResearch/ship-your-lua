import Lua.Ast.Syntax

/-!
# Big-step semantics `LuaSem` of F1 source (Layer B)

An inductive big-step relation over the F1 AST, in the style of
ship-your-interpreter's `Vsa/While/Semantics.lean`. Values, integer
operations, `print`'s output and `Host` are shared with the bytecode
semantics (`Lua/Bytecode/Semantics.lean`), so the two can be compared
directly.

Scoping: the environment is a stack of locals; `local` pushes, a block
(`while`/`repeat`/`if`/`for` body) pops what it pushed (`scope`), and
assignment updates the innermost binding. Loops catch `break`; `if`
propagates it. Runtime errors (arithmetic on non-integers, `//`/`%` by
zero, comparing non-integers, a zero `for` step) have no rule: such a
program has no behaviour.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host printLine idiv imod forCount)

abbrev Env := List (String × Value)

def Env.lookup (ρ : Env) (x : String) : Option Value := (ρ.find? (·.1 = x)).map (·.2)

def Env.update : Env → String → Value → Option Env
  | [], _, _ => none
  | (y, w) :: ρ, x, v => if y = x then some ((y, v) :: ρ) else ((y, w) :: ·) <$> Env.update ρ x v

/-- Leave a block: drop the locals it pushed, keep its updates to outer
locals. -/
def scope (outer inner : Env) : Env := inner.drop (inner.length - outer.length)

def BinOp.arith : BinOp → Option (BitVec 64 → BitVec 64 → Option (BitVec 64))
  | .add => some fun x y => some (x + y)
  | .sub => some fun x y => some (x - y)
  | .mul => some fun x y => some (x * y)
  | .idiv => some Lua.Bytecode.idiv
  | .mod => some Lua.Bytecode.imod
  | _ => none

def BinOp.cmp : BinOp → Option (BitVec 64 → BitVec 64 → Bool)
  | .lt => some fun x y => decide (x.toInt < y.toInt)
  | .le => some fun x y => decide (x.toInt ≤ y.toInt)
  | .gt => some fun x y => decide (x.toInt > y.toInt)
  | .ge => some fun x y => decide (x.toInt ≥ y.toInt)
  | _ => none

/-- Expression evaluation (F1 expressions are pure). -/
inductive Eval : Env → Expr → Value → Prop where
  | nil {ρ} : Eval ρ .nil .nil
  | bool {ρ b} : Eval ρ (.bool b) (.bool b)
  | int {ρ i} : Eval ρ (.int i) (.int i)
  | var {ρ x v} : ρ.lookup x = some v → Eval ρ (.var x) v
  | arith {ρ op a b x y f r} : Eval ρ a (.int x) → Eval ρ b (.int y) →
      op.arith = some f → f x y = some r → Eval ρ (.binop op a b) (.int r)
  | eq {ρ a b va vb} : Eval ρ a va → Eval ρ b vb → Eval ρ (.binop .eq a b) (.bool (decide (va = vb)))
  | ne {ρ a b va vb} : Eval ρ a va → Eval ρ b vb → Eval ρ (.binop .ne a b) (.bool (decide (va ≠ vb)))
  | cmp {ρ op a b x y f} : Eval ρ a (.int x) → Eval ρ b (.int y) → op.cmp = some f →
      Eval ρ (.binop op a b) (.bool (f x y))
  | neg {ρ a x} : Eval ρ a (.int x) → Eval ρ (.neg a) (.int (0 - x))
  | not {ρ a v} : Eval ρ a v → Eval ρ (.not a) (.bool v.isFalse)
  | andF {ρ a b v} : Eval ρ a v → v.isFalse = true → Eval ρ (.and a b) v
  | andT {ρ a b v w} : Eval ρ a v → v.isFalse = false → Eval ρ b w → Eval ρ (.and a b) w
  | orT {ρ a b v} : Eval ρ a v → v.isFalse = false → Eval ρ (.or a b) v
  | orF {ρ a b v w} : Eval ρ a v → v.isFalse = true → Eval ρ b w → Eval ρ (.or a b) w

/-- Pointwise evaluation of call arguments, left to right. -/
inductive EvalList : Env → List Expr → List Value → Prop where
  | nil {ρ} : EvalList ρ [] []
  | cons {ρ e es v vs} : Eval ρ e v → EvalList ρ es vs → EvalList ρ (e :: es) (v :: vs)

/-- Completion of a statement list. -/
inductive Sig where
  | normal
  | brk
  deriving DecidableEq

mutual
/-- `Exec H ρ o ss ρ' o' sg`: running `ss` in `ρ` with output so far `o`
ends in `ρ'` with output `o'`, completing with `sg`. -/
inductive Exec (H : Host) : Env → String → List Stat → Env → String → Sig → Prop where
  | nil {ρ o} : Exec H ρ o [] ρ o .normal
  | local_ {ρ o x e v ss ρ' o' sg} : Eval ρ e v → Exec H ((x, v) :: ρ) o ss ρ' o' sg →
      Exec H ρ o (.local_ x e :: ss) ρ' o' sg
  | assign {ρ o x e v ρ₁ ss ρ' o' sg} : Eval ρ e v → ρ.update x v = some ρ₁ →
      Exec H ρ₁ o ss ρ' o' sg → Exec H ρ o (.assign x e :: ss) ρ' o' sg
  | print {ρ o args vs ss ρ' o' sg} : EvalList ρ args vs →
      Exec H ρ (o ++ printLine H vs) ss ρ' o' sg → Exec H ρ o (.print args :: ss) ρ' o' sg
  | brk {ρ o ss} : Exec H ρ o (.break_ :: ss) ρ o .brk
  | whileF {ρ o c b v ss ρ' o' sg} : Eval ρ c v → v.isFalse = true →
      Exec H ρ o ss ρ' o' sg → Exec H ρ o (.while_ c b :: ss) ρ' o' sg
  | whileT {ρ o c b v ρ₁ o₁ ss ρ' o' sg} : Eval ρ c v → v.isFalse = false →
      Exec H ρ o b ρ₁ o₁ .normal → Exec H (scope ρ ρ₁) o₁ (.while_ c b :: ss) ρ' o' sg →
      Exec H ρ o (.while_ c b :: ss) ρ' o' sg
  | whileB {ρ o c b v ρ₁ o₁ ss ρ' o' sg} : Eval ρ c v → v.isFalse = false →
      Exec H ρ o b ρ₁ o₁ .brk → Exec H (scope ρ ρ₁) o₁ ss ρ' o' sg →
      Exec H ρ o (.while_ c b :: ss) ρ' o' sg
  | repeatDone {ρ o b c v ρ₁ o₁ ss ρ' o' sg} : Exec H ρ o b ρ₁ o₁ .normal → Eval ρ₁ c v →
      v.isFalse = false → Exec H (scope ρ ρ₁) o₁ ss ρ' o' sg →
      Exec H ρ o (.repeat_ b c :: ss) ρ' o' sg
  | repeatAgain {ρ o b c v ρ₁ o₁ ss ρ' o' sg} : Exec H ρ o b ρ₁ o₁ .normal → Eval ρ₁ c v →
      v.isFalse = true → Exec H (scope ρ ρ₁) o₁ (.repeat_ b c :: ss) ρ' o' sg →
      Exec H ρ o (.repeat_ b c :: ss) ρ' o' sg
  | repeatB {ρ o b c ρ₁ o₁ ss ρ' o' sg} : Exec H ρ o b ρ₁ o₁ .brk →
      Exec H (scope ρ ρ₁) o₁ ss ρ' o' sg → Exec H ρ o (.repeat_ b c :: ss) ρ' o' sg
  | ifN {ρ o c t e v ρ₁ o₁ ss ρ' o' sg} : Eval ρ c v →
      Exec H ρ o (if v.isFalse then e else t) ρ₁ o₁ .normal →
      Exec H (scope ρ ρ₁) o₁ ss ρ' o' sg → Exec H ρ o (.if_ c t e :: ss) ρ' o' sg
  | ifB {ρ o c t e v ρ₁ o₁ ss} : Eval ρ c v →
      Exec H ρ o (if v.isFalse then e else t) ρ₁ o₁ .brk →
      Exec H ρ o (.if_ c t e :: ss) (scope ρ ρ₁) o₁ .brk
  | forSkip {ρ o x e₁ e₂ e₃ b i l st ss ρ' o' sg} :
      Eval ρ e₁ (.int i) → Eval ρ e₂ (.int l) → Eval ρ e₃ (.int st) → st ≠ 0 →
      forCount i l st = none → Exec H ρ o ss ρ' o' sg →
      Exec H ρ o (.numFor x e₁ e₂ e₃ b :: ss) ρ' o' sg
  | forRun {ρ o x e₁ e₂ e₃ b i l st n ρ₁ o₁ ss ρ' o' sg} :
      Eval ρ e₁ (.int i) → Eval ρ e₂ (.int l) → Eval ρ e₃ (.int st) → st ≠ 0 →
      forCount i l st = some n → ForIter H ρ o x i st n b ρ₁ o₁ →
      Exec H ρ₁ o₁ ss ρ' o' sg → Exec H ρ o (.numFor x e₁ e₂ e₃ b :: ss) ρ' o' sg

/-- The iterations of a numeric `for` with `n` further iterations after
this one (the bytecode's count): the control variable is a fresh local of
each iteration. -/
inductive ForIter (H : Host) : Env → String → String → BitVec 64 → BitVec 64 → BitVec 64 →
    List Stat → Env → String → Prop where
  | last {ρ o x i st n b ρ₁ o₁ sg} : Exec H ((x, .int i) :: ρ) o b ρ₁ o₁ sg →
      (sg = .brk ∨ n = 0) → ForIter H ρ o x i st n b (scope ρ ρ₁) o₁
  | next {ρ o x i st n b ρ₁ o₁ ρ' o'} : Exec H ((x, .int i) :: ρ) o b ρ₁ o₁ .normal → n ≠ 0 →
      ForIter H (scope ρ ρ₁) o₁ x (i + st) st (n - 1) b ρ' o' →
      ForIter H ρ o x i st n b ρ' o'
end

/-- **`LuaSem H s out`**: the chunk `s` runs to completion printing `out`. -/
def LuaSem (H : Host) (s : Chunk) (out : String) : Prop :=
  ∃ ρ', Exec H [] "" s ρ' out .normal

/-! ## The source fragment -/

mutual
/-- Every variable is a declared local in scope, no local is called
`print`, and `break` only occurs inside a loop. -/
def scopedE (bound : List String) : Expr → Bool
  | .nil | .bool _ | .int _ => true
  | .var x => bound.contains x
  | .binop _ a b | .and a b | .or a b => scopedE bound a && scopedE bound b
  | .neg a | .not a => scopedE bound a

def scopedEs (bound : List String) : List Expr → Bool
  | [] => true
  | e :: es => scopedE bound e && scopedEs bound es
end

mutual
def scopedS (bound : List String) (inLoop : Bool) : List Stat → Bool
  | [] => true
  | .local_ x e :: ss => x != "print" && scopedE bound e && scopedS (x :: bound) inLoop ss
  | .assign x e :: ss => bound.contains x && scopedE bound e && scopedS bound inLoop ss
  | .print args :: ss => scopedEs bound args && scopedS bound inLoop ss
  | .while_ c b :: ss => scopedE bound c && scopedS bound true b && scopedS bound inLoop ss
  | .repeat_ b c :: ss => scopedRepeat bound b c && scopedS bound inLoop ss
  | .if_ c t e :: ss => scopedE bound c && scopedS bound inLoop t && scopedS bound inLoop e &&
      scopedS bound inLoop ss
  | .numFor x a b c body :: ss => x != "print" && scopedE bound a && scopedE bound b &&
      scopedE bound c && scopedS (x :: bound) true body && scopedS bound inLoop ss
  | .break_ :: ss => inLoop && scopedS bound inLoop ss

/-- `repeat b until c`: `c` sees `b`'s locals. -/
def scopedRepeat (bound : List String) : List Stat → Expr → Bool
  | b, c => scopedS bound true b && scopedE (bound ++ declared b) c

def declared : List Stat → List String
  | [] => []
  | .local_ x _ :: ss => x :: declared ss
  | _ :: ss => declared ss
end

/-- **`AstSupported s`**: `s` is a well-scoped F1 chunk. -/
def AstSupported (s : Chunk) : Prop := scopedS [] false s = true

end Lua.Ast

import Lua.Ast.Syntax

/-!
# Big-step semantics `LuaSem` of Lua source (Layer B)

An inductive big-step relation over the full Lua 5.4 syntax
(`Lua/Ast/Syntax.lean`), in the style of ship-your-interpreter's
`Vsa/While/Semantics.lean`. Rules exist for fragment F1; every other form
(and every runtime error) has no rule, so a program using it has no
behaviour. `AstSupported` (below) is the decidable F1 predicate. Values,
integer operations, `print`'s output and `Host` are shared with the bytecode
semantics (`Lua/Bytecode/Semantics.lean`), so the two can be compared.

Meanings, each Lua 5.4's (manual §3, `lparser.c`):

* **Names** (§3.2, `singlevar`): a name is the innermost local of that
  name; otherwise it is the global `_ENV.x`, where `_ENV` is the main chunk's
  upvalue (only when no local `_ENV` is in scope). The global table is the
  one the chunk starts with, and F1 reads one global: `print`, the builtin.
  F1 never writes a global, so the table stays as it started.
* **Calls** (§3.3.6, §3.4.10): `f(args)` evaluates `f`, then the arguments
  left to right, then calls. The only function value in F1 is `print`
  (`luaB_print`: `tostring` of each argument, tab-separated, then a newline);
  a call of anything else has no rule.
* **Assignment** (§3.3.3): every expression is evaluated first, the values
  are adjusted to the number of variables (missing ones `nil`, extras
  dropped), then stored. The manual leaves the order of the stores
  undefined; this is the reference compiler's (`restassign` stores the last
  variable first), which only matters when a variable repeats.
* **Locals** (§3.3.7, §3.5): `local x₁, …, xₙ = e₁, …, eₘ` evaluates the
  `eᵢ` in the outer scope, then binds left to right with the same adjustment.
  `<const>` only forbids assignment (a static check, in `lparser.c` and in
  `AstSupported`); `<close>` needs a `__close` metamethod: no rule.
* **Blocks** (§3.5): the environment is a stack of locals; a block pops
  what it pushed (`scope`), and assignment updates the innermost binding. A
  `repeat` condition sees the body's locals.
* **Control** (§3.3.4): a statement completes normally, by `break`, or by
  `goto l` (`Sig`). Loops catch `break`. A block catches `goto l` when `l`
  is one of its own labels and resumes after the label, with its locals
  declared before the label still in scope (`findLabel`, `jumpEnv`);
  otherwise the `goto` propagates outwards, leaving loops. The visibility
  rules (a label is visible in its block and nested blocks, a `goto` may
  not jump into the scope of a local unless the label is the block's last
  statement) are static, in `AstSupported`.
* **Numeric `for`** (§3.3.5): start, limit and step (default the integer
  1) are evaluated once; on integers the iteration count is `forprep`'s
  (`forCount`), and the control variable is a fresh local of each
  iteration. A zero step is an error: no rule.
* **Operators** (§3.4): integer `+ - * // %` (wrapping; `//`, `%` floor,
  by zero an error), bitwise `& | ~ << >> ~` (`luaV_shiftl`), order
  comparisons on integers, `==`/`~=` raw equality, short-circuit
  `and`/`or`, `not`. Floats, strings, tables and metamethods have no rule.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host Builtin printLine idiv imod shiftl shiftr forCount)

abbrev Env := List (Name × Value)

def Env.lookup (ρ : Env) (x : Name) : Option Value := (ρ.find? (·.1 = x)).map (·.2)

def Env.update : Env → Name → Value → Option Env
  | [], _, _ => none
  | (y, w) :: ρ, x, v => if y = x then some ((y, v) :: ρ) else ((y, w) :: ·) <$> Env.update ρ x v

/-- The globals F1 reads from the table the main chunk starts with (the
base library's `print`; `luaL_openlibs`). -/
def initGlobal (x : Name) : Option Value :=
  if x = "print" then some (.builtin .print) else none

/-- Bind the names of `local x₁, …, xₙ = …` to the values, left to right
(the last name is innermost); missing values are `nil`, extra ones are
dropped. -/
def bindLocals : List Name → List Value → Env → Env
  | [], _, ρ => ρ
  | x :: xs, [], ρ => bindLocals xs [] ((x, .nil) :: ρ)
  | x :: xs, v :: vs, ρ => bindLocals xs vs ((x, v) :: ρ)

/-- Store adjusted values into a `varlist` of locals, the last variable
first (`restassign`). A non-local target is outside F1 (`none`). -/
def assignLocals : Env → List Var → List Value → Option Env
  | ρ, [], _ => some ρ
  | ρ, .name x :: vars, vals =>
    (assignLocals ρ vars vals.tail).bind fun ρ₁ => ρ₁.update x (vals.headD .nil)
  | _, _, _ => none

/-- Leave a block: drop the locals it pushed, keep its updates to outer
locals. -/
def scope (outer inner : Env) : Env := inner.drop (inner.length - outer.length)

/-- Integer binary operators (`luaV_arith`/`luaV_bitwise` on integers); the
inner `none` is a runtime error. -/
def BinOp.arith : BinOp → Option (BitVec 64 → BitVec 64 → Option (BitVec 64))
  | .add => some fun x y => some (x + y)
  | .sub => some fun x y => some (x - y)
  | .mul => some fun x y => some (x * y)
  | .idiv => some Lua.Bytecode.idiv
  | .mod => some Lua.Bytecode.imod
  | .band => some fun x y => some (x &&& y)
  | .bor => some fun x y => some (x ||| y)
  | .bxor => some fun x y => some (x ^^^ y)
  | .shl => some fun x y => some (shiftl x y)
  | .shr => some fun x y => some (shiftr x y)
  | _ => none

/-- Integer order comparisons. -/
def BinOp.cmp : BinOp → Option (BitVec 64 → BitVec 64 → Bool)
  | .lt => some fun x y => decide (x.toInt < y.toInt)
  | .le => some fun x y => decide (x.toInt ≤ y.toInt)
  | .gt => some fun x y => decide (x.toInt > y.toInt)
  | .ge => some fun x y => decide (x.toInt ≥ y.toInt)
  | _ => none

/-- Expression evaluation (F1 expressions are pure). -/
inductive Eval : Env → Exp → Value → Prop where
  | nil {ρ} : Eval ρ .nil .nil
  | false {ρ} : Eval ρ .false (.bool false)
  | true {ρ} : Eval ρ .true (.bool true)
  | int {ρ i} : Eval ρ (.numeral (.int i)) (.int i)
  | local_ {ρ x v} : ρ.lookup x = some v → Eval ρ (.prefixexp (.var (.name x))) v
  /-- `_ENV.x`, with `_ENV` the main chunk's upvalue. -/
  | global {ρ x v} : ρ.lookup x = none → ρ.lookup "_ENV" = none → initGlobal x = some v →
      Eval ρ (.prefixexp (.var (.name x))) v
  | paren {ρ e v} : Eval ρ e v → Eval ρ (.prefixexp (.paren e)) v
  | arith {ρ op a b x y f r} : Eval ρ a (.int x) → Eval ρ b (.int y) →
      op.arith = some f → f x y = some r → Eval ρ (.binop op a b) (.int r)
  | eq {ρ a b va vb} : Eval ρ a va → Eval ρ b vb →
      Eval ρ (.binop .eq a b) (.bool (decide (va = vb)))
  | ne {ρ a b va vb} : Eval ρ a va → Eval ρ b vb →
      Eval ρ (.binop .ne a b) (.bool (decide (va ≠ vb)))
  | cmp {ρ op a b x y f} : Eval ρ a (.int x) → Eval ρ b (.int y) → op.cmp = some f →
      Eval ρ (.binop op a b) (.bool (f x y))
  | andF {ρ a b v} : Eval ρ a v → v.isFalse = true → Eval ρ (.binop .and a b) v
  | andT {ρ a b v w} : Eval ρ a v → v.isFalse = false → Eval ρ b w → Eval ρ (.binop .and a b) w
  | orT {ρ a b v} : Eval ρ a v → v.isFalse = false → Eval ρ (.binop .or a b) v
  | orF {ρ a b v w} : Eval ρ a v → v.isFalse = true → Eval ρ b w → Eval ρ (.binop .or a b) w
  | neg {ρ a x} : Eval ρ a (.int x) → Eval ρ (.unop .neg a) (.int (0 - x))
  | bnot {ρ a x} : Eval ρ a (.int x) → Eval ρ (.unop .bnot a) (.int (~~~x))
  | not {ρ a v} : Eval ρ a v → Eval ρ (.unop .not a) (.bool v.isFalse)

/-- Pointwise evaluation of an `explist`, left to right. -/
inductive EvalList : Env → List Exp → List Value → Prop where
  | nil {ρ} : EvalList ρ [] []
  | cons {ρ e es v vs} : Eval ρ e v → EvalList ρ es vs → EvalList ρ (e :: es) (v :: vs)

/-- How a statement completes. -/
inductive Sig where
  | normal
  | brk
  | goto_ (l : Name)
  deriving DecidableEq, Repr

/-- A loop's completion from its body's abrupt one: `break` ends the loop
normally, a `goto` leaves it. -/
def Sig.exitLoop : Sig → Sig
  | .brk => .normal
  | sg => sg

/-- The statements after label `l` among a block's top-level statements,
and how many locals the block declares before it (starting from `k`). -/
def findLabel (l : Name) : List Stat → Nat → Option (List Stat × Nat)
  | [], _ => none
  | .label m :: ss, k => if m = l then some (ss, k) else findLabel l ss k
  | .local_ xs _ :: ss, k => findLabel l ss (k + xs.length)
  | .localfunction _ _ :: ss, k => findLabel l ss (k + 1)
  | _ :: ss, k => findLabel l ss k

/-- Where a block resumes when its statements complete with `sg`: after
its own label, for a `goto` to it. -/
def Sig.target (all : List Stat) : Sig → Option (List Stat × Nat)
  | .goto_ l => findLabel l all 0
  | _ => none

/-- The environment at a label of the block entered with `base` that
declares `k` locals before the label. -/
def jumpEnv (base : Env) (k : Nat) (ρ : Env) : Env := ρ.drop (ρ.length - (base.length + k))

/-- The step of a numeric `for` without one. -/
def Stat.forStep : Option Exp → Exp
  | some e => e
  | none => .numeral (.int 1)

section
variable (H : Host)

mutual
/-- `ExecS H ρ o st ρ' o' sg`: the statement `st` run in `ρ` with output
so far `o` ends in `ρ'` (with its new locals pushed) and output `o'`,
completing with `sg`. -/
inductive ExecS : Env → String → Stat → Env → String → Sig → Prop where
  | semi {ρ o} : ExecS ρ o .semi ρ o .normal
  | label {ρ o l} : ExecS ρ o (.label l) ρ o .normal
  | local_ {ρ o vars es vs} : vars.all (·.attrib != .close) = true → EvalList ρ es vs →
      ExecS ρ o (.local_ vars es) (bindLocals (vars.map (·.name)) vs ρ) o .normal
  | assign {ρ o vars es vs ρ₁} : EvalList ρ es vs → assignLocals ρ vars vs = some ρ₁ →
      ExecS ρ o (.assign vars es) ρ₁ o .normal
  /-- A call statement `f(args)` of the builtin `print`. -/
  | callPrint {ρ o f args vs} : Eval ρ (.prefixexp f) (.builtin .print) → EvalList ρ args vs →
      ExecS ρ o (.functioncall (.call f (.explist args))) ρ (o ++ printLine H vs) .normal
  | brk {ρ o} : ExecS ρ o .break_ ρ o .brk
  | goto_ {ρ o l} : ExecS ρ o (.goto_ l) ρ o (.goto_ l)
  | do_ {ρ o b ρ₁ o₁ sg} : ExecB ρ o b ρ₁ o₁ sg → ExecS ρ o (.do_ b) (scope ρ ρ₁) o₁ sg
  | whileF {ρ o c b v} : Eval ρ c v → v.isFalse = true → ExecS ρ o (.while_ c b) ρ o .normal
  | whileT {ρ o c b v ρ₁ o₁ ρ' o' sg} : Eval ρ c v → v.isFalse = false →
      ExecB ρ o b ρ₁ o₁ .normal → ExecS (scope ρ ρ₁) o₁ (.while_ c b) ρ' o' sg →
      ExecS ρ o (.while_ c b) ρ' o' sg
  | whileX {ρ o c b v ρ₁ o₁ sg} : Eval ρ c v → v.isFalse = false →
      ExecB ρ o b ρ₁ o₁ sg → sg ≠ .normal →
      ExecS ρ o (.while_ c b) (scope ρ ρ₁) o₁ sg.exitLoop
  | repeatDone {ρ o b c ρ₁ o₁ v} : ExecB ρ o b ρ₁ o₁ .normal → Eval ρ₁ c v →
      v.isFalse = false → ExecS ρ o (.repeat_ b c) (scope ρ ρ₁) o₁ .normal
  | repeatAgain {ρ o b c ρ₁ o₁ v ρ' o' sg} : ExecB ρ o b ρ₁ o₁ .normal → Eval ρ₁ c v →
      v.isFalse = true → ExecS (scope ρ ρ₁) o₁ (.repeat_ b c) ρ' o' sg →
      ExecS ρ o (.repeat_ b c) ρ' o' sg
  | repeatX {ρ o b c ρ₁ o₁ sg} : ExecB ρ o b ρ₁ o₁ sg → sg ≠ .normal →
      ExecS ρ o (.repeat_ b c) (scope ρ ρ₁) o₁ sg.exitLoop
  | ifT {ρ o c t eifs els v ρ₁ o₁ sg} : Eval ρ c v → v.isFalse = false →
      ExecB ρ o t ρ₁ o₁ sg → ExecS ρ o (.if_ c t eifs els) (scope ρ ρ₁) o₁ sg
  | ifElseif {ρ o c t c' t' eifs els v ρ' o' sg} : Eval ρ c v → v.isFalse = true →
      ExecS ρ o (.if_ c' t' eifs els) ρ' o' sg →
      ExecS ρ o (.if_ c t ((c', t') :: eifs) els) ρ' o' sg
  | ifElse {ρ o c t b v ρ₁ o₁ sg} : Eval ρ c v → v.isFalse = true →
      ExecB ρ o b ρ₁ o₁ sg → ExecS ρ o (.if_ c t [] (some b)) (scope ρ ρ₁) o₁ sg
  | ifNone {ρ o c t v} : Eval ρ c v → v.isFalse = true →
      ExecS ρ o (.if_ c t [] none) ρ o .normal
  | forSkip {ρ o x e₁ e₂ e₃ b i l st} :
      Eval ρ e₁ (.int i) → Eval ρ e₂ (.int l) → Eval ρ (Stat.forStep e₃) (.int st) → st ≠ 0 →
      forCount i l st = none → ExecS ρ o (.fornum x e₁ e₂ e₃ b) ρ o .normal
  | forRun {ρ o x e₁ e₂ e₃ b i l st n ρ' o' sg} :
      Eval ρ e₁ (.int i) → Eval ρ e₂ (.int l) → Eval ρ (Stat.forStep e₃) (.int st) → st ≠ 0 →
      forCount i l st = some n → ForIter ρ o x i st n b ρ' o' sg →
      ExecS ρ o (.fornum x e₁ e₂ e₃ b) ρ' o' sg

/-- A statement list, stopping at the first abrupt completion. -/
inductive ExecL : Env → String → List Stat → Env → String → Sig → Prop where
  | nil {ρ o} : ExecL ρ o [] ρ o .normal
  | cons {ρ o st ss ρ₁ o₁ ρ' o' sg} : ExecS ρ o st ρ₁ o₁ .normal → ExecL ρ₁ o₁ ss ρ' o' sg →
      ExecL ρ o (st :: ss) ρ' o' sg
  | stop {ρ o st ss ρ₁ o₁ sg} : ExecS ρ o st ρ₁ o₁ sg → sg ≠ .normal →
      ExecL ρ o (st :: ss) ρ₁ o₁ sg

/-- `ExecBF H base all ρ o ss ρ' o' sg`: the block with statements `all`,
entered in `base`, running from its suffix `ss` in `ρ`; a `goto` to one of
its labels resumes after the label. -/
inductive ExecBF : Env → List Stat → Env → String → List Stat → Env → String → Sig → Prop where
  | done {base all ρ o ss ρ₁ o₁ sg} : ExecL ρ o ss ρ₁ o₁ sg → sg.target all = none →
      ExecBF base all ρ o ss ρ₁ o₁ sg
  | jump {base all ρ o ss ρ₁ o₁ sg rest k ρ' o' sg'} : ExecL ρ o ss ρ₁ o₁ sg →
      sg.target all = some (rest, k) → ExecBF base all (jumpEnv base k ρ₁) o₁ rest ρ' o' sg' →
      ExecBF base all ρ o ss ρ' o' sg'

/-- A block without `return` (a `retstat` is outside F1). The final
environment still has the block's locals; the enclosing statement drops
them (`scope`). -/
inductive ExecB : Env → String → Block → Env → String → Sig → Prop where
  | mk {ρ o ss ρ' o' sg} : ExecBF ρ ss ρ o ss ρ' o' sg → ExecB ρ o (.mk ss none) ρ' o' sg

/-- The iterations of a numeric `for` with `n` further iterations after
this one (the bytecode's count): the control variable is a fresh local of
each iteration. -/
inductive ForIter : Env → String → Name → BitVec 64 → BitVec 64 → BitVec 64 → Block →
    Env → String → Sig → Prop where
  | last {ρ o x i st n b ρ₁ o₁ sg} : ExecB ((x, .int i) :: ρ) o b ρ₁ o₁ sg →
      (sg ≠ .normal ∨ n = 0) → ForIter ρ o x i st n b (scope ρ ρ₁) o₁ sg.exitLoop
  | next {ρ o x i st n b ρ₁ o₁ ρ' o' sg} : ExecB ((x, .int i) :: ρ) o b ρ₁ o₁ .normal →
      n ≠ 0 → ForIter (scope ρ ρ₁) o₁ x (i + st) st (n - 1) b ρ' o' sg →
      ForIter ρ o x i st n b ρ' o' sg
end

end

/-- **`LuaSem H c out`**: the chunk `c` runs to completion printing `out`. -/
def LuaSem (H : Host) (c : Chunk) (out : String) : Prop :=
  ∃ ρ', ExecB H [] "" c ρ' out .normal

/-! ## The source fragment F1 -/

/-- A label of a block, for the `goto` rules: its name, how many locals the
block declares before it, and whether it is the block's last statement up
to `;` and labels (then, as `lparser.c`'s `createlabel` says, the block's
locals count as out of scope; never in a `repeat` body, whose `until` sees
them). -/
structure LabelInfo where
  name : Name
  nloc : Nat
  last : Bool
  deriving DecidableEq, Repr

/-- The statement is `;` or a label. -/
def Stat.isVoid : Stat → Bool
  | .semi | .label _ => true
  | _ => false

/-- The locals a statement declares for the rest of its block, innermost
first. -/
def Stat.binds : Stat → List (Name × Attrib)
  | .local_ vars _ => (vars.map fun a => (a.name, a.attrib)).reverse
  | .localfunction x _ => [(x, .reg)]
  | _ => []

/-- The labels of a block's statements (`tail` is whether the block ends
where its statements end: no `return`, not a `repeat` body). -/
def blockLabels (tail : Bool) : List Stat → Nat → List LabelInfo
  | [], _ => []
  | st :: ss, k =>
    (match st with
      | .label l => [⟨l, k, tail && ss.all Stat.isVoid⟩]
      | _ => []) ++ blockLabels tail ss (k + st.binds.length)

/-- The locals a block's statements declare, innermost first (what a
`repeat` condition sees). -/
def declaredIn : List Stat → List (Name × Attrib)
  | [] => []
  | st :: ss => declaredIn ss ++ st.binds

/-- The locals a block's statements declare. -/
def Block.declared : Block → List (Name × Attrib)
  | .mk ss _ => declaredIn ss

/-- An enclosing block for the `goto` rules: its labels, and how many
locals it had declared where the inner statement is. -/
structure Frame where
  labels : List LabelInfo
  here : Nat

/-- A `goto l` is legal: the innermost block with a label `l` is
enclosing, and the jump does not enter the scope of a local (manual
§3.3.4). -/
def gotoOk (l : Name) : List Frame → Bool
  | [] => false
  | f :: fs =>
    match f.labels.find? (·.name = l) with
    | some lab => lab.last || decide (lab.nloc ≤ f.here)
    | none => gotoOk l fs

/-- Is `x` a local in scope? -/
def isBound (bound : List (Name × Attrib)) (x : Name) : Bool := bound.any (·.1 = x)

/-- `x` is a local that may be assigned (not `<const>`/`<close>`). -/
def isAssignable (bound : List (Name × Attrib)) (x : Name) : Bool :=
  (bound.find? (·.1 = x)).any (·.2 = .reg)

/-- F1's operators on integers. -/
def BinOp.inF1 (op : BinOp) : Bool :=
  op.arith.isSome || op.cmp.isSome || op = .eq || op = .ne || op = .and || op = .or

def UnOp.inF1 : UnOp → Bool
  | .neg | .not | .bnot => true
  | _ => false

mutual
/-- An F1 expression: `nil`, booleans, integer numerals, locals in scope,
parentheses, and F1's operators. -/
def supE (bound : List (Name × Attrib)) : Exp → Bool
  | .nil | .false | .true | .numeral (.int _) => true
  | .prefixexp (.var (.name x)) => isBound bound x
  | .prefixexp (.paren e) => supE bound e
  | .binop op a b => op.inF1 && supE bound a && supE bound b
  | .unop op a => op.inF1 && supE bound a
  | _ => false

def supEs (bound : List (Name × Attrib)) : List Exp → Bool
  | [] => true
  | e :: es => supE bound e && supEs bound es

def supOE (bound : List (Name × Attrib)) : Option Exp → Bool
  | none => true
  | some e => supE bound e
end

/-- A `varlist` of assignable locals. -/
def supVars (bound : List (Name × Attrib)) : List Var → Bool
  | [] => true
  | .name x :: vs => isAssignable bound x && supVars bound vs
  | _ :: _ => false

/-- The static context of a statement: locals in scope, whether it is in
a loop, the enclosing blocks' labels (innermost first, the current block
included), and the labels already visible. -/
structure SCtx where
  bound : List (Name × Attrib)
  inLoop : Bool
  frames : List Frame
  seen : List Name

mutual
/-- One F1 statement. -/
def supStat (Γ : SCtx) : Stat → Bool
  | .semi => true
  | .label l => !Γ.seen.contains l
  | .goto_ l => gotoOk l Γ.frames
  | .break_ => Γ.inLoop
  | .local_ vars es => vars.all (·.attrib != .close) && supEs Γ.bound es
  | .assign vars es => supVars Γ.bound vars && supEs Γ.bound es
  | .functioncall (.call (.var (.name f)) (.explist args)) =>
    f == "print" && !isBound Γ.bound "print" && !isBound Γ.bound "_ENV" && supEs Γ.bound args
  | .do_ b => supBlock Γ false b
  | .while_ c b => supE Γ.bound c && supBlock { Γ with inLoop := true } false b
  | .repeat_ b c => supBlock { Γ with inLoop := true } true b &&
      supE (b.declared ++ Γ.bound) c
  | .if_ c t eifs els => supE Γ.bound c && supBlock Γ false t && supElseifs Γ eifs &&
      supOB Γ els
  | .fornum x a b step body => supE Γ.bound a && supE Γ.bound b && supOE Γ.bound step &&
      supBlock { Γ with bound := (x, .reg) :: Γ.bound, inLoop := true } false body
  | _ => false

/-- The statements of a block from its current position: `labs` are the
block's labels, `k` the locals it declared so far. -/
def supStats (Γ : SCtx) (labs : List LabelInfo) (k : Nat) : List Stat → Bool
  | [] => true
  | st :: ss =>
    supStat { Γ with frames := ⟨labs, k⟩ :: Γ.frames } st &&
      supStats { Γ with bound := st.binds ++ Γ.bound,
                        seen := (match st with | .label l => [l] | _ => []) ++ Γ.seen }
        labs (k + st.binds.length) ss

/-- A block without `return`; `inRepeat` for a `repeat` body. -/
def supBlock (Γ : SCtx) (inRepeat : Bool) : Block → Bool
  | .mk ss none => supStats Γ (blockLabels (!inRepeat) ss 0) 0 ss
  | .mk _ (some _) => false

def supElseifs (Γ : SCtx) : List (Exp × Block) → Bool
  | [] => true
  | (c, b) :: r => supE Γ.bound c && supBlock Γ false b && supElseifs Γ r

def supOB (Γ : SCtx) : Option Block → Bool
  | none => true
  | some b => supBlock Γ false b
end

/-- **`AstSupported c`**: the chunk is in F1, with Lua's static rules:
statements `;`, `local` (no `<close>`), assignment to non-`<const>` locals,
`print(…)` calls of the global `print`, labels and `goto` (a visible label,
not jumping into a local's scope, no label visible twice), `break` in a
loop, `do`, `while`, `repeat`, `if`, numeric `for`; no `return`; the F1
expressions (`supE`). -/
def AstSupported (c : Chunk) : Prop := supBlock ⟨[], false, [], []⟩ false c = true

instance (c : Chunk) : Decidable (AstSupported c) := inferInstanceAs (Decidable (_ = true))

end Lua.Ast

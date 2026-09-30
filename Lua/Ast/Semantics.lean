import Lua.Ast.Syntax
import Lua.Ast.Rulebook

/-!
# Big-step semantics `LuaSem` of Lua source (Layer B)

A big-step relation over the full Lua 5.4 syntax (`Lua/Ast/Syntax.lean`),
given as a **rulebook** (`Lua/Ast/Rulebook.lean`): one non-recursive program
per construct (`rules`), whose calls are the premises and whose Lean
`if`/`match` branches are the side conditions, so the rules of a construct
are exclusive by construction. `LuaSem` is the least relation resolving the
calls (`Lua.Rulebook.Sem`); the generic graph law makes the interpreter
(`Lua/Ast/Exec.lean`) sound and complete and the relation deterministic
(`Lua/Ast/Determinism.lean`), with no per-construct proof. Rules exist for
fragment F1; every other form
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
  `and`/`or`, `not`. Strings (F4-lite, `abstractions/pilot/SUITE.md`
  H1–H5): literals, `..` of strings and integers (`tostring`), `#`, order
  by bytes (`l_strcmp` in the C locale), and `+ - * // %` and unary `-` on
  strings that convert to integers (the string metatable's `tonum`).
  Floats, tables and other metamethods have no rule.
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host Builtin printLine idiv imod shiftl shiftr forCount)
open Lua.Rulebook (Rulebook Prog Sem)

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

/-- A name: the innermost local, else the global `_ENV.x` (with `_ENV` the
main chunk's upvalue, i.e. no local `_ENV` in scope). -/
def evalName (ρ : Env) (x : Name) : Option Value :=
  match ρ.lookup x with
  | some v => some v
  | none => if ρ.lookup "_ENV" = none then initGlobal x else none

/-! ### Strings (F4-lite: `abstractions/pilot/SUITE.md` H1–H5) -/

/-- `lisspace` in the C locale. -/
def isSpace (c : UInt8) : Bool := c = 32 || (9 ≤ c && c ≤ 13)

/-- A digit's value in base 10 or 16. -/
def digitVal (base : Nat) (c : UInt8) : Option Nat :=
  if 48 ≤ c ∧ c ≤ 57 then some (c.toNat - 48)
  else if base = 16 ∧ 97 ≤ c ∧ c ≤ 102 then some (c.toNat - 87)
  else if base = 16 ∧ 65 ≤ c ∧ c ≤ 70 then some (c.toNat - 55)
  else none

/-- `l_str2int` (`lobject.c`) on the whole string, as `lstrlib.c`'s
`tonum` requires: spaces, a sign, decimal digits (rejected on overflow:
then the string is a float) or `0x` hex digits (wrapping), spaces. -/
def str2int (s : List UInt8) : Option (BitVec 64) :=
  let s := s.dropWhile isSpace
  let (neg, s) : Bool × List UInt8 := match s with
    | 45 :: r => (true, r)
    | 43 :: r => (false, r)
    | r => (false, r)
  let (base, s) : Nat × List UInt8 := match s with
    | 48 :: x :: r => if x = 120 ∨ x = 88 then (16, r) else (10, s)
    | r => (10, r)
  let ds := s.takeWhile fun c => (digitVal base c).isSome
  let n := ds.foldl (fun a c => a * base + (digitVal base c).getD 0) 0
  if ds = [] ∨ !(s.drop ds.length).all isSpace ∨
      (base = 10 ∧ n > 2 ^ 63 - 1 + (if neg then 1 else 0)) then none
  else some (if neg then 0 - BitVec.ofNat 64 n else BitVec.ofNat 64 n)

/-- `luaV_concat`'s operands: a string, or an integer by `tostring`
(`%d`). -/
def concatBytes : Value → Option (List UInt8)
  | .str s => some s
  | .int i => some ((toString i.toInt).toList.map fun c => c.toNat.toUInt8)
  | _ => none

/-- An arithmetic operand: an integer, or a string the string metatable's
`__add`/… converts to one (`tonum`; a float-valued string is out of
scope: no rule). -/
def arithInt : Value → Option (BitVec 64)
  | .int i => some i
  | .str s => str2int s
  | _ => none

/-- `l_strcmp` in the C locale: byte-lexicographic order. -/
def bytesLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a = b && bytesLt as bs)

/-- String order comparisons. -/
def BinOp.strCmp : BinOp → Option (List UInt8 → List UInt8 → Bool)
  | .lt => some bytesLt
  | .le => some fun a b => !bytesLt b a
  | .gt => some fun a b => bytesLt b a
  | .ge => some fun a b => !bytesLt a b
  | _ => none

/-- The arithmetic operators the string metatable implements. -/
def BinOp.coerces : BinOp → Bool
  | .add | .sub | .mul | .idiv | .mod => true
  | _ => false

/-- The strict binary operators on values (`none`: no rule). -/
def binOp : BinOp → Value → Value → Option Value
  | .eq, va, vb => some (.bool (decide (va = vb)))
  | .ne, va, vb => some (.bool (decide (va ≠ vb)))
  | .concat, va, vb => do
    let a ← concatBytes va
    let b ← concatBytes vb
    pure (.str (a ++ b))
  | op, .int x, .int y =>
    match op.arith, op.cmp with
    | some f, _ => (f x y).map .int
    | none, some g => some (.bool (g x y))
    | none, none => none
  | op, va, vb =>
    match va, vb, op.strCmp with
    | .str a, .str b, some f => some (.bool (f a b))
    | _, _, _ =>
      if op.coerces then do
        let f ← op.arith
        let x ← arithInt va
        let y ← arithInt vb
        (f x y).map .int
      else none

/-- The unary operators on values (`none`: no rule). -/
def unOp : UnOp → Value → Option Value
  | .neg, v => (arithInt v).map fun x => .int (0 - x)
  | .bnot, .int x => some (.int (~~~x))
  | .not, v => some (.bool v.isFalse)
  | .len, .str s => some (.int (BitVec.ofNat 64 s.length))
  | _, _ => none

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

/-! ## The rulebook -/

/-- The judgments of `LuaSem`, as calls:

* `eval ρ e`: expression `e` in `ρ` gives a value (F1 expressions are pure);
* `stat ρ o st`: statement `st` run in `ρ` with output so far `o` ends in
  `ρ'` (its new locals pushed) and output `o'`, completing with `sg`;
* `list ρ o ss`: a statement list, stopping at the first abrupt completion;
* `blockFrom base all ρ o ss`: the block with statements `all`, entered in
  `base`, running from its suffix `ss`; a `goto` to one of its labels
  resumes after the label;
* `block ρ o b`: a block without `return`; the final environment still has
  the block's locals (the enclosing statement drops them, `scope`);
* `forIter ρ o x i st n b`: the iterations of a numeric `for` from control
  value `i` with `n` further iterations after this one (the bytecode's
  count); the control variable is a fresh local of each iteration. -/
inductive Call where
  | eval (ρ : Env) (e : Exp)
  | stat (ρ : Env) (o : String) (st : Stat)
  | list (ρ : Env) (o : String) (ss : List Stat)
  | blockFrom (base : Env) (all : List Stat) (ρ : Env) (o : String) (ss : List Stat)
  | block (ρ : Env) (o : String) (b : Block)
  | forIter (ρ : Env) (o : String) (x : Name) (i st n : BitVec 64) (b : Block)

/-- A statement-level outcome: environment, output, completion. -/
abbrev Outcome := Env × String × Sig

/-- What a judgment answers. -/
@[reducible] def Call.Res : Call → Type
  | .eval .. => Value
  | _ => Outcome

/-- Rule bodies: programs that call the judgments. -/
abbrev Rule := Prog Call Call.Res

section
def eval (ρ : Env) (e : Exp) : Rule Value := .call (.eval ρ e) .ret
def stat (ρ : Env) (o : String) (st : Stat) : Rule Outcome := .call (.stat ρ o st) .ret
def execList (ρ : Env) (o : String) (ss : List Stat) : Rule Outcome := .call (.list ρ o ss) .ret
def blockFrom (base : Env) (all : List Stat) (ρ : Env) (o : String) (ss : List Stat) :
    Rule Outcome := .call (.blockFrom base all ρ o ss) .ret
def block (ρ : Env) (o : String) (b : Block) : Rule Outcome := .call (.block ρ o b) .ret
def forIter (ρ : Env) (o : String) (x : Name) (i st n : BitVec 64) (b : Block) : Rule Outcome :=
  .call (.forIter ρ o x i st n b) .ret

/-- An `explist`, left to right. -/
def evalList (ρ : Env) : List Exp → Rule (List Value)
  | [] => pure []
  | e :: es => do let v ← eval ρ e; let vs ← evalList ρ es; pure (v :: vs)

/-- A nested block, with its locals dropped. -/
def inScope (ρ : Env) (r : Rule Outcome) : Rule Outcome := do
  let (ρ₁, o₁, sg) ← r
  pure (scope ρ ρ₁, o₁, sg)
end

open Lua.Rulebook.Prog (lift) in
/-- **The rulebook of `LuaSem`**: one program per construct. A form with no
program (`.fail`) has no rule: it is outside the fragment, or a runtime
error. -/
def rules (H : Host) : Rulebook Call Call.Res
  -- expressions
  | .eval _ .nil => pure .nil
  | .eval _ .false => pure (.bool false)
  | .eval _ .true => pure (.bool true)
  | .eval _ (.numeral (.int i)) => pure (.int i)
  | .eval _ (.string s) => pure (.str s)
  | .eval ρ (.prefixexp (.var (.name x))) => lift (evalName ρ x)
  | .eval ρ (.prefixexp (.paren e)) => eval ρ e
  | .eval ρ (.binop .and a b) => do
    let v ← eval ρ a
    if v.isFalse then pure v else eval ρ b
  | .eval ρ (.binop .or a b) => do
    let v ← eval ρ a
    if v.isFalse then eval ρ b else pure v
  | .eval ρ (.binop op a b) => do
    let va ← eval ρ a
    let vb ← eval ρ b
    lift (binOp op va vb)
  | .eval ρ (.unop op a) => do lift (unOp op (← eval ρ a))
  | .eval _ _ => .fail
  -- statements
  | .stat ρ o .semi => pure (ρ, o, .normal)
  | .stat ρ o (.label _) => pure (ρ, o, .normal)
  | .stat ρ o (.local_ vars es) =>
    if vars.all (·.attrib != .close) then do
      let vs ← evalList ρ es
      pure (bindLocals (vars.map (·.name)) vs ρ, o, .normal)
    else .fail
  | .stat ρ o (.assign vars es) => do
    let vs ← evalList ρ es
    let ρ₁ ← lift (assignLocals ρ vars vs)
    pure (ρ₁, o, .normal)
  | .stat ρ o (.functioncall (.call f (.explist args))) => do
    let fv ← eval ρ (.prefixexp f)
    let vs ← evalList ρ args
    if fv = .builtin .print then pure (ρ, o ++ printLine H vs, .normal) else .fail
  | .stat ρ o .break_ => pure (ρ, o, .brk)
  | .stat ρ o (.goto_ l) => pure (ρ, o, .goto_ l)
  | .stat ρ o (.do_ b) => inScope ρ (block ρ o b)
  | .stat ρ o (.while_ c b) => do
    let v ← eval ρ c
    if v.isFalse then pure (ρ, o, .normal) else
    let (ρ₁, o₁, sg) ← block ρ o b
    if sg = .normal then stat (scope ρ ρ₁) o₁ (.while_ c b)
    else pure (scope ρ ρ₁, o₁, sg.exitLoop)
  | .stat ρ o (.repeat_ b c) => do
    let (ρ₁, o₁, sg) ← block ρ o b
    if sg ≠ .normal then pure (scope ρ ρ₁, o₁, sg.exitLoop) else
    let v ← eval ρ₁ c
    if v.isFalse then stat (scope ρ ρ₁) o₁ (.repeat_ b c) else pure (scope ρ ρ₁, o₁, .normal)
  | .stat ρ o (.if_ c t eifs els) => do
    let v ← eval ρ c
    if !v.isFalse then inScope ρ (block ρ o t) else
    match eifs, els with
    | (c', t') :: eifs', _ => stat ρ o (.if_ c' t' eifs' els)
    | [], some b => inScope ρ (block ρ o b)
    | [], none => pure (ρ, o, .normal)
  | .stat ρ o (.fornum x e₁ e₂ e₃ b) => do
    let v₁ ← eval ρ e₁
    let v₂ ← eval ρ e₂
    let v₃ ← eval ρ (Stat.forStep e₃)
    match v₁, v₂, v₃ with
    | .int i, .int l, .int st =>
      if st = 0 then .fail else
      match forCount i l st with
      | none => pure (ρ, o, .normal)
      | some n => forIter ρ o x i st n b
    | _, _, _ => .fail
  | .stat _ _ _ => .fail
  -- statement lists, blocks, `goto`, `for` iterations
  | .list ρ o [] => pure (ρ, o, .normal)
  | .list ρ o (st :: ss) => do
    let (ρ₁, o₁, sg) ← stat ρ o st
    if sg = .normal then execList ρ₁ o₁ ss else pure (ρ₁, o₁, sg)
  | .blockFrom base all ρ o ss => do
    let (ρ₁, o₁, sg) ← execList ρ o ss
    match sg.target all with
    | none => pure (ρ₁, o₁, sg)
    | some (rest, k) => blockFrom base all (jumpEnv base k ρ₁) o₁ rest
  | .block ρ o (.mk ss none) => blockFrom ρ ss ρ o ss
  | .block _ _ (.mk _ (some _)) => .fail
  | .forIter ρ o x i st n b => do
    let (ρ₁, o₁, sg) ← block ((x, .int i) :: ρ) o b
    if sg ≠ .normal ∨ n = 0 then pure (scope ρ ρ₁, o₁, sg.exitLoop)
    else forIter (scope ρ ρ₁) o₁ x (i + st) st (n - 1) b

/-- **`LuaSem H c out`**: the chunk `c` runs to completion printing `out`. -/
def LuaSem (H : Host) (c : Chunk) (out : String) : Prop :=
  ∃ ρ', Sem (rules H) (.block [] "" c) (ρ', out, .normal)

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

/-- F1's operators, with F4-lite's `..` and `#`. -/
def BinOp.inF1 (op : BinOp) : Bool :=
  op.arith.isSome || op.cmp.isSome || op = .eq || op = .ne || op = .and || op = .or ||
    op = .concat

def UnOp.inF1 : UnOp → Bool
  | .neg | .not | .bnot | .len => true

mutual
/-- An F1 expression: `nil`, booleans, integer numerals, string literals,
locals in scope, parentheses, and F1's operators. -/
def supE (bound : List (Name × Attrib)) : Exp → Bool
  | .nil | .false | .true | .numeral (.int _) | .string _ => true
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

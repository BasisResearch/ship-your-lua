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
* **Numeric `for`** (§3.3.5, `forprep`): start, limit and step (default
  the integer 1) are evaluated once; with an integer start and step the
  limit is `forlimit`'s (`forLimit`: a numeral string is coerced, a float
  floored or ceiled, out of range clipped) and the iteration count is
  `forCount`; otherwise all three are converted to floats (`tonumber`) and
  the loop runs `floatforloop`'s float steps (`forIterF`). The control
  variable is a fresh local of each iteration. A zero step is an error: no
  rule.
* **Operators** (§3.4): Lua's operations on values, shared with the
  bytecode semantics: arithmetic on integers and floats (`luaO_rawarith`;
  `//`, `%` floor, integer division by zero an error), bitwise operators on
  integral numbers, order on numbers (`LTnum`) and strings (`l_strcmp` in
  the C locale), `==`/`~=` raw equality (`1 == 1.0`), `..` of strings and
  numbers (`tostring`), `#` of strings, short-circuit `and`/`or`, `not`, and
  the string library's arithmetic metamethods (`"1.5" + 1` is `2.5`). Float
  numerals, `/`, `^`, tables and other metamethods have no rule (or are not
  in `AstSupported`).
-/

namespace Lua.Ast

open Lua.Bytecode (Value Host Builtin printLine forCount forLimit δ)
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

/-- A name: the innermost local, else the global `_ENV.x` (with `_ENV` the
main chunk's upvalue, i.e. no local `_ENV` in scope). -/
def evalName (ρ : Env) (x : Name) : Option Value :=
  match ρ.lookup x with
  | some v => some v
  | none => if ρ.lookup "_ENV" = none then initGlobal x else none

/-! ### Operators: Lua's operations on values

The operators are Lua's operations on values, shared with the bytecode
semantics (`Lua/Bytecode/Semantics.lean`, over the number layer `Lua.Num`):
arithmetic and bitwise operators are `Value.arith` (`lua_arith`: the fast
path on numbers, then the string library's metamethods), order is `δ .lt`/
`δ .le` (`LTnum`/`LEnum`, `l_strcmp`), equality is `Value.rawEq`
(`luaV_equalobj`), `..` is `δ .concat` (`luaV_concat`, `tostring` of
numbers), and the unary operators are `δ .unm`, `δ .bnot`, `δ .len`. -/

-- `l_str2int` is the shared layer's (`Lua/Num/Decimal.lean`).
export Lua.Num (str2int)

/-- The arithmetic and bitwise operators (`lua_arith`'s `LUA_OP*`). -/
def BinOp.toBc : BinOp → Option Lua.Bytecode.BinOp
  | .add => some .add | .sub => some .sub | .mul => some .mul | .div => some .div
  | .idiv => some .idiv | .pow => some .pow | .mod => some .mod
  | .band => some .band | .bxor => some .bxor | .bor => some .bor
  | .shr => some .shr | .shl => some .shl
  | _ => none

/-- The strict binary operators on values (`none`: no rule). `a > b` is
`b < a` and `a >= b` is `b <= a` (manual §3.4.4; `lcode.c` swaps them). -/
def binOp : BinOp → Value → Value → Option Value
  | .eq, va, vb => some (.bool (va.rawEq vb))
  | .ne, va, vb => some (.bool !(va.rawEq vb))
  | .concat, va, vb => δ .concat [va, vb]
  | .lt, va, vb => δ .lt [va, vb]
  | .le, va, vb => δ .le [va, vb]
  | .gt, va, vb => δ .lt [vb, va]
  | .ge, va, vb => δ .le [vb, va]
  | op, va, vb => op.toBc.bind fun o => Value.arith o va vb

/-- The unary operators on values (`none`: no rule). -/
def unOp : UnOp → Value → Option Value
  | .neg, v => δ .unm [v]
  | .bnot, v => δ .bnot [v]
  | .not, v => some (.bool v.isFalse)
  | .len, v => δ .len [v]

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
  count); the control variable is a fresh local of each iteration;
* `forIterF ρ o x v i l st b`: the iterations of a float numeric `for`
  (`forprep`'s float loop, `floatforloop`) with control value `v`, index
  `i`, limit `l` and step `st`. -/
inductive Call where
  | eval (ρ : Env) (e : Exp)
  | stat (ρ : Env) (o : String) (st : Stat)
  | list (ρ : Env) (o : String) (ss : List Stat)
  | blockFrom (base : Env) (all : List Stat) (ρ : Env) (o : String) (ss : List Stat)
  | block (ρ : Env) (o : String) (b : Block)
  | forIter (ρ : Env) (o : String) (x : Name) (i st n : BitVec 64) (b : Block)
  | forIterF (ρ : Env) (o : String) (x : Name) (v : Value) (i l st : Float.Model) (b : Block)

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
def forIterF (ρ : Env) (o : String) (x : Name) (v : Value) (i l st : Float.Model) (b : Block) :
    Rule Outcome :=
  .call (.forIterF ρ o x v i l st b) .ret

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
    | .int i, l, .int st =>
      if st = 0 then .fail else
      match forLimit l st with
      | none => .fail
      | some none => pure (ρ, o, .normal)
      | some (some lim) =>
        match forCount i lim st with
        | none => pure (ρ, o, .normal)
        | some n => forIter ρ o x i st n b
    | i, l, st =>
      match l.tonumber?, st.tonumber?, i.tonumber? with
      | some (.flt fl _), some (.flt fs _), some (.flt fi ni) =>
        if Float.Model.beq fs Lua.Num.zero then .fail
        else if (if Float.Model.lt Lua.Num.zero fs then Float.Model.lt fl fi
                 else Float.Model.lt fi fl) then pure (ρ, o, .normal)
        else forIterF ρ o x (.flt fi ni) fi fl fs b
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
  | .forIterF ρ o x v i l st b => do
    let (ρ₁, o₁, sg) ← block ((x, v) :: ρ) o b
    let idx := Float.Model.add i st
    if sg ≠ .normal ∨ (if Float.Model.lt Lua.Num.zero st then Float.Model.le idx l
                         else Float.Model.le l idx) = false
    then pure (scope ρ ρ₁, o₁, sg.exitLoop)
    else forIterF (scope ρ ρ₁) o₁ x (.ofFloat idx) idx l st b

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

/-- F1's operators, with F4-lite's `..` and `#` (not yet `/` and `^`:
FLOAT-DESIGN.md S3, `luac` folds `^` with the host's `pow`). -/
def BinOp.inF1 : BinOp → Bool
  | .div | .pow => false
  | _ => true

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

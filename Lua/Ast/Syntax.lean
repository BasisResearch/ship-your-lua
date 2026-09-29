import Lua.Bytecode.Semantics

/-!
# Lua source syntax, fragment F1 (Layer B)

A deep embedding of the Lua subset whose bytecode is F1: integer locals,
arithmetic and comparisons, `and`/`or`/`not`, `while`, `repeat`, `if`, numeric
`for`, `break`, and `print(...)` of the global `print`. Later fragments add
tables, functions, strings and metatables (PHASES.md, Layer B).
-/

namespace Lua.Ast

/-- Binary operators of F1. -/
inductive BinOp where
  | add | sub | mul | idiv | mod
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

/-- Expressions of F1. -/
inductive Expr where
  | nil
  | bool (b : Bool)
  | int (i : BitVec 64)
  | var (x : String)
  | binop (op : BinOp) (a b : Expr)
  | neg (a : Expr)
  | not (a : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  deriving Repr

/-- Statements of F1. -/
inductive Stat where
  /-- `local x = e` -/
  | local_ (x : String) (e : Expr)
  /-- `x = e` (to a local) -/
  | assign (x : String) (e : Expr)
  /-- `print(e₁, …, eₙ)` -/
  | print (args : List Expr)
  | while_ (c : Expr) (body : List Stat)
  /-- `repeat body until c` (`c` sees the body's locals) -/
  | repeat_ (body : List Stat) (c : Expr)
  | if_ (c : Expr) (t e : List Stat)
  /-- `for x = start, stop, step do body end` -/
  | numFor (x : String) (start stop step : Expr) (body : List Stat)
  | break_
  deriving Repr

/-- A chunk is a block. -/
abbrev Chunk := List Stat

end Lua.Ast

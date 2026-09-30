import Lua.Bytecode.Semantics

/-!
# Lua 5.4 source syntax (Layer B)

A deep embedding of the complete syntax of Lua 5.4, following the
reference manual's §9 ("The Complete Syntax of Lua",
`vendor/lua-5.4.7/doc/manual.html`) nonterminal by nonterminal:

```
chunk ::= block
block ::= {stat} [retstat]
stat ::=  ';' | varlist '=' explist | functioncall | label | break |
          goto Name | do block end | while exp do block end |
          repeat block until exp |
          if exp then block {elseif exp then block} [else block] end |
          for Name '=' exp ',' exp [',' exp] do block end |
          for namelist in explist do block end |
          function funcname funcbody | local function Name funcbody |
          local attnamelist ['=' explist]
attnamelist ::=  Name attrib {',' Name attrib}
attrib ::= ['<' Name '>']
retstat ::= return [explist] [';']
label ::= '::' Name '::'
funcname ::= Name {'.' Name} [':' Name]
var ::=  Name | prefixexp '[' exp ']' | prefixexp '.' Name
exp ::=  nil | false | true | Numeral | LiteralString | '...' | functiondef |
         prefixexp | tableconstructor | exp binop exp | unop exp
prefixexp ::= var | functioncall | '(' exp ')'
functioncall ::=  prefixexp args | prefixexp ':' Name args
args ::=  '(' [explist] ')' | tableconstructor | LiteralString
functiondef ::= function funcbody
funcbody ::= '(' [parlist] ')' block end
parlist ::= namelist [',' '...'] | '...'
tableconstructor ::= '{' [fieldlist] '}'
field ::= '[' exp ']' '=' exp | Name '=' exp | exp
```

Lists (`varlist`, `explist`, `namelist`, `fieldlist`, `{stat}`) are Lean
`List`s. Operator precedence is the parser's business: the tree is the
parse. Parentheses are kept (`prefixexp ::= '(' exp ')'`, which also
truncates multiple results), as are `;` statements and labels.

Two attributes are allowed (lparser.c `getlocalattribute` rejects any other
name). A `Numeral` is an integer (`lua_Integer`, 64-bit two's complement) or a
float (its IEEE-754 bits). A `LiteralString` is its bytes after escape
processing.

`scripts/gen_ast.py` parses `.lua` files into this syntax, following
`llex.c`/`lparser.c`, including lparser's static errors (`goto`/label
visibility, `<const>` assignment, `...` outside a vararg function). Which
programs have rules in the semantics is `AstSupported`
(`Lua/Ast/Semantics.lean`), not the syntax.
-/

namespace Lua.Ast

/-- `Name`: an identifier (ASCII letters, digits and `_`, not starting with
a digit, not a reserved word). -/
abbrev Name := String

/-- `LiteralString`: the bytes of a string literal. -/
abbrev LiteralString := List UInt8

/-- `Numeral`: an integer, or a float given by its IEEE-754 binary64 bits. -/
inductive Numeral where
  | int (i : BitVec 64)
  | float (bits : BitVec 64)
  deriving DecidableEq, Repr

/-- `attrib ::= ['<' Name '>']`: none, `<const>` or `<close>`. -/
inductive Attrib where
  | reg
  | const
  | close
  deriving DecidableEq, Repr

/-- One entry of `attnamelist`: `Name attrib`. -/
structure AttName where
  name : Name
  attrib : Attrib
  deriving DecidableEq, Repr

/-- `binop`: `+ - * / // ^ % & ~ | >> << .. < <= > >= == ~= and or`. -/
inductive BinOp where
  | add | sub | mul | div | idiv | pow | mod
  | band | bxor | bor | shr | shl
  | concat
  | lt | le | gt | ge | eq | ne
  | and | or
  deriving DecidableEq, Repr

/-- `unop`: `- not # ~`. -/
inductive UnOp where
  | neg | not | len | bnot
  deriving DecidableEq, Repr

/-- `funcname ::= Name {'.' Name} [':' Name]`. -/
structure FuncName where
  name : Name
  fields : List Name
  method : Option Name
  deriving DecidableEq, Repr

mutual
/-- `exp`. -/
inductive Exp where
  | nil
  | false
  | true
  | numeral (n : Numeral)
  | string (s : LiteralString)
  /-- `...` -/
  | vararg
  /-- `functiondef ::= function funcbody` -/
  | functiondef (f : FuncBody)
  | prefixexp (p : PrefixExp)
  | tableconstructor (fields : List Field)
  | binop (op : BinOp) (a b : Exp)
  | unop (op : UnOp) (a : Exp)
  deriving Repr

/-- `prefixexp ::= var | functioncall | '(' exp ')'`. -/
inductive PrefixExp where
  | var (v : Var)
  | functioncall (c : FunctionCall)
  | paren (e : Exp)
  deriving Repr

/-- `var ::= Name | prefixexp '[' exp ']' | prefixexp '.' Name`. -/
inductive Var where
  | name (x : Name)
  | index (p : PrefixExp) (k : Exp)
  | field (p : PrefixExp) (x : Name)
  deriving Repr

/-- `functioncall ::= prefixexp args | prefixexp ':' Name args`. -/
inductive FunctionCall where
  | call (f : PrefixExp) (args : Args)
  | method (o : PrefixExp) (m : Name) (args : Args)
  deriving Repr

/-- `args ::= '(' [explist] ')' | tableconstructor | LiteralString`. -/
inductive Args where
  | explist (es : List Exp)
  | tableconstructor (fields : List Field)
  | string (s : LiteralString)
  deriving Repr

/-- `field ::= '[' exp ']' '=' exp | Name '=' exp | exp`. -/
inductive Field where
  | index (k v : Exp)
  | name (x : Name) (v : Exp)
  | exp (v : Exp)
  deriving Repr

/-- `funcbody ::= '(' [parlist] ')' block end`, with
`parlist ::= namelist [',' '...'] | '...'`. -/
inductive FuncBody where
  | mk (params : List Name) (isVararg : Bool) (body : Block)
  deriving Repr

/-- `stat`. -/
inductive Stat where
  /-- `;` -/
  | semi
  /-- `varlist '=' explist` -/
  | assign (vars : List Var) (exps : List Exp)
  | functioncall (c : FunctionCall)
  /-- `label ::= '::' Name '::'` -/
  | label (x : Name)
  | break_
  | goto_ (x : Name)
  | do_ (b : Block)
  | while_ (c : Exp) (b : Block)
  | repeat_ (b : Block) (c : Exp)
  /-- `if exp then block {elseif exp then block} [else block] end` -/
  | if_ (c : Exp) (t : Block) (elseifs : List (Exp × Block)) (else_ : Option Block)
  /-- `for Name '=' exp ',' exp [',' exp] do block end` -/
  | fornum (x : Name) (start limit : Exp) (step : Option Exp) (b : Block)
  /-- `for namelist in explist do block end` -/
  | forin (xs : List Name) (es : List Exp) (b : Block)
  /-- `function funcname funcbody` -/
  | function_ (n : FuncName) (f : FuncBody)
  /-- `local function Name funcbody` -/
  | localfunction (x : Name) (f : FuncBody)
  /-- `local attnamelist ['=' explist]` (`[]` when there is no `=`; an
  `explist` is never empty) -/
  | local_ (vars : List AttName) (exps : List Exp)
  deriving Repr

/-- `block ::= {stat} [retstat]`, with `retstat ::= return [explist] [';']`. -/
inductive Block where
  | mk (stats : List Stat) (retstat : Option (List Exp))
  deriving Repr
end

/-- `chunk ::= block`. -/
abbrev Chunk := Block

end Lua.Ast

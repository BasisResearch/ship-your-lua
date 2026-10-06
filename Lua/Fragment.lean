import Lua.Bytecode.Semantics

/-!
# Fragments: which programs Layer A covers, and the ledger of the rest

`Supported p` is the hypothesis of `vm_refinement` (Layer A). It is a
decidable check on a `Proto` with three parts:

1. **Opcodes.** Every instruction has a kernel (`kernel`, the opcode table
   of `Lua/Bytecode/Semantics.lean`), whose existence carries the operand
   side conditions (e.g. `GETTABUP` only of `_ENV.print`, `LOADK` only of
   non-float constants, `CALL` with fixed argument and result counts), or
   is a `RETURN*`. Every opcode without a kernel is in `ledger`, with the
   fragment that brings it in. The kernels also cover a strings slice of F4
   (literals, `CONCAT`, `LEN` and order on strings, string arithmetic
   through `MMBIN*`: abstractions/pilot/SUITE.md H1–H5).
2. **Well-formedness.** Lua 5.4 does not verify loaded bytecode
   (`lundump.c` checks only the header), so `luaV_execute` on a malformed
   `Proto` is undefined behaviour. `Supported` requires in-range edge
   targets and register operands (`< maxstacksize`), and no fall-through
   off the end.
3. **Definite initialisation.** At `luaV_execute`'s entry the frame's
   registers hold whatever the stack held, and a `CALL` clobbers every
   register above its results. `BcSem` says ⊥ for both (the entry state and
   the call's kill ports), and reading ⊥ is stuck. The check is the forward
   must-analysis `st[t] ⊆ (st[pc] \ kill) ∪ def` over the kernels' edges
   (bit masks over the 256 registers, fixpoint by iteration, rejecting if no
   fixpoint within fuel), with every read port in the mask. `luac` output
   satisfies it. `Lua/FragmentSound.lean` proves it sound by the generic
   certain-answers theorem: `bcSemFrom_iff` (entry registers are
   unobservable) and `cbcSem_iff` (so are all kill ports).

`reads`, `regTop` and `edges` are folds of the kernel, not tables.

`Supported whileProto` is checked by the kernel in `Lua/Programs/Supported.lean`.
-/

namespace Lua.Bytecode

/-- Fragments, in the planned order (README.md, PHASES.md). -/
inductive Fragment where
  /-- integers, moves, constants, integer arithmetic, integer bitwise
  operators (the former F1b, phase A2), compare+jump, numeric for, return,
  `print` -/
  | F1
  /-- tables, `next` order, global writes, generic `for` over `pairs` -/
  | F2
  /-- closures, upvalues, Lua calls, varargs, multiple results, tail calls -/
  | F3
  /-- strings, `..`, metatables and metamethods, to-be-closed variables -/
  | F4
  /-- floats and `%.14g` -/
  | Float
  /-- coroutines (and `longjmp` across `lua_resume`) -/
  | Coroutine
  deriving DecidableEq, Repr

/-- The fragment that brings each opcode in. -/
def OpCode.fragment : OpCode → Fragment
  | .MOVE | .LOADI | .LOADK | .LOADFALSE | .LFALSESKIP | .LOADTRUE | .LOADNIL
  | .GETTABUP
  | .ADDI | .ADDK | .SUBK | .MULK | .MODK | .IDIVK
  | .ADD | .SUB | .MUL | .MOD | .IDIV
  | .MMBIN | .MMBINI | .MMBINK
  | .UNM | .NOT | .JMP
  | .EQ | .LT | .LE | .EQK | .EQI | .LTI | .LEI | .GTI | .GEI | .TEST | .TESTSET
  | .CALL | .RETURN | .RETURN0 | .RETURN1 | .FORLOOP | .FORPREP | .VARARGPREP
  | .BANDK | .BORK | .BXORK | .SHRI | .SHLI | .BAND | .BOR | .BXOR | .SHL | .SHR
  | .BNOT => .F1
  | .LOADKX | .EXTRAARG | .GETTABLE | .GETI | .GETFIELD | .SETTABUP | .SETTABLE | .SETI
  | .SETFIELD | .NEWTABLE | .SETLIST | .LEN | .TFORPREP | .TFORCALL | .TFORLOOP => .F2
  | .GETUPVAL | .SETUPVAL | .CLOSE | .CLOSURE | .TAILCALL | .VARARG | .SELF => .F3
  | .CONCAT | .TBC => .F4
  | .LOADF | .POWK | .DIVK | .POW | .DIV => .Float

/-- **The ledger of opcodes outside F1**, each with its fragment and what it
needs. (F1b, integer bitwise, is merged into F1: phase A2.) (`Coroutine` brings in no opcode: coroutines are library calls.) -/
def ledger : List (OpCode × Fragment × String) :=
  [ (.LOADKX, .F2, "constant tables above 2^17 entries (with EXTRAARG)"),
    (.EXTRAARG, .F2, "operand extension for LOADKX/NEWTABLE/SETLIST"),
    (.GETTABLE, .F2, "table read (luaH_get, luaV_finishget)"), (.GETI, .F2, "table read, integer key"),
    (.GETFIELD, .F2, "table read, short-string key"), (.SETTABUP, .F2, "global write (_ENV table)"),
    (.SETTABLE, .F2, "table write (luaH_newkey, rehash)"), (.SETI, .F2, "table write, integer key"),
    (.SETFIELD, .F2, "table write, short-string key"), (.NEWTABLE, .F2, "table allocation"),
    (.SETLIST, .F2, "table constructor"), (.LEN, .F2, "length (luaH_getn border)"),
    (.TFORPREP, .F2, "generic for"), (.TFORCALL, .F2, "generic for: iterator call (next)"),
    (.TFORLOOP, .F2, "generic for"),
    (.GETUPVAL, .F3, "upvalue read"), (.SETUPVAL, .F3, "upvalue write (barrier)"),
    (.CLOSE, .F3, "close upvalues (luaF_close)"), (.CLOSURE, .F3, "closure creation (luaF_newLclosure)"),
    (.TAILCALL, .F3, "tail call (luaD_pretailcall)"), (.VARARG, .F3, "varargs"),
    (.SELF, .F3, "method call"),
    (.CONCAT, .F4, "string concatenation (luaV_concat, string interning)"),
    (.TBC, .F4, "to-be-closed variable (__close)"),
    (.LOADF, .Float, "float literal"), (.POWK, .Float, "pow (always float)"),
    (.DIVK, .Float, "float division"), (.POW, .Float, "pow (always float)"),
    (.DIV, .Float, "float division") ]

/-- The ledger lists exactly the non-F1 opcodes. -/
theorem ledger_exact :
    ∀ o ∈ OpCode.all, (o.fragment ≠ .F1 ↔ o ∈ ledger.map (·.1)) := by decide

/-- Every ledger entry's fragment is its opcode's fragment. -/
theorem ledger_fragment : ∀ e ∈ ledger, e.1.fragment = e.2.1 := by decide

theorem ledger_length : ledger.length = 29 := rfl

/-! ## Register sets as bit masks -/

/-- Registers `a, …, a+n-1` as a mask. -/
def rmask (a n : Nat) : Nat := (2 ^ n - 1) * 2 ^ a

/-- All 256 registers. -/
def allRegs : Nat := 2 ^ 256 - 1

/-- `s ⊆ t` on masks. -/
def msub (s t : Nat) : Bool := s &&& t == s

/-- The registers of a list, as a mask. -/
def listMask (l : List Nat) : Nat := l.foldr (fun r m => rmask r 1 ||| m) 0

/-- `s \ t` on masks. -/
def mdiff (s t : Nat) : Nat := s ^^^ (s &&& t)

/-! ## Per-instruction facts: folds of the kernel -/

/-- An edge as the analysis sees it: target, def mask, kill mask. -/
abbrev Edge := Nat × Nat × Nat

/-- The analysis view of a kernel edge. -/
def KEdge.toEdge (e : KEdge) : Edge := (e.tgt, listMask e.defs, rmask e.killLo e.killN)

/-- Highest register index a kernel touches, plus one. -/
def Kernel.regTop {V : Type} (K : Kernel V) : Nat :=
  let top (l : List Nat) := l.foldr (fun r m => max (r + 1) m) 0
  K.edges.foldr (fun e m => max (max (top e.defs) (e.killLo + e.killN)) m) (top K.reads)

section
variable (p : Proto)

/-- Registers an instruction reads (its kernel's read ports), as a mask. -/
def reads (pc : Nat) (w : Word) : Nat := ((kernel p pc w).map fun K => listMask K.reads).getD 0

/-- Highest register index an instruction touches, plus one (0 if none). -/
def regTop (pc : Nat) (w : Word) : Nat := ((kernel p pc w).map Kernel.regTop).getD 0

/-- Instructions with no successor: `RETURN*`. -/
def noSucc (w : Word) : Bool :=
  match w.op? with
  | some .RETURN | some .RETURN0 | some .RETURN1 => true
  | _ => false

/-- Outgoing edges of the instruction at `pc` (its kernel's edges), `none`
if it has no kernel (outside the fragment, or a side condition fails) or a
target is out of range. No target is pc 0: the entry instruction
(`OP_VARARGPREP` in every main chunk `luac` emits) runs once, at the entry
state (`DefInit.pc_pos`). -/
def edges (pc : Nat) : Option (List Edge) :=
  match p.fetch pc with
  | none => none
  | some w =>
    match kernel p pc w with
    | some K =>
      if K.edges.all (fun e => decide (0 < e.tgt ∧ e.tgt < p.code.length)) then
        some (K.edges.map KEdge.toEdge)
      else none
    | none => if noSucc w then some [] else none

/-- One sweep of the must-initialised analysis:
`st[t] := st[t] ∩ ((st[pc] \ kill) ∪ def)` over edges `pc → t`. Entry (pc 0)
stays empty. -/
def sweep (es : List (List Edge)) (st : List Nat) : List Nat :=
  let upd (st : List Nat) (pc : Nat) : List Nat :=
    (es.getD pc []).foldl (fun st (t, d, k) =>
      if t = 0 then st
      else st.set t (st.getD t 0 &&& (mdiff (st.getD pc 0) k ||| d))) st
  (List.range es.length).foldl upd st

/-- Iterate `sweep` to a fixpoint within `fuel` rounds. -/
def fixpoint (es : List (List Edge)) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, st =>
    let st' := sweep es st
    if st' == st then some st else fixpoint es fuel st'

/-- **Support check.** -/
def supportedB : Bool :=
  let n := p.code.length
  p.protos.isEmpty && 0 < n && p.maxstacksize ≤ 255 &&
  match (List.range n).mapM (edges p) with
  | none => false
  | some es =>
    (List.range n).all (fun pc => match p.fetch pc with
      | some w => regTop p pc w ≤ p.maxstacksize
      | none => false) &&
    match fixpoint es (2 * n + 2) (0 :: List.replicate (n - 1) allRegs) with
    | none => false
    | some st =>
      (List.range n).all fun pc => match p.fetch pc with
        | some w => msub (reads p pc w) (st.getD pc 0)
        | none => false

end

/-- **`Supported p`**: `p` is a well-formed, definitely-initialising F1
main chunk (see the module docstring). -/
def Supported (p : Proto) : Prop := supportedB p = true

instance (p : Proto) : Decidable (Supported p) := inferInstanceAs (Decidable (_ = true))

end Lua.Bytecode

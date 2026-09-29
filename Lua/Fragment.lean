import Lua.Bytecode.Semantics

/-!
# Fragments: which programs Layer A covers, and the ledger of the rest

`Supported p` is the hypothesis of `vm_refinement` (Layer A). It is a
decidable check on a `Proto` with three parts:

1. **Opcodes.** Every instruction is an F1 opcode (`OpCode.fragment = .F1`),
   with F1's operand side conditions (e.g. `GETTABUP` only of `_ENV.print`,
   `LOADK` only of non-float, non-string constants, `CALL` with fixed
   argument and result counts). Every other opcode is in `ledger`, with the
   fragment that brings it in.
2. **Well-formedness.** Lua 5.4 does not verify loaded bytecode
   (`lundump.c` checks only the header), so `luaV_execute` on a malformed
   `Proto` is undefined behaviour. `Supported` requires in-range jump
   targets, constant indices, register operands (`< maxstacksize`), a
   conditional test followed by an instruction to take the jump from, and no
   fall-through off the end.
3. **Definite initialisation.** At `luaV_execute`'s entry the frame's
   registers hold whatever the stack held (`luaL_requiref` and
   `VARARGPREP` leave stale values above `top`), and a `CALL` clobbers every
   register from its base up except its results. `BcSem` starts from all-`nil`
   registers and leaves registers unchanged across `print`; the two agree
   exactly on programs that never read a register before writing it on every
   path. The check is that forward must-analysis (bit masks over the 256
   registers, fixpoint by iteration, rejecting if no fixpoint within fuel).
   `luac` output satisfies it. `Lua/FragmentSound.lean` proves it sound:
   `bcSemFrom_iff` (entry registers are unobservable) and `cbcSem_iff` (so
   is what a call leaves above its results).

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

/-! ## Per-instruction facts -/

/-- A control-flow edge: target pc and the registers written along it. -/
abbrev Edge := Nat × Nat

section
variable (p : Proto)

/-- Registers an F1 instruction reads (as a mask), on any path. -/
def reads (w : Word) : Nat :=
  match w.op? with
  | some .MOVE | some .UNM | some .NOT | some .TESTSET | some .BNOT => rmask w.b 1
  | some .ADD | some .SUB | some .MUL | some .MOD | some .IDIV
  | some .BAND | some .BOR | some .BXOR | some .SHL | some .SHR => rmask w.b 1 ||| rmask w.c 1
  | some .ADDI | some .ADDK | some .SUBK | some .MULK | some .MODK | some .IDIVK
  | some .BANDK | some .BORK | some .BXORK | some .SHRI | some .SHLI => rmask w.b 1
  | some .EQ | some .LT | some .LE => rmask w.a 1 ||| rmask w.b 1
  | some .EQK | some .EQI | some .LTI | some .LEI | some .GTI | some .GEI | some .TEST =>
    rmask w.a 1
  | some .FORPREP | some .FORLOOP => rmask w.a 3
  | some .CALL => rmask w.a w.b
  | _ => 0

/-- Highest register index an instruction touches, plus one (0 if none). -/
def regTop (w : Word) : Nat :=
  match w.op? with
  | some .MOVE | some .UNM | some .NOT | some .TESTSET | some .BNOT => max (w.a + 1) (w.b + 1)
  | some .ADD | some .SUB | some .MUL | some .MOD | some .IDIV
  | some .BAND | some .BOR | some .BXOR | some .SHL | some .SHR =>
    max (w.a + 1) (max (w.b + 1) (w.c + 1))
  | some .ADDI | some .ADDK | some .SUBK | some .MULK | some .MODK | some .IDIVK
  | some .BANDK | some .BORK | some .BXORK | some .SHRI | some .SHLI =>
    max (w.a + 1) (w.b + 1)
  | some .EQ | some .LT | some .LE => max (w.a + 1) (w.b + 1)
  | some .LOADNIL => w.a + w.b + 1
  | some .FORPREP | some .FORLOOP => w.a + 4
  | some .CALL => max (w.a + w.b) (w.a + w.c - 1)
  | some .RETURN | some .RETURN0 | some .RETURN1 | some .VARARGPREP | some .JMP => 0
  | some .MMBIN | some .MMBINI | some .MMBINK => 0
  | _ => w.a + 1

/-- The target of the jump that follows a test at `pc` (`donextjump`: the
`JMP` at `pc + 1`, relative to `pc + 2`). -/
def nextJump (pc : Nat) : Option Nat :=
  (p.fetch (pc + 1)).bind fun ni => jumpTo (pc + 2) ni.sj

/-- Edges of a conditional test (`docondjump`): skip the jump, or take it. -/
def condEdges (pc : Nat) : Option (List Edge) :=
  (nextJump p pc).map fun t => [(pc + 2, 0), (t, 0)]

/-- Outgoing edges of the instruction `w` (opcode `o`) at `pc`, before the
range check: (successor, registers written on that edge). `none` if the
instruction is not F1, violates an F1 side condition, or jumps before 0.
RETURNs and never-executed `MMBIN*` have no edges. -/
def edgesOf (pc : Nat) (w : Word) : OpCode → Option (List Edge)
  | .MOVE | .LOADI | .LOADFALSE | .LOADTRUE | .UNM | .NOT | .BNOT =>
    some [(pc + 1, rmask w.a 1)]
  | .LOADK =>
    match p.const w.bx with
    | some (.int _) | some (.bool _) | some .nil => some [(pc + 1, rmask w.a 1)]
    | _ => none
  | .LFALSESKIP => some [(pc + 2, rmask w.a 1)]
  | .LOADNIL => some [(pc + 1, rmask w.a (w.b + 1))]
  | .GETTABUP =>
    if w.b = 0 ∧ p.const w.c = some (.str printKey) then some [(pc + 1, rmask w.a 1)]
    else none
  | .ADD | .SUB | .MUL | .MOD | .IDIV | .ADDI
  | .BAND | .BOR | .BXOR | .SHL | .SHR | .SHRI | .SHLI => some [(pc + 2, rmask w.a 1)]
  | .ADDK | .SUBK | .MULK | .MODK | .IDIVK | .BANDK | .BORK | .BXORK =>
    match p.const w.c with
    | some (.int _) => some [(pc + 2, rmask w.a 1)]
    | _ => none
  | .MMBIN | .MMBINI | .MMBINK => some []
  | .JMP => (jumpTo (pc + 1) w.sj).map fun t => [(t, 0)]
  | .EQK =>
    match p.const w.b with
    | some (.float _) | none => none
    | _ => condEdges p pc
  | .EQ | .LT | .LE | .EQI | .LTI | .LEI | .GTI | .GEI | .TEST => condEdges p pc
  | .TESTSET => (nextJump p pc).map fun t => [(pc + 2, 0), (t, rmask w.a 1)]
  | .FORPREP =>
    some [(pc + 1, rmask (w.a + 1) 1 ||| rmask (w.a + 3) 1), (pc + 1 + w.bx + 1, rmask (w.a + 3) 1)]
  | .FORLOOP =>
    (jumpTo (pc + 1) (-(w.bx : Int))).map fun t =>
      [(pc + 1, 0), (t, rmask w.a 2 ||| rmask (w.a + 3) 1)]
  | .CALL => if w.b ≠ 0 ∧ w.c ≠ 0 then some [(pc + 1, rmask w.a (w.c - 1))] else none
  | .RETURN | .RETURN0 | .RETURN1 => some []
  | .VARARGPREP => some [(pc + 1, 0)]
  | _ => none

/-- Outgoing edges of the instruction at `pc` (`edgesOf`), `none` also if a
target is out of range. -/
def edges (pc : Nat) : Option (List Edge) :=
  match p.fetch pc with
  | none => none
  | some w =>
    match w.op? with
    | none => none
    | some o =>
      match edgesOf p pc w o with
      | none => none
      | some l => if l.all (fun e => decide (e.1 < p.code.length)) then some l else none

/-- Registers a CALL at `pc` leaves defined below its base: everything a
call clobbers (base and above) is removed on its edge before its results are
added. -/
def keepMask (pc : Nat) : Nat :=
  match (p.fetch pc).bind Word.op?, p.fetch pc with
  | some .CALL, some w => rmask 0 w.a
  | _, _ => allRegs

/-- One sweep of the must-initialised analysis: `st[t] := st[t] ∩ ⋂ (st[pc] ∩ keep ∪ written)`
over edges `pc → t`. Entry (pc 0) stays empty. -/
def sweep (es : List (List Edge)) (st : List Nat) : List Nat :=
  let upd (st : List Nat) (pc : Nat) : List Nat :=
    (es.getD pc []).foldl (fun st (t, wr) =>
      if t = 0 then st
      else st.set t (st.getD t 0 &&& ((st.getD pc 0 &&& keepMask p pc) ||| wr))) st
  (List.range es.length).foldl upd st

/-- Iterate `sweep` to a fixpoint within `fuel` rounds. -/
def fixpoint (es : List (List Edge)) : Nat → List Nat → Option (List Nat)
  | 0, _ => none
  | fuel + 1, st =>
    let st' := sweep p es st
    if st' == st then some st else fixpoint es fuel st'

/-- **F1 support check.** -/
def supportedB : Bool :=
  let n := p.code.length
  p.protos.isEmpty && 0 < n && p.maxstacksize ≤ 255 &&
  match (List.range n).mapM (edges p) with
  | none => false
  | some es =>
    (List.range n).all (fun pc => match p.fetch pc with
      | some w => (w.op?.map OpCode.fragment) == some .F1 && regTop w ≤ p.maxstacksize
      | none => false) &&
    match fixpoint p es (2 * n + 2) (0 :: List.replicate (n - 1) allRegs) with
    | none => false
    | some st =>
      (List.range n).all fun pc => match p.fetch pc with
        | some w => msub (reads w) (st.getD pc 0)
        | none => false

end

/-- **`Supported p`**: `p` is a well-formed, definitely-initialising F1
main chunk (see the module docstring). -/
def Supported (p : Proto) : Prop := supportedB p = true

instance (p : Proto) : Decidable (Supported p) := inferInstanceAs (Decidable (_ = true))

end Lua.Bytecode

# Brief for ontologists (abstraction-discovery round 1)

You are proposing new PROOF ABSTRACTIONS: new logics, representations or
rules. A proof project's cost per case is rising, and your job is to change
the concepts its proofs are written in so that whole clusters of obligations
become one proved rule each. You are judged later by a measured bake-off, not
by argument.

## The project

The project proves in Lean 4 that a bare-metal RISC-V build of the Lua 5.4.7
interpreter refines a formal semantics, in two layers:

```
LuaSem s out  ↔  BcSem (compile s) out  ↔  Halts c out 0
 (source big-step)   (bytecode small-step)   (Sail RISC-V machine)
```

You may read these SEMANTICS files (definitions only):
- `Lua/Bytecode/Semantics.lean`: `Value`, `State` (pc, registers `Nat → Value`,
  output), and `Step`, an inductive small-step relation with one constructor per
  opcode case, transcribed from `lvm.c`. `BcSem` is reachability of a return.
- `Lua/Fragment.lean`: the fragment check `Supported`. It is a per-opcode table
  of control-flow edges with the registers written on each edge, the registers
  read, and a dataflow "definite initialisation" analysis.
- `Lua/Ast/Syntax.lean`, `Lua/Ast/Semantics.lean`: the full Lua 5.4 syntax and
  `LuaSem`, a big-step relation (mutual inductives over statements, blocks, loops,
  goto) with rules for the integer fragment.
- `Lua/Theorems.lean`: the theorem statements.
- `abstractions/ROUND-1.md` §1–2: the obligation census and the four LAWS.
- `abstractions/pilot/SUITE.md`: the held-out pilot suite.

You may NOT read any proof file (`Lua/Bytecode/Exec.lean`,
`Lua/FragmentSound.lean`, `Lua/Ast/Exec.lean`, `Lua/Ast/Determinism.lean`,
`Lua/Compile/*`, `Lua/Programs/*`, `Vsa/**`, `VsaIris/**`), git history, or other
agents' output. Don't look at them even if you think it would help: blindness is
the point.

## What is costly (from the census)

- **Per bytecode rule.** Every rule of `Step` is re-proved in 3 theorems:
  - that an executable stepper is sound for the rule;
  - that the stepper is complete for it;
  - that two states agreeing on the rule's read registers step alike (for the
    definite-initialisation soundness).

  On top of that come the rule's definitions in about 5 places. The per-case
  cost rose from 1.4 to 8.3 lines, averaging 8.5 per rule over 39 rules, and
  growing with every fragment.
- **Per source construct.** Every construct is re-proved in an executable
  interpreter's soundness and in determinism, by pairwise inversion of the
  rules that share a construct. The per-case cost doubled, from 2.3 to 4.6 lines.
- **Next.** Every bytecode rule will also need a proof that the corresponding
  arm of the compiled C function `luaV_execute` (4,020 RISC-V instructions,
  one jump-table dispatch) simulates it. That cost is unmeasured here; the
  predecessor project spent months on the equivalent per-site proofs.

## The laws (each should become ONE proved rule)

- **L-B1, footprint:** an instruction's effect depends only on the registers it
  reads; it writes only its edge's write set; it lands only on its listed edges.
- **L-B2:** the executable stepper IS the semantics: `Step ↔ step? = some`.
- **L-A1:** the source semantics is the graph of a function (determinism,
  soundness and completeness at once).
- **L-C1:** every machine arm simulates its rule, from dispatch head to
  dispatch head.

All four passed cheap checks: random testing and differential runs against
native Lua.

## Forbidden vocabulary

You may not propose the current primitives or tools as the answer:
- per-rule hand-written cases;
- an executable stepper or interpreter plus a separately proved soundness
  theorem;
- per-opcode tables maintained beside the relation;
- per-site or per-instruction lemma batteries, per-word decode lemmas, or
  generator scripts that emit per-case lemmas;
- "segments", "bridges", "sites";
- SMT solvers, Houdini, fuzzers, model checkers, or proof search as the
  abstraction. Tools may check laws; they are not abstractions.

## Your output contract

Return **5 abstractions**, in this shape for each:

1. **Name.**
2. **The idea:** the new concept, logic or representation the proofs would be
   written in.
3. **Core rules:** which LAW becomes which single proved rule, and its
   statement.
4. **What it makes free:** which census obligations disappear, and why.
5. **What it costs:** the setup, and what gets harder.
6. **Theories:** at least TWO theories from DISTANT fields that it draws on
   (databases, concurrency, compilers, category theory, economics, physics,
   linguistics, biology…), with the specific result or construction, marked
   *known* (give a citation you are confident of) or *novel*.
7. **Pilot:** how you'd demonstrate it on the held-out suite (strings: H1–H4)
   and on the refactor targets, with the smallest thing to build.
8. **Seed:** which part of your seed drove it.

Prefer depth and specificity over safe coverage. Mark anything recalled from
memory that should be checked.

# Brief for ontologists (abstraction-discovery round 4: the kit's hidden costs, A1)

You are proposing new PROOF ABSTRACTIONS: new logics, representations or rules. Change the concepts the proofs are written in, so that each of the costly clusters below becomes ONE proved rule. A measured bake-off judges you later, not argument.

## The project

The project proves in Lean 4 that the RISC-V machine code of `luaV_execute` (the C bytecode interpreter of Lua 5.4.7, compiled by GCC for rv64i) refines a formal bytecode semantics, on the Sail RISC-V model.
- There is one dispatch head that fetches an instruction and jumps through a table, then one "arm" of machine code per opcode, which jumps back to the head.
- Arms call helper functions: `__muldi3`, `__moddi3`, `luaV_equalobj`, `luaV_tointeger`, `memcmp`, `strcmp`, ….
- For each opcode, the obligation is:

```
sim_X : Supported p → VmRel p c s → fetch/opcode = X → Step p s s'
        → ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'
```

The current route (adopted in round 3, "the kit") already makes the ordinary case cheap: about 4 hand lines per path.
- It evaluates the kernel forward, branches on tag lemmas over the value representation, and chains straight-line machine runs by name.
- It closes the relation once on final memory, and calls helpers through a summary rule.

It has four costs it cannot express, and they block the remaining arms. This round is about those four.

**You may read** (definitions, statements and cost reports only):
- `Lua/Bytecode/Semantics.lean`, `Lua/Bytecode/Kernel.lean`: the kernel terms and δ.
- `Lua/Vm/Sim/Rel.lean`: `VmRel` (`Win`, `Scratch`, `Core`, `ValRepr`, `TStringRepr`, the intern map `ι`).
- `Lua/Vm/Loaded.lean`, `Lua/Vm/Runtime.lean`.
- `abstractions/ROUND-3.md` and `abstractions/ROUND-4.md`: the census, the laws and their checks.
- `abstractions/bakeoff3/KIT.md` and `abstractions/ledger/kit-arms-{1,2}.md`: how the kit works and what cost the most.
- `Vsa/Sim/DeriveLoop.lean`: the existing generic loop combinator, which the kit does not use.
- The disassembly (`~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump -d c/lua-riscv-htif.elf`), and `vendor/lua-5.4.7/src/*.c`.

**You may NOT read** proof files (`Lua/Vm/Sim/Kit/*.lean`, `Lua/Vm/Sim/Arms/*`, `Lua/Vm/Arms/*`), generator scripts, `abstractions/pilot/*` other than this brief, git history, or other agents' output.

## What is costly (census, ROUND-4.md §1)

1. **C-loop.** Each machine loop (`__muldi3`'s shift-add, `__udivdi3`'s two, LOADNIL's slot loop) is proved by a hand-written induction with its own invariant: 20–60 lines each. `memcmp`, `strcmp`/`strlen`, table walks and the stdio chain will bring many more.
2. **C-call.** At every helper call and return, the machine state (the caller's live registers and its frame) is written out by hand. The generator's liveness pass already knows it.
3. **C-budget.** Lean's default per-declaration elaboration budget (200k heartbeats; raising it is forbidden) forces paths to be split by hand at arbitrary points, with a hand-stated intermediate state. FORPREP does not fit at all. Disjunctive separation facts multiply the arithmetic-tactic cost by about 4.
4. **C-str.** A register's string bytes, and the `'\0'` after them, are outside what `VmRel` relates. So EQ/EQK on long strings (`memcmp`), LT/LE on strings (`strcmp`/`strcoll`) and UNM on numeric strings are left as named premises.

## The laws (ROUND-4.md §2, with check results in §2b)

- **L4-loop:** one loop rule over chained machine runs, given an invariant and a measure.
- **L4-call:** a call's frame is derivable from the call site, never stated.
- **L4-split:** provability composes at run boundaries, at no extra statement cost.
- **L4-str:** no F1 arm store touches an existing string's bytes or terminator, so string content is invariant along a run.

## Forbidden vocabulary (not acceptable as the answer)

- a hand-written induction per loop;
- a hand-written frame statement per call site;
- hand-chosen split points per arm;
- a named premise per string arm;
- one relation field per resource;
- one hand-written contract per helper;
- raising `maxHeartbeats`/`maxRecDepth`;
- generator scripts that emit per-arm proofs;
- SMT, fuzzers, model checkers or proof search as the abstraction (tools may only check laws).

## Output contract: 5 abstractions

For each:

1. **Name.**
2. **The idea.**
3. **Core rules:** which law becomes which single proved rule.
4. **What it makes free:** which census instances disappear.
5. **What it costs:** setup, and what gets harder.
6. **Theories:** two or more from DISTANT fields, marked known (with a citation) or novel.
7. **Pilot.** The held-out cases are:
   - FORPREP (two calls, the budget);
   - IDIV (two helpers, the budget);
   - EQ on two long strings (`memcmp` loop + C-str);
   - LT on two strings (`strcmp` loops + C-str).

   Refactors: LOADNIL (loop) and MODK (split + call frame). Give the smallest thing to build.
8. **Seed:** which part of your seed drove it.

Prefer depth and specificity over safe coverage. Mark anything recalled from memory for checking.

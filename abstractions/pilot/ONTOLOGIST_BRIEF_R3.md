# Brief for ontologists (abstraction-discovery round 3: machine arms, A1)

You are proposing new PROOF ABSTRACTIONS: new logics, representations or
rules. A proof project's per-case cost is rising. Change the concepts its
proofs are written in, so that whole clusters of obligations become one
proved rule each. A measured bake-off judges you later, not argument.

## The project

The project proves in Lean 4 that the RISC-V machine code of `luaV_execute`
(the C bytecode interpreter of Lua 5.4.7, compiled by GCC for rv64i) refines
a formal bytecode semantics, on the Sail RISC-V model. The layer here is
Layer A's arm simulation. The machine loop has:

- **one dispatch head:** it fetches a 32-bit instruction, then `jr` through
  an 82-entry jump table;
- **one "arm" of machine code per opcode:** 4,020 instructions in total;
- **the return:** each arm jumps back to the head.

For each opcode, the obligation is:

```
sim_X : Supported p → VmRel p c s → fetch/opcode = X → Step p s s'
        → ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'
```

**You may read** (definitions and statements only):
- `Lua/Bytecode/Semantics.lean` and `Lua/Bytecode/Kernel.lean`: `Step` is
  `KStep` over `opKernel`, one kernel term per opcode. It is built from a few
  combinators (`opArith`, `docondjump`, `setR`, `forloop`, …) with read, def
  and kill ports and a shared value function δ.
- `Lua/Vm/Sim/Rel.lean`: `VmRel`, the machine–VM relation.
  - Registers are pinned at the head: `s0` = L, `s7` = ci, `s9` = base,
    `s11` = pc, `s5` = trap.
  - VM registers are the TValues at `base + 16i`.
  - The rest is a complement memory, image, heap and so on.
  - `RegsOk` says all registers are present.
- `Lua/Vm/Loaded.lean`, `Lua/Vm/Runtime.lean`: the entry state layout.
- `abstractions/ROUND-3.md` §1–2: the census and the LAWS, with their checks
  against real traces. Also the earlier rounds' decisions (`ROUND-1.md`,
  `ROUND-2.md`).
- `experiments/a1-falsifiers/REPORT.md`: arm exits, dependence classes,
  stack relocation.
- The disassembly, via `~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump -d c/lua-riscv-htif.elf`.
- `vendor/lua-5.4.7/src/lvm.c` and the other Lua sources.

**You may NOT read** proof files (`Lua/Vm/Sim/Arms/*`, `Lua/Vm/Sim/Close.lean`,
`StepK.lean`, `Entry.lean`, `Lua/Vm/Arms/*`), generator scripts
(`scripts/gen_lua_arm*.py`), `abstractions/pilot/*`, `abstractions/bakeoff*`,
git history, or other agents' output.

## What is costly (census)

- **Per new decision tree:** 30–273 hand lines each. These go into a
  per-kind template, guard lemmas (one pair per branch shape), a kernel
  inversion, and a "close" lemma that re-establishes `VmRel` after the arm's
  stores.
  - 25 of the 51 sim-shaped arms are proved, covering 15 of 34 pruned trees.
  - The remaining 26 arms need 19 new trees.
  - Hand cost per arm rose from 47.2 to 63.9 lines.
- **Relation widening:** each new resource (constants, registers present, …)
  is a field of `VmRel` and costs 100–250 lines.
  - The blocked arms need at least four more: `savedpc`/`L->top` written by
    `Protect`, `func` moving (VARARGPREP), heap/strings/global state
    changing, and console output from a callee.
- **Callee contracts:** 18 of the 26 open arms call helpers.
  - Soft-int `__muldi3`/`__divdi3`/`__moddi3`/`__udivdi3`,
    `luaV_equalobj`, string compare, `luaT_adjustvarargs`.
  - CALL `print` runs `luaD_precall` → `luaB_print` → `luaL_tolstring` →
    `fwrite` → newlib stdout → HTIF.
  - The error chains `longjmp`.
  - 131 distinct helpers are reached dynamically.

## The laws (each should become ONE proved rule)

- **L-C4 (holds, 1,424 real steps):** at every dispatch-head crossing, the VM
  state decoded from memory is exactly the one the executable semantics
  predicts.
- **L-C6′ (refined):** an arm's stores fall inside its edge's def/kill ports,
  plus its own C frame, plus `{savedpc, L->top}` and a callee frame for
  helper-calling arms. Four store shapes cover every non-CALL store, in
  compiler order, not kernel order.
- **L-C3′ (refined): three callee shapes.**
  - *pure:* the result is a function of argument values; nothing at or above
    `sp` changes except declared out-pointers.
  - *runtime:* a named footprint of `L`/`ci`/`G` fields, slots from `R[A]`
    up, and heap ownership; `func` may move.
  - *noreturn:* the helper never returns and the program exits nonzero.
- **L-C2′ (refined):** arms that share a pruned, value-parameterised decision
  tree share one proof plus a table row. A layout-generic proof saves only
  about 7%.

## Forbidden vocabulary (not acceptable as the answer)

- per-arm or per-kind templates;
- generator scripts that emit per-arm or per-site lemmas;
- per-instruction or per-pc step lemmas;
- "segments", "sites", "bridges";
- adding one field to the relation per resource;
- one hand-written contract per helper function;
- SMT, fuzzers, model checkers or proof search as the abstraction (tools may
  only check laws).

The previous bake-off also evaluated a verified symbolic executor
(`SymExec`). It lost because it:

- costs 2–4× more hand lines per arm;
- has no call nodes;
- proves a weaker theorem.

You may build on it or improve it, but say how you fix those three things.

## Output contract: 5 abstractions

For each:

1. **Name.**
2. **The idea.**
3. **Core rules:** which law becomes which single proved rule.
4. **What it makes free:** which census obligations disappear.
5. **What it costs:** the setup, and what gets harder.
6. **Theories:** two or more from DISTANT fields, marked known (with a
   citation) or novel.
7. **Pilot:** held-out arms MUL, EQ and MOD, plus refactoring `sim_ADD`,
   with the smallest thing to build.
8. **Seed:** which part of your seed drove it.

Prefer depth and specificity over safe coverage. Mark anything recalled from
memory for checking.

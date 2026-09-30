# A1 cheap falsifiers (ROUND-1 C7–C9): orbits, `ADD`'s exits, stack relocation

This is a read-only analysis of `c/lua-riscv-htif.elf` at main `237e007`,
done with Python, gawk, objdump/nm and the Lean RISC-V emulator. No lake.
`run.sh` reruns everything in a few minutes. The thresholds were fixed before
running (ROUND-1 §3, R2-2/R2-4/R2-5/R2-6).

## Verdicts

| falsifier | pre-fixed rule | measured | verdict |
|---|---|---|---|
| F1 dependence-graph orbits (C8) | dead if {MUL,ADD,SUB}/{MULK,ADDK,SUBK} don't merge modulo the ALU op, or more than ~30 classes | they merge; **46 classes** modulo ALU (54 exact) | **DEAD** (class count) |
| F1 shared-prefix tree | dead if MST edit weight / total > 0.4 | **0.521** canonical modulo ALU (0.538 exact, 0.570 raw) | **DEAD**; 0.33 without CALL/RETURN*/FORPREP |
| F2 `ADD`'s exits | "two normal exits: integer fast path, and fall-through into the MMBIN arm" | two next-pc classes, both returns to the dispatch head; MMBIN's code is never entered from ADD | **refuted as stated**; the shape is two head returns: (R[A] written, pc+2) and (nothing written, pc+1) |
| F3 stack relocation (R2-6 #5) | realloc/grow after `luaV_execute` entry? `base` moving within an activation? | never in the current F1 programs; `CALL print` reallocates mid-activation with ≥ 15 locals; `VARARGPREP` moves `base` in every main chunk | **objection stands** |

## Setup from the current ELF

- **Dispatch.** `luaV_execute` is at `0x8001bf68`, with one `jr` at
  `0x8001c008`.
  - The jump table is at `0x8005336c` (base in `s8`): 82 int32 entries,
    bound check `bltu` against `s1=81`, default target `0x8001c1e4` (also
    EXTRAARG).
  - The dispatch head is `lw s4,0(s11)` at `0x8001bfe8`; the trap check
    `bnez s5` is at `0x8001bfe4`.
  - Arms return with `j 0x8001bfe4` or `beqz s5,0x8001bfe8`.
- **The head's register interface:**
  - `s0`=L, `s7`=ci, `s9`=base, `s11`=pc, `s5`=trap;
  - `s8`=table, `s1`=81, `s2`=3 (`LUA_VNUMINT`);
  - `0(sp)` = k.
- **The F1 set** is 54 opcodes (from `Lua/Fragment.lean`), 2,993 static
  instructions walked to the head. The census arm table matches the current
  ELF.

## F1: orbits (`canon.py`, `f1_orbits.py`, `selftest.py`)

**Canonical form.** Starting at the head, symbolic execution with hash-consed
terms makes the form invariant under:

- *register renaming:* only the head interface is named, and spill slots
  whose address is never taken are treated as registers;
- *scheduling:* a DAG of pure operations, commutative operands sorted, memory
  in epochs with calls as barriers, and loads depending only on
  possibly-aliasing stores;
- *branch polarity and layout:* branches are normalised to EQ/LT/LTU with
  (true, false) successors, and a join is shared when the live state is
  equal.

**Self-test.** 54/54 arms keep their class under:
- flipping all 376 branches;
- 3,000 swaps of adjacent independent instructions;
- register swaps;
- all three combined.

The negative control (changing one immediate) changes 52/54 classes.

**Counts.**
- Exact: 54 classes.
- Modulo ALU: **46**. The merges are {ADD,SUB,MUL}, {ADDK,SUBK,MULK},
  {BAND,BOR,BXOR} and {BANDK,BORK,BXORK}.
- Even forgiving predicate and constant differences (LTI/GTI operand order
  and helper, the TM event constants), about 36 classes remain.

**Shared-prefix MST** (Prim; Levenshtein distance over linearised canonical
tokens):
- 3,364/6,454 = 0.521 modulo ALU.
- Raw objdump text: 1,705/2,993 = 0.570.
- The call and return arms dominate: RETURN unfolds to 1,154 tokens from 86
  instructions, and its nearest neighbour is 1,031 edits away.

## F2: exits (`f2_exits.py`)

The walk stops at other opcodes' jump-table targets, so a fall-through into
the `MMBIN` code would be visible. There is none.

- **ADD** (52 instructions): 7 paths, all returning to the head.

  | paths | exit | writes | helpers |
  |---|---|---|---|
  | 1 | pc+2 | R[A] | none (int + int) |
  | 1 | pc+2 | R[A] | `__adddf3` (float) |
  | 2 | pc+2 | R[A] | `__floatdidf`, `__adddf3` (mixed) |
  | 3 | pc+1 | nothing | none (not a number: the next dispatch runs MMBIN) |

  SUB and MUL reach the pc+1 return through the shared default-target tail.
- **Other arithmetic arms.**
  - MOD, IDIV, MODK and IDIVK add a non-returning `luaG_runerror` exit.
  - UNM and BNOT call `luaT_trybinTM` directly and return pc+1; no MMBIN
    follows them.
- **EQI** (41 instructions): 6 paths, all to the head, with no stores. They
  go to pc+2, or to the computed `donextjump` target (pc+1+sJ, with trap
  reloaded).
- **FORLOOP** (55 instructions): 6 paths, all to the head, all reloading
  trap. They exit at pc+1, or jump back (pc−Bx) writing count, index and
  control variable. There are integer and float variants.

## F3: stack relocation (`f3_stack.sh`, `f3_stack.out`, `f3_probe.out`)

**Method.** Streamed `--trace-pcs` on five points: `luaV_execute`,
`startfunc` `0x8001bfb0`, the dispatch `jr`, `luaD_reallocstack` and
`luaD_growstack`. Activations are tracked per C frame as a CallInfo stack,
and `base` is read from `s9` at each dispatch.

**Inputs.** The 18 difftests and the 4 validation chunks.

**Results.**
- *No growth in the F1 programs.* These never grow or reallocate the stack:
  - f1_*, while, f1_ops, f1b_bits, f4_strlite;
  - f2_*, f4_strings, f4_objects, f5 and f7.
- *`VARARGPREP` shifts `base` inside one activation in every program*
  (`luaT_adjustvarargs`: `ci->func += actual+1`, then `updatebase`).
- *Relocations do occur elsewhere:*
  - f3_closures: a grow via `luaD_precall`'s Lua path, then a realloc to 80
    slots;
  - f3_pcall: doubling 80→640;
  - f3_varargs: via `precallC`;
  - f4_metatables: a metamethod tail call;
  - f6_coroutines: coroutine stacks.

**Probe.** Programs of the form `local a1..aN = 1..N; print(aN)`:
- For N ≤ 14 nothing grows.
- For N = 15–30, `CALL print` runs `precallC` → `checkstackGCp(20)` →
  `luaD_growstack`, a realloc inside the main activation. The move is picked
  up by `trap` → `luaG_traceexec` → `updatebase` at the next head.
- For N = 40 it grows before `luaV_execute`.
- The largest current chunk (f1_ops) is about 5 registers below the
  threshold.

**Consequence for C9 and A1's `VmRel`.**
- Decode registers relative to `ci->func`/`L->stack`, re-read at the head
  after a trap. Otherwise either `Supported` bounds the frame (about CALL
  A+B ≤ 16 in the main chunk), or the CALL rule gets a "stack may move, trap
  set" clause.
- In every case, model `VARARGPREP`'s base shift.

## Caveats

- **Alias model and call arities are heuristic.** Aliasing is same width and
  same base; arities come from prototypes plus a libgcc/libc table. The
  self-tests show no splits.
- **Tree unfolding inflates token counts for branchy arms.** The raw
  instruction MST is the unit-free cross-check.

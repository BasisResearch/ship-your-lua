# Abstraction discovery, round 3: A1 (machine arms), steps 1–2

The gate triggered this round (`a871702`). `a1-arm-sim` has 25 cases, and its
per-arm hand cost rose from 47.2 to 63.9 lines between the first and last
quarter. Proving is paused. This file holds the census (§1) and the laws with
their checks (§2). The fan-out, retrieval, variation and bake-off steps come
later.

The scripts and raw outputs are in `abstractions/checks/round3/`. Each
`*_RESULTS.md` there records the method and the rerun commands for one check.

## 1. Obligation census

**Sources.**
- The ledger `abstractions/ledger/a1-arm-sim.tsv`.
- `census_a1.py`. It attributes every hand declaration of the A1 files to its
  introducing commit (`git log -S`, oldest first), clusters it by the shape
  it re-proves, and counts the lines each A1 commit added to the generator.
  The output is `census_a1.out`.
- `lc2_layout.py`. It classifies the 54 `Lua/Fragment.lean` opcodes into
  canonical decision trees.
- `callee_census.py` and `callee_groups.py`. These build the static and
  dynamic call graph.
- `pilot/A1-incumbent.md` and `bakeoff2/incumbent.md`.

Lines are non-blank, non-comment lines.

### Cluster table

| cluster | cases | cost per case over time | trend | two instances |
|---|---|---|---|---|
| **(a) per-arm template (ledger)** | 25 arms | first quarter 47.2, last quarter 63.9 lines per arm | **rising** (gate FAILS) | ADDI 113 (arith, `sC` operand plus unification); NOT/TEST/TESTSET 91 each (truth) |
| (a1) new tree (new kind, or a new operand-access form) | 15 arms | 846 lines, mean 56.4. By kind: copy 30, imm 35, jump 42, arith 61, condjump 61, forloop 54, cmpI 132, settag+loadk 115, bnot 53, truth 273, ADDI 111 | **rising**: the first three kinds cost 30–42, the last three 53–273 | cmpI (`3079c33`: 76 generator lines + 44 guard + 2 inversion); truth (`8358d37`: 149 generator lines + 59 guard + 23 inversion + 9 store shape) |
| (a2) new layout of a proved tree | 4 arms | 92.5 lines, mean 23.1 | flat | SUB (24: float-test layout); SUBK |
| (a3) table row only | 6 arms | 127.5 lines, mean 21.2 as ledgered. Real cost is 1–2 lines: BAND/BOR/BXOR together cost 6 | at the floor | BAND 2; BXOR 2 |
| (a4) guard lemmas: a branch on a tag byte, constant or `slt` decides a `ValRepr` or kernel predicate; one `_t`/`_f` pair per branch shape | 40 decls, 191 lines | added per new-tree commit: 81 → 4 → 44 → 3 → 59. Mean per decl 4.3 → 3.7 | flat per decl, but grows with every new tree | `guard_tag_eq`/`guard_tag_ne`; `guard_kb_ne_t`/`_f` |
| (a5) kernel inversions, one per combinator (`step_setR`, `step_opArith`, `step_condjump`, `step_forloop`, `step_testset`, …) | 19 decls, 209 lines | mean 8.5 → 18.5 | **rising** | `step_forloop` 42; `step_testset` 23 |
| (a6) ALU value lemmas (`add_val`, `alu_val`, `dec_val`, `not_val`) | 4 decls, 32 lines | 17 → 5 | falling (after `alu_val` generalised it) | `alu_val` 4; `not_val` 5 |
| **(b) callee contracts** | 17 of 54 opcodes call a helper on a live integer path; 29 arms are blocked (below) | **no case is proved yet** (forecast). The existing batteries are at WHILE addresses (`Muldi3Spec`, `udivdi3_spec`, `MemcpySpec`), or are sites only with no spec (`__divdi3`, `__moddi3`, `__umoddi3`), or not ported (stdio A0.2) | forecast; the size is below | `__muldi3` for MUL/MULK; `luaD_precall` → `luaB_print` → … → HTIF for CALL |
| **(c) frame/relation maintenance** (closes `Core.write`/`jump`/`update`/`forloop`; store-shape lemmas `slotStore_*`, `ForStore`; `*_of` transports) | 28 decls, 245 lines | mean per decl 6.9 → 5.3. Each new close shape costs 9–39 lines (`Core.forloop` 39 + `forloop_store` 30); each new store shape 4–10 lines (`slotStore_sb`, `_sd_sb`, `_copy` 10, `_copy_tv` 9) | flat per case; a new case with most new trees | `Core.forloop` (39: four stores into three slots, two of them payload-only); `slotStore_copy_tv` (9) |
| (c1) `RegsOk` preservation | 10 decls, 85 lines, once | then one generated line per segment step (`gen_segment.py` `"ok"`) | **at the automation floor** | `RegsOk.of_step` 37; `alu` 10 |
| **(d1) relation widening** (a new resource enters `VmRel`/`Complement`/`Ranges`, and `vmRel_entry` must discharge it) | 3 so far | total reads +57 −34; `RegsOk` +218 −51; constant array +135 −26, plus `vmRel_entry` +80 | **rising**. The blocked arms need at least 4 more: `ci->savedpc`/`L->top` (`Protect`), `func` moves (VARARGPREP, realloc), heap/strings/`G` evolving (CALL), console growth by a callee | `81c9439` (`Core.kptr`, `Complement.kconst`, `Ranges.k_*`); `564c9c8` (`RegsOk`) |
| (d2) field and bit arithmetic (`sext_shr`, `kraw_eq`, `sbraw_eq`, `slot_addr`, …) | 30 decls, 189 lines | 7.3 → 5.1 | flat, falling slightly | `sbraw_eq` (the cmpI `maxRecDepth` fix); `addiw_bias` |
| (d3) segment interface extensions (`KEEP`, `live_keep`, `OK`, `NORM`, `KPARAM`) | 5 | 131 → 32 → 28 → 1–2 lines per arm commit | falling, at the floor | `live_keep` (the ADD `KeyError: 'x15'`); `KPARAM` |
| (d4) generated volume (not hand) | 25 files | `sim_<OP>` file 71–338 lines; about paths × depth segment calls | rising with branchiness | EQI 338; TESTSET 338 |
| (d5) failed builds | about 1 per arm | pilot 27 for 3 arms; bake-off 26 for 3; 25 for 19 | falling | cmpI `maxRecDepth` ×2; truth `insert_frame` |

**The rising clusters.**
- (a1) new trees, with their (a4) guards and (a5) inversions, are rising.
- (d1) relation widening is rising.
- (b) callee contracts has no proved case, but it blocks 26 of the 29 open
  arms.
- Everything else is flat, falling or at the floor.

**Where the hand lines of the 19 post-bake-off arms landed** (`791175d`..`8358d37`,
777 added lines; `lc2_RESULTS.md`):

| destination | lines | share |
|---|---|---|
| kind templates in the generator | 374 | 48% |
| hand Lean | 231 | 30% |
| operand-access templates | 76 | 10% |
| shared infrastructure | 41 | 5% |
| table rows | 37 | 5% |
| branch-layout data | 18 | **2%** |

### Remaining arms (`lc2_RESULTS.md`)

The 51 sim-shaped arms (all of the 54 but `RETURN*`) have **34 distinct
F1-pruned trees**. The 25 proved arms cover 15 of them. Of the 26 unproved
sim-shaped arms:

- **3 reuse a proved tree** and still need a callee: MUL and MULK
  (`__muldi3`), UNM (`luaT_trybinTM`).
- **8 are inline:**
  - new trees: BANDK, SHL, SHLI, SHRI, LOADNIL (a loop);
  - rows of those trees: BORK, BXORK, SHR.
- **15 need callees** and make 14 new trees plus one row: MOD, MODK, IDIV,
  IDIVK, EQ, EQK, LT, LE, MMBIN, MMBINI, MMBINK, GETTABUP, VARARGPREP, CALL,
  FORPREP.

`RETURN`/`RETURN0`/`RETURN1` are the `Final` clause (`vmRel_final_Statement`).
BANDK/BORK/BXORK need the `Supported` premise "`K[C]` is an integer".

At the current new-tree mean of 56 lines, the 19 new trees cost about 1,070
hand lines before any callee contract.

### Size of the contract problem (`callee_census.out`, `callee_groups.out`)

**Static transitive closure** (objdump call graph; `jal`, tail `j`, and 3
`jalr` resolved by hand: `luaB_print`, `l_alloc`, `__swrite`; 21 indirect
sites unresolved):

| from | functions | cut at GC / re-entry / metamethods |
|---|---|---|
| the arms' direct callees | 315 | 196 |
| the error paths | 320 | 155 |
| CALL, RETURN and the exit chain | 343 | 304 |
| stack growth and VARARGPREP | 315 | 154 |
| **all** | **343** | **320 functions, 32,087 instructions** |

**Dynamic** (functions entered at or below `luaV_execute` in 12 runs: the 5
validation programs, `f1_while`, and 6 targeted `progs/lc3_*.lua`):

| group | functions | instructions |
|---|---|---|
| arm helpers, normal paths | 11 | 557 |
| error chains | 81 | 11,608 |
| CALL print | 81 | 9,155 |
| RETURN and exit | 19 | 837 |
| stack growth | 7 | 754 |
| VARARGPREP | 1 | 64 |
| **total distinct** | **131** | **14,583** |

- 37 of the 54 opcodes call nothing on a live integer path.
- The other 17 need 16 direct callees:
  - soft-int: `__muldi3`, `__moddi3`, `__divdi3`, `__hidden___udivdi3`;
  - FORPREP's conversions: `luaV_tointeger`, `luaV_tonumber_`;
  - comparison: `luaV_equalobj`, `l_strcmp` (→ `strcoll`/`strcmp`/`strlen`);
  - GETTABUP: `luaH_getshortstr`, `luaV_finishget`;
  - calls: `luaD_precall`, `luaD_poscall`, `luaT_adjustvarargs`.

**The contract problem is `print` and the error chains** (81 functions each),
not the arm helpers (11 functions).

## 2. Laws

Every law was checked against the Sail runs of the real ELF, the
disassembly, and the real Lean `step?`. None was checked only against a
model. Tools here only check laws; none of them is a proposed abstraction.

**Replay validity.** Every trace-based check rebuilds memory as the PT_LOAD
bytes plus every traced store in order. That shadow memory matched
**372,411/372,411** traced loads (L-C4 pass) and every traced load of the
L-C3 pass (0 mismatches).

### L-C4, the value law (the trace-level check pending since round 1)

> At every crossing of the dispatch head (`lw s4,0(s11)`, `0x8001bfe8`) in a
> real run, decode the state:
> - pc = (s11 − code)/4;
> - `R[j]` from the tag byte at `s9+16j+8` and the payload at `s9+16j`
>   (strings through the TString header, `print` by address);
> - out = the console so far.
>
> The decoded state equals, on pc, out and every register the model defines,
> the state that `step?` gives from the previous crossing.

**Method.**
- `lc4_trace.py` streams `--trace-all` and decodes at each head.
- `LC4Check.lean.in` and `lc4_run.sh` run the real
  `Lua.Bytecode.step? binaryHost` on each program's `Proto` (`lake env lean`,
  under `MemoryMax=30G`). They check two forms:
  - **(i)** the model iterated from `State.init` matches the decoded machine;
  - **(ii)** `step?` applied to the decoded state, masked to the model's
    defined registers, matches the next decoded head.

**Result: 0 counterexamples.**

| program | Sail steps | heads | (i) checked / bad | (ii) checked / bad | stops at |
|---|---|---|---|---|---|
| while | 215,723 | 671 | 671/0 | 670/0 | RETURN |
| f1_ops | 271,860 | 186 | 186/0 | 185/0 | RETURN |
| f1b_bits | 320,764 | 220 | 220/0 | 219/0 | RETURN |
| print_print | 188,129 | 8 | 8/0 | 7/0 | RETURN |
| f1_src | 221,516 | 265 | 265/0 | 264/0 | RETURN |
| f4_strlite | 236,227 | 110 | 13/0 | 12/0 | CONCAT (first non-F1) |
| difftest f1_arith | 317,386 | 374 | 16/0 | 15/0 | `GETTABUP _ENV.type` (no kernel step) |
| difftest f1_cond | 401,320 | 4,779 | 2/0 | 1/0 | CLOSURE |
| difftest f1_for | 210,874 | 119 | 52/0 | 51/0 | SETTABUP |
| **total** | | | **1,433/0** | **1,424/0** | |

- The word loaded at each head equals `Proto.fetch pc` every time, and
  `s9 = ci->func + 16` at every head.
- The checks step 45 F1 opcodes. The whole `CALL print` activation, from the
  CALL's head to the next head, is checked 33 times; VARARGPREP 5 times.
- One CALL reallocates the stack (f1_src, 19 slots, pc 145: `func` moves from
  `0x8006f360` to `0x80073680`). The law still holds because decoding is
  relative to `s9`.
- **Never exercised:** ADDK, SUBK, RETURN0, RETURN1 (and LE and MMBIN* only
  beyond F1). f4_strlite's F4-lite kernels also agree past the boundary
  (110 heads, 0 bad).

**Refinements.**
- Add the premise "the kernel at pc steps" (`Supported`).
- Decode relative to `s9`/`ci->func`, as `VmRel` already does.
- A string's header tag (4/20) is not its TValue tag (68/84). The decoder bug
  was ours, and `TStringRepr` already states it.

### L-C6 (new): the arm store footprint

> Between two head crossings, every store lands in the slot of a register in
> the def or kill ports of the edge taken (`decide? (kernelAt p)`), or in
> `luaV_execute`'s own C frame `[sp, sp+176)`.

**Method.** The same trace pass classifies every store by region (`lc4_*`).

**Result: false as stated.**
- **Opcodes other than CALL store outside the window.** MOD, MODK, IDIV,
  IDIVK, FORPREP and EQ write `ci->savedpc` and `L->top` (`Protect`) on every
  execution. EQ, EQK and FORPREP also write callee stack frames.
- **10 slot stores fall outside the ports.**
  - 9 are VARARGPREP, which copies the closure to the new `func` (the old
    slot 0).
  - 1 is the reallocating CALL (`free` bookkeeping in the old block).
- MUL stores nothing outside its slots (`__muldi3` is a leaf), and GETTABUP
  only spills into its own frame.

**Refined law L-C6′.** Measure the ports against the post-step frame, and only
while the old frame is live. The footprint is:
- the edge's ports;
- the own C frame;
- for helper-calling opcodes, `{ci->savedpc, L->top}` plus the callee's C
  frame below `sp`.

Only CALL and VARARGPREP are unrestricted; for them L-C3's "runtime" shape
applies.

**Store shapes** (these drive cluster (c)). Four cover every non-CALL store:
- tag `sb` and payload `sd`, in either order;
- tag-only `sb` (LOADTRUE/LOADFALSE/LFALSESKIP/NOT/LOADNIL);
- FORLOOP's payload-only stores (`r1+0/8 r3+8/1 r0+0/8 r3+0/8`).

CALL adds one 16-byte copy. The order is compiler layout, not kernel
structure:
- tag first: ADD, ADDI, SUB, BAND/BOR/BXOR, LOADI, UNM, GETTABUP;
- payload first: MOVE, MUL, MULK, the shifts, the K-bitwise opcodes, BNOT,
  LOADK, MOD/IDIV.

So one law, "after the arm the slot's 9 bytes represent v and nothing else in
the window changed", would replace every `slotStore_*` variant and every
per-close lemma.

### L-C3, the callee frame law

> Every helper call an arm makes writes only within its own stack frame plus
> its declared outputs, and returns a pure function of its inputs.

**Method.** `lc3_trace.py` and `lc3_footprint.py`. For each helper activation
entered from a `luaV_execute` arm, they log every store until the matching
return (or a `longjmp`) and classify it by region. For purity, they compare
`a0` with an oracle:
- the soft-int helpers against Python arithmetic on `a0`/`a1`;
- `luaV_equalobj`/`l_strcmp` against an oracle over the TValue/TString bytes
  behind the argument pointers.

The runs are the 5 validation programs, `f1_while`, and 6 targeted programs
(`progs/lc3_{arith,strcmp,grow,div0,forerr,opint}.lua`).

**Result: false as stated.** It holds only for pure leaves.

- **Holds:**
  - the soft-int calls (316 activations) match the oracle and write only
    below `sp`;
  - `luaV_equalobj` (7) and `l_strcmp` (6) match with inputs read through
    memory;
  - `luaH_getshortstr` (48) is read-only.

  This covers 10 of the 11 helpers the arms enter on normal paths.
- **Counterexample 1 (out-parameters).** `luaV_tointeger` (FORPREP) writes
  `luaV_execute`'s frame at `sp+40`.
- **Counterexample 2 (runtime state).**
  - `luaD_precall`/print writes:
    - `L->top`, `L->ci`, `L->nci`, `ci->next->*`;
    - slots from `R[A]` up and above `maxstacksize`;
    - the heap (interned strings, the new CallInfo, the stdio buffer);
    - `G` fields (GCdebt, allgc, `strt.nuse`, totalbytes, strcache);
    - the stdout `FILE`, the malloc state, errno, the fd table and HTIF.
  - `luaT_adjustvarargs` writes `ci->func`/`top`/`nextraargs`, `L->top` and
    slots from `R[A]` up.
  - `luaD_poscall` writes `L->top` and `L->ci`.
- **Counterexample 3 (the arm's own stores).** `Protect` writes
  `ci->savedpc`/`L->top` in CALL and MOD/MODK/IDIV/IDIVK (230/230 for MODK),
  in EQ/LT/LE on strings, FORPREP and MMBIN*, and in RETURN (also
  `ci->func`).
- **Counterexample 4 (stack growth).** At 20 locals, `_free_r`, `_malloc_r`
  and `luaE_extendCI` overwrite the old block, including slots below `R[A]`
  and `base`. `correctstack` rewrites `ci->func`/`L->stack`, and `trap` is set
  at the next head. Not checked: that the new block's `R[<A]` equals the old.
- **Counterexample 5 (errors).** All 3 error activations `longjmp`. They
  write the heap, `G`, `L->top` and `errorJmp->status` in
  `luaD_rawrunprotected`'s frame.

**Refined L-C3: three laws, one per callee shape.**
- **pure.** `a0 = f(argument values read through memory)`. Memory at or above
  the caller's `sp` is unchanged, except declared out-pointers. Memory below
  `sp` is havocked. This covers the soft-int helpers, `luaV_equalobj`,
  `l_strcmp`, `luaH_getshortstr` and `luaV_tointeger` (with its out-pointer).
- **runtime.** A named footprint of `L`/`ci`/`G` fields, slots from `R[A]`
  up relative to `base`, and heap ownership. `func` may move, with `R[<A]`
  preserved up to relocation. This covers CALL, VARARGPREP, RETURN and stack
  growth: the kill-port shape of round 1 (C2), plus the allocator.
- **noreturn.** The helper never returns to the head, and the program exits
  nonzero. This covers the `luaG_*error` chains, i.e. the `stuck_sim` side.

### L-C2, the layout law

> Two arms of one combinator kind differ only in their branch layout, so one
> proof keyed by the combinator's decision tree covers all of them.

**Method.** `lc2_layout.py` re-hashes the round-2 canonicaliser (`canon.py`,
invariant under renaming, scheduling and branch polarity) at coarser levels:
- L3p: ALU op, predicate and constants become parameters;
- P: branches on a Lua tag byte are pruned to `ValRepr`'s tags, so the float
  paths drop;
- raw layout: the branch mnemonics in address order.

| level | classes (54 opcodes) |
|---|---|
| exact | 54 |
| modulo ALU op | 46 |
| L3p | 45 |
| P1 | 45 |
| **P3p (L3p, pruned)** | **37** |
| P5 (bare skeleton, pruned) | 28 |
| raw layouts | 33 |

**Result: false as stated.** The `opKernel` combinator is the wrong key. At
P3p:
- `opArith` covers 21 arms in 11 trees;
- `docondjump` covers 10 arms in 6 trees;
- `setR:move` covers 7 arms in 5 trees.

**Counterexamples:**
- operand access: register, `K` and immediate (ADD / ADDK / ADDI);
- BANDK has no `K[C]` tag test (the missing `Supported` premise);
- MOD/IDIV: helper calls, sign fix-ups and an error exit;
- the shifts' amount branches;
- LOADI vs LOADTRUE: a different store count;
- EQ/EQK (`luaV_equalobj`) and LT/LE (`l_strcmp`, `luaT_callorderTM`);
- VARARGPREP vs JMP;
- TESTSET vs TEST: TESTSET stores;
- FORLOOP/FORPREP keep float-loop paths that only the kernel or FORPREP
  invariant excludes, not `ValRepr`.

**Refined law L-C2′.** Arms with the same F1-pruned, value-parameterised tree
(P3p: the lvm.c macro × operand access × named helper leaves) share one proof,
with only a table row per arm (ALU op, predicate, constants, layout string).

It holds on every multi-arm tree (raw layouts per tree in brackets):
- {ADD, SUB, MUL, BAND, BOR, BXOR} [3]. Over F1 values, `op_arith` and
  `op_bitwise` are the same tree.
- {ADDK, SUBK, MULK} [3]
- {BANDK, BORK, BXORK} [2]
- {LOADTRUE, LOADFALSE, LFALSESKIP} [1]
- {LTI, LEI, GTI, GEI} [2]
- {LT, LE} [2]
- {SHL, SHR} [1]
- {UNM, BNOT} [2]

**Consequence.**
- Layout is 2% of the recent hand cost, rows 5%.
- A layout-generic proof alone saves at most about 7%.
- The cost is per tree, and 19 new trees remain.

The target is therefore:
- a vocabulary in which a new tree is cheap: its guards (a4), its kernel
  inversion (a5) and its close (c) derived rather than written;
- the callee laws (L-C3′), since 18 of the 26 open sim-shaped arms need
  them.

### Law-to-cluster map for step 3

| cluster | law that discharges it once | check |
|---|---|---|
| (a1) new trees, (a4) guards, (a5) inversions | L-C4 at the arm level: from any head state representing `s`, the arm's pruned tree reaches a head state representing `step? s`. The per-branch guard is "this branch decides the kernel's case predicate on the represented value", one rule for every tag, constant and `slt` test | L-C4: 1,424 steps, 0 bad; L-C2′ gives the tree count |
| (a2)/(a3) layouts and rows | L-C2′ | 8 multi-arm trees, 0 counterexamples |
| (b) callee contracts | L-C3′ pure / runtime / noreturn | pure: 377 activations, 0 bad; runtime and noreturn are footprints named from traces |
| (c) closes and store shapes | L-C6′: after an arm, the def slots represent the new values and the window is otherwise unchanged; stores are free up to shape | 4 store shapes; 0 violations after refinement |
| (d1) relation widening | L-C3′ runtime plus L-C6′: the relation's complement is the kill-port and heap-ownership footprint, not a list of fields added one resource at a time | counterexamples 2–4 name the fields |

## 3. Blind ontologist fan-out (deep seeded, 2 rounds × 5)

The brief is `abstractions/pilot/ONTOLOGIST_BRIEF_R3.md`. The raw answers are
in `abstractions/fanout/R3-R1-*.md` and `R3-R2-*.md` (3 character seeds and
2 word seeds per round). Round 3 was not run, because round 2 converged on
refinements of round-1 mechanisms.

**Agreement.** 22–25 of the 25 round-1 ideas reduce to six mechanisms; three
round-2 agents tabulated this independently (R2-1, R2-2, R2-3).

### Mechanisms (the cheapest member of each, per round 2)

| # | mechanism | cheapest form | rounds, agents |
|---|---|---|---|
| M1 | arm proof by forward kernel evaluation (no inversion) | `kstep_iff` + `simp`, with the δ entry restated in `lvm.c`'s branch order, e.g. `imodC_eq` | R1-3#5, R1-5#1, R1-1#4 → R2-1#2, R2-4#4, R2-5#3 |
| M2 | guards factor through a canonical value representation | about 7 tag lemmas over a TIGHTENED `ValRepr` (nil tag = 0, string variant by length ≤ 40) | R1-2#2, R1-3#1, R1-1#4 → R2-3#2, R2-5#2 |
| M3 | one close on final memory | `bleach`, no write-log or patch datatype | R1-5#2, R1-1#1, R1-2#3, R1-3#3 → R2-5#1 |
| M4 | dead-at-head cells without widening `VmRel` | re-witness `∃ w` (`Complement.rebase` + `PhaseOk`) or a stale-complement `Scratch` premise; NOT a larger `Win` (it breaks `Ranges.ci_out`, R2-4 N2) | R1-1#2, R1-4#1/#5, R1-5#2 → R2-1#1, R2-2#1, R2-3#1, R2-4#1 |
| M5 | callee summaries after F1 value pruning | a call node returning to `ra₀`/`t0`, helpers classified *after* pruning; the libgcc integer block `[0x8002f6c8,0x8002f7ec)` has no memory operations, so one region spec (or relocation of the WHILE specs) covers it | R1-2#4, R1-3#4, R1-4#2, R1-5#3 → R2-1#3, R2-2#4/#5, R2-3#4, R2-4#3, R2-5#4/#5 |
| M6 | string equality without heap-wide interning | an intern map `ι : content → ptr` in the witness; CONCAT pays for it | R1-5#1 → R2-4#2, R2-5#2 (R2-2#2's "strings only from K" fails: CONCAT is in F1, R2-4 N3) |

### One-offs worth keeping

- **Tablebase tails** (R2-3 #3). GCC shares tails heavily: the pc+1 tail has
  more than 64 in-edges. Prove each shared tail once, keyed by the decoded
  kernel value at the join, and stop arm proofs there.
- **An executable decoder as the gate** (R2-4 #5). The Python L-C4 checker
  held on 1,424 steps while `sim_MOD`/`sim_EQ` are *false* against `VmRel`.
  Make the decoder executable Lean, tied to `VmRelAt` by one lemma, so traces
  test relation changes.
- **A lockstep product executor, KProd** (R1-2 #5). Round 2 keeps it as the
  fallback carrier if the direct kit leaves `sim_ADD` at 20 lines or more
  (R2-3's stop rule).

### Soundness corrections found (independent of any abstraction)

- **`sim_MOD`/`sim_EQ` are false against today's `VmRel`.** Three causes:
  - `LuaStateAt.top` pins `L->top = func+16`, but `Protect` rewrites it;
  - `savedpc` is written;
  - `luaV_equalobj`'s `sd ra` falls outside `Win`.

  Found by R1-1, R1-3, R1-5, R2-2 N3 and R2-4 N1.
- **`L->top` is not dead in general.** It is live after `CALL print` with
  C=1 (`ldo.c` `moveresults`: `L->top = ra`), and GC reads it (R2-1 N4/N5,
  R2-2 N2). It is dead at the head only for F1 non-IT instructions; in F1
  the only IT head is VARARGPREP at pc 0.
- **`LuaStateAt.next = 0` breaks at the first CALL** (`luaE_extendCI`) and is
  read by the next CALL (R2-3 N6).
- **`ValRepr` is too loose for EQ.**
  - nil is any `t % 16 = 0`, while the machine compares `tt & 63`;
  - equal-content short and long strings compare unequal on the machine but
    equal under δ (R2-3 N2, R2-2 N5).
- **Soft-int helpers.**
  - `__moddi3` returns through `t0` and gets the remainder from
    `__udivdi3`'s `a1`;
  - `__divdi3` falls through;
  - symbol names are not code regions (R2-5 N2, R2-2 N4, R2-4 N5).
- **`luaV_equalobj` is neither pure nor position-independent.** It uses an
  `auipc` jump table and can reach `luaT_callTMres` (R2-5 N3, R2-3 N1).

| seed type | agents | ideas | only that seed type |
|---|---|---|---|
| chars | 6 | 30 | tablebase tails (R2-3), region spec for the libgcc block (R2-2), KProd (R1-2), stale snapshot (R2-2) |
| words | 4 | 20 | executable decoder as gate (R2-4), call nodes with residual rows (R1-4), graded footprint rings (R1-4), camera-square decode (R1-5) |

## 4. Retrieval by law

- **L-C4 / M1 (the arm refines the rule, via its C handler):**
  - Necula, "Translation Validation for an Optimizing Compiler", PLDI 2000,
    which validates gcc's register allocation, scheduling and branch
    optimisation, the source of our 46 dependence classes;
  - Tristan and Leroy, "Formal verification of translation validators",
    POPL 2008;
  - RISC-V interaction-tree semantics (arXiv 2605.04933).
- **M5 (callee summaries):** Myreen's decompilation into logic handles
  subroutines with specifications that name only the changed state
  (FMCAD 2012 "Improved"; "Machine-code verification for multiple
  architectures").
- **M3/M4 (frame, dead cells):** separation logic's frame rule; lenses with
  constant complement (Bancilhon & Spyratos, TODS 1981).
- **M6:** hash-consing and interning, the standard technique for pointer
  equality as content equality (Filliâtre & Conchon, ML Workshop 2006;
  recalled, to check).

## 5. Variation (ideonomy, 1 operator: negation)

- *Negate "prove each path"* → prove each join (tablebase tails, already in
  the pool).
- *Negate "relation carries the heap"* → the relation carries only
  registers and the heap is a rely (R1-4 #3 `regrow`, kept as the M4
  fallback).
- *Negate "helpers are callees"* → helpers inlined as arm code when
  loop-free after pruning (R2-1 #3). This is already in M5 as "classified
  after pruning".

No new survivor. The pool for the bake-off is M1–M6, plus tails, plus the
decoder gate. The executor is optional.

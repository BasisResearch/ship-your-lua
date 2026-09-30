# L-C2 (layout law): results

Input for `abstractions/ROUND-3.md` §2. Read-only over `c/lua-riscv-htif.elf`
and git history; no lake.

    python3 abstractions/checks/round3/lc2_layout.py      # ~5 s; writes lc2_arms.tsv
    python3 abstractions/checks/round3/lc2_layout.py > abstractions/checks/round3/lc2_layout.out

## The law as stated, and the verdict

**L-C2.** Two arms whose opcodes share an `opKernel` combinator differ only
in branch layout, so one proof keyed by the combinator's decision tree covers
both.

**Verdict: false as stated, true after two refinements.**
- The kernel combinator is the wrong key. `opArith` covers 21 arms and 11
  distinct machine decision trees; `docondjump` covers 10 arms and 6 trees;
  `setR`/`move` covers 7 arms and 5 trees.
- Refinement 1: the domain. The trees must be taken over F1's value domain,
  where no register or constant is a float. The float subtrees are what the
  proved arms already discharge one by one with `ValRepr.ne_float`.
- Refinement 2: the key. Group arms by the **pruned decision tree** P3p
  defined below: roughly the lvm.c macro, plus the operand access form, plus
  the named helper calls. Within one P3p tree the law holds: arms differ only
  in layout (1–3 raw layouts per tree) and in parameters (the ALU op, the
  predicate, the constants).

## Method

Arms are canonicalised with the round-2 falsifier canonicaliser
(`experiments/a1-falsifiers/canon.py`). It runs symbolic execution from the
dispatch head and is invariant under register renaming, scheduling, branch
polarity and block layout; its self-test is 54/54. The script re-hashes the
term DAG at progressively coarser levels:

| level | abstraction | classes (54 F1 opcodes) |
|---|---|---|
| L0 | exact | 54 |
| L1 | mod ALU (canon level 1) | 46 |
| L2 | + compare predicates, unordered successors (canon level 2) | 46 |
| L3 | + constants → K, shifts/slt → ALU | 43 |
| L3p | + every maximal pure computation → F(its non-pure leaves); the operand access stays | 45 |
| L4p | L3p with the pure libgcc helpers inside F | 40 |
| L5 | skeleton: branch/exit shape, #stores, names of non-pure callees | 33 |
| L6 | bare branch/exit shape | 27 |
| **P1** | L1 of the **F1-pruned** tree | 45 |
| **P3p** | L3p of the F1-pruned tree | **37** |
| P4p | L4p of the F1-pruned tree | 37 |
| P5 | L5 of the F1-pruned tree | 28 |
| raw layout | the conditional-branch mnemonics in address order | 33 |

How the F1 pruning works (`prune_dom`):
- It applies to every TValue tag byte of a Lua register or constant: an
  `lbu` at offset 8 mod 16 from `base` (s9) or from `k` (the `ld 0(sp)`).
- Each such tag ranges over `ValRepr`'s tags: nil variants, false, true,
  int, short/long string and light C function. Float is not in the range.
- The head constant s2 is 3 (`VmRel`'s `Pins`).
- A branch decided by one such tag is evaluated for each remaining value, and
  a successor that no value reaches is dropped.
- Tags of other objects, such as `_ENV`'s table in GETTABUP, are not pruned.

No level separates arms into classes that cut across combinators, except at
L6, which is too coarse (JMP≡MMBIN*, ADDI≡UNM).

## Per combinator (classes at L0 … P5; raw layouts)

| combinator | arms | L0 | L1 | L3p | P1 | P3p | P5 | layouts |
|---|---|---|---|---|---|---|---|---|
| opArith | 21 | 21 | 13 | 16 | 12 | **11** | 6 | 15 |
| docondjump | 10 | 10 | 10 | 8 | 10 | **6** | 4 | 7 |
| setR:move | 7 | 7 | 7 | 5 | 7 | **5** | 3 | 2 |
| setR:δ | 3 | 3 | 3 | 3 | 3 | **2** | 2 | 3 |
| mmbin | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 1 |
| jump | 2 | 2 | 2 | 2 | 2 | 2 | 2 | 2 |
| final (RETURN*) | 3 | 3 | 3 | 3 | 3 | 3 | 3 | 3 |
| callK, forloopK, forprepK, setNils, testsetK | 1 each | | | | | | | |

The multi-arm P3p trees, which are the classes where the refined law has
content:

| tree (P3p) | combinator | raw layouts | proved |
|---|---|---|---|
| ADD SUB MUL BAND BOR BXOR | opArith (RR) | 3 | 5 of 6 (not MUL) |
| ADDK SUBK MULK | opArith (RK) | 3 | 2 of 3 |
| BANDK BORK BXORK | opArith (RK) | 2 | 0 |
| LOADFALSE LFALSESKIP LOADTRUE | setR:move | 1 | 3 of 3 |
| LTI LEI GTI GEI | docondjump | 2 | 4 of 4 |
| LT LE | docondjump | 2 | 0 |
| SHL SHR | opArith (RR/shift) | 1 | 0 |
| UNM BNOT | setR:δ | 2 | 1 of 2 |

Two notes on these trees:
- ADD and BAND (op_arith vs op_bitwise) are different trees only because of
  floats (L1: 2 classes). Over F1 values they are the same tree (P1: 1
  class).
- LTI/LEI/GTI/GEI become one tree only once the predicate is a parameter
  (L3p). At L3 the `slt`+`seqz` form still separates them.

## Counterexamples to the stated law

These are pairs with one combinator but different pruned trees:
1. **Operand access form.**
   - RR, RK and RI differ (ADD / ADDK / ADDI).
   - The `K` operand is read through `ld 0(sp)`.
   - ADDI has one tag test, not two.
2. **BANDK/BORK/BXORK vs ADDK/SUBK/MULK.**
   - The bitwise-K arms have no tag test on `K[C]`.
   - This is the already-recorded statement bug: `Supported` must say that
     `K[C]` is an integer.
3. **Division family (MOD, IDIV, MODK, IDIVK).**
   - It adds `__moddi3`/`__divdi3` leaves, sign-fixup branches (5–6 F1
     branches, against 2) and a `luaG_runerror` exit.
   - It is its own tree per operand form, and MOD ≠ IDIV.
4. **Shifts.**
   - SHL and SHR are one tree (P3p). SHLI and SHRI are two trees: the
     operand roles differ (`luaV_shiftl(ic, ib)` vs `(ib, -ic)`), and they
     merge only at the P5 skeleton.
   - The shift trees differ from ADD's: they have 4–5 inline branches for
     the shift amount.
5. **LOADI vs LOADTRUE/LOADFALSE.** Both are `move` of an immediate, but
   `setbtvalue` stores no payload. The store count differs, even at P5.
6. **EQ/EQK vs EQI.** `luaV_equalobj` is a callee on every path; EQI is
   inline. **LT/LE vs LTI…GEI:** 7 branches plus `l_strcmp` and
   `luaT_callorderTM`.
7. **JMP vs VARARGPREP** (`jump`). VARARGPREP calls `luaT_adjustvarargs`.
   **TEST vs TESTSET**: TESTSET stores.
8. **MUL ≡ ADD as a tree, but `__muldi3` is a machine call.**
   - The tree identity holds because `__muldi3` is a pure ALU leaf.
   - The proof still needs the soft-int callee contract. The tree law does
     not remove the callee cost.
9. **Residual paths the value domain cannot remove.**
   - FORLOOP keeps its float-loop subtree (5 F1 branches) and FORPREP keeps
     23 branches. The "step not integer ⇒ float loop" test is `ttisinteger`,
     which is excluded only by the kernel/FORPREP invariant, not by
     `ValRepr`.
   - These are kernel-vacuous paths. A tree proof needs the kernel's
     precondition as a named pruning premise.

## Refined law (L-C2′)

For arms `o₁` and `o₂` whose F1-pruned, value-parameterised decision trees
are equal (P3p), `sim_o₂` is `sim_o₁`'s proof with a different table row.
The row gives:
- the ALU function;
- the predicate;
- the constants;
- the branch-layout string.

The tree is determined by (lvm.c macro, operand access form, named helper
leaves), not by the `opKernel` combinator.

Counts:
- 51 sim-shaped F1 arms (54 minus RETURN*) have **34 distinct trees**.
- The 25 proved arms cover **15** of them.
- The 29 unproved arms need **19 new trees** (P3p against the proved set).

## Does the incumbent's hand cost follow trees? (ledger + git)

The script replays the ledger order: an arm is a new tree, a new layout of a
proved tree, or a row (tree and layout both seen).

| category | arms | ledger hand lines | mean |
|---|---|---|---|
| new tree | 15 | 846.0 | 56.4 |
| new layout of a proved tree | 4 (SUB, SUBK, BAND, LEI) | 92.5 | 23.1 |
| row | 6 (BOR, BXOR, GTI, GEI, LOADFALSE, LFALSESKIP) | 127.5 | 21.2 |

The ledger splits each commit's lines evenly over its arms, which inflates
the row and layout means (GTI/GEI are charged 33 each). By commit:
- commits made only of layouts and rows are cheap: SUB 23 lines,
  BAND+BOR+BXOR 6;
- commits that add a tree cost 53–136 lines per new tree: ADDI 111, BNOT 53,
  NOT/TEST/TESTSET 272 for 3 trees.

**Where the hand lines of the 19 post-bake-off arms went** (commits
`791175d`..`8358d37`, 777 added code lines; the script's `commit_costs`
classifies each added line by its enclosing top-level definition in
`gen_lua_arm.py`):

| category | lines | share |
|---|---|---|
| kind templates (PRE2/FACTS2/paths per kind) | 374 | 48% |
| hand Lean (Close/StepK/Rel/Mem/Entry: guards, inversions, closes) | 231 | 30% |
| operand-access templates (ARITH_PRE/FACTS, KFACTS, KPARAM…) | 76 | 10% |
| shared infrastructure (walk/chain2/pins…) | 41 | 5% |
| table rows (ARMS2, SIM_OPS) | 37 | 5% |
| branch-layout data (ARITH_RR/BIT/RK, CMPI, TAG_TEST, FLOAT_TEST, SETTAG, TAGSLOT) | **18** | **2%** |

Branch layout is 2% of the cost. The cost is new trees, as kind templates
plus their hand Lean. The generator's kinds are already keyed roughly by
tree:
- `arith` spans 3 operand-form trees plus the op_bitwise layout;
- `cmpI` is one tree;
- `truth` spans 3 trees.

**Implication.** A layout-generic proof removes only the 2% layout share, or
at most the rows as well (about 7%). The gate stays red as long as each new
arm is mostly a new tree, and 19 of the 29 remaining arms are.

## Prediction for the 29 unproved F1 arms (P3p against the proved 25)

The segment set's "52 F1 arms" is the Fragment's 54 minus MMBIN/MMBINI/MMBINK,
plus LOADF; the table uses the Fragment's 54.

| arm | tree class | F1 branches | callees / helper leaves |
|---|---|---|---|
| MUL | row (ADD's tree) | 2 | `__muldi3` |
| MULK | new layout (ADDK's tree) | 2 | `__muldi3` |
| UNM | new layout (BNOT's tree) | 1 | `luaT_trybinTM` (the non-number path) |
| BANDK, BORK, BXORK | 1 new tree, then 2 rows | 1 | none (inline; the `K[C]` integer premise is missing) |
| SHL, SHR | 1 new tree + 1 row | 5 | none (inline) |
| SHLI, SHRI | 2 new trees | 4 | none (inline) |
| LOADNIL | new tree | 1 (a loop) | none (`loopFromBody`) |
| MOD, MODK, IDIV, IDIVK | 4 new trees | 5–6 | `__moddi3`, `__divdi3`, `luaG_runerror` (error exit) |
| EQ, EQK | 2 new trees (one P5 skeleton) | 1 | `luaV_equalobj` |
| LT, LE | 1 new tree + 1 layout | 7 | `l_strcmp`, `luaT_callorderTM` |
| MMBIN, MMBINI, MMBINK | 3 new trees | 0 | `luaT_trybin{,i,assoc}TM` |
| GETTABUP | new tree | 2 | `luaH_getshortstr`, `luaV_finishget` |
| VARARGPREP | new tree | 1 | `luaT_adjustvarargs`, `luaD_hookcall` |
| CALL | new tree | 5 | `luaD_precall` (→ print chain), `luaG_tracecall` |
| FORPREP | new tree | 23 | `__hidden___udivdi3`, `luaV_tointeger`, `luaV_tonumber_`, `luaG_forerror`, `luaG_runerror` |
| RETURN, RETURN0, RETURN1 | not sim-shaped (`vmRel_final_Statement`) | 8–59 | `luaD_poscall`, `luaF_close`, `luaG_tracecall` |

**Summary of the 26 sim-shaped unproved arms** (the 29 minus the three
RETURN*):
- **3 arms reuse a proved tree** (row or layout): MUL, MULK and UNM. All
  three still need a callee contract: `__muldi3` or `luaT_trybinTM`.
- **8 arms are inline, with no callee:**
  - 5 new trees: BANDK, SHL, SHLI, SHRI and LOADNIL;
  - 3 rows of those trees: BORK, BXORK and SHR.
- **15 arms need callees.** They make 14 new trees, plus LE as a row of
  LT's tree:
  - MOD, MODK, IDIV, IDIVK;
  - EQ, EQK, LT;
  - MMBIN ×3;
  - GETTABUP, VARARGPREP, CALL, FORPREP.

New trees: 5 + 14 = 19. After the tree law, 18 of the 26 arms need callee
contracts (L-C3) and 5 need new inline trees. Layout is not the remaining
cost.

## Caveats

- The new levels (L3p/P*) reuse canon.py's term DAG, whose self-test covers
  its invariances. The pruning and pure-value collapse were not separately
  fuzzed. The tag-load recogniser is syntactic: an offset ≡ 8 (mod 16) from
  `base` or `k`, with an address built only from `base`, the fetched
  instruction and `k`.
- The per-line classification of generator diffs is by enclosing top-level
  definition. Rows count modified lines as added. Docstrings inside
  templates count as code.

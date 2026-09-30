# Abstraction discovery — round 1

Procedure: `~/.claude/skills/abstraction-discovery/SKILL.md`. Started 2026-09-30,
triggered by the gate (`abstractions/gate.py`, check.sh stage 3c) on its first
run. Proving is paused for the round: the A0.6 boot-witness agent and the A1
pilot-arm agent were stopped at a clean point, and their unproved cases are
held out.

## 1. Obligation census

`python3 abstractions/census.py` lists every hand-written proof outside the
verbatim copies and generated files. `python3 abstractions/gate.py --report`
lists the cases of each cluster in introduction order (git blame). Cost is
counted in non-blank, non-comment proof lines per case; for an arm that
contains other arms, only its own lines count.

| cluster | cases | first-quarter mean | last-quarter mean | trend | gate |
|---|---|---|---|---|---|
| `ast-construct-fanout`: per source construct, the interpreter-soundness and determinism arms | 187 | 2.3 | 4.6 | rising ×2.0 | **FAIL** |
| `bc-rule-fanout`: per bytecode rule, `step?_sound`/`step?_complete`/`Step.sim` arms | 75 | 1.4 | 8.3 | rising ×5.9 | **FAIL** |
| `tv-program`: per program, the TV facts | 21 | 1.6 | 2.0 | flat, at the floor | ok |
| `os-trace`: per trace, facts about `next` | 18 | 1.5 | 2.5 | flat, at the floor | ok |
| `a1-arm-sim`: per opcode, the machine-arm simulation | 0 | — | — | forecast | — |
| `boot-witness`: facts of the `VmLoaded` witness | 0 | — | — | forecast | — |

**Aggregate per bytecode rule.** Summed over the three metatheory theorems
(`step?_sound`, `step?_complete`, `Step.sim`), a rule costs 8.5 lines on
average and up to 16 (`EQK`, `arith`). On top of that come the definitions
the rule needs in 5 more places: its `Step` constructor, its `step?` arm, and
its `edgesOf`, `reads` and `regTop` entries. Adding the 11 bitwise opcodes (F1b)
touched all of them, and `BNOT` alone cost 10 proof lines. A1 will add one
machine-arm simulation per rule. In ship-your-interpreter the equivalent
per-site families reached 706 site rows in 40 `*_sites.tsv` tables and 250
`Vsa/Sim/rows` modules.

**Aggregate per source construct.** A construct costs one interpreter arm, a
soundness arm (`execSound`: `while_`/`repeat_` 19 lines each, `if_` 16,
`fornum` 15), and determinism arms. The determinism proof inverts each pair
of rules that share a construct (`whileT` × `whileF` × `whileX` …), so its
arm count grows with the square of the number of rules per construct:
`Eval.det` has 50 arms, `ExecS.det` 53.

Representative instances:

- `bc-rule-fanout`:
  - `Step.sim` arm `forloopAgain` (13 lines). It re-derives, for one rule,
    that equal read registers give equal written registers.
  - `step?_sound` arm `TESTSET` (12 lines). It re-derives, for one rule,
    that the stepper's output is the rule's conclusion.
- `ast-construct-fanout`:
  - `execSound` arm `while_` (19 lines). It re-derives, for one construct,
    that the interpreter's case is the relation's rule.
  - `ExecS.det` arms `whileT`/`whileF`/`whileX`. They re-derive, for one
    construct, that the rules' guards are exclusive.

## 2. Laws

**L-B1: bytecode footprint.** For every F1 instruction `w` at a pc whose
edges exist, take two states that agree on pc, output and the registers
`reads w`. Then they are both stuck, or both step to the same pc and output.
There is then an edge `(pc', wr)` of `edgesOf` such that the successors agree
on `wr`, and every register outside `wr` is unchanged. This one law is the
content of every `Step.sim` arm.

- **Check** (`abstractions/checks/FootprintLaw.lean`, random states and
  instruction words, against the executable `step?`): 200,000 trials, 77,129
  steps, 85,442 both stuck, **0 counterexamples** over all 54 F1 opcodes.
- **Two refinements came out of the first run** (97 counterexamples):
  - The law needs the precondition "the edges exist". That is what
    `Supported` gives: a `LOADK` of a string, or a `FORLOOP` jumping before 0,
    steps but has no edges.
  - The quantifier must be *some* edge with that target, not *the* edge.
    `TESTSET` has two edges with the same target when `sJ = 0`, and only one
    of them writes `R[A]`.

**L-B2: the stepper is the semantics.** `Step H p s s' ↔ step? H p s = some s'`.
This one law is the content of every `step?_sound` and `step?_complete` arm.

- **Check:** both directions are already proved, rule by rule
  (`step?_sound`, `step?_complete`). The law holds; it is the cost that is
  the target.

**L-A1: the source semantics is the graph of a function.** `LuaSem H c out ↔
∃ fuel, luaRun H fuel c = some out`. The `→` direction is completeness; `←` is
`luaRun_sound`. Determinism and soundness of every construct are instances of
it.

- **Check** (`abstractions/checks/graph_law.py`, random well-scoped F1
  programs with bounded loops, `goto continue`, all integer operators): the
  interpreter against native `lua`. Seed 1: 32 programs; seed 7: 121 programs.
  **0 mismatches**, and every program is `AstSupported`. Programs that raise
  a runtime error in native Lua (arithmetic on a boolean) are skipped: they
  have no behaviour on either side.

**L-C1 (forecast, A1): one machine arm per rule.** For each F1 rule `r`, run
from the dispatch head on any machine state representing `s`, the
`luaV_execute` arm for `r`'s opcode reaches the dispatch head on a state
representing `s'`, where `Step s s'` by `r`.

- **Check (indirect):** 18 difftests agree on output with native Lua, and
  the kernel validations of `while`/`f1_ops`/`f1b_bits`/`print_print` give
  `BcSem` output equal to the ELF's.
- A trace-level check, decoding the VM state at every dispatch head of a
  traced run and comparing it with `step?`, needs A0.6's representation
  decoders. It is pending.

Tools were used here only to check laws (step 2). None of them is proposed as
an abstraction.

## 3. Blind ontologist fan-out (deep seeded, 2 rounds × 6)

The brief is `abstractions/pilot/ONTOLOGIST_BRIEF.md`. Agents saw only the
semantics, the census, the laws and the suite, never a proof file. The raw
answers are in `abstractions/fanout/R1-*.md` and `R2-*.md`. Round 1 used 4
character-string seeds and 2 word seeds; round 2 had the same split and read
all of round 1. Round 3 was not run: round 2's contributions were
corrections and extensions of round-1 ideas, not ideas with no round-1
precursor. The one exception is the oracle `Host`, which matters for F2 and
not for this bake-off.

**Agreement.**
- 5 of 6 round-1 agents independently reached a single per-opcode first-order
  term with `Step`, `step?` and the tables derived from it (C1).
- 6 of 6 proposed a generic "rulebook is a function" or determinism-format
  theorem for the source side (C4).
- 4 of 6 proposed a shared primitive δ (C3).
- In round 2, 5 of 6 agents objected to C1's write sets and converged on
  kill ports (C2).

### Candidates, clustered by mechanism

**C1. One per-opcode term; everything else derived (bytecode; L-B1, L-B2).**
- *Sources:*
  - R1-1 #1: intrinsically-footprinted micro-op trees (chars).
  - R1-2 #1: register micro-code (chars).
  - R1-2 #2: section-typed transfer functions (chars). A variant: the
    footprint is carried in the type, and L-B1 follows by `congrArg`.
  - R1-3 #1: static-footprint kernel (chars).
  - R1-4 #1: read–choose–write normal form (chars).
  - R1-5 #1: port-typed kernels (words).
  - R1-6 #1: avatar microcode, a selective-applicative term (words).
  - R1-6 #2: dialysis-membrane frames (words), which is close to R1-2 #2.
- *Mechanism.* `Step` has one constructor: fetch, then run the opcode's term.
  `reads`/`edgesOf`/`regTop` are folds of that term, and `step?` is the same
  term run in `Option`.
  - L-B2 holds by definition.
  - L-B1 is one induction over the term (or `congrArg` in the section-typed
    variant).
  - The "*some* edge" refinement is free, because the term chooses an edge
    *index*.
- *Known.* Selective applicative functors (Mokhov et al., ICFP 2019);
  algebraic effects (Plotkin & Power 2003); Sail's one specification with
  several interpretations (Armstrong et al., POPL 2019).
- *Novel.* Deriving the definite-initialisation analysis's input as an
  abstract interpretation of the opcode term.

**C2. Kill ports / poisoned writes (bytecode; the correction to C1).**
- *Sources:*
  - Round 1: R1-1 #3 (X-propagating registers, chars) and R1-5 #2 (poisoned
    stores and query certificates, words).
  - Round 2: R2-1 #1, R2-2 #1, R2-3 #1, R2-4 #1, R2-5 #2 and R2-6 #2 (every
    round-2 agent).
- *Mechanism.* An edge is (target, defs, kills), and killed registers hold ⊥.
  - Reads are strict, and one theorem `kill_unobservable` (certain answers)
    replaces `keepMask`, the CALL special case, `bcSemFrom_iff` and
    `cbcSem_iff`.
  - It is required for a faithful H2. The round-1 kernels that gave `CONCAT`
    the write set `{A}` make L-B1 false (R2-6 #2 and others; checked by the
    coordinator in `lvm.c`). Kernels that give the whole range instead must
    copy `luaV_concat`'s passes into the trusted text.
- *Known.* Certain answers over nulls (Imieliński & Lipski 1984); LLVM poison
  (Lee et al., PLDI 2017); Scott's flat domains.

**C3. Shared primitive δ used by both layers.**
- *Sources:*
  - R1-1 #4: factored opcodes Prim × Addr × Cont.
  - R1-2 #4: one δ.
  - R1-4 #5: sort-erased core algebra.
  - R1-3 #2: microcode dictionary, which adds per-macro machine templates.
  - R2-3 #2 and R2-6 #4: three-valued δ (`ok | meta | err`), objecting that
    stuck is not free, because failed arithmetic falls through to the
    `MMBIN` arm.
- *Mechanism.* H2–H5 become δ cases. Operator agreement between the layers
  is `rfl`.
- *Known.* CompCert's shared `eval_operation`; initial-algebra semantics
  (Goguen et al., JACM 1977); order-sorted algebra (Goguen & Meseguer, TCS
  1992).

**C4. The source semantics is the graph of a generic rulebook (L-A1).**
- *Sources:*
  - R1-1 #2: discriminant skeletons (chars).
  - R1-2 #3: derivations as parses, LL(1) (chars).
  - R1-3 #3: the graph of a reified recursion, a free call monad (chars).
  - R1-4 #2: construct trees (chars).
  - R1-5 #3: a determinism rule format (words).
  - R1-6 #3: LL(1) rule grammars (words).
- *Mechanism.* Rules become data: a construct's tree or description.
  - One generic theorem, `graph : Sem D x y ↔ ∃ fuel, run D fuel x = some y`,
    gives determinism, soundness and completeness at once.
  - The quadratic pairwise inversion disappears.
- *Known.*
  - Owens et al., functional big-step (ESOP 2016).
  - Bove & Capretta (MSCS 2005); interaction trees (Xia et al., POPL 2020).
  - Aceto et al., rule formats for determinism (SCP 2012); skeletal semantics
    (Bodin et al., POPL 2019); Freyd & Scedrov (maps in allegories).
- *Novel.* Reading big-step determinism as an LL(1) condition on derivations.

**C5. Pretty-big-step with one abort rule.**
- *Sources:* R1-3 #4 and R1-4 #3.
- *Mechanism.* It keeps the inductive, and determinism becomes linear. This
  is the control for C4.
- *Known.* Charguéraud (ESOP 2013).

**C6. Definite initialisation as noninterference.**
- *Source:* R1-6 #5.
- *Mechanism.* Low-equivalence becomes A1's representation relation, which
  links C2 across the two layers.
- *Known.* Goguen–Meseguer; Hunt–Sands (POPL 2006).

**C7. Machine arms, the delta half (A1): lift or parse each arm into a C1
term, then compare.**
- *Sources:*
  - R1-1 #5: lifted micro-op traces up to Mazurkiewicz reordering.
  - R1-2 #5: dispatch head as a Poincaré section, with a verified symbolic
    evaluator and one `rfl` per arm.
  - R1-4 #4: idiom grammar decompiler.
  - R2-1 #5: certificate-checked arms, where an untrusted certificate plus a
    verified checker absorbs branch polarity, renaming and scheduling.
  - R2-2 #5: tag-symbolic arms, with finite control checked by automaton
    product.
- *Known.* Myreen's decompilation into logic (FMCAD 2008), with a Lean 4
  RISC-V port at github.com/dhsorens/riscv-decomp; proof by reflection
  (Boutin 1997); Islaris (PLDI 2022).

**C8. Machine arms, sharing between arms.**
- *Sources:*
  - Round 1 (orbits and templates): R1-5 #4, R1-6 #4, R1-3 #2.
  - Round 2 objections (prefix/phylogeny trees; dependence-graph orbits;
    `-O` flags that preserve sharing): R2-4 #4, R2-2 #4, R2-5 #3, R2-6 #3,
    R2-3 #5.
- *Evidence.* The coordinator's objdump check (§2) found exact identity
  within `{BAND,BOR,BXOR}`, `{LTI,LEI,GTI,GEI}`, `{ADDK,SUBK}` and `{LT,LE}`.
  `ADD`/`SUB` differ by branch sense; `MUL`/`MULK` by register allocation and
  scheduling.
- *No saving on the held-out arms.* ADD, EQI and FORLOOP are in three
  different families (R2-4, R2-5).

**C9. Machine arms, the frame half (A1).**
- *Sources:*
  - R1-3 #5: a lens with constant complement.
  - R1-5 #5: tethered separation.
  - R2-4 #5: rely-lenses for GC and allocation.
  - R2-6 #5: a relocatable view.
  - R2-5 #5: content-named strings.
- *Objections from round 2:*
  - `print`'s call entry (`checkstackGCp`) can reallocate the Lua stack, so
    registers must be decoded by offset from `L->stack` (R2-6 #5).
  - GC and interning break a "constant complement" (R2-4 #5).

**C10. Surviving F2 (not measurable on H).**
- *Oracle `Host` fields:* `next` order and printed addresses as functions of
  the history (R2-1 #2, R2-2 #3, R2-3 #3, R2-4 #2, R2-5 #4, R2-6 #1).
- *Two-speed footprints:* static register ports and adaptive heap queries
  (R2-2 #2, R2-3 #4, R2-4 #3, R2-5 #1), plus a ghost `top` register for
  multi-result calls (R2-1 #3).
- *A1 priced per callee:* R2-1 #4.

**Findings produced by the fan-out and checked by the coordinator.**
- H2's write set is the whole range (`lvm.c`); the suite is corrected.
- String arithmetic coerces, and `"1.5"+1` gives a float (native run). A
  strings fragment is not closed without floats; the suite gets H5 and the
  plan changes (SUITE.md).

| seed type | distinct ideas contributed | ideas only that seed type produced |
|---|---|---|
| chars (8 agents) | 40 | Mazurkiewicz-trace arm comparison (R1-1 #5); Poincaré-section arms (R1-2 #5); LZ microcode dictionary (R1-3 #2); lens with constant complement (R1-3 #5); idiom-grammar decompiler (R1-4 #4); certificate-checked arms (R2-1 #5); tag-symbolic arms (R2-2 #5); typed-error sink (R2-3 #2); `-O` flags that preserve sharing (R2-3 #5) |
| words (4 agents) | 20 | orbit transport (R1-6 #4, R1-5 #4); DI as noninterference (R1-6 #5); tethered separation logic (R1-5 #5); relocatable view (R2-6 #5); content-named strings (R2-5 #5) |

## 4. Retrieval by law

Every candidate is *known* except the pieces marked novel above. Searches were
phrased by the law, not by the project:

- *"relational big-step semantics defined as the graph of a functional
  interpreter, deterministic by construction"*:
  - Owens, Myreen, Kumar, Tan, "Functional Big-Step Semantics", ESOP 2016
    (cakeml.org/esop16.pdf);
  - Charguéraud, "Pretty-Big-Step Semantics", ESOP 2013;
  - Bodin et al., "Skeletal Semantics and their Interpretations", POPL 2019
    (arXiv 1809.09749).
- *"instruction footprint read/write sets derived from one instruction
  specification"*: Isla, which derives Sail instruction footprints by
  symbolic execution (Armstrong et al., FMSD 2023).
- *"machine code turned into a function with a certificate"*:
  - Myreen, decompilation into logic (FMCAD 2008; Cambridge TR-765);
  - a Lean 4 RISC-V implementation, github.com/dhsorens/riscv-decomp;
  - Islaris (Sammler et al., PLDI 2022), machine code against Sail with an
    Iris separation logic.

## 5. Variation (ideonomy)

Drawn tuple: operators *tree-finding* and *dimension-identification*;
organon *periodic grid*; prompts *connectivity*, *scope*, *source*. Applied
to the top two candidates:

- **A** = C1+C2, the per-opcode kernel with read/def/kill ports;
- **B** = C4, the source semantics as the graph of a rulebook.

### Tree of "specify once as data, prove one generic theorem"

```
  meta-semantics: one datum, many interpretations  (root; too general)
  └─ executable specification with derived metatheory
     ├─ operators as data .................... C3 δ
     ├─ instructions as data ................. A (kernel + ports)
     ├─ rules as data ........................ B (rulebook graph)
     ├─ machine arms as data ................. C7 (certificates / lifted terms)
     └─ loaded state as data ................. the A0.6 boot generator (today:
                                                per-program witness data)
```

The siblings share a parent, so B and A should share the same leaves:

- B's primitive premises are A's δ and kernel terms (variant V3).
- The "by level" cut between one opcode and the whole semantics is the
  lvm.c macro (`op_arith`, `op_order`, `docondjump`). That is R1-3 #2's
  scope, one level up from A. It predicts that A's terms should be built
  from about 9 macro combinators, not 54 free-standing terms.

### Periodic grid: layer × property proved once

Every cell should hold one generic theorem over data. Rows are the layers;
columns are the three properties the refinement chain needs.

```
                    | functional (graph)      | footprint / frame            | refines the layer below
--------------------+-------------------------+------------------------------+-------------------------------
source (LuaSem)     | B: graph of rulebook    | (V1) EMPTY -> rulebook-      | (V2) EMPTY -> compile check
                    |                         |  derived free-var footprint  |  as a data-level comparison
bytecode (Step)     | A: kernel run = Step    | A+C2: footprint w/ kills     | C7: arm certificates / lift
machine arm         | Sail: Halts.deterministic| C9: relocatable frame view  | (none: bottom layer)
                    |  (already proved)       |                              |
loaded state (boot) | undump as a function    | n/a                          | (V4) EMPTY -> generic undump
                    |  (gen_proto = lundump?) |                              |  theorem (lundump refines it)
```

The empty cells are predictions:

- **V1 (source × footprint).**
  - The prediction: "an expression's value depends only on the locals it
    mentions", derived from the rulebook exactly as A derives `reads`.
  - Who needs it: B2's register allocation (compiling locals to registers)
    needs this frame lemma for every construct. Without V1 it is the next
    per-construct cluster.
- **V2 (source × refinement).**
  - The prediction: if rules (B) and instructions (A) are both data,
    compiler correctness can be stated as one generic theorem, "a rule
    simulated by its code template", plus a *decidable* per-construct check
    that compares the rule's data with its compiled kernel terms.
  - Novel. It turns B2's per-construct simulation cluster into `decide`.
- **V4 (loaded state × refinement).**
  - The prediction: undump (`lundump.c`) as a Lean function, with the
    `ProtoRepr` witness stated once for every chunk.
  - Who needs it: without V4, the boot-witness cluster is per-program data
    with per-program `decide` facts. That is flat at best, and the gate will
    fire on it.
- **Source prompt.** A kernel *derived from lvm.c* by a verified C-to-kernel
  translation, not hand-written. As a variant this is near-nonsense at
  today's scale. It shows that the trusted base is carried by the reviewed
  transcription, which is why C1 must keep terms readable next to `lvm.c`.
- **Connectivity prompt.** A's opcodes are independent: sparse connectivity,
  so parallel per-opcode terms. B's constructs are densely connected through
  mutual recursion (blocks, loops, goto). That explains why B's setup is
  larger in every round-1 estimate (300–700 lines against A's 150–250).
- **Scope prompt.** Both A and B are "global" to the layer. Narrowed to one
  construct family (`Eval` only, or arith opcodes only), each still pays
  most of its setup. The pilot must build the whole generic theorem, and the
  bake-off measures setup at full scope.

Added to the pool: V1, V2 and V3. V4 is recorded for the A0.6 cluster.

## 6. Pilot bake-off

The protocol is in the scratchpad (`bakeoff.md`), reproduced in each
report. Each contender, in its own worktree off `79b6082`, did three things:

1. **Setup:** built its abstraction.
2. **Refactor:** re-seated R1 or R2 on it, keeping every public theorem name
   and every kernel check against the ELF.
3. **Held-out:** implemented H1–H5 (the F4-lite strings of
   `abstractions/pilot/SUITE.md`), proving `c/tests/f4_strlite.lua`'s
   output against the Sail run.

Cost is counted in non-blank, non-comment Lean lines. Per-contender tables
are in `abstractions/bakeoff/*.md`.

### bc-rule-fanout (bytecode)

| contender | setup | R1 after refactor (orig. 857) | held-out spec | held-out proof | tables | failed builds | wall |
|---|---|---|---|---|---|---|---|
| incumbent (hand per-rule) | 0 | 857 | 87 (+49 shared) | **135** | hand | 1 | ~17 min |
| A′: section-typed transfer (R1-2 #2 + kills) | 47 | 417 (464 with setup) | 88 | 0 | hand-written, type-checked | 3 | 35 min |
| **A: kernel terms + kill ports + δ (C1+C2+C3)** | 197 | **324 (440 with setup)** | **79** | **0** | **derived** | **0** | 42 min |

### ast-construct-fanout (source)

| contender | setup | R2 after refactor (orig. 510) | held-out spec | held-out proof | failed builds | wall |
|---|---|---|---|---|---|---|
| incumbent (hand per-construct) | 0 | 510 | 44 (+49 shared) | **94** | 0 | ~6 min |
| C5: pretty-big-step + one abort rule (control) | ~43 | 200 (243 with setup) | 66 | 0 | 3 | 34 min |
| **B: graph of a generic rulebook (C4)** | 113 | **20 (94 with setup)** | 63 | **0** | 4 | 22 min |

### Findings from the bake-off

The contenders found these independently:

- **`CONCAT` clobbers every register above `A`, not only `A+1..A+B-1`.**
  `checkGC` runs with `top = ra+1`, and an atomic GC step clears the stack
  above `top`. This mattered only if the collector runs; ours is stopped.
  - Found by the incumbent, A′ and R2-2.
  - With kill ports it is a one-token choice. The incumbent had to copy
    CALL's 14-line clobbering case (its duplication signal).
- **`UNM` calls `luaT_trybinTM` in its own arm; no `MMBIN` follows it.**
  - Found by the incumbent and A′. SUITE.md's H5 wording was wrong here.
- **`"10.0"+1` is a float.** String arithmetic gives an integer only when
  `luaO_str2num` does.
- **Every arithmetic opcode gains a real edge to its `MMBIN*`**, so the old
  "`MMBIN` is never executed" model had to go.
- **What removes the held-out proof on the source side.** C5 attributes it to
  operators written as one partial function (δ/`binVal`), which both source
  contenders used. The abort rule and the rulebook account for the *refactor*
  gains.
- **A's derived tables close a faithfulness hole A′ keeps.** A too-small
  hand-written def mask silently under-writes. A's per-kernel read ports are
  slightly coarser than `lvm.c`: `FORLOOP`'s exit edge reads `R[A]`. This is
  invisible on `Supported` programs.

## 7. Decision

A candidate wins a cluster if its held-out cost falls AND its refactor shrinks,
both measured against the incumbent.

- **bc-rule-fanout → A (kernel terms with read/def/kill ports and a shared δ).**
  - Held-out proof: 135 → 0.
  - R1: 857 → 440 including setup.
  - It beats A′ on refactor (440 vs 464), held-out spec (79 vs 88) and failed
    builds (0 vs 3). It also derives the tables instead of hand-keeping them.
  - Merged as `00507d5`.
- **ast-construct-fanout → B (the graph of a generic rulebook).**
  - Held-out proof: 94 → 0.
  - R2: 510 → 94 including setup.
  - It beats C5 (243 including setup).
  - Merged as `84c45e2`.

**Enforcement.**
- CLAUDE.md: the new mandatory routes for a new opcode (one `opKernel` entry)
  and for a new construct (one rulebook arm).
- `scripts/discipline_rules.tsv`:
  - **R16** rejects files with more than 4 hand rule arms (`| @…`) in `Lua/`;
  - **R17** rejects re-introducing an inductive `Step`/`Exec`/`Eval`/`ForIter`.
- The gate is re-baselined at the adoption commit:

baseline bc-rule-fanout 84c45e2
baseline ast-construct-fanout 84c45e2

**Not decided this round.**
- **A1 (machine arms).** Candidates C7–C9 are recorded with their cheap
  falsifiers: a Python canonicaliser for dependence-graph orbits, a count of
  `ADD`'s exits, and a log of `L->stack` at each dispatch head. A1 has no
  proofs yet to measure, so it waits for a round 2 once the first arms are
  proved and the gate has data.
- **Boot witness (V4, generic undump).** Same: it waits for data.
- **F2 survival.** Oracle `Host` and two-speed footprints (C10) go into PHASES
  as design constraints for F2.
- **Plan change.** Strings must land with floats (SUITE.md finding).

## Carried to round 2 (A1)

**Incumbent to evaluate.** syi-7e reports that the "verified symbolic
evaluator, one check per arm" candidate (C7) already exists on
ship-your-interpreter's `exponentiate` branch:

- `VsaIris/Vsa/SymExec.lean`: `symRun`, `symRun_auto` (proved sound against
  `SWP`), the reflective obligation checker `obCheck` over interval `Geom`
  facts, and the image code pins `CodeAt`/`rangeText`;
- the tactic `sym_run` (`VsaIris/Interp/SymInterp.lean`).

**Measured there:** 3.3–5.7× less CPU per run piece than per-pc lemma
stepping.

**Known gaps** (a v2 is in progress there):
- decode is paid per instruction;
- only 64-bit store forwarding;
- no call nodes, so every `jal ra` stops the run;
- no branch merging.

**Plan.** Round 2's A1 bake-off should include it as a contender, copied once
merged, rather than build a second evaluator. The ship-your-lua segment
batteries (A0.7/A0.8) are the per-site incumbent it competes with.

**Update from syi-7e (2026-09-30).**
- *Status.* `exp-A` is merged into `exponentiate` (draft PR
  BasisResearch/ship-your-interpreter#13, base `cleanup` #8). It is not on syi
  main, so not yet copyable here.
- *Contents:*
  - `Vsa/Sim/TextImage.lean`: code residency as image ranges, with generic
    byte pins in `chain_facts`;
  - `VsaIris/Vsa/StepGen.lean`: `#step_table`, step lemmas elaborated from the
    image, with a per-ELF `Tbl`. Its compile cost is about that of generated
    tables;
  - `SymExec`/`sym_run`.
- *Their round-1 allocator bake-off:*
  - surgery permits: −29–66% lines, CPU neutral;
  - region-keyed memory: −53–63% lines, but 1.6–1.85× slower per theorem;
  - a combined candidate is being measured.
- *For our round 2.* Include `SymExec` and `TextImage` as A1 contenders once
  merged. Their region-keyed memory result says to record per-theorem CPU,
  not only lines.

**Update from syi-7e (later, 2026-09-30).** `exponentiate` has no per-pc
step tables at all:

- Step lemmas are elaborated on demand from the image, as instances of one
  rule set (`VsaIris/Vsa/StepRules.lean`, `StepGen.driverLemma?`).
- Every interpreter run goes through `sym_run`.
- A clean build of the cleanup cone is 3,774 module-seconds, against 32,740
  before.

This is the strongest A1 contender for round 2, once it is merged on syi
main. Our incumbent is the generated segment batteries (`Lua/Vm/Arms`, about
132k generated lines) plus `gen_lua_arm.py`
(`abstractions/pilot/A1-incumbent.md`).

# Abstraction discovery, round 5: float arms and soft-float specifications

**Trigger.** The float pilot (lane float-m0, `abstractions/ledger/float-m0.md`)
failed its cost test:
- the held-out float `FORLOOP` costs 29 hand lines, 10–14× an int arm;
- the held-out mean is 2.8–3.8× the int-arm mean, against a 1.5× bound;
- gate cluster `a1-float-arm` (12 cases) costs 2.7 lines per case in the
  first quarter and 13.3 in the last;
- `ADDI` needed a new 20-line kit hand-off (`at_farith`);
- no level-(b) equation "lifted routine = `F64` spec" exists. All eight are
  one named premise, `SoftFloatSpec`.

**Base.** Branch `r5-census`, from float-m0's head `66d822e`, not yet on main.
The build outputs are float-m0's own.

**Gate.** Still wired on this branch: `scripts/check.sh` stage 3c runs
`abstractions/gate.py` and fails with "a1-float-arm: 12 cases — FAIL (first-quarter
mean 2.7 lines, last-quarter mean 13.3)".

**Measurement rules (shared machine).**
- No `lake build Lua`. Every number comes from a single-file
  `lake env lean` under an 8 GB cap, started only when at least 25 GB are
  free (`abstractions/checks/round5/run_lean.sh`).
- The other numbers come from scripts over the ELF and the generated files.
- The scripts and their outputs are in `abstractions/checks/round5/`.

## 1. Census

### 1.0 What the headline theorems reach

The headline theorems are `vm_refinement_of_open`/`vm_refinement_of_open'`
(`Lua/Vm/Sim/Fold.lean`, `StuckErr.lean`). They take `FloatArms` as an open
structure.

None of float-m0's output is referenced outside its own files: the six
`sim_*_flt`, the nine `Lua.Vm.Fn.<R>.sum` and `SoftFloatSpec`. A grep for
those names outside `Kit/AtFlt*`, `Vm/At/` and `Vm/Fn/` finds only doc
comments. So the constant closure of the headline excludes all of it.

The ledger says why: "the proved arms are not yet joined into
`FloatArms`/`armTable`". Joining them also changes `FloatArms`'s statement:
every proved field takes `(hsf : SoftFloatSpec)`, so the structure (or its
consumer) must take that premise too. The cut deletes nothing, because these
theorems are the cluster's members. It records that the cluster's cost so
far buys no headline progress until that join.

**Correction to the brief.** `FloatArms` has **39** fields, not 36
(`Fold.lean:350–429`). Six are proved, so 33 remain.

### 1.1 The float-arm cluster, by conclusion predicate

The gate selects by name stem (`AtFlt[A-Z]*.lean`, `*_flt_{take,skip}`,
`sim_*_flt`). By conclusion predicate the same 12 theorems split into four
families. A fifth family is the per-shape hand-offs, which the gate does not
count.

| conclusion predicate | members | hand lines (ledger) | file CPU (user, s) | heartbeats (k) | first commit |
|---|---|---|---|---|---|
| `SimArm .LOADF` | `sim_LOADF_flt` | 8 | 1.8 | 4.0 | `29af681` 10-06 21:51 |
| `ArmBody o (FltTest t b)` | `{lti,eqi,gei}_flt_{take,skip}` (6) | 1–2 each | (in arm files) | 6.1–12.9 each | `29af681` |
| `SimArmOn o FltA` (via `sim_fcond`) | `sim_{LTI,EQI,GEI}_flt` | 1 each | LTI 2.8, EQI 3.4, GEI 2.9 | 0.03 | `29af681` |
| `SimArmOn .ADDI FltB` | `sim_ADDI_flt` | 3 | 2.6 | 10.3 | `221033d` 22:05 |
| `SimArmOn .FORLOOP FltStep` | `sim_FORLOOP_flt` | 29 | 7.0 | 56.7–59.1 | `ebbe30a` 22:05 |
| per-shape hand-off (macro, setup) | `at_fcond` (17), `at_farith` (20) | 37 | `AtFlt.lean` 2.4 | — | `29af681`, `221033d` |
| float-value bridge lemmas (setup) | `FltVal.lean`: 5 comparison idioms, immediates, `model_add_comm`, … | 126 | 2.2 | — | `29af681` |

Notes:
- CPU is per single-file compile with the imports prebuilt
  (`cpu_census.out`). Loading the imports alone costs about 1.5 s.
- All the proofs date from one lane, a 46-minute window on 10-06. "First
  quarter → last quarter" is therefore training (LOADF, LTI, EQI) against
  held-out cases (GEI, ADDI, FORLOOP) in proof order, not a drift over time.

**The second axis, CPU.** The generated at-lemma modules cost far more CPU
than the hand files:

| module | lemmas | CPU (s) |
|---|---|---|
| `At/Loadf` | 4 | 12.1 |
| `At/Lti` | 14 | 20.1 |
| `At/Gei` | 14 | 19.8 |
| `At/Addi` | 11 | 23.7 |
| `At/Forloop` | 26 | **55.7** |

- `At/Forloop` is 8× its hand file (7.0 s).
- The summaries: `Fn/Floatsidf` 9.5 s, `Fixdfdi` 13.4 s, `Eqdf2` 17.7 s,
  `Ledf2` 34.8 s, `Floatdidf` 30.7 s; `Adddf3` about 250 s and `Subdf3` about
  180 s (ledger).
- All of this is generated, so it costs build time, not agent effort. The
  gate's target is hand lines.

### 1.2 FORLOOP's proof, by line and by tactic

`ProfForloop.lean` is `sim_FORLOOP_flt` with `at_go` expanded. It adds a
heartbeat log between steps, and `at_run_log`, a copy of `at_run` that logs
every at-lemma it takes and the heartbeats spent on candidates it rejected
before that one. Options: `Elab.async false`, `profiler true`. Totals:
59.1k heartbeats, 7.9 s user CPU, 2.2 GB peak.
By the profiler's categories (cumulative, nested), `simp` dominates: 11.4 s
`simp`, 10.7 s tactic execution, 0.8 s typeclass inference, 0.6 s type
checking. The `simp` time is the closers (`at_hyp`'s `simp … at_fspec …`) and
the kernel unfolding.

**The 29 lines, by role:**

| role | lines | share | shared with the GEI/ADDI hand-offs? |
|---|---|---|---|
| reading R[A], R[A+1], R[A+2]: `kit_bound`, `kit_reg` ×3, `hT` against `hr2`, the non-float cases refuted by `cases v0 <;> cases v1` | 8 | 28% | `at_fcond` and `at_farith` do this for **one** register, inside the macro |
| payload models and tags bundled for the closers (`flt_parts` ×3, `hta`, `hxm`, `hnj`) | 6 | 21% | inside the macros, one register |
| jump target (`jumpTo` split, `hbx`, `ht`, `subst`) | 4 | 14% | no (`docondjump` has `kit_nj`) |
| kernel outcomes: step sign × bound (`rcases … <;> split <;> rename_i`, `e`) | 4 | 14% | one `Bool` in `FltTest` |
| `luai_numadd` operand order (`model_add_comm`) | 1 | 3% | no |
| arm boilerplate (`sim_arm_on`, `kit_setup`, `simp forloopK`, successor `simp`, `subst`, `at_go`) | 6 | 21% | the int arms' 2–3 lines |

**The 59.1k heartbeats, by step** (thousands; `ProfForloop.out`):

| step | k | share |
|---|---|---|
| setup before the split: `kit_setup` 1.0, `jumpTo` 0.3, `simp forloopK` 2.1, `kit_reg` ×3 3.7, **refute non-float** 2.9, jump target 1.1, bundle 0.1 | 11.2 | 19% |
| per outcome: the kernel split, successor `simp` and `at_go` prelude (≈1.0 × 4) | 4.1 | 7% |
| `at_run`, 4 outcomes: 9.8 + 10.4 + 7.4 + 6.4 | 34.0 | 57% |
| `at_close`: 4.3 (jump back) + 1.2 (exit) + 4.2 + 1.2 | 10.8 | 18% |

Where `at_run`'s 34.0k goes (per-lemma log):

| item | k | share |
|---|---|---|
| **candidates rejected before the right polarity**: 1.9; 1.9 + 4.2; 0; 2.2 | **10.3** | 17% of the proof |
| **the shared prefix replayed per outcome**: tag test `c1ec` 0.7–0.8, three payload loads `e158` 1.9–2.3, the two calls and the short segments 0.1; 2.7–3.1 per run, run 4× where 1× suffices | **8.3 redundant** | 14% |
| stores `e1a0` and the tail `c240` on the two jump-back outcomes | 6.3 | |
| guard segments taken | 0.2–0.3 each | |

- **Lines.** The dominant cost is the arm reading **three** float registers
  when its operand predicate (`FltStep`) names one. The other two are
  refuted from the kernel by hand, and each register's tag and model are
  bundled by hand (14 of 29 lines, 48%).
- **Heartbeats.** The dominant costs are the proof splitting into the four
  kernel outcomes *before* the run, and `at_run` choosing a branch polarity
  by trial. Splitting first replays the machine prefix the outcomes share
  4×. Trying the closers is round 4's residue ("pick the polarity by
  evaluating the guard"), still 17% here. Neither is near the 200k budget
  for FORLOOP. §1.3 shows that 16 of the remaining fields have more outcomes.

**The ELF explains the extra registers.** `floatforloop` tests only R[A+2]'s
tag (`lbu a5,40(s5)` at `0x8001c1fc`, one tag load on the float path;
`float_paths.out`). It loads the index, the limit and the step payloads
untested (`0x8001e158–60`).

- The kernel's float clause `[.flt i _, .flt l _, .flt st _]` makes the two
  untested registers' types a *kernel* fact: `none` otherwise.
- So the refutation is a kernel inversion, not a machine read.

The ELF also computes `__adddf3(step, idx)` and `__gedf2(limit, idx) ≥ 0`.
`lvm.c` writes `idx + step` and `idx <= limit`.

### 1.3 The 33 remaining `FloatArms` fields, by shape

`float_paths.py` enumerates the acyclic paths of `luaV_execute` from each
arm's jump-table target. A path is a **float path** if it calls a soft-float
or libm routine. The columns are:
- `fp`: the float paths;
- `vforks`: branches after the first soft-float call;
- `tags`: tag loads on float paths;
- `shared`: the share of float-path instructions that a non-float path also
  executes.

The full table is `float_paths.out`. Grouped by shape:

| shape (nearest pilot) | fields | `fp` | `vforks` | `shared` | tier |
|---|---|---|---|---|---|
| **GEI-like**: R[A] fixed by `Q`, an immediate, one conversion + one compare, `docondjump`; or inline (UNM) | LEI, GTI, UNM | 2 (UNM 0) | 1 | 0.72–0.84 | T1, T0 |
| **ADDI-like with a register or K partner**: the partner is a float, an int (`__floatdidf`) or a non-number (the MMBIN edge); one arithmetic call (IDIV/IDIVK add `floor`) | ADD, SUB, MUL, ADDK, SUBK, MULK, IDIV, IDIVK | 3 | 0 | 0.61–0.63 | T2–T4 |
| **all-float kernels**: every number path is float (both ints converted); POW has `pow`'s `b == 2` fast path | DIV, DIVK, POW, POWK | 5–9 | 2–3 | 0.35–0.43 | T3–T4 |
| **FORLOOP-like or worse**: forks on soft-float answers, chained calls | MOD, MODK (15); BAND, BOR, BXOR (13); SHL, SHR (22); BANDK, BORK, BXORK, BNOT (4); SHRI, SHLI (7); LT, LE (24); FORPREP (10, plus `luaV_tonumber_` → `strtod`) | 4–24 | 3–11 | 0.27–0.55 | T3–T4 |
| **float semantics inside a callee** (`luaV_equalobj`) | EQ, EQK | (in callee) | — | — | T3 |

Sizes: GEI-like 3, ADDI-like 8, all-float 4, **FORLOOP-like or worse 16**,
callee 2; 33 in total. For comparison, FORLOOP has `fp` 4, `vforks` 2,
`tags` 1 and `shared` 0.22.

**Sample** of 10 of the 33 (`random.seed(5)`): ADDK, BNOT, BORK, DIV, EQ,
FORPREP, GTI, MULK, SHLI, SHRI. Each member's obligation shapes come from its
paths' call sequences (ELF) and its kernel classes (`LawChecks.out`):

| obligation | in the sample | FORLOOP |
|---|---|---|
| payload model and tag per float register (O-pay) | 9/10 (not EQ) | ×3 |
| partner or extra register types beyond `Q`, by kernel inversion (O-inv) | 4/10 (ADDK, DIV, MULK, FORPREP) | yes |
| int → float conversion call (O-conv) | 5/10 | — |
| machine fork on a soft-float answer (O-vfork) | 5/10 (BNOT, BORK, SHLI, SHRI, FORPREP) | 2 forks |
| the inlined `luaV_flttointeger` chain `floor > __eqdf2 > __gedf2 > __ledf2 > __fixdfdi` (O-f2i) | 4/10 (BNOT, BORK, SHLI, SHRI) | — |
| comparison-answer idiom (O-idiom) | 5/10 | 3 idioms |
| operand order or relation swap, lvm.c against ELF (O-ord) | 2/10 (GTI: `__gedf2(x, imm) > 0` for `imm < x`; FORPREP) | 2 |
| MMBIN or metamethod edge on a float path (O-mm) | 8/10 | — |
| jump target (O-jump) | 1/10 (FORPREP) | yes |
| float semantics in a callee summary (O-callee) | 2/10 (EQ; FORPREP's `luaV_tonumber_`) | — |

**Sizing by shape, not by name.**
- FORLOOP's dominant line costs (O-inv, O-pay on several registers) appear
  in every member with a register or K partner: 12 of the 33 (ADD-like 8,
  DIV/DIVK, LT/LE).
- Its dominant heartbeat cost (replaying the prefix per outcome, polarity by
  trial) grows with `fp`: 13 of the 33 have `fp` ≥ 7.
- Linear extrapolation is a forecast only, not a measurement: about 15k
  heartbeats per outcome (FORLOOP: 59k over 4). That puts SHL/SHR (22) and
  LT/LE (24) over the 200k budget, so round 4's C-budget returns for them.

**A new recurring chain.** `idioms.out` finds 22 `jal floor` sites in
`luaV_execute`, 20 of them the inlined `luaV_flttointeger` chain. They
come in 6 layout variants of the same C, differing in branch polarity
(`beqz`/`bnez`, `bgez`/`bltz`) and in `j` placement. That is 13 of the 33
fields (the bitwise family 11, LT/LE).

### 1.4 The hand-offs and bridges that accumulate

- **Per (kernel shape × operand predicate) hand-offs.**
  - So far: `at_fcond` (`docondjump`, FltA + immediate) and `at_farith`
    (`opArith`, FltB + immediate).
  - Still needed by §1.3:
    - `opArith` with FltBC (3 value combinations + MMBIN);
    - `opArith` with FltBK;
    - all-float `/` and `^`;
    - `docondjump` with FltAB (LT/LE: `LTnum`'s mixed int/float, with the
      f2i chain);
    - `docondjump` with FltAKb;
    - bitwise over the f2i chain, binary and K forms;
    - unary over f2i (BNOT);
    - UNM inline;
    - FORPREP;
    - MOD's `fmod` sign fix.
  - That is about 10 more, about 20 lines each. The pilot's "no new per-arm
    lemma kind" criterion was broken once (by `at_farith`), and the shapes
    predict about 10 more breaks.
- **Comparison idiom bridges** (`FltVal.lean`: `slt_ledf2`, `slt1_ledf2`,
  `seqz_eqdf2`, `ge_gedf2`, `blez_gedf2`, 4–5 lines each).
  - `luaV_execute` makes 93 calls to `__{le,ge,eq}df2` and uses their
    answers through 17 instruction idioms (`idioms.out`).
  - 69 of the calls feed a branch directly
    (`beqz`/`bnez`/`bgez`/`bltz`/`blez`); 7 feed `slti`; 4 feed `sgtz`; 3 feed
    `not; srli 63`; 2 feed `srli 63`; 1 feeds `seqz`; 7 are spilled or moved.
  - Each new idiom costs a hand lemma, proved the same way (`rcases` on the
    4-valued `compare`, then `decide`).

### 1.5 Level (b): what one routine-equals-spec proof contains

`lifted_dag.py` reads the generated lifted functions and `stage_sites.py`
reads the ELF:

| routine | ELF insns | `N_` nodes | `if`s | **paths** | variable shifts | frame reloads (`bytesT8 m`) | `clz64` | inlined round / sticky / pack sites |
|---|---|---|---|---|---|---|---|---|
| `__floatsidf` | 36 | 3 | 1 | 2 | 16 | 2 | 2 | 0 / 0 / 2 |
| `__floatdidf` | 86 | 14 | 7 | 11 | 7 | 8 | 2 | 1 / 1 / 4 |
| `__fixdfdi` | 30 | 9 | 4 | 6 | 2 | 0 | 0 | 0 / 0 / 0 |
| `__eqdf2` | 28 | 9 | 7 | 19 | 0 | 0 | 0 | — |
| `__ledf2`, `__gedf2` | 41, 40 | 18 | 15 | 67 | 0 | 0 | 0 | — |
| **`__adddf3`** | 418 | 133 | 76 | **497** | 42 | 14 | 2 | **6 / 5 / 4** |
| `__subdf3` | 440 | 142 | 83 | 509 | 34 | 14 | 2 | 5 / 5 / 4 |
| `__muldf3`, `__divdf3` (no level (a) yet) | 307, 328 | — | — | — | — | — | — | 3 / 1 / 3, 2 / 1 / 3 |

**One equation `Adddf3.F m s r a b = F64.add a b` contains:**

1. **Frame forwarding.**
   - `F` reloads 14 of its own stack spills (around the `__clzdi2` call)
     through the `writeMap8` chain of its frame stores.
   - Each is a read-over-write fact before any arithmetic.
   - `SpecTest` runs on the empty memory, so it never exercises these
     reads, but the proof must.
2. **Unpack.** The machine's fields (`(x >> 52) & 0x7ff`, `(x << 12) >> 12`,
   `x >> 63`) against `F64.cls`'s Nat `div`/`mod`, once per operand.
3. **497 paths of guards**, each a `BitVec` comparison to be turned into a
   Nat fact by `toNat` and `omega`. `bv_decide` is not allowed (law 2).
4. **Align with sticky.**
   - 5 inlined `_FP_FRAC_SRS` sites, shifts by the exponent difference.
   - These are among the 42 variable-amount shifts, which are nonlinear for
     `omega`: `x >>> k` is `x / 2^k` with a symbolic `k`.
5. **Add or subtract** with carry or borrow, then **normalise** by `clz64` /
   `__clzdi2` (the relation to `Nat.log2`).
6. **Round** (`rne` with 3 work bits; 6 inlined sites), the carry out of
   bit 56, the overflow to ∞.
7. **Pack** (4 sites).

On the spec side, `F64.add` is a 9-clause match on `cls`. Its finite case
goes through `normalize` → `roundExact` → `round` (`target` via `Nat.log2`,
`shr`, `rne`, `finish`, `packFin`).

**Why none closed.** None was attempted:
- the lane stopped at the M1 gate failure (rule 1);
- the level-2 pilot FLOAT-DESIGN §4 planned (a stage library on
  `__floatdidf` + `__ledf2`, `__fixdfdi` + `__gedf2` held out) was never
  started.

What blocks an attempt is visible in the artefact:
- **(i) no stage vocabulary.** `F` is a DAG of raw node functions over
  `BitVec 64`. Nothing names the `(sign, exp, frac)` triple the stages pass
  along. Any proof re-derives soft-fp's invariants node by node, and the
  generator's node boundaries do not line up with the stages: rounding is
  tail-duplicated into 6 sites that jump to one pack join.
- **(ii) frame reloads.** They put `m` into `F`.
- **(iii) variable shifts.** They are outside `omega`.
- **(iv) 497 paths**, if the proof follows the code's branches.

FLOAT-DESIGN estimates 2–4 weeks for the add/sub pair.

### 1.6 Target clusters

| # | cluster | members (done / left) | per-case trend | what it costs |
|---|---|---|---|---|
| C5-arm | float-arm paths (`SimArmOn o Q` / `ArmBody o (FltTest …)`) | 6 / 33 | 2.7 → 13.3 lines (gate FAIL) | register inversion + payload bundle (48% of FORLOOP's lines); prefix replay + polarity trial (31% of its heartbeats) |
| C5-handoff | per-shape hand-offs (`at_fcond`, `at_farith`, …) | 2 / ≈10 | 17–20 lines each, flat | one macro per (kernel shape × operand predicate) |
| C5-idiom | comparison-answer bridges (`FltVal`) | 5 / ≈12 more idioms (17 in the ELF) | 4–5 lines each, flat | one hand lemma per idiom |
| C5-f2i | inlined `luaV_flttointeger` chains | 0 / 20 sites in 13 fields | (forecast) | 5 calls, 3–4 forks per site, 6 layouts |
| C5-spec | level (b) `F = S` per routine | 0 / 8 (+ `__muldf3`, `__divdf3`, `floor`, `fmod`, `pow`) | none closed | 497 paths, 14 reloads, 42 variable shifts for `__adddf3` alone |

## 2. Laws

The scripts and their outputs are in `abstractions/checks/round5/`. Every
check runs the **generated lifted functions** (equal to the machine by the
level-(a) theorems), the ELF, or the bytecode kernels. None runs a model
that restates the law.

### L5-read: a float register read refutes the non-float cases generically (C5-arm)

**Statement (as given).** For each float-arm kernel `κ` and operand
predicate `Q`: if `κ.body (reads ↦ regs) = some o` and `Q` holds, then every
register that `κ`'s float clause reads holds a float. The non-float cases
are refuted by one generic inversion, not by `cases` per arm.

**Check** (`LawChecks.lean`, the `classes` section). Every operand tuple
over 10 skeleton values (nil, bool, two ints, 1.5, 0.0, NaN, two strings, a
builtin) that satisfies `Q` is classed by the kernel's answer:

| kernel, `Q` | classes |
|---|---|
| `forloopK`, R[A+2] float | `none` 273; exit (`e0`) 23 and back-jump (`e2:[flt, flt]`) 4, **both only with all three floats** |
| `opArith .add/.div/.mod`, FltBC | `e1` (MMBIN) 30 with a non-number partner; `e0:[flt]` 21 with partners {flt, int} |
| `opArith .band`, FltBC | `e1` 46 (a non-integral float also falls to MMBIN); `e0:[int]` 5 |
| `δ .lt`, FltAB | `none` 30 with a non-number partner (the order error); `e0:[bool]` 21 |
| `δ .le` with an int immediate (GEI); `δ .unm` | one class |

**Verdict: holds for FORLOOP, false as stated for the arithmetic and order
arms.**
- In those arms a non-number partner is a **path**, not a refutation: the
  MMBIN edge for arithmetic, the error exit for order. An int partner is a
  third value case through `__floatdidf`.

**L5-read′.** Under `Q`, a kernel's answers fall into a fixed, small set of
classes, and the read registers' constructors determine the class.

| kernel | classes |
|---|---|
| `forloopK` | refuted (`none`), exit, back-jump |
| `opArith` | value with partner ∈ {flt, int}, MMBIN |
| `δ` order | bool with partner ∈ {flt, int}, error |
| `docondjump` / unary with an immediate | one class |

The classes, and each class's register constructors, are a function of the
kernel's clause list (the table above is computed from it). They can be
emitted per kernel combinator, not written per arm.
- What a member then supplies is one line per class: the class and its
  at-lemma run.
- The per-register payload model and tag (FORLOOP's 6 bundling lines) belong
  to the same law. For each register a class names as a float,
  `ValRepr.flt_parts` gives the tag and model as one named fact.
- The machine side agrees: `floatforloop` tests one tag (`tags` = 1). The
  other two registers' types come from the kernel class, never from a
  machine read.

### L5-comm: operand order of commutative soft-float calls is irrelevant (C5-arm, O-ord)

**Check** (`LawChecks.out`, on the 2,900 `SpecTest` pairs: 30×30 edges with
NaN payloads, plus 2,000 random):

| law on the lifted functions | holds |
|---|---|
| `Adddf3.F a b = Adddf3.F b a` | 2,900 / 2,900 |
| `Eqdf2.F a b = Eqdf2.F b a` | 2,900 / 2,900 |
| `Ledf2.F a b = −Gedf2.F b a` (unordered: 2 against −2) | 2,900 / 2,900 |
| `Subdf3.F a b = Adddf3.F a (b ^ 2^63)` | 2,900 / 2,900, NaNs included |
| `F64.sub a b = F64.add a (b ^ 2^63)` (spec) | 2,900 / 2,900 |

The spec side is already proved: `F64.add_comm`, `F64.mul_comm`,
`F64.compare_swap`, `model_add_comm`.

**Verdict: holds, bit for bit, on the artefact.** But the census prices it
at 1 of FORLOOP's 29 lines, and 2 of the 10 sampled members have a swap.
- **It is not a cost driver for C5-arm.** Fold it into the call-node
  specification as a normal form: each `f<k>_eq` states its answer in lvm.c's
  operand order and relation, by `add_comm` and `compare_swap`.
- **Its real value is level (b).** `sub = add ∘ (flip the sign bit)` holds on
  the machine. So `SoftFloatSpec.subdf3` follows from `.adddf3`, provided
  the sign-flip identity is proved once on `F64`, and `__subdf3`'s level
  (b) costs nothing. `__ltdf2 = __ledf2` and `__gtdf2 = __gedf2` are already
  single entries.

### L5-share: a kernel's float path and its int path share all but the value leaf (C5-arm, C5-handoff)

**Check.**

On the kernel:
- `opArith` and `docondjump` have the same `reads`, `edges` and defs for
  every value type. Only the leaf (`fastArith`, or `δ`'s numeric case)
  differs.
- `forloopK` does not. Its int clause is count-based, writes
  `[A+1, A, A+3]` on edge 1 and has no compare. Its float clause compares
  and writes `[A, A+3]` on edge 2. `forprepK` is the same.

On the machine (`float_paths.out`, `shared`), the share of float-path
instructions that some non-float path also executes:

| arms | `shared` |
|---|---|
| EQI, LEI, GEI | 0.82–0.85 |
| LTI, GTI | 0.72 |
| ADD-like | 0.61–0.63 |
| bitwise | 0.38–0.55 |
| MOD | 0.39 |
| LT/LE | 0.27–0.28 |
| **FORLOOP** | **0.22** |

FORLOOP's float loop is separate code (`0x8001e158–e1bc`, `0x8001edf0`). It
rejoins only at the dispatch tail `0x8001c240`.

**Verdict: false for FORLOOP and FORPREP; holds for `opArith`/`docondjump`,
refined.**

**L5-share′.** For kernels built by `opArith` and `docondjump`, the float
path's proof is the int path's proof with:
- the value leaf replaced: `fastArith`/`δ` on `Float.Model` instead of
  `BitVec`;
- the stored tag replaced: 19 instead of 3;
- an arithmetic call node in place of the inline ALU op, plus the conversion
  call per int partner (L5-read′'s classes).

The machine shares the dispatch prefix and the store/jump tail (61–85% of
the instructions for the docondjump and ADD-like arms). So the hand-off
should be **one per kernel combinator, parametric in the number domain**,
not one per (shape × operand predicate). That replaces C5-handoff's ≈10
macros by the combinators in `opKernel`: `opArith`, `docondjump`, `setR`
unary, `bitwiseRK`, plus FORLOOP and FORPREP alone.

### L5-fork: the case split follows the machine's fork tree (C5-arm, heartbeats)

From the profile, not in the brief. FORLOOP splits on the kernel's four
outcomes, then runs the machine four times.
- It replays the prefix those outcomes share (8.3k redundant).
- At each fork, it tries closers of the wrong polarity before the right one
  (10.3k).

**Statement.** For a float path, run the shared machine prefix once. Split
only where the machine forks. Pick each fork's side by evaluating its guard
against the kernel class fact (L5-read′) with one `decide`, never by trying
closers.

**Check** (from the per-lemma log):
- The four runs' common prefix (`c1ec` → `call_8001e17c`) is identical in all
  four logs: same lemmas, 2.7–3.1k each.
- The two fork points are `e17c` (`blez` on `__gedf2(step, 0)`) and `e194`
  (`bnez` on the bound idiom). Each splits the four kernel outcomes into
  matching halves.
- So the machine tree and the kernel's outcome tree have the same shape (2×2)
  for FORLOOP, and the saving is bounded by the measured 18.6k (31%).
- For the 16 FORLOOP-like fields, with `fp` 4–24, the replay saving grows
  with `fp`. This is the budget forecast of §1.3.

**Refinement.** The machine's fork order and the kernel's need not agree.
FORLOOP's kernel tests the sign, then the bound; the ELF does the same. For
the f2i chain, the machine forks 3–4 times (`eqdf2`, `gedf2`, `ledf2`)
where `δ`'s `tointegerns` has one `Option`. There, several machine leaves map
to one kernel class, and the split must follow the machine. This is
untested: no f2i arm exists yet.

### L5-idiom: every comparison idiom is a function of the 4-valued compare (C5-idiom)

**Statement.** For each routine `R ∈ {__ledf2, __gedf2, __eqdf2}` and each
idiom `ι`, a predicate or 0/1 value on `a0` such as `slti 1`, `sgtz`,
`not; srli 63` or a branch, `ι (R.S a b) = g_ι (F64.compare a b)`. This
holds for an explicit `g_ι : Option Ordering → Bool`. The proof is the same
4-case `decide` for every `ι`, because `R.S` ranges over at most four values.

**Check.** `FltVal.lean` proves 5 idioms exactly this way (`rcases o <;>
decide`). `idioms.out` lists the 17 idioms at 93 sites, all of this form.
- 69 sites are a branch on the sign of `a0`, and 17 more compute a 0/1 value
  from it (`slti`, `sgtz`, `seqz`, `srli 63`, `not; srli 63`).
- The remaining 7 spill or move `a0`. They need the `Loc.fn` value carried,
  not an idiom.

**Verdict: holds.** The law is a generator rule: emit the idiom lemma per
(routine, idiom) from the ELF, as `gen_lua_at.py` emits `f<k>_eq`. That
removes C5-idiom.

### L5-chain: the inlined `luaV_flttointeger` is one summary at every site (C5-f2i, forecast)

**Statement.** At each of its inlined sites, the chain `floor → __eqdf2 →
(range: __gedf2, __ledf2) → __fixdfdi` computes `tointegerns` with mode
`F2Ieq`, i.e. `some n` iff the float is integral and in range. It is stated
once over the chain's call-node results, whatever its layout.

**Check** (`idioms.out`). 20 of the 22 `floor` sites carry the chain, in 6
layouts: `beqz`/`bnez`, `bgez`/`bltz`, `j` placement, one with `__adddf3`
(`F2Iceil`) and one without `__eqdf2` (`F2Ifloor`). The other 2 are
`luai_numidiv`'s and `luai_nummod`'s `floor` next to `__divdf3`/`__muldf3`.
- The layouts differ only in branch polarity and in which side falls
  through. The polarity is exactly what L5-idiom normalises.
- **Refinement.** The law must quantify over the mode (`F2Ieq`, `F2Ifloor`,
  `F2Iceil`) and over the polarity of each idiom. It needs `floor`'s level
  (b) (libm `s_floor.c`, bit masks) as a named premise beside
  `SoftFloatSpec`.

### L5-stage: one normalise-round-pack stage algebra across the soft-float routines (C5-spec)

**Statement.** Each soft-float routine's lifted `F` factors through a fixed
vocabulary of stage functions, the libgcc soft-fp macros:
- unpack;
- `_FP_FRAC_SRS` (shift right with sticky) by `1 ≤ k ≤ 63`;
- `__FP_CLZ`;
- `_FP_ROUND_NEAREST` with 3 work bits (`rne3`), with the carry out of bit
  56;
- `_FP_PACK_SEMIRAW`.

Each stage has one closed-form Nat semantics. Their composition
`roundPack (s, E, f)` **is** `F64.round` on the same value.
- `F = S` then reduces to stage lemmas proved once over `BitVec ↔ Nat`,
  plus a per-routine *core* equation in exact Nat arithmetic: the aligned
  sum with sticky, which is round-invariant.
- The core uses no variable `BitVec` shifts, because the SRS stage absorbs
  them.

**Checks**, by evaluation (`LawChecks.out`) and on the ELF
(`stage_sites.out`):

| claim | instances | holds |
|---|---|---|
| one `packSemiraw s e f` (`f >> 3`; all-ones exponent with a nonzero fraction → `0x7ff8…`; pack) = `__adddf3`'s join node `N_8002d92c` | 7,326 (`e` ∈ {0, 1, 2, 1022–1024, 2045–2047}, `f` < 2^56 random + edges, both signs) | 7,326 |
| the same function = `__subdf3`'s join node `N_8002ea50` (different code, parameters permuted) | 7,326 | 7,326 |
| the machine's SRS idiom (`srl`, `sll` by `64 − k`, `snez`, `or`; copied from `N_8002dcd0`) = `x / 2^k ||| [x mod 2^k ≠ 0]`, `1 ≤ k ≤ 63` | 18,900 | 18,900 |
| the same idiom at `k = 0` | 300 | **141**: counterexample |
| `roundPack s E f` (machine `rne3`, carry, overflow → ∞, `packSemiraw`) = `F64.round s (f/8) (E − 1075) rb st`, normal | 6,070 | 6,070 |
| the same, subnormal `E = 0` (a carry into bit 55 gives the smallest normal) | 1,210 | 1,210 |
| inlined stage sites on the ELF: round / sticky / clz / pack | `__adddf3` 6/5/1/4, `__subdf3` 5/5/1/4, `__muldf3` 3/1/2/3, `__divdf3` 2/1/2/3, `__floatdidf` 1/1/1/4, `__floatsidf` 0/0/1/2 | 58 sites, 4 stage lemmas |

**Verdict: holds where checked, refined.**

- **SRS needs `1 ≤ k ≤ 63`.** At `k = 0`, `sll` by 64 is a shift by 0, so
  the sticky bit becomes `x ≠ 0`. soft-fp's C has `x << 64` undefined there,
  and the code branches around it. The precondition is a named part of the
  stage lemma, discharged at each site by the guard that branched there.
  Counts `≥ 64` take another branch (`f ≠ 0` as pure sticky), a separate
  stage case.
- **Syntactic sharing is weak.** Only 21 of 281 alpha-normalised node
  bodies recur across routines, all trivial (`lifted_dag.out`). The add and
  sub join nodes are different terms with permuted parameters that compute
  the same function.
  - So the law is **semantic**: a stage lemma is stated over the stage
    function and *matched* to each routine's node by an equation proved per
    site (a `decide`-free `BitVec` identity, like `srsMachine`).
  - It is not a shared definition the generator can point to.
- **The node boundaries are the compiler's, not the stages'.** Rounding is
  inlined at 6 sites that jump to one join. For the stage lemmas to apply by
  rewriting, the generator would have to cut `F` at stage boundaries (or
  name the `(s, e, f)` triple at the join), so that each path is
  `packSemiraw ∘ rne3 ∘ core`.
- **Not checked: the core.** The per-routine core is the exact aligned sum
  with sticky, and the classic lemma "rounding after a sticky collapse
  equals rounding the exact value" (`F64.shr`'s design). It is the one
  per-routine proof left, and the place 497 paths must collapse into
  `F64.add`'s 9 clauses. The ontologists should get it as the open part.
- **`__subdf3` is free** given `__adddf3` (L5-comm's sign-flip law).
- **The frame reloads** (14 per add/sub, 8 in `__floatdidf`) are outside the
  stage law. They are read-over-write facts on `F`'s own `writeMap8` frame,
  which the generator could forward when it emits `F`. Then `F` would no
  longer depend on `m`.

### Verdicts

| law | target | verdict |
|---|---|---|
| L5-read | register reads refute non-float cases | **refined** (false as stated for arith/order arms): L5-read′, kernel answer classes under `Q` emitted per combinator, with per-class register constructors and payload facts |
| L5-comm | commutative operand order irrelevant | **holds** bit for bit (add, eq, le/ge swap; sub = add ∘ sign flip, NaNs included); a 1-line cost for arms; its value is level (b) (`__subdf3` free) |
| L5-share | float and int paths share all but the leaf | **false** for FORLOOP and FORPREP (separate kernel clauses, 22% shared code); **refined** L5-share′ for `opArith`/`docondjump`: one hand-off per combinator, parametric in the number domain |
| L5-fork | split at the machine's forks, polarity by evaluation | **holds** for FORLOOP (2×2 tree, matching); bounded saving 18.6k of 59.1k; f2i arms' many-to-one leaves untested |
| L5-idiom | comparison idioms by one 4-case schema | **holds** (17 idioms, 93 sites); a generator rule |
| L5-chain | inlined `flttointeger` is one summary | **forecast**: 20 sites, 6 layouts, mode and polarity quantified, `floor` a new named premise |
| L5-stage | normalise-round-pack algebra shared across routines | **holds where checked** (pack join ×2 routines, SRS for `1 ≤ k ≤ 63`, `roundPack = F64.round`, 58 ELF sites); semantic, not syntactic; core round-invariance unchecked; generator must cut at stage boundaries |

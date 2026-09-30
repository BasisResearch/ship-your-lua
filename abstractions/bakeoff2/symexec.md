# A1 bake-off, round 2: contender `symexec`

ship-your-interpreter's symbolic executor (`exponentiate` at `118e5f3c`), run
on the Lua ELF's `luaV_execute` arms. Measurement only: syi was read from a
scratch clone and never modified.

## Summary

| setup (hand) | per-arm hand lines ADD / EQI / FORLOOP | generated lines | build CPU (s), per arm ADD / EQI / FORLOOP | peak mem | refactor `sim_MOVE` | failed builds | wall |
|---|---|---|---|---|---|---|---|
| 641 (+52 verbatim excerpt; +2,442 copied verbatim) | 113 / 210 / 210 (theorem + its combinator inversion + its field lemmas); theorems alone 77 / 115 / 145 | 0 | 5.8 / 4.7 / 7.0 (wall 5.3 / 4.7 / 6.0); setup 24 s CPU once | 2.96 GB | 59 lines, 3.0 s CPU (incumbent: 78 generated + ~30 template lines, 3.0 s CPU plus its 2 generated segments) | ~52 | ~70 min |

**The held-out theorems prove a weaker conclusion than the incumbent's.**
The executor's soundness is stated on a machine model that tracks byte values,
not byte presence. So the arms end in `VmRelZ` (`VmRel` of a configuration
with the same registers and total reads), and they need the named premise
`SymOk` (every GPR present, HTIF mailbox idle), which `VmRel` does not carry.
Both gaps are explained below, with the evidence.

## What was built

| piece | file | kind | code lines |
|---|---|---|---|
| executor: `symRun`, `symRun_swp`, `symRun_auto`, `obCheck`, `Geom`, `sym_eval`, `sym_dec`, `geom_auto` | `VsaIris/Vsa/SymExec.lean` | copied verbatim | 2,236 |
| `sltu`/`sltiu` steps | `VsaIris/Vsa/SymObsStep.lean` | copied verbatim | 98 |
| `TextPiece`, `rangeText`, `piecesText` | `Vsa/Sim/TextImage.lean` | copied verbatim | 108 |
| the Lua ELF's configuration (syi's `cfgI`/`Tbl` counterpart): image `img`, code range `rT`, tracked registers, known head constants, `hasB`; `codeAt`; `SymOk`; `swp_run`, the `SWP` to `StepsN` adequacy | `Lua/Vm/Sim/Sym/Run.lean` | hand | 163 |
| `geomOf` (the `Geom` of a run, read off its obligations) | `Lua/Vm/Sim/Sym/Run.lean` | verbatim excerpt of syi's `SymInterp.lean` | 52 |
| `geom%` (evaluates `Γ` at elaboration time), `sym_split` (splits a literal tree's WP) | `Lua/Vm/Sim/Sym/Run.lean` | hand (tactics) | included above |
| `dispatchS`: the fetch head, through the executor, for every opcode | `Lua/Vm/Sim/Sym/Head.lean` | hand | 123 |
| `VmRelZ`, `simZ` (composition), `HeadImg`/`ArmQ`, `arm_close`, `ArmEnv`, `arm_swp`, slot-store and tag lemmas, `arm_den`/`arm_guards`/`head_reg`/`slot_peel` | `Lua/Vm/Sim/Sym/Close.lean` | hand | 351 |
| kernel inversions `step_arith`, `step_condjump`, `step_forloop` | `Lua/Vm/Sim/Sym/Step.lean` | hand, one per combinator | 116 |
| field lemmas: `kbit_eq`, `sB_eq`, `ltu_one_eq`, `nextjump_eq`, `bx4_eq` | `Lua/Vm/Sim/Sym/Fields.lean` | hand | 94 |
| `sim_MOVE`, `sim_ADD`, `sim_EQI`, `sim_FORLOOP` | `Lua/Vm/Sim/Sym/{Move,Add,Eqi,Forloop}.lean` | hand | 59 / 77 / 115 / 145 |

Line counts are non-blank and non-comment. They were counted per declaration
with the same stripping as `abstractions/census.py`.

`StepGen`/`driverLemma?` (syi's `Tbl`) was not needed. The executor has no
per-pc step lemmas. It proves each instruction through the generic
`swpx_line`/`swpx_br`/`swpx_j`/`swpx_jr` and `aluStep_sltu`/`sltiu`. The
per-ELF data are the `Cfg` fields above. `StepGen` imports syi's WHILE
interpreter (`IRun`, `EnvRun`, `NRun`), so it could not be copied WHILE-free.

The copied layer stays WHILE-free. `experiments/port/port_census.py --copyset`
reports: "modules here: 766; WHILE roots in their closure: none; imported but
absent: none". The three files were copied verbatim. They are listed in
`experiments/port/copied.txt` and `ATTRIBUTION.md`. Their imports already
resolve to this repository's copies, which are newer supersets of syi's at
`118e5f3c`.

## The theorems

For every arm `X` in {MOVE, ADD, EQI, FORLOOP} (`Lua/Vm/Sim/Sym/*.lean`):

```lean
theorem sim_X {p : Proto} (hS : Supported p) {c : Config} {s s' : State}
    (hR : VmRel p c s) (hok : SymOk c) {ins : Word} (hf : p.fetch s.pc = some ins)
    (hop : ins.op? = some .X) (hstep : Step binaryHost p s s') :
    ∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRelZ p c' s' ∧ SymOk c'
```

- `VmRelZ p c s := ∃ c₀, Vsa.Densify.CEqv c c₀ ∧ VmRel p c₀ s`.
- `simZ` lifts any such lemma to the hypothesis `VmRelZ`, through
  `Vsa.Densify.stepsN_sim` and `stepOnce_resp`. So the arms compose, and
  `Halts`/`Diverges` transfer through `CEqv`.

**Paths covered.** Every path the machine can take is covered. Kernel-excluded
paths are discharged, not assumed away:

- **ADD**: 7 leaves.
  - int + int: `R[A]`, then pc+2.
  - int + non-number: pc+1.
  - non-number: pc+1.
  - 4 float leaves, discharged by `ValRepr.not_float`: no F1 value has tag 19.
- **EQI**: 5 leaves.
  - non-int with `k`: pc+2.
  - non-int without `k`: the jump `pc+2+sJ`, with `trap` reloaded.
  - int, test = `k`: the jump.
  - int, test ≠ `k`: pc+2.
  - the float leaf: discharged.
- **FORLOOP**: 3 leaves and 4 store-forwarding obligations.
  - count 0: exit to pc+1.
  - count ≠ 0: `R[A+1]`, `R[A]`, `R[A+3]` written; jump to `pc+1−Bx`.
  - the float-step leaf (the call to `__adddf3`): discharged by
    `ValRepr.int_tag`.
- **MOVE**: 1 leaf, plus 1 forwarding obligation (the `lbu` of `R[B]` past
  the `sd` to `R[A]`).

All obligations are closed. `#print axioms` gives `[propext, Classical.choice,
Quot.sound]` for `symRun_auto`, `swp_run`, `dispatchS`, `arm_close`, `simZ`,
`sim_MOVE`, `sim_ADD`, `sim_EQI` and `sim_FORLOOP`. They are in `check.sh`
stage 6, and `scripts/check.sh` passes (all stages).

## CPU and memory

The protocol is the incumbent pilot's: `lake env lean <file>`, sequential,
with dependencies cached. Each module was run 3 times on the same machine in
the same session. The table gives wall and user CPU in seconds (range over the
3 runs) and the maximum peak RSS.

| module | wall (s) | CPU (s) | peak RSS |
|---|---|---|---|
| `Vsa/Sim/TextImage` (copied) | 0.70–0.77 | 0.65–0.72 | 0.85 GB |
| `VsaIris/Vsa/SymObsStep` (copied) | 1.46–1.62 | 1.05–1.20 | 2.58 GB |
| `VsaIris/Vsa/SymExec` (copied) | 4.97–5.43 | 11.4–12.6 | 2.85 GB |
| `Sym/Run` | 1.84–1.89 | 1.49–1.51 | 2.68 GB |
| `Sym/Head` (`dispatchS`) | 2.31–2.39 | 2.02–2.04 | 2.74 GB |
| `Sym/Close` | 2.73–3.33 | 2.94–3.27 | 2.71 GB |
| `Sym/Step` | 1.61–1.64 | 2.77–2.89 | 0.85 GB |
| `Sym/Fields` (with one `decide +kernel` over 256 `sB` values) | 2.31–3.07 | 1.69–1.83 | 2.68 GB |
| **`Sym/Move`** | 2.81–4.07 | 3.01–4.08 | 2.78 GB |
| **`Sym/Add`** | 4.91–5.41 | 5.64–6.18 | 2.96 GB |
| **`Sym/Eqi`** | 4.59–4.71 | 4.60–4.71 | 2.96 GB |
| **`Sym/Forloop`** | 5.92–6.19 | 6.96–7.14 | 2.94 GB |
| incumbent `Arms/Move` (for reference) | 2.43–2.82 | 2.78–3.14 | 1.97 GB |
| incumbent `Arms/Segs/G20` (12 segments, MOVE's 2 among them) | 5.85–6.14 | 15.8–16.2 | 2.18 GB |
| incumbent `Arms/Segs/G22` (12 segments) | 2.98–3.40 | 5.2–5.9 | 1.97 GB |
| incumbent `Arms/Sites/S16` (41 site lemmas) | 2.07–2.36 | 4.4–4.7 | 1.88 GB |

Reading the table:

- **Setup, once.** About 24 s CPU across 8 modules. 12 s of it is the copied
  `SymExec`.
- **Per arm.** 3–7 s CPU in one module, with no generated modules. The kernel
  check of `sym_eval` (the tree as one definitional unfolding) is cheap: MOVE
  and the whole dispatch cost about 2 s each.
- **The incumbent's held-out arms.** They would need the generated segments
  `arms.tsv` lists: ADD 24, EQI 16 and FORLOOP 19. They would also need their
  site batteries, and those segments regenerated with the `KEEP` pins of
  `SIM_OPS`, as G20's were.
  - At the measured 0.5–1.3 s CPU per segment and about 0.11 s per site, that
    is about 10–30 s of generated-module CPU per arm, plus the arm's own module.
  - This is an estimate from G20, G22 and S16, not a measurement of those arms.
- **Memory.** The executor route peaks about 1 GB higher: 2.8–3.0 GB against
  1.9–2.2 GB. The SWP/Iris import base alone is 2.6 GB (`SymObsStep`).
- **syi's "1.6–1.85× slower" finding does not recur per arm here.**
  - Refactored MOVE matches the incumbent's MOVE module: 3.0 against 3.0 s CPU.
  - It needs no segment modules, where the incumbent needs its generated ones.

## What the route could not express, with evidence

1. **`VmRel` does not give the executor's invariant (`VsaOk`).**
   - The executor's soundness (`symRun_swp` → `SWP`) is `LocalRun` over
     `vsaModel live`. Its `SegFrom` quantifies over states with
     `M.ok σ = VsaOk live σ` (`VsaIris/LocalRun.lean:131`,
     `VsaIris/Vsa/Instance.lean:63`).
   - `VsaOk` needs `gpr : ∀ n ∈ [1,31], (gprGet σ n).isSome` and
     `htifIdle : htif_payload_writes = some 0`.
   - `VmRel`'s `Core` pins 10 registers (`Pins`) and `GoodState`, which pins
     neither.
   - The incumbent's generated segments (`SegSt`) keep only their listed pins,
     so presence is not carried through `dispatch` either.
   - `MachineAt`/`CStackAt` (`Lua/Vm/Loaded.lean`, `Lua/Vm/Runtime.lean`) state
     only `a0`, `a1`, `sp`, `ra`, `gp` and the callee-saved registers. So
     `vmRel_entry` cannot supply it today.
   - **Resolution here:** the named premise `SymOk` (`Run.lean`), which every
     arm re-establishes (`SymOk c'` in the conclusion).
   - **To close it for real:** add `SymOk` to `MachineAt` (the boot state has
     every GPR) and carry it through the prologue by the executor. This
     changes `VmRel`, `vmRel_entry` and the incumbent's pilot arms.
2. **`VmRel`'s frame is presence-exact; the executor fixes only total reads.**
   - `vsaModel.mem c a := (c.σ.mem[a]?).getD 0`, and `SegFrom`'s frame is
     `M.mem σ' a = M.mem σ a`.
   - `Core.frame` is `c.σ.mem[a]? = w.mo[a]?` for every `a` outside the
     window.
   - A byte absent at entry could become `some 0` without `SWP` saying so. So
     `VmRel p c' s'` at the real endpoint is not derivable.
   - The arms rebuild `VmRel` on `c₀ = c'` with memory
     `M = writeLog c.σ.mem stores` (the run's own symbolic store log), and
     prove `CEqv c' c₀`.
   - The machine cannot tell `c'` from `c₀` (`Vsa.Densify.stepsN_sim`,
     `halts_iff_of_ceqv`). `simZ` shows the arms still compose.
   - **Recommendation:** state `Core.frame` on total reads (`MemEqv`). That is
     CLAUDE.md's own rule for byte reads ("never demand presence"). It would
     make `VmRelZ` and `VmRel` coincide.
3. **No call nodes.**
   - Each float path ends at its `jal` as a `.stop` leaf: ADD at `0x8001e7e4`
     and `0x8001e7f0`, EQI at `0x8001c824`, FORLOOP at `0x8001e168`.
   - The leaf's continuation must then be proved directly. That works here
     only because the path is infeasible.
   - An arm whose live path calls (`CALL`, `MMBIN`, `CONCAT`, `GETTABUP`, and
     `print`'s newlib chain) cannot be run through `symRun`. It needs a split
     at each `jal ra` and the Iris call rules (`swp_jal`, `MachWP`), outside
     the executor.
4. **Branch operands ignore known registers.**
   - `rdB` reads entry registers raw (`SE.raw`), not through `Cfg.known`. So
     `bnez s5` with `s5 = 0` is not pruned.
   - `dispatchS` refutes that side by hand (1 goal). The same happens for
     `bltu s1, a4`.
5. **Indirect jumps with a symbolic target stop the run.**
   - The dispatch `jr a5` target (a table word) is symbolic, so the run ends
     in a `.jr` leaf, and `dispatchS` proves the target is
     `armTarget op` (`armTarget_eq`, one `decide +kernel`).
   - A per-opcode `kvM` entry could make it constant, at one proof per opcode.
6. **Store forwarding across different atoms leaves `.disj` obligations.**
   - MOVE: 1 (`lbu 8(R[B])` after `sd 0(R[A])`). FORLOOP: 4 (the `trap`
     reload `lw 40(ci)` after four slot stores).
   - `obCheck`'s interval facts cannot separate two slots of unknown index, or
     `ci` from the window. These close by `omega` from `Ranges`. Same-atom
     forwarding (`sepC`) handled FORLOOP's reloads of `R[A]`/`R[A+2]` after the
     store to `R[A+1]`.
7. **`Geom` must be a literal.**
   - `geomOf` sorts with `Array.qsort`, which the kernel does not reduce. With
     `Γ := geomOf …` in the term, the kernel rejected `sym_eval`'s conversion
     ("(kernel) application type mismatch").
   - `geom%` evaluates `Γ` at elaboration time instead (syi's `sym_run` does
     the same inside its driver).
8. **syi's `sym_run`/`sym_run1` driver is not portable as is.**
   - It targets `IW` goals, is written to reproduce the interpreter's
     step-lemma form, and imports `ITac`/`AllocTac`.
   - The Lua arms use the executor's entry lemmas (`symRun_auto`) directly,
     with a 40-line splitter (`sym_split`) and the normalisers `arm_den`,
     `arm_guards` and `head_reg`.

## Per-arm hand cost, and what repeats

- Each arm is written by hand, leaf by leaf. It takes:
  - the kernel inversion of its combinator;
  - one `ValRepr` tag fact per branch on a tag;
  - `HeadImg.ofMem` with `head_reg` for the registers it does not write;
  - `Core.memJump`, `Core.memWrite` + `slotStore_*` (one slot), or
    `slot_peel` (several) for memory.
- The repeated shape is the leaf close. The pc+1/pc+2 leaves are 3 lines
  each; a jump leaf adds the target lemma.
- The per-combinator parts are shared by every opcode of the family:
  - `step_arith`: SUB … BXOR;
  - `step_condjump` + `kbit_eq`/`sB_eq`/`nextjump_eq`: EQK, LTI, LEI, GTI, GEI.
- A template per combinator could generate these arms, as `gen_lua_arm.py`
  does for the incumbent; one was not written.

## Effort

**Wall clock.** About 70 minutes, taken from commit timestamps.

| phase | time | minutes |
|---|---|---|
| reading, copy, `Cfg`, adequacy, `dispatchS` and `sim_MOVE` | 16:50–17:26 | 36 |
| ADD | 17:26–17:34 | 8 |
| EQI | 17:34–17:42 | 9 |
| FORLOOP | 17:42–17:50 | 7 |
| integration, `check.sh`, measurement | 17:50–17:58 | 8 |

There was no wait for machine memory.

**Failed elaborations.** About 52, each a single-file `lake env lean` of 1–8 s:

| phase | failed |
|---|---|
| setup and `dispatchS` | about 20 |
| `Close` | 8 |
| kernel inversions | 7 |
| field lemmas | 4 |
| MOVE | 5 |
| ADD | 5 |
| EQI | 6 |
| FORLOOP | 4 |

- None was a heartbeat timeout.
- One hit the maximum recursion depth: `simp` normalised EQI's `donextjump`
  register inside `head_reg`. It was fixed by closing that goal on its own.
- One was the kernel rejection of item 7.

# Abstraction discovery, round 2: A1 (machine arms)

Round 2 was a bake-off only. Round 1 (ROUND-1.md §3 C7–C9, "Carried to
round 2") had already supplied the census, laws and candidates. The cheap
falsifiers ran first (`experiments/a1-falsifiers/REPORT.md`):

- dependence-graph orbits (C8): dead, 46 classes;
- shared-prefix tree: dead, MST weight 0.52;
- `ADD`'s exits: both are head returns;
- stack relocation: `VmRel` must be relative to `ci->func`.

Two contenders remained. The protocol is in the scratchpad (`bakeoff2.md`):

- **held-out:** `sim_ADD`, `sim_EQI`, `sim_FORLOOP` against `VmRel`/`dispatch`;
- **refactor:** `sim_MOVE`.

**Contenders.**
- **incumbent:** generated segments (`gen_lua_arms.py`) composed by
  `gen_lua_arm.py` with one template per kernel combinator.
- **symexec:** ship-your-interpreter's verified symbolic executor
  (`SymExec`, `TextImage`), copied verbatim from `exponentiate` at `118e5f3c`
  for measurement only; its PR (#13) is not on syi main.

The contenders' own reports are `abstractions/bakeoff2/incumbent.md` and
`symexec.md`.

| | incumbent | symexec |
|---|---|---|
| theorem shape | exact: `VmRel` → `VmRel` | weaker: extra premise `SymOk` (all GPRs present, HTIF idle); conclusion `VmRelZ` (`VmRel` up to zero-fill) |
| setup (hand) | 464 Lean + 175 Python | 641 Lean (+2,442 copied) |
| held-out hand lines ADD/EQI/FORLOOP | **61/61/54** (templates) | 113/210/210 |
| generated lines | 724 sims + 2,623 segments | **0** |
| CPU per arm (module) | 6.7/6.9/6.5 s, plus about 10–30 s per arm for segments (estimate) | **5.8/4.7/7.0 s** |
| peak memory | **2.0 GB** | 2.96 GB |
| refactor `sim_MOVE` | 107 (77 generated + 30 template) | **59** |
| arms with live calls | expressible | not expressible (no call nodes) |
| failed builds / wall | 26 / 43 min | 52 / 70 min |

## Decision: no adoption. The incumbent stays.

The rule is that a winner needs held-out cost to fall AND the refactor to
shrink.

- *symexec wins the refactor* (59 vs 107 lines) and generated volume (0),
  and ties on CPU.
- *It loses the held-out hand cost* (2–4× the incumbent's template lines).
- *Disqualifying on its own:* it proves a weaker theorem than required, and
  it cannot reach the call arms that F1 needs (`CALL print`, the MMBIN paths).

The incumbent's arms (`sim_ADD`/`sim_EQI`/`sim_FORLOOP`) are merged. The
symexec branch is kept unmerged for reference.

## What would change the decision (round 3, when data warrants)

**Executor gaps**, reported to syi-7e for their v2:
- call nodes (or callee contracts at `jal`);
- branch reads that use known constants;
- total-read memory that matches the caller's frame.

**On our side, independently of the executor:**
- state `Core.frame` on total reads (`getD`), not exact presence. CLAUDE.md
  law: never demand presence the densification already gives. Then `VmRelZ`
  and `VmRel` coincide.
- carry "all GPRs present, HTIF idle" in `MachineAt`/`VmRel`.

Either change removes one of symexec's two shape gaps, and costs the
incumbent nothing.

**Incumbent's own limits** (incumbent.md):
- the ALU value lemma is per opcode;
- path templates are keyed to the compiled branch layout;
- generated size grows with paths × depth.

With 46 arm classes (the falsifiers), template reuse across arms will be
low. Watch the `a1-arm-sim` gate cluster, now 6 cases: if per-arm hand cost
does not fall by the 8th, round 3 runs.

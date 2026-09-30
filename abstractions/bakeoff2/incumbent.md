# A1 bake-off 2: `incumbent` (generated segments + `gen_lua_arm.py` templates)

**Route.**
- The machine side comes only from the generated `SegSt` segment theorems
  (`scripts/gen_lua_arms.py` → `Lua/Vm/Arms/Segs/G*.lean`), composed by
  `scripts/gen_lua_arm.py`.
- The generator has one template per kernel combinator, over `dispatch` and
  `VmRel` (unchanged from the pilot).
- The held-out arms need three new kinds:
  - `arith`: `opArith`, with two head-return exits;
  - `condjump`: `docondjump`;
  - `forloop`: `OP_FORLOOP`.
- For these kinds the generator walks the arm's segments by **branch
  polarity**, one path per exit. Along each path it substitutes each post's
  values into the next segment's arguments. Each path ends with its exit's
  close.

## Result

All three are proved, generated, and pass the gate.

| theorem | file | paths (exits) |
|---|---|---|
| `sim_ADD` | `Lua/Vm/Sim/Arms/Add.lean:24` | 3: int+int (write `R[A]`, pc+2); B int and C not int (pc+1); B not int (pc+1) |
| `sim_EQI` | `Lua/Vm/Sim/Arms/Eqi.lean:23` | 4: {int, not int} × {jump taken, skip} |
| `sim_FORLOOP` | `Lua/Vm/Sim/Arms/Forloop.lean:21` | 2: count 0 (exit, pc+1); count ≠ 0 (three stores, jump back pc+1−Bx) |

- The statements have the shape of `sim_MOVE`. The hypotheses are
  `Supported p`, `VmRel p c s`, the fetch, `ins.op? = some .OP` and
  `Step binaryHost p s s'`. The conclusion is
  `∃ c' n, 0 < n ∧ StepsN n c c' ∧ VmRel p c' s'`.
- **Float paths are discharged, not assumed.**
  - Every float branch is a `li 19; bne` or `beq` on a register's tag byte.
  - `ValRepr.ne_float` (`Close.lean`) proves that no F1 value has tag 19, so
    the float polarity is never taken:
    - `ADD`: the B and C tests;
    - `EQI`: the A test;
    - `FORLOOP`: `R[A+2]` must be an integer, because the kernel needs
      `.int st`, so the integer branch is taken.
- **Kernel cases with no step are vacuous.** They are:
  - a non-integer `R[A]` with count ≠ 0 in `FORLOOP`;
  - a missing next jump in `EQI` (`nextJump = none`).
  Both are closed from `Step`.

`#print axioms` for `sim_ADD`, `sim_EQI`, `sim_FORLOOP`, `Core.update` and
`Core.forloop`: each depends on `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` passes all stages; the stage-6 list gained 5 entries.

## Measurements

Line counts are non-blank and non-comment. Doc comments are excluded from
the Lean counts, and docstrings from the Python counts. Build times come from
`lake env lean <file>` under `/usr/bin/time`. Each time is for one module
whose dependencies are already built. It is measured after the final version,
on the shared 32-core machine.

### Setup (paid once, beyond the pilot's 533 hand lines)

| piece | kind | lines |
|---|---|---|
| `Lua/Vm/Sim/StepK.lean`: kernel inversions `step_opArith`, `step_condjump`, `step_forloop`; `cond_int`/`cond_nonint`, `jumpTo_neg`/`jumpTo_eq`, `mapM1/2/3` | hand Lean | 133 |
| `Lua/Vm/Sim/Close.lean`: see the list below | hand Lean | 331 |
| **hand Lean setup** | | **464** (57 declarations) |
| `gen_lua_arm.py` path machinery: `walk`, `chain2`, `subst`, pin fix-ups, `close_skip`, `render_arm2`, `gtag`, `indent` | Python | 143 |
| `gen_lua_arms.py`: `SIM_OPS` + `live_keep` (carry live temporaries through SIM segments) + second spec pass | Python | 25 + 7 |

`Close.lean` holds:
- the tag lemmas;
- 12 guard lemmas;
- the field terms: `sext_shr`, `field1`, `and255`, `addiw_bias`,
  `kraw_eq`/`sbraw_eq`, `ult_one_sub`;
- `nextjump_pc`, `add_val`/`dec_val`/`step_val`;
- `Core.update`, `ForStore`/`forloop_store`, `Core.forloop`;
- the `slot_arith` and `len_arith` tactics.

### Per arm

The hand template lines of a kind are its Lean text inside the generator:
- `PRE2`: the bytecode inversion;
- `FACTS2`: the operand representations and bounds;
- `paths2`: the case split, the per-path polarities and guard proofs, and
  the closes.

Each arm is currently the only arm of its kind, so the whole template is
charged to it.

| arm | kind | hand template lines (PRE + FACTS + paths) | per-arm table entry | generated `sim_<OP>` (theorem lines / file lines / bytes) | segment calls (distinct segments) | side conditions (`slot_arith`) | guards | segments used: lines / KB |
|---|---|---|---|---|---|---|---|---|
| ADD | `arith` | 8 + 13 + 40 = **61** | 1 | 219 / 232 / 20.8 KB | 10 (9) | 30 | 7 | 933 / 108 |
| EQI | `condjump` | 16 + 6 + 39 = **61** | 1 | 322 / 334 / 30.7 KB | 18 (12) | 30 | 10 | 1127 / 126 |
| FORLOOP | `forloop` | 12 + 9 + 33 = **54** | 1 | 183 / 193 / 16.0 KB | 7 (5) | 43 | 4 | 563 / 66 |

**Regenerated segment modules.**
- `SIM_OPS` now includes ADD, EQI and FORLOOP, so all 59 of their segments
  carry the head frame (`KEEP` + output).
- 13 segments also carry live temporaries (`live_keep`).
- 17 G modules changed: +1216 / −668 lines.
- MOVE, LOADI and JMP and their segments are byte-identical (no drift).

### Build

| module | wall (s) | CPU user (s) | peak RSS (GB) |
|---|---|---|---|
| `Lua.Vm.Sim.StepK` | 1.0 | 1.2 | 0.84 |
| `Lua.Vm.Sim.Close` | 4.2 | 4.9 | 1.92 |
| `Lua.Vm.Sim.Arms.Add` | 6.0 | 6.7 | 1.99 |
| `Lua.Vm.Sim.Arms.Eqi` | 6.7 | 6.9 | 2.01 |
| `Lua.Vm.Sim.Arms.Forloop` | 5.4 | 6.5 | 2.01 |
| 17 regenerated `Segs/G*` (first regeneration), `lake build` each | 50.2 total | 93.1 total | 2.10 max |
| 8 `Segs/G*` rebuilt after `live_keep` | 23.4 total | 45.9 total | 2.09 max |
| `Lua.Vm.Sim.Arms.Move` (refactor case, for reference) | 2.6 | 3.0 | 1.93 |

- About 1.8 GB of each peak is the imported environment.
- No module needed a raised `maxHeartbeats`.

### Refactor case: `sim_MOVE`

The incumbent route is unchanged, so `sim_MOVE` is the pilot's generated
proof.

| | value |
|---|---|
| generated theorem lines | 77 (86 in the file) |
| hand template (kind `copy`: prelude + close) | 9 + 21 = 30 |
| segments | 2 (306 lines, 40 KB) |
| side conditions | 13 (`arm_arith`) |
| build | 2.6 s wall, 3.0 s CPU, 1.93 GB |

### Failed builds and wall time

- **Failed elaborations: 26.** Each was a single-file `lake env lean` of
  1–15 s.

  | file | failures | what failed |
  |---|---|---|
  | `StepK` | 10 | `split`/`rename_i` names, a dependent `match` in `forloop` |
  | `Close` | 6 | 1 was a missing `.olean`; 1 was a `whnf` timeout from a `rfl` on `% 2^1` (fixed by `Nat.pow_one`, not by raising a limit) |
  | `Add` | 6 | see "What the route could not express" below |
  | `Eqi` | 1 | |
  | `Forloop` | 2 | one heartbeat timeout; see finding 3 below |
  | `Lua.Vm.Sim` | 1 | a name clash: `sext64` is already in `Entry.lean`; renamed to `sext64_id` |

- There were also 2 diagnostic runs (`trace_state`) and 1 generator crash
  (Python).
- One full `scripts/check.sh` failed only on the expected axiom-report count
  (100 → 105).
- **Wall time per phase**, from commit timestamps:

  | phase | wall |
  |---|---|
  | reading and regenerating/building segments | about 5 min (16:52–16:57) |
  | hand setup (`StepK`, `Close`) | 13 min (to 17:10) |
  | generator templates, until all three were proved | 14 min (to 17:24) |
  | gate and measurement | about 10 min |
  | **total** | **about 43 min** |

### Summary row

| contender | setup (hand Lean / new generator Python) | per-arm hand lines ADD / EQI / FORLOOP | generated lines (sim proofs; segments used) | build CPU (s) (sims; + segments) | peak mem | refactor `sim_MOVE` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| incumbent | 464 / 175 (143 + 32) | 61 / 61 / 54 template lines (+1 table line each) | 724 (219 + 322 + 183); 2,623 segment lines | 20.1 (+ 6.1 setup; + 139 segment regeneration) | 2.0 GB | 77 generated + 30 template (unchanged) | 26 | about 43 min |

## What the route could NOT express directly (evidence)

1. **Temporaries across segments.**
   - The segment generator threads only the registers a segment reads, plus
     `KEEP`. `ADD` computes the slots of `R[A]` and `R[B]` (s6, a5) before
     the tag-C branch and uses them after it.
   - The first generation failed with `KeyError: 'x15'`: the pin was not in
     `seg_8001e7d0_8001e7d8_t`'s post.
   - The fix is a liveness pass in `gen_lua_arms.py` (`live_keep`, 25
     lines). It adds 13 carried registers over ADD, EQI and FORLOOP.
2. **`omega` is incomplete on `% 2^64` address forms.**
   - After `slot_arith`'s normalisation, `2147483648 ≤ (w.base + ins/2^24·16
     + 8) % 2^64` failed. It is provable, and a hand `Nat.mod_eq_of_lt` step
     proves it.
   - `slot_arith` now removes each `% 2^64` first (`simp (disch := omega)
     only [Nat.mod_eq_of_lt]`).
   - Mixing `>>>` atoms with `/ 2^k` atoms also blocked `omega`. The fix is
     `Nat.shiftRight_eq_div_pow` in the simp set.
3. **Pin positions inside posts that hold store terms.**
   - `pinsHold_get … (by simp)` (the pilot's form) hit the heartbeat limit on
     `seg_8001c214_8001c240`'s post. Its values contain
     `bytesT8 (writeMap8 …)`.
   - `decide` cannot be used either: the goal has free variables.
   - The fix is `len_arith`: `simp only [List.length_cons, List.length_nil]`
     then `omega`.
4. **The closes are per combinator, and one of them is new setup.**
   - `Core.write` covers one full-slot store.
   - `FORLOOP`'s jump back makes four stores to three slots, and two of them
     are payload-only (`chgivalue`), which `SlotStore` cannot state.
   - It needed `ForStore`, `forloop_store` and `Core.forloop` (about 90
     lines).
5. **The ALU value is named per opcode.**
   - `add_val` has the `ld; ld; add; sd` payload built in.
   - A higher-order `f (sext x) (sext y)` pattern does not unify under
     `rw`, so SUB and MUL would each need their own value lemma and template
     parameter.
   - Not verified: F2 of the falsifier report says SUB and MUL reach pc+1
     through a shared default-target tail. Their branch layout, and so their
     polarity strings, may therefore differ from ADD's.
6. **Paths repeat their prefixes.**
   - The case split is made on the bytecode side (tags, `k`, count) before
     the chain. Each path therefore re-runs its prefix segments:
     - ADD makes 10 calls for 9 distinct segments;
     - EQI makes 18 calls for 12 distinct segments.
   - Generated size grows as paths × depth. A shared-prefix split would need
     the guard proof to be deferred to the branch point, which the
     `SegSt`-to-`SegSt` interface does not offer.
7. **Branch polarity is layout data.**
   - A template's paths are polarity strings: `"tt"`, `"tnt"`, `"nt"` for
     `arith`, and so on.
   - They encode how the compiler laid out `beq`/`bne` for that arm, not the
     combinator. An arm of the same combinator with a different layout needs
     new strings.

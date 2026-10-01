# A1 bake-off, round 3: contender KPROD (kernel-directed product executor)

KPROD runs ship-your-interpreter's reflective symbolic executor (`symRun`,
copied verbatim from `exponentiate` `118e5f3c`) over the Lua ELF, in lockstep
with the kernel term. The kernel's edges are evaluated forward. Each edge hands
the machine run a set of labels: tag-byte facts that the run's branch guards
meet after normalisation. A `jal ra` to a summarised helper is a call node. A
leaf at the fetch head is closed by one lemma.

## Summary

| setup | callee proofs | per-arm hand lines MUL / EQ / MOD | generated lines | build CPU (s) | peak mem | refactor `sim_ADD` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 878 Lean, plus 23 relation-widening lines, plus 2,442 copied verbatim | 692 (`__muldi3` 106, `__udivdi3` 228, `__moddi3` 65, `luaV_equalobj` 293) | **36 / 197 / 172** (MOD includes 97 lines of `smod` algebra) | **0** | 85.8 user-s KProd (+15.0 copied executor) | 3.22 GB (`Mod`) | **16 lines** (incumbent: 233 generated + its `arith` template) | 140 of 236 elaborations (95/171 via `el.sh`/`lb.sh` + 45/65 via `run6.sh`), 2 memory blow-ups | 3 h 20 min |

**What is proved.** Every theorem builds, and its axioms are
`[propext, Classical.choice, Quot.sound]`.

| theorem | statement |
|---|---|
| `Lua.Vm.Sim.KProd.sim_ADD` | exactly `SimArm .ADD` (refactor case) |
| `Lua.Vm.Sim.KProd.sim_MUL` | exactly `SimArm .MUL` |
| `Lua.Vm.Sim.KProd.sim_MOD` | exactly `sim_MOD_Statement` |
| `Lua.Vm.Sim.KProd.sim_EQ_of` | `LngEq → sim_EQ_Statement`: **partial**. One named obligation remains: two long strings. |
| `muldi3_summ`, `udivdi3_summ`, `moddi3_summ` | helper summaries at the Lua ELF's addresses, proved with no assumption |
| `equalobj_summ` | `LngEq → Summ luaV_equalobj …`, every F1 tag pair but long/long |

Every path the kernel's `Step` can take on F1 values is covered. Kernel-excluded
paths are discharged by the labels, not assumed away:

- **float tags.** `ValRepr.ne_float` and the tag-pair lemmas refute them.
- **`n % 0`.** `imod_eq_smod` gives `y ≠ 0`, which refutes the `luaG_opinterror` leaf.
- **the other kernel edge.** `IntLabels`/`NonIntLabels` refute the leaves of the edge not taken.

## Design: what was built

| file | role | lines |
|---|---|---|
| `VsaIris/Vsa/SymExec.lean`, `SymObsStep.lean`, `Vsa/Sim/TextImage.lean` | the executor, copied verbatim (ATTRIBUTION.md, `experiments/port/copied.txt`) | 2,442 |
| `KProd/Exec.lean` | the Lua configuration, `krun` (one executor run), `swp_run`/`localRun_run` adequacy, `VsaOk` from `Core`, the normaliser `kden`, `kframe`, `withRegs` | 303 |
| `KProd/Call.lean` | **call nodes**: `Summ` (a continuation-passing summary), a generic `jalx` (any `jal ra` site: bytes, decode by `rfl`), `swp_call`, `lw_frame` (the post-call symbolic state), `khrun`/`khloop` | 98 |
| `KProd/Close.lean` | **one close**: `HeadQ`, `Touch`, `Keep`, `close`, `arm_sim` (dispatch, then one `LW` run, gives exactly `SimArm`'s conclusion); `Env`/`ArmEnv`; address and tag normal forms; peel lemmas; `kpins`, `kkeep`, `kslot` | 302 |
| `KProd/Arith.lean` | the `op_arith` kernel half (`arith_sim`, `IntLabels`/`NonIntLabels`), `Regs3`, and the run tactics `kgeom`, `knorm`, `khead`, `kdead`, `krunA`, `karith`, `kenv` | 175 |
| `KProd/{Muldi3,Udivdi3,Moddi3,Equalobj}.lean` | helper summaries | 692 |
| `KProd/{Add,Mul,Mod,ModMath,Eq}.lean` | the arms | 16 / 36 / 172 / 197 |

### How the three round-2 losses are fixed

1. **Weaker theorem.**
   - Round 2 had to add a `SymOk` premise and conclude only `VmRelZ`.
   - The base `VmRel` now carries `RegsOk` and a total-read frame, so `VsaOk`
     follows from `Core` (`vsaOk_of_core`).
   - `close` rebuilds `VmRelAt` on the run's real end configuration. `arm_sim`'s
     conclusion is literally `SimArm`'s.
   - Checked: `example : SimArm .MUL := sim_MUL` and `example : sim_MOD_Statement := sim_MOD`.
2. **No call nodes.**
   - The executor stops at `jal ra`, because it decodes only `jal x0`.
   - `swp_call` takes one generic `jal` step, applies the helper's `Summ`, and
     continues from the return address with the post-call state `withRegs R₁ R clob`.
   - Summaries quantify over every post `Q`, so composition stays at `SWP` level
     with no uniform-fuel argument.
   - Loops inside helpers (`__muldi3`, both `__udivdi3` loops) are proved by
     induction, one executor run per iteration (`khloop`).
   - Call nesting works: `__moddi3`'s two `jal __udivdi3` are call nodes inside
     a summary proof, and MOD's `jal __moddi3` is a call node inside the arm.
3. **Glue cost.**
   - Round 2 needed 77–210 lines per arm.
   - Here the glue is factored into `arith_sim`, `close`/`HeadQ`, and the leaf
     tactics: normalise, refute by labels, close the pins, keep the store log,
     read back the written slot.
   - `sim_ADD` is 16 lines and `sim_MUL` 36.

### Kernel-directed labelling

- **`op_arith`.** `arith_sim` inverts the kernel once (`step_opArith`). The
  integer edge gives `IntLabels`: both tags are `LUA_VNUMINT`, and the payloads
  are the operands. The other edge gives `NonIntLabels`: no float tag, and not
  both integers.
- **Pruning.** `kdead` refutes each machine leaf whose guards contradict its
  labels. The run itself is not pruned.
- **`luaV_equalobj`.** The labels are fed into the executor as known entry
  words (`kvM`): the tag bytes and the jump-table word. With those, the
  `switch (ttypetag)` jump is computed, and each same-tag class is one
  straight path (`eq_unit`, `eq_pay`).
- **Different tags.** The run stays symbolic. Two decided tag-pair lemmas
  (`tags_g1`, `tags_g3`) refute every non-returning leaf.

## Relation widening (needed by MOD and EQ, all at the base)

The base claimed `VmRel` was sound for MOD/EQ. It was not, as stated: three
facts were missing.

1. `Ranges.scratch_out`. The `Scratch` words miss the register slots and the C
   frame.
   - Without it, `savestate`'s `sd` to `L->top`, or a callee frame, could
     overwrite a register slot or `0(sp)`.
   - `vmRel_entry` proves it from `VmRegionsAt`, using one new boot-witness
     field, `L_sep_stack` (the `lua_State` and the Lua stack are distinct
     `l_alloc` blocks).
2. `Ranges.L_hi`. `L` lies in RAM. Only `L_lo` existed, so `w.L` could wrap
   under `BitVec.ofNat`.
3. `Ranges.{L_al, ci_al}`. `L` and `ci` are 8-aligned. The executor's store rule
   needs aligned `sd`, which matches Sail's misaligned-store behaviour. These are
   new boot-witness fields.

`gen_lua_boot_witness.py --check` holds at both traced entries: "all fields
hold". The change is 23 hand lines across `Rel.lean`, `Entry.lean`,
`Runtime.lean` and the generator. No generated file changed.

## What the route could not express (with evidence)

1. **EQ on two long strings: the relation lacks string-object separation.**
   - `luaS_eqlngstr` reads `lnglen` and `memcmp`s the contents in the machine
     memory. `ValRepr.str` only states `TStringRepr` over the complement `mo`.
   - `Core.frame` equates the machine memory with `mo` only outside `Win`.
     Nothing places a register's string object outside `Win` (the slots, the C
     frame, `Scratch`).
   - So `SimArm .EQ` is not derivable from `VmRel` alone.
   - It is left as the named obligation `LngEq` (`KProd/Equalobj.lean`). That
     obligation also needs a `memcmp` summary, which is not written (two loops).
   - The fix belongs in the relation: carry "string objects ⊆ heap minus the Lua
     stack" through `ValRepr`/`Core`, supplied by the allocator. That touches
     every arm that writes a register, so it is out of a contender's scope.
2. **Closed-term limit of `sym_eval`.**
   - The executor's tree must be a closed term.
   - A known entry word that depends on a variable (e.g. the next instruction
     word `ni` for `donextjump`) cannot be passed as `kvM`. It is rewritten
     after the run instead (`h27`, `nextjump_n`).
3. **Arithmetic with 2⁶⁴-scale literals blows up.**
   - `omega` or `simp [BitVec.toNat_ofNat]` on `(sp + 18446744073709551568#64).toNat`
     drove one elaboration to 24–26 GB RSS.
   - This happened twice in development. Both runs were killed: one by hand,
     one by the memory cap.
   - The fix is per-offset rewrite lemmas (`frame_base`, `frame_m8` … `frame_m64`),
     each proved through `BitVec.sub`.
   - Every elaboration after that ran under a 6–8 GB `MemoryMax` cap.
4. **Heartbeats per declaration.** One theorem holding a whole arm with a call
   ran over the default budget (MOD). The limit was not raised. The arm is split
   into per-edge and continuation theorems instead (`mod_int`, `mod_nonint`,
   `mod_cont`; `eq_run`, `eq_cont`).
5. **`decide` on 64-bit `sign_extend`/image words in the elaborator** (as
   opposed to `decide +kernel` on 32-bit table words) blew up. Table words are
   stated as 32-bit `decide +kernel` facts (`eqJt_0` …).

## CPU and memory

`lake env lean <file>` with imports prebuilt, one file at a time, `MemoryMax=12G`, run sequentially at the end:

| module | wall (s) | user CPU (s) | peak RSS |
|---|---|---|---|
| copied: `SymObsStep` / `TextImage` / `SymExec` | 2.1 / 0.8 / 5.9 | 1.5 / 0.8 / 12.7 | 2.74 GB |
| `Exec` | 2.5 | 2.3 | 2.62 GB |
| `Call` | 2.2 | 1.7 | 2.59 GB |
| `Close` | 3.0 | 2.9 | 2.64 GB |
| `Arith` | 3.6 | 3.1 | 2.62 GB |
| `Add` (refactor) | 6.1 | 5.8 | 2.89 GB |
| `Muldi3` | 2.9 | 2.5 | 2.64 GB |
| `Mul` | 7.3 | 7.0 | 3.06 GB |
| `Udivdi3` | 3.0 | 3.3 | 2.68 GB |
| `Moddi3` | 2.4 | 2.0 | 2.65 GB |
| `ModMath` | 1.0 | 1.0 | 0.83 GB |
| `Mod` | 12.7 | 22.4 | 3.22 GB |
| `Equalobj` | 17.5 | 25.2 | 3.19 GB |
| `Eq` | 5.2 | 6.7 | 2.77 GB |
| **KProd total** | 72.4 | **85.8** | **3.22 GB** |
| incumbent `Lua/Vm/Sim/Arms/Add.lean` (for comparison) | 7.6 | 8.3 | 1.96 GB |

About 2.6 GB of the baseline RSS is the imported Sail/executor environment.
The incremental `lake build Lua.Vm.Sim.KProd` took 16.7 s wall, 48 s user and 3.2 GB peak.

**Failed builds.**
- 95 of 171 logged elaborations failed (`el.sh`/`lb.sh`; 5 of them in scratch test files).
- 45 of 65 unlogged `run6.sh` elaborations had errors. That count is reconstructed from the session transcript.
- Two of the failures were runaway-memory events at 24–26 GB, before the 6–8 GB cap was adopted.
- `sim_ADD` was the first arm, and it absorbed 25 failed elaborations while the leaf tactics were being found.

## Forecast for the remaining arms

| arm | forecast |
|---|---|
| CALL print | Needs the `runtime` summary shape: `L->top`, the heap and `ci` change, and `func` may move. `Summ`'s post would carry a new `w'` and a `VmRel`-level frame. That is a relation-level change, not an executor one. Call nodes compose, but the stdio callee closure (81 functions) is A0 work; with `SWPO`/stdio step tables it would be summaries. Not cheaper here than elsewhere. |
| VARARGPREP | One call node to `luaT_adjustvarargs`. Its summary moves `func`, so it needs the same relation change (re-witnessed `w`) as CALL. |
| FORPREP | Two call nodes (`luaV_tointeger`, `luaV_tonumber_`). Pure summaries with an out-pointer into the C frame, which is `Win` and so free. Moderate: a structure like MOD, about 100–150 lines. |
| LOADNIL | A loop inside the arm. `khloop` with induction over the count, as in the helpers; about 40 lines. |
| RETURN | The `Final` clause, not a `SimArm`. It needs the exit chain's summaries (`luaD_poscall`, `ccall`, `exit`). Call nodes would carry it, but the callee closure is large. |
| other `op_arith` arms (SUB, BAND, BOR, BXOR, MULK, IDIV …) | `arith_sim` plus `karith`. The inline ones are about 12–16 lines (as ADD). Call ones are about 36 (as MUL); IDIV is about 70 (as MOD, with `__divdi3`). |

## Wall time by phase (UTC, from commit times)

| phase | span | minutes |
|---|---|---|
| reading, executor restore, `Exec`, `Call`, `__muldi3` (≈25 min waiting for machine memory) | 23:05–23:49 | 44 |
| `Close`, `Arith`, `sim_ADD` | 23:49–00:05 | 16 |
| `sim_MUL` | 00:05–00:15 | 10 |
| `__udivdi3`, `__moddi3` | 00:15–00:21 | 6 |
| `sim_MOD` (and the widenings `L_hi`/`L_al`/`ci_al`) | 00:21–00:36 | 15 |
| `luaV_equalobj` (including the two memory blow-ups and a rate-limit interruption) | 00:36–01:50 | 74 |
| `sim_EQ_of` | 01:50–02:15 | 25 |
| check, measurement, report | 02:15–02:25 | 10 |

## Gate

- `scripts/check.sh --static-only` passes every stage except 3c, which is the
  expected `a1-arm-sim` gate.
- The full `scripts/check.sh`, with stage 3c skipped, passes stages 1, 2, 3, 3b, 4, 5, 5b and 6: the full `lake build Lua Vsa VsaIris`, the OS traces, and the axioms.
- Stage 6 initially failed only on its fixed report count. The count is now updated from 131 to 139.
- Stage 6 now lists `sim_ADD`/`sim_MUL`/`sim_MOD`/`sim_EQ_of` and the four
  summaries.

# A1 pilot with the incumbent tooling: MOVE, LOADI, JMP

The first machine-arm simulation proofs. They are built only from the incumbent
segment layer: the generated `SegSt` segment theorems (`Lua.Vm.Arms.seg_*`,
A0.8) and their site batteries. This pilot is the incumbent's data point for
the round-2 A1 bake-off (ROUND-1 "Carried to round 2"). The held-out arms ADD,
EQI and FORLOOP were not touched.

## What was built

| piece | file | kind |
|---|---|---|
| fetch-head segment `seg_8001bfe4_8001c00c` (trap check, `lw`, bound check, table `lw`, `jr`), 10 site lemmas | `Lua/Vm/Arms/Head{,Sites}.lean` | generated (`gen_lua_arms.py`) |
| SIM arms' segments carry the fetch-head registers (`KEEP`) and `sailOutput` | `Lua/Vm/Arms/Segs/G12,G20.lean` | generated (new `keep`/`output` options of `disasm_to_segment.py`/`gen_segment.py`) |
| `VmRel` / `VmRelAt` / `Core` / `ArmAt`, `Core.write`, `Core.jump` | `Lua/Vm/Sim/Rel.lean` | hand |
| `dispatch`, `sim_of_run`, `pinsHold_get` | `Lua/Vm/Sim/Dispatch.lean` | hand |
| instruction-field lemmas, `arm_arith` tactic | `Lua/Vm/Sim/Bits.lean` | hand |
| slot stores, jump table (`jtWord_eq`, `armTarget_aligned`) | `Lua/Vm/Sim/Mem.lean` | hand |
| kernel inversions per combinator (`step_setR`, `step_jump`), `supported_regTop` | `Lua/Vm/Sim/Step.lean` | hand |
| `sim_MOVE`, `sim_LOADI`, `sim_JMP` | `Lua/Vm/Sim/Arms/*.lean` | generated (`scripts/gen_lua_arm.py`) |

## Measurements

The line counts are non-blank, non-comment lines (the `abstractions/census.py`
declaration counter for proofs).

**Setup (paid once).**

| file | code lines | declarations |
|---|---|---|
| `Rel.lean` (relation + write/jump re-establishment) | 152 | 7 (`Core.write` 28) |
| `Dispatch.lean` | 110 | 4 (`dispatch` 86) |
| `Bits.lean` | 123 | 15 |
| `Mem.lean` | 98 | 12 |
| `Step.lean` | 50 | 5 |
| **total hand setup** | **533** | 43 |
| generator changes (`gen_lua_arms.py`, `disasm_to_segment.py`, `gen_segment.py`) | +131 −25 lines of Python | — |
| new generator `gen_lua_arm.py` | 393 lines of Python | — |

**Per arm.**

| arm | kind | generated proof lines (`sim_<OP>`) | segments | side conditions (`arm_arith`) | hand template lines in the generator (kind prelude + close) |
|---|---|---|---|---|---|
| MOVE | copy | 77 | 2 | 13 | 9 + 21 |
| LOADI | imm | 68 | 1 | 7 | 10 + 25 |
| JMP | jump | 75 | 1 | 3 | 8 + 34 |

About 25 lines of skeleton are shared by all kinds (dispatch, preamble facts,
segment chaining). All per-arm arithmetic that a hand proof would repeat is
generated: segment arguments, pin positions, and one `arm_arith` per side
condition. The only hand cost left per arm is its kind's close, which is
shared by every opcode of that combinator (`copy`: MOVE; `imm`: LOADI, and with
a different value LOADF/LOADFALSE/LOADTRUE/LOADK; `jump`: JMP, VARARGPREP's
no-op edge).

**Build (kernel + elaboration, `lake env lean`, sequential, cached deps).**

| module | wall | peak RSS |
|---|---|---|
| Bits | 9.3 s | 1.9 GB |
| Mem | 11.0 s | 1.9 GB |
| Step | 6.7 s | 0.8 GB |
| Rel | 9.6 s | 1.8 GB |
| Dispatch | 9.4 s | 1.9 GB |
| Arms/Move | 8.7 s | 1.9 GB |
| Arms/Loadi | 8.1 s | 1.9 GB |
| Arms/Jmp | 13.9 s | 1.9 GB |
| Arms/Head (segment) | 3.1 s | — |

The regenerated segment modules G12/G20 build in 4–8 s.

**Effort.**
- About 80 minutes of wall-clock time in this session, from reading to the
  last commit. About 10 minutes of it were spent waiting for machine memory.
- About 27 failed elaborations while iterating. Every one was a single-file
  `lake env lean` check, and each took 2–15 s:
  - bit-vector field lemmas: 6;
  - store/read-back lemmas: 3;
  - kernel inversions: 3;
  - `Rel`: 3;
  - `dispatch`: 3;
  - the three arms by hand: 8;
  - the generated arms: 1, a missing implicit argument, fixed in the
    generator.
- None of them was a timeout or heartbeat problem.

## Findings for round 2

1. **The incumbent segments lack a frame.** A1 needs registers the segment
   does not touch, and the console output. The `SegSt` segments of A0.8 kept
   neither. So `gen_lua_arms.py` now pins `KEEP` (12 registers) and threads
   `sailOutput` on the segments of `SIM_OPS` arms only.
   - Cost: the pin lists are about 2.5 times longer.
   - The rebuild is cheap (seconds per module). Other arms pay nothing until
     they join `SIM_OPS`.
2. **Unification cannot be trusted with segment values.** Passing `_` for a
   segment's register values makes Lean whnf `BitVec.ofNat` and `sign_extend`
   into structure literals, and `arm_arith` then fails. The generator passes
   every value explicitly and normalises each value a later segment needs
   (`NORM`: MOVE's `R[B]` address, via `slot_addr`).
3. **Side conditions are uniform.** Every `h*_<step>` of the three arms (23)
   closes with one tactic, `arm_arith`: `field8`/`shl_ofNat`/`add_imm`
   normalisation, then `omega` over `Ranges`.
4. **The closes are per combinator, not per opcode.** This matches the round-1
   kernel abstraction (`setR`, `jump`, …), and a C7-style evaluator would have
   to reproduce it.
5. **Relocation.** Registers are decoded from `ci->func`, which lives in the
   complement memory (`Complement.func_word`, `base = func + 16`). The
   falsifier report (`experiments/a1-falsifiers/REPORT.md`) confirms two
   things:
   - `VARARGPREP` moves `ci->func` in every main chunk;
   - `CALL print` can reallocate the stack at ≥ 15 locals.

   Both re-establish `VmRel` with a new `func`, not a new relation.

## The entry lemma (`vmRel_entry`)

`vmRel_entry : vmRel_entry_Statement` (`Lua/Vm/Sim/Entry.lean`): from
`VmLoaded luaLayout p c`, `luaV_execute`'s prologue runs from the entry to the
fetch head in `VmRel p c' State.init`. It was built with the incumbent route
only: generated segments, then one hand composition.

**What was built.**

| piece | file | kind |
|---|---|---|
| the prologue, two segments cut at `startfunc` (`seg_8001bf68_8001bfb0`: C frame, `L`/`ci`, jump table; `seg_8001bfb0_8001bfe4`: `startfunc`'s loads, s1/s2, the `trap` check, `base`), 28 new site lemmas (3 `startfunc` sites shared with the `OP_CALL`/`OP_TAILCALL` batteries) | `Lua/Vm/Arms/Prologue{,Sites}.lean` | generated (`gen_lua_arms.py` `prologue_specs`, `keep = [gp, s8]` + output) |
| `VmRegionsAt` (heap placement and separations), `HarnessAt` (`tick < 2`, empty console), `RtPtrs.{cl, proto, code, sizecode}` | `Lua/Vm/Runtime.lean` | hand, checked natively on while and f1_ops by `gen_lua_boot_witness.py` |
| `rdLE_spec` (`rd32`/`rd64` → `bytesT4`/`bytesT8`), `AgreeOut` (C-frame memory frame), `ProtoRepr.code`, `vmRel_entry` | `Lua/Vm/Sim/Entry.lean` | hand |

**Measurements.**

| item | cost |
|---|---|
| `Entry.lean` | 228 code lines, 13 theorems (census counter) |
| of which `vmRel_entry` | about 160 lines |
| generator changes | `gen_lua_arms.py` +97 lines, `gen_lua_boot_witness.py` +35, `gen_lua_arm.py` ±3 (index import) |
| `Runtime.lean` | +64 lines (two structures, four `RtPtrs` fields) |
| build `Entry` | 11.6 s, 2.0 GB |
| build `Prologue` / `PrologueSites` | 4.1 s / 1.5 s, 2.0 / 1.8 GB |
| failed elaborations | 8, each a single-file check of 10–15 s; none a timeout or heartbeat problem |

**How the side conditions close.**
- Segment 1's 52 side conditions (13 `sd` × lo/hi/window/alignment) are ground,
  since `sp` is `RuntimeData.spEntry`. They close with
  `repeat (specialize H1 (by decide))`.
- Segment 2's 27 side conditions close with one `first` combinator:
  - a normalising `simp` over five read facts `hR*`, each read through
    `AgreeOut` and `rdLE_spec`, then `omega` over `VmRegionsAt`;
  - or `decide` when the side condition is ground.
- The relation's fields come from:
  - `VmEntryData` for the pointers (`w.mo` is the entry memory);
  - `LuaStateAt` for `trap_word` and `RuntimeMem`;
  - `VmRegionsAt` for `Ranges` (one `omega` each).

**Findings.**
1. **`luaLayout` lacked placement facts.** The `Ranges` of `VmRel`, and the
   prologue loads of `L->hookmask`, the closure and the `Proto`, need
   addresses in RAM, off `tohost`, and apart from the register window. Nothing
   in `luaRuntimeReady` stated them. `VmRegionsAt` states them as heap
   placement, `[_end, __heap_end)` below the C stack (`cstack_room`), plus two
   separations from the Lua stack. Both traced entries satisfy it.
2. **The harness facts belong to the layout.** `SegSt` needs `tick < 2`, and
   `Core.out` at `State.init` needs an empty console. ship-your-interpreter
   takes both as hypotheses of its `Loaded` instance. Here they are
   `HarnessAt`, and `RuntimeReadyAt` now takes the `Config`.
3. **Cut the prologue where its memory changes role.** In one segment, every
   `startfunc` load was stated over the 13-store chain: 561 KB of statement.
   Cut at `startfunc` (the first prologue address the arms reach), it is
   111 KB, and segment 2's loads read its entry memory. The C frame is
   discharged once (`AgreeOut`).
4. **`VARARGPREP` is not part of the prologue.** The relation holds at the
   head before the first instruction, with `func = ci->func` at entry. The
   `func` shift is `VARARGPREP`'s arm.

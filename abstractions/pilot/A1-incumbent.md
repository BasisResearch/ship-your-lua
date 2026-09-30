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

## More arms: the relation fixes of round 2, and 19 new arms

**The relation.** Two changes named by `abstractions/ROUND-2.md` ("On our
side"), and one extension the `K` arms need. Each is its own commit.

- **Total reads** (`Core.frame`). Outside the window the machine's
  `bytesT1` (`getD 0`) is the complement's; exact presence is no longer
  demanded. The segments' fetches still need `.text` present (`SegSt`'s
  `TextLoaded`), so that one presence is its own field, `Core.text`.
  - Cost: +57 −34 hand lines (`Mem.lean`: `bytesT4_congrT`, `bytesT8_congrT`,
    `RodataRead`; `Rel.lean`: `Core.rodata`, `Core.text_of`, `Core.frame_of`).
  - **No proof got shorter.** `vmRel_entry` stays at 160 lines, the six arms
    are byte-identical but for one argument (`hc1.text`), and `Core.write`
    grew by one line (28 → 29). The gain is the shape: `VmRel` is now
    invariant under zero-fill except for `.text`, whose presence the segment
    layer requires.
- **Registers present, mailbox idle** (`Core.ok : RegsOk`, named structure
  `Lua.Vm.RegsOk`, the register half of syi's `VsaOk`).
  - `MachineAt.regs` carries it at the entry. `gen_lua_boot_witness.py`
    `check_regs` checks it natively on both traces: all 31 GPRs are traced,
    no boot store touches `tohost`, and the choice source's undefined bit
    vectors are 0.
  - Every `sim` segment threads it. `gen_segment.py` has a new `"ok"`
    option that adds one line per step, with one lemma per step class
    (`Lua/Vm/Arms/RegsOk.lean`: `alu`, `store`, `btaken`, `bnottaken`,
    `jal`, `jr`).
  - The arm payload is now the named `ArmPay` with one accessor per field
    (`SegSt.armText/armMem/armOut/armOk`). The closes read the output and
    `RegsOk` from the segment.
  - Cost: +218 −51 hand lines (110 of them the two `RegsOk` files).
    Regenerating the segments costs about 140 s CPU.
- **The constant array** (for `ADDK`/`SUBK`/`LOADK`).
  - `Core.kptr`: `0(sp) = k`.
  - `Complement.kconst`: `ConstRepr` → `ValRepr` for every `kval`.
  - `Ranges.k_lo/k_hi/k_al/k_out/k_sep/frame_sep`.
  - `VmRegionsAt.kArr/sizek/k_*` are checked natively by the boot witness.
  - `vmRel_entry` discharges `Core.kptr` from the prologue's `sd`
    (+80 lines).
  - The closes take a frame that is exact outside the register slots
    (`Slots`), which also keeps `0(sp)`.
  - Cost: +135 −26.

**The arms.** 25 are proved, all generated by `scripts/gen_lua_arm.py`:

- the pilot: MOVE, LOADI, JMP;
- bake-off 2: ADD, EQI, FORLOOP;
- new here: SUB, ADDI, ADDK, SUBK, BAND, BOR, BXOR, LTI, GTI, LEI, GEI,
  LOADTRUE, LOADFALSE, LFALSESKIP, LOADK, BNOT, NOT, TEST, TESTSET.

The segment set now covers all 52 F1 opcodes of `Lua/Fragment.lean`
(`draft_f1_arms.F1_EXTRA_OPS`; 1212 segments).

The new kinds, or layout parameters of existing kinds:

| kind | arms | what is per arm |
|---|---|---|
| `arith` (unified) | ADD, SUB, ADDI, ADDK, SUBK, BAND, BOR, BXOR | a table entry: `BinOp`, the ALU function (`HAdd.hAdd` …), the C operand form (register, `sC`, `K`) and the branch layout (`beq`/`bne` tag tests, float test) |
| `cmpI` | LTI, GTI, LEI, GEI | a table entry: the primitive, the operand order, the machine boolean (`slt`, `slt`+`seqz`) and the final branch (`beq`/`bne`) |
| `settag` | LOADTRUE, LOADFALSE, LFALSESKIP | (boolean, pc step) |
| `loadk` | LOADK | — |
| `bnot` | BNOT | — |
| `truth` | NOT, TEST, TESTSET | one path table each (`l_isfalse` tag tests) |

**Per arm.**
- *Hand lines* are the non-blank, non-comment lines added to the hand files
  (generator, `Close`/`StepK`/`Rel`/`Mem`/`Entry`) by the arm's commit,
  divided by the arms in the commit. The relation commits are setup and are
  not charged.
- *Generated* lines are the `sim_<OP>` theorem (census counter) and the
  file.
- *CPU* is `lake env lean` on the arm module with its dependencies built.
  Peak RSS is 1.9–2.1 GB for every arm.

| # | arm | kind | hand lines | generated (theorem / file) | CPU user (s) |
|---|---|---|---|---|---|
| 7 | SUB | arith | 24 | 229 / 255 | 7.0 |
| 8 | ADDI | arith (`sC`; the template unification) | 113 | 150 / 173 | 4.5 |
| 9 | ADDK | arith (`K`) | 33.5 | 263 / 287 | 9.3 |
| 10 | SUBK | arith (`K`) | 33.5 | 263 / 288 | 9.0 |
| 11 | BAND | arith (`op_bitwise`) | 2 | 292 / 317 | 11.0 |
| 12 | BOR | arith | 2 | 292 / 318 | 8.4 |
| 13 | BXOR | arith | 2 | 292 / 316 | 8.1 |
| 14 | LTI | cmpI | 33 | 189 / 212 | 4.8 |
| 15 | GTI | cmpI | 33 | 189 / 213 | 4.4 |
| 16 | LEI | cmpI | 33 | 213 / 237 | 5.2 |
| 17 | GEI | cmpI | 33 | 213 / 236 | 4.7 |
| 18 | LOADTRUE | settag | 28.75 | 57 / 78 | 1.6 |
| 19 | LOADFALSE | settag | 28.75 | 57 / 78 | 1.6 |
| 20 | LFALSESKIP | settag | 28.75 | 57 / 78 | 1.7 |
| 21 | LOADK | loadk | 28.75 | 83 / 104 | 3.6 |
| 22 | BNOT | bnot | 53 | 95 / 117 | 3.4 |
| 23 | NOT | truth | 91 | 182 / 205 | 4.5 |
| 24 | TEST | truth | 91 | 299 / 321 | 6.0 |
| 25 | TESTSET | truth | 91 | 322 / 345 | 9.3 |

For reference, the six earlier arms are MOVE 30, LOADI 35, JMP 42, ADD 61,
EQI 61 and FORLOOP 54 hand template lines.

**Failed builds: about 25**, each a single-module build of 1–15 s. None was
fixed by raising a limit.

| where | failures | what failed |
|---|---|---|
| `RegsOk` | 2 | `Quiet` had to be reducible for `decide`; `_root_` names for `SegSt.arm*` |
| ADDI and the unification | 3 | `rfl` in `scraw_eq`; the hypothesis list of the facts |
| the constant array | 1 | `_root_` names |
| ADDK/SUBK | 3 | a missing parenthesis, the `sp` bound, `rw` inside a pin list |
| the segment extension | 1 | stale G-module imports |
| cmpI | 5 | two `maxRecDepth` failures when unifying an `sB` hole, fixed by normalising `sB` first (`sbraw_eq`), not by a limit; `htop` needed `immB` |
| the loads | 2 | `subst` direction; the `k` load inside side conditions (`KPARAM`) |
| truth | 6 | `step_testset`, `isFalse_of_ne`; TESTSET's `trap` and next-instruction reads go through the tag's `sb` (`insert_frame`, `Core.fetch_of`) |
| `vmRel_final_Statement` | 1 | an argument of `Final` |

**Wall time.** About 1 h 10 min from the first commit to the last arm,
including builds and waiting on memory.

### The gate

**`check.sh` stage 3c is blind to these arms.** The `a1-arm-sim` cluster
counts hand-written `sim_[A-Z0-9]+` theorems. `gate.py` skips every file with
a `GENERATED` header, and every `sim_<OP>` is generated, so it reports
"0 cases — ok". The 6 cases that `ROUND-2.md` counted were never seen by the
gate.

**Applied by hand, the rule fails.** The rule is: at 8 or more cases, the
mean of the last quarter must be a third below the mean of the first
quarter.

| cases | last arm | first-quarter mean | last-quarter mean | rule |
|---|---|---|---|---|
| 8 | ADDI | 32.5 | 68.5 | **fails** |
| 9–10 | ADDK, SUBK | 32.5 | 73.2 / 33.5 | **fails** |
| 11–16 | BAND … LEI | 32.5–42.0 | 2.0–25.2 | ok |
| 17–19 | GEI … LOADFALSE | 42.0 | 30.9–33.0 | **fails** |
| 20–21 | LFALSESKIP, LOADK | 45.8 | 29.6–30.4 | ok |
| 22–25 | BNOT … TESTSET | 45.8–47.2 | 33.6–63.9 | **fails** |

The cost is per kind, not per arm:
- a new kind or layout costs 30–90 lines;
- a repeated layout costs 1–2 lines (BAND/BOR/BXOR 2 each, SUBK 1);
- there are 46 arm classes (the round-2 falsifiers), so new kinds keep
  coming.

Round 2's prediction ("template reuse across arms will be low; if per-arm
hand cost does not fall by the 8th, round 3 runs") holds. **The next task is
abstraction-discovery round 3, not more arms.**

### What blocks the remaining F1 arms

| arms | obstruction (evidence) |
|---|---|
| MUL, MULK | `jal __muldi3` on the integer path (`0x8001f094`); needs the soft-int battery at Lua addresses (A0) |
| MOD, MODK, IDIV, IDIVK | `luaV_mod`/`luaV_idiv` → `__moddi3`/`__divdi3`. The arm also stores `ci->savedpc` and `L->top` (`0x8001dc64`, `0x8001dc6c`: `Protect`), which the complement must let vary. Division by zero → `luaG_runerror`, where the kernel's `imod`/`idiv` are `none`: no step, so that path is vacuous |
| FORPREP | `jal __hidden___udivdi3` (×2) whenever the step is not 1; `luaG_forerror` paths have no step |
| EQ, EQK | `luaV_equalobj` on every path |
| LT, LE | two strings: `lessthanothers` → `l_strcmp` (the kernel's `δ .lt/.le` is defined on two strings) |
| UNM | a numeric string: `luaT_trybinTM` → the string library's `__unm` (`δ .unm` converts it) |
| BANDK, BORK, BXORK | **not provable as stated**. The arm reads `K[C]`'s payload with no tag test (`0x8001d740`), but the kernel skips on a non-integer `K[C]`. `Supported` (or the kernel entry) needs "the `K` operand of a bitwise-`K` opcode is an integer", which `lcode.c` guarantees |
| SHL, SHR, SHLI, SHRI | inline, but a new kind: the shift-amount branches (`0x8001ddd0`, `0x8001dddc`) against `shiftl` |
| LOADNIL | a loop (`do … while (b--)`): `loopFromBody` |
| VARARGPREP | `luaT_adjustvarargs` (callee), which moves `ci->func`; `VmRel` is re-established with a new `func` |
| RETURN, RETURN0, RETURN1 | **not `sim_<OP>`-shaped.** "Halt" is `Vsa.Machine.Halts c s.out 0`: `luaD_poscall` (a call), `luaV_execute` returns (`CIST_FRESH`), then `ccall` → `lua_pcallk` → `main` → `exit(0)` through HTIF. Stated as `vmRel_final_Statement` (`Lua/Vm/Sim/Rel.lean`), the `Final` clause of the `VmSim` fold |
| CALL (print), GETTABUP | not started (a separate task). **CALL needs:** callee contracts `luaD_precall` → `luaB_print` → `luaL_tolstring` (`lua_pushfstring` → string interning `luaS_newlstr`, possibly `luaS_resize`) → `lua_writestring` = `fwrite` → newlib stdout (`__sfvwrite_r`, `_write`) → HTIF, i.e. the A0.2 stdio tables at Lua addresses. `checkstackGCp` can reallocate the stack at ≥ 15 locals (`VmRel` with a new `func`). The complement must evolve (heap, strings, `StdioBoot`/`MemfsBoot`); `savepc` writes `ci->savedpc`; `trap` is reloaded; `Core.out` grows by the printed line. **GETTABUP** is the `_ENV.print` lookup (`luaH_getshortstr`) |

# Round-5 bake-off, axis A: contender A-INC (the current route)

A-INC closes the held-out float arms on the location-list route as lane
float-m0 left it. It uses `at_go`/`at_run`, the soft-float call nodes of
`scripts/gen_lua_at.py` (`FCALLS`) and one hand-off per kernel shape, as
`Kit/AtFlt*.lean` does. It adds no new abstraction. The base is main
`754321c`. The branch is `worktree-agent-af308d3f0fd62a0df`.

## Summary row

| setup | held-out lines (per case) | generated | CPU | peak | largest decl | refactor `sim_FORLOOP_flt` | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 291 Lean + 51 Python (kit 25: `At` 1, `AtCond` 8, `AtFloat` 16; per-shape hand-offs 81: `at_farith2` and helpers 32, `at_lt_flt` and its closers 49; `FltValLt` bridges 151; `Floor` premise 34) | SUB **3**; LT **91** (classes 18, 9 class lemmas 37, assembly 29, `LtCls.both` 7); FORPREP **not reached** | +3,215 / −273 (`At/Sub` 815 new, `At/Lt` 275 → 2,401, 9 segment modules re-kept, 6 `At/*` headers) | new hand modules 54 s (`AtFltLt` 41.2, `AtFltSub` 10.5, `FltValLt` 1.9, `Floor` 1.0); new or regrown generated modules 516 s (`At/Lt` 405, `At/Sub` 111) | 4.50 GB (`At/Lt`); hand modules ≤ 2.49 GB | hand: `sim_SUB_flt` 131.7k, `lt_if_in` 124.5k; generated: `At.LT.at_8001eaf4_8001eb1c_3` 126.3k | 29 → 29 (unchanged) | 16 (+5 debugging copies, +2 OOM kills of a parallel `lake build Lua.Vm.Sim.Kit`) | ≈ 1 h 55 min (≈ 35 min of it sequential rebuilds) |

How these are measured:
- Lines are non-blank and non-comment. `--` lines and `/- … -/` blocks are dropped,
  docstrings included.
- Setup counts the lines added to existing kit files, measured by
  `git diff 754321c`.
- CPU is the user time of `lake env lean <file>` (imports built, 8 GB cap).
- Heartbeats are `IO.getNumHeartbeats` around each declaration, in
  `maxHeartbeats` units (limit 200,000). They come from scratch copies with
  `Elab.async false`. For comparison, `sim_FORLOOP_flt` measures 60.4k this way.

## What is proved

Everything below is built by `lake build Lua Vsa VsaIris` (1,885 jobs, OK). Every
listed theorem has axioms `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` stage 6 lists them. Every stage passes except 3c (gate
`a1-float-arm`: 14 cases, first quarter 2.7, last quarter 13.0, FAIL as
before).

| theorem | file:line | statement |
|---|---|---|
| `At.sim_SUB_flt` | `Lua/Vm/Sim/Kit/AtFltSub.lean:22` | `SoftFloatSpec → SimArmOn .SUB FltBC` (= `FloatArms.SUB`) |
| `At.sim_LT_flt` | `Lua/Vm/Sim/Kit/AtFltLt.lean:194` | `SoftFloatSpec → FloorSpec → SimArmOn .LT FltAB` (= `FloatArms.LT`) |
| `At.fixdfdi_model` | `Lua/Vm/Sim/Kit/FltValLt.lean:212` | off NaN, `__fixdfdi`'s spec `Fixdfdi.S x` is the model's `toInt64` (via `fixdfdi_cls`, `roundToInt_eq`, `ofIntClamp_bv`) |
| `Fn.Floor.sum`, `Fn.Floor.spec` | `Lua/Vm/Fn/Floor.lean:77` | `floor`'s call summary and result model, from the premise |

**New named premise: `FloorSpec`** (`Lua/Vm/Fn/Floor.lean:53`). It states that
libm `floor` at `0x8002bb14` (a 64-byte frame, calling `__adddf3` and
`__gedf2`: 112 bytes of stack) has *some* result function and frame contents
(`Floor.Sum`). That result's model is `Lua.Num.floor` (`Floor.Spec`). `F` and
`Fm` are chosen by `Classical.epsilon`, so the generated call node uses them
as it uses a generated summary's. The protocol allows this premise, since
`floor` is outside the pilot. `gen_lua_fn.py` cannot fold `floor`, because its
callees `__adddf3` and `__gedf2` are not memory-keeping leaves like
`__clzdi2`.

`SoftFloatSpec` and `FloorSpec` stay open. Neither field is joined into
`FloatArms`/`armTable`, as for the pilot.

### SUB (3 lines per case)

- `sim_SUB_flt` is one instance of a new per-shape hand-off, `at_farith2`
  (`Kit/AtFlt.lean`, 20 lines). It runs `op_arith` on `FltBC`: `R[B]` and
  `R[C]` are cased by constructor, `hT` refutes the cases with no float, and in
  each of the 11 remaining cases `flt_facts` gives the tag and model.
- It also uses three small helpers in `Kit/AtFlt.lean`: `flt_facts`,
  `ValRepr.other_tags` and `zext_19`, plus three names in `at_new_ext`'s list.
- The generator needed two changes:
  - two call nodes (`__subdf3`, `__floatdidf`);
  - a liveness fix in `gen_lua_arms.py`: a soft-float call's argument
    registers are live at its `jal` (`FLOAT_ARGS`), because `OP_SUB` sets `a1`
    in a predecessor segment, which `ADDI` never did.
- Heartbeats: the 11 cases sit in one declaration, at 131.7k.

### LT (91 lines per case)

LT has 12 operand classes × 2 polarities, which matches the census's `fp`
of 24. Each class is a `LtCls P tk` predicate with one `ArmBody`, written as
an instance of `at_lt_flt (destructuring)`:
- two floats;
- float × integer: in `l_intfitsf`'s window, or `floor` with the range check
  in range, below or not below 2^63;
- integer × float: in the window, or `eq` (integral or not) × {in, below,
  not below}.

`sim_LT_flt` reads the registers, and the kernel refutes a non-number partner
(the order error has no `Step`). It then splits on `intfitsf`, `beq y (floor
y)`, `le minIntF _` and `lt _ (-minIntF)` (29 lines), and calls the class
lemmas.

What the held-out case forced, all on the INC route:

| forced piece | where | lines |
|---|---|---|
| `floor` call node, `noncomputable section` for premised sites, `auipc` as a literal `.rodata` address, `sgtz`, `sext.w` of a symbolic value, `OP_LT`'s float walk | `gen_lua_at.py` | (in the 51 Python) |
| `atCands` suffixes `_1…_7` → `_1…_15` (11 rows reach the join `0x8001c900`) | `Kit/At.lean` | 1 |
| `WinFrame` excludes `luaV_execute`'s C frame: LT spills `R[B]` to `16(sp)` before a call, and `jmp_at`/`trap_ld` then read through it. The old `WinFrame` was false for such a log | `Kit/AtCond.lean` | 8 |
| `at_ground` (a ground `auipc` address evaluated, one `decide`), hooked into `at_addr` and `at_eq_ext`; `at_fnSp` up to 112 bytes | `Kit/AtFloat.lean` | 16 |
| idioms `sgtz`/`bltz` of `__gedf2`, `bgez`/`srli 63` of `__ledf2`, `beqz` of `__eqdf2`, `sext.w` of 0/1; `l_intfitsf`'s `bgeu`/`bltu` | `Kit/FltValLt.lean` | 42 |
| `.rodata` constants `±2^63`, `1.0` (`rod8`, `rod_min`/`rod_max`/`rod_one`, models by `decide +kernel`) | `Kit/FltValLt.lean` | 30 |
| `fixdfdi_model`: `__fixdfdi` against `Float.Model.toInt64` (truncation and saturation), which `luaV_flttointeger`'s `numberToInteger` needs | `Kit/FltValLt.lean` | 79 |
| the hand-off: `lt_disch` (`fixdfdi_model`'s side condition through the call-site specs), a two-stage `at_hyp` rule (idioms before the generic `slt_toInt`, which otherwise pre-empts `slt_ledf2`), `at_lt_flt` | `Kit/AtFltLt.lean` | 49 |

## What the route could not express

1. **FORPREP (`SimArmOn .FORPREP ForCoerce`): not reached.** No case is
   proved. The obstruction is machine-checked by the generator's own walk:
   with `OP_FORPREP`'s float walk on, `gen_lua_at.py` drops these paths:
   ```
   seg_8001e2a4_8001e2b4  call to 0x8001ab58   (luaV_tonumber_, limit)
   seg_8001e2d8_8001e2ec  call to 0x8001ab58   (luaV_tonumber_, step)
   seg_8001e310_8001e320  call to 0x8001ab58   (luaV_tonumber_, init)
   seg_8001c1a8_8001c1b0  x11 unknown          (forlimit's luaV_tointeger)
   seg_8001ecf4_8001ecfc  x11 unknown
   ```
   It also emits `luaV_tointeger`'s call node only with `ht : tag = 3`
   (`toint_sum`). Three further constructions are needed:
   - **`luaV_tonumber_` writes its result through an out-parameter** (`a1 =
     sp+40/48/32`) and returns 0/1. The call nodes support only a result in
     `a0` and a callee frame below `sp`, so the premise needs a new call-effect
     kind (a store into the caller's frame, as `toint_sum` has) plus the
     premise itself, stated over `ValRepr` (strings included).
   - **`forlimit`'s `luaV_tointeger` on a float or string limit** (int `init`
     and `step`, `ForCoerce`'s first sub-case). The float path is
     `luaV_tointegerns` → `luaV_flttointeger` (`floor`, `__eqdf2`, range
     check). The string path is `l_strton` → `luaO_str2num` → `strtod`. The
     string path lies outside both permitted premises (it never reaches
     `luaV_tonumber_`). The float path needs a callee proof on the
     callee-context route (`--fn`), which no float path has used yet.
   - The float loop's own classes:
     - each of 3 registers float-tagged or converted;
     - step zero (no `Step`), sign × skip/run.
     This is about 8 classes, a FORLOOP-sized hand-off.
2. **Kernel order is not machine order.** `sim_SUB_flt` and the LT class
   lemmas are split *by the kernel's class*, so each path re-runs the shared
   prefix (`at_run` from the head). The 12 LT classes replay the
   tag-dispatch prefix 24 times. That cost is CPU (`At/Lt` 405 s and
   `AtFltLt` 41 s), not lines.
3. **Joins become row variants.** The join `0x8001c900` is reached in 11
   rows, so the generator emits 11 copies of the same two segments, and
   `at_run` disambiguates them by row. The suffix limit `_7` had to be raised.
4. **One per-shape hand-off per (kernel combinator × operand predicate).**
   `at_farith2` (`opArith`/`FltBC`) and `at_lt_flt` (`docondjump`/`FltAB` with
   `LTnum`) are new; LE needs a copy of `at_lt_flt` with `leNum`'s modes.
   `at_lt_flt`, its class predicates and `ltV` are hard-wired to `OP_LT`
   (pc, namespace, `ltNum`). The census predicted this growth (C5-handoff)
   and it happened twice.
5. **Generated-file churn.** A float arm's segment liveness changes the
   kept registers of shared segments. SUB and LT rewrote 9 segment modules,
   which rebuilds `Lua.Vm.Arms` and everything above it (≈ 30 min
   sequentially under the 12 GB cap; a parallel `lake build Lua.Vm.Sim.Kit`
   was OOM-killed twice). The integer proofs of the same arms (`Sim/Arms/Sub`,
   `Kit/AtStr`'s `sim_LT`) were regenerated or re-checked and still build.

## Refactor: `sim_FORLOOP_flt`

29 → 29, kept as is. The INC route has nothing that removes FORLOOP's
three-register read or its 4-way outcome split:
- `flt_facts` (new here) replaces `flt_parts` one for one;
- the class-lemma pattern of LT would move the 4 outcomes into 4 declarations
  but add the class definitions and an assembly, so it costs more lines.

## Forecast for the other 33 `FloatArms` fields (INC route)

These are by shape, from the cost of SUB and LT above:

| shape | fields | forecast per field | what it needs first |
|---|---|---|---|
| GEI-like | LEI, GTI | 8 (as GEI) | GTI's operand swap `__gedf2(x, imm) > 0` is `sgtz_gedf2` (now present) |
| `op_arith`/`FltBC` | ADD | 3 | `at_farith2` as is |
| `op_arithK`/`FltBK` | ADDK, SUBK | 3 each, after a `K` hand-off (≈ 25) | an `at_farith2K` |
| needs `__muldf3`/`__divdf3` level (a) | MUL, MULK, DIV, DIVK, IDIV, IDIVK, POW, POWK | 3–8 each, after level (a) | `gen_lua_fn.py` cannot fold them: their callees (`__muldi3`, `__udivdi3`, …) need framed or leaf call support in the fold, the same gap as `floor`; IDIV adds `floor`; POW adds `pow` (a premise) |
| order | LE | ≈ 90 (a copy of LT's classes and hand-off with `leNum`, `F2Ifloor`/`F2Iceil` swapped) | — |
| f2i chain (`luaV_flttointeger`, `F2Ieq`) | BAND, BOR, BXOR, SHL, SHR, BANDK, BORK, BXORK, SHRI, SHLI, BNOT | first ≈ 120 (a bitwise hand-off over the f2i classes: integral and in range, not integral → MMBIN, out of range → MMBIN; per float operand), then ≈ 40–60 each | `FltValLt`'s idioms, constants and `fixdfdi_model` carry over unchanged |
| MOD, MODK | 2 | ≈ 100 first, ≈ 40 second | `fmod` premise, the sign fix (3 more compares) |
| UNM | 1 | ≈ 10 (inline sign flip) | — |
| callee | EQ, EQK | ≈ 100+ | `luaV_equalobj`'s float path as a callee summary (`F2Ieq`) |
| FORPREP | 1 | not reachable on this route (above) | `luaV_tonumber_` out-parameter node, `luaV_tointeger` float and string paths |

Totals:
- **Lines.** With LE and the f2i family dominant, about 1,200–1,800 hand
  lines across the 33 fields, plus the level-(a) generator work.
- **Heartbeats.** The hand class lemmas stay well under budget (largest
  124.5k). The f2i arms have more classes per operand pair (two operands ×
  4 outcomes), so a SUB-style single declaration would exceed 200k. They must
  be split per class, as LT is.

## Commits

```
b8095eb A-INC: OP_SUB float paths on at-lemmas (Subdf3/Floatdidf call nodes, at_farith2)
d4dcd6a A-INC: OP_LT float paths on at-lemmas (floor premise, rodata constants, C-frame spills)
dcb395f A-INC: OP_LT float paths proved (12 operand classes, fixdfdi bridge, rodata constants)
7d7853b A-INC: index the new float arms, axioms list, PHASES note
```

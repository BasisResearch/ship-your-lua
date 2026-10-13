# Lane F1-F6: DIV, DIVK, and IDIV's and IDIVK's float paths on the join route

The base is main `b773b32`. The route is CLAUDE.md's float-arm row (round 5's
A-JOIN), with lanes F2/F3/F5's shape macros.

The numbers are taken as in lanes F2, F3 and F5:

- **Hand lines** are non-blank, non-comment lines, without `import`, `open`,
  `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports
  built (`LEAN_NUM_THREADS=4`). **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k,
  100k or 150k under which the file builds. The limit is never raised; the
  default is 200k.

## Result

| target | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| `__divdf3` call node | **wired** | `FCALLS[0x8002de30] = Divdf3`, 112-byte frame; `f<k>_eq` by `Divdf3.spec_proved`; the frame by `divdf3_sumG` (`FRAME_G`) | 15 (`Kit/AtFloat.lean`) | every float at-file's irreducible line | 2.7 s | 2.05 GB | — |
| DIV | **proved** (`SimArm`, every path) | `sim_DIV` (`Kit/AtFltDiv.lean`) | 3 | `At/Div` 948, `Segs/XDIV` 1773, `Sites/SXDIV` 1729 | 6.2 s (at-file 142.4 s) | 2.55 GB (at-file 3.51 GB) | ≤ 150k (at-file ≤ 50k) |
| DIVK | **proved** (`SimArm`, every path) | `sim_DIVK` (`Kit/AtFltDivk.lean`) | 3 | `At/Divk` 901, `Segs/XDIVK` 1840, `Sites/SXDIVK` 1797 | 6.5 s (at-file 136.4 s) | 2.54 GB (at-file 3.51 GB) | ≤ 150k (at-file ≤ 50k) |
| IDIV (float paths) | **proved** | `sim_IDIV_flt` (`Kit/AtFltIdiv.lean`) | 3 | `At/IdivF` 1337 | 5.5 s (at-file 246.4 s) | 2.54 GB (at-file 4.62 GB) | ≤ 100k (at-file ≤ 100k) |
| IDIVK (float paths) | **proved** | `sim_IDIVK_flt` (`Kit/AtFltIdivk.lean`) | 3 | `At/IdivkF` 1352 | 5.7 s (at-file 268.1 s) | 2.54 GB (at-file 4.75 GB) | ≤ 100k (at-file ≤ 100k) |

`FloatArms` loses `DIV`, `DIVK`, `IDIV` and `IDIVK`. It keeps 6 fields:
`soft` (empty), `POW`, `POWK`, `MOD`, `MODK` and `FORPREP : FpCoerce_Statement`.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
They are in check.sh stage 6: `sim_DIV`, `sim_DIVK`, `sim_IDIV_flt`,
`sim_IDIVK_flt`, `divdf3_sumG`, `FloorR.sum`, `FloorR.S_bits`.

## Setup

| file | hand lines | what |
|---|---|---|
| `scripts/gen_lua_at.py` | +52/−10 python | `Divdf3` in `FCALLS`/`FPROVED`; `FRAME_G` (a frame over the caller's saved registers); `FCALL_ARM` (an arm's own call node, and its irreducible line); `OP_DIV`, `OP_DIVK`, `OP_IDIV_F`, `OP_IDIVK_F` in `FLOAT_ARMS`; DIVK's and IDIVK's `AtFrame` import |
| `scripts/gen_lua_arms.py` | +8 python | `__divdf3` in `FLOAT_CALLS`; DIV, DIVK, IDIV, IDIVK in `FLOAT_ARMS`; DIV, DIVK in `EXTRA_ARMS` (outside the census F1 list). This regenerates `Segs/G25, G26, G37, G49, G50, G52` (IDIV's and IDIVK's float call nodes keep `s6`, `a0` live); `At.sim_IDIV` and `At.sim_IDIVK` still build. |
| `Kit/AtFloat.lean`, `Kit/AtFnFlt.lean` | +15, +1 | `frame4`, `divdf3_Fm_frame4` (`rfl`), `divdf3_sumG`, `fn_congr6` (a frame's six arguments compared); both import `Lua.Vm.Fn.Divdf3` for the irreducible line |
| `Kit/AtJoinDiv.lean` (new) | 40 | `at_keep_tags`, `at_jarith_both`, `at_jarithA`, `at_jarithAK`; the stored-float rule for `__divdf3` and `floor ∘ __divdf3` |
| `Lua/Vm/Fn/FloorR.lean` (new) | 27 | `floor` with the reference as its result: `F`, `Fm`, `sum` (`Floor.sum_ref`), `spec_proved`, `canon_toModel`, `S_bits` |

## How

1. **`__divdf3`'s frame stores the caller's registers.** `Divdf3.Fm` takes
   the caller's `SFrame` `g`: the routine spills `s0`–`s3` mid-body
   (lane float-sf4). The arm's call node keeps a frame `k<k> X M` that is a
   function of the row, but a register the row leaves dead (`s6`, `s10`)
   is a free pin at the call. `Fm` reads only `g.s0 … g.s3`, so
   `divdf3_Fm_frame4 : Fm m s r g a b = Fm m s r (frame4 g.s0 g.s1 g.s2 g.s3) a b`
   holds by `rfl` (2.7 s for all of `Kit/AtFloat.lean`), and
   `divdf3_sumG` is `Divdf3.sum` with that frame. The generator
   (`FRAME_G`) emits `k<k>` over `frame4` of the row's `s0`–`s3`, and
   `at_fsite_eq` compares the six arguments (`fn_congr6`).
2. **DIV and DIVK are every path.** `rawArith .div` has no integer case, so
   their fields were `SimArm`, not `SimArmOn`. `at_jarithA` takes both
   operands by their views (`num_reg`: float, integer through
   `__floatdidf`, or no number, the fall-through to `MMBIN`). The first
   view's tag facts are renamed (`at_keep_tags`): `at_tags` reads the
   context by name, and the second `num_reg`'s `htn` shadows the first's.
   DIVK reads `K[C]`'s tag through `__floatdidf`'s frame (`ld a4, 0(sp)`),
   which lane F3's `AtFrame` forwarding handles.
3. **IDIV's stored `floor`.** `luai_numidiv` stores `floor(a / b)`. The call
   node `Floor` gives `floor`'s result through `FloorSpec`'s chosen
   function (`Classical.epsilon`), of which only the model is known. A
   stored float's bits are the kernel's `Value.ofFloat` (the sign bit too,
   for a NaN), so the model is not enough. `FloorR` takes the reference
   `SfRef.floor` itself as the result (`Floor.sum_ref`). Its bits are the
   canonical datum of `Lua.Num.floor` (`S_bits`: `floor_model`, and
   `SfRef.floor`'s result is `qnan`, a non-NaN datum, or `normalize`'s,
   which is a model datum's bits). The generator gives IDIV's and IDIVK's
   float paths this node (`FCALL_ARM`); the other arms keep `Floor`.
4. **The arms.** IDIV and IDIVK are `at_jarith`/`at_jarithK` unchanged.
   DIV and DIVK are `at_jarithA`/`at_jarithAK`. All four share one
   stored-float rule (`Divdf3.S`, `F64.div_eq_model`, `FloorR.S_bits`,
   `numidiv`).

## Open

- **POW, POWK, MOD, MODK** need newlib `pow` and `fmod` (lane float-sf5).
- **FORPREP**'s `FpCoerce_Statement` needs `strtod`.

## Builds

- **Module builds.** Every float at-file (regenerated: the irreducible line names
  `Divdf3.F`/`Fm`), the callee-route `AtF/Eqobj{FF,IF,FI}`, the integer `At/Idiv`,
  `At/Idivk` (their segments changed), every `Kit/AtFlt*` arm, `Lua.Vm.Sim.Kit` and
  `Lua.Vm.Sim.Fold` build with exit 0, two modules at a time
  (`LEAN_NUM_THREADS=4`, 14 GB cap). `lake build Lua Vsa VsaIris` completes (2181 jobs), and `scripts/check.sh` passes every stage.
- **Gate.** `python3 abstractions/gate.py` is ok: `a1-float-arm` 38 cases (first 3.0,
  last 3.1); `a1-kit-arm` ok.
- **Obstacle met.** `Lua/Vm/AtF/EqobjFF.lean` failed on the new irreducible line until
  `Kit/AtFnFlt.lean` imported `Lua.Vm.Fn.Divdf3` (as it does `Muldf3`).

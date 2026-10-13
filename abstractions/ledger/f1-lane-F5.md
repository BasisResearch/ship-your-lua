# Lane F1-F5: `FloorSpec` discharged, MUL and MULK on the join route, `EqiFlt_Statement`

The base is main `fcd4cb8`. The route is CLAUDE.md's float-arm row (round 5's A-JOIN), with lanes F2/F3's shape macros.

The numbers are taken as in lanes F2 and F3:

- **Hand lines** are non-blank, non-comment lines, without `import`, `open`, `namespace` and `end`.
- **CPU** is the user time of one `lake env lean <file>` with its imports built. **Peak** is that run's maximum RSS.
- **Largest declaration** is a bracket: the lowest `-DmaxHeartbeats` of 50k, 100k or 150k under which the file builds. The limit is never raised, and the default is 200k.

## Result

| target | status | theorem (file) | hand lines | generated | CPU | peak | largest decl |
|---|---|---|---|---|---|---|---|
| `FloatArms.floor` | **discharged** | the at-lemmas pass `Lua.Vm.Sim.floorSpec_proved`; no arm takes `FloorSpec` | 0 (the arm files lose their `hfl`) | all float at-files regenerated | — | — | — |
| `__muldf3` call node | **wired** | `FCALLS[0x8002e504] = Muldf3`, 80-byte frame; `f<k>_eq` by `Muldf3.spec_proved` | — | every float at-file's irreducible line | — | — | — |
| MUL | **proved** | `sim_MUL_flt` (`Kit/AtFltMul.lean`) | 3 | `At/Mul` 761 | 6.9 s (at-file 88.4 s) | 2.35 GB (at-file 3.17 GB) | ≤ 100k |
| MULK | **proved** | `sim_MULK_flt` (`Kit/AtFltMulk.lean`) | 3 | `At/Mulk` 761 | 6.0 s (at-file 89.3 s) | 2.35 GB (at-file 3.13 GB) | ≤ 100k |
| EQI (`EqiFlt_Statement`) | **proved** | `eqiFlt_proved` (`Kit/FltEqi.lean`) | 148 | — | 4.8 s | 2.48 GB | ≤ 50k |

`FloatArms` now has 12 fields: `soft` (empty), 10 `SimArm`/`SimArmOn` arm fields (DIV, DIVK, POW, POWK, MOD, IDIV, MODK, IDIVK, EQ, EQK) and `FORPREP : FpCoerce_Statement`.

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`. They are in check.sh stage 6: `sim_MUL_flt`, `sim_MULK_flt`, `model_mul_comm`, `eqiFlt_proved`, `f2iEqW_eq`, `eq_cls`, `cls_inj`.

## Setup

| file | hand lines | what |
|---|---|---|
| `scripts/gen_lua_at.py` | +26 python | `PREMISE_PROOF` (a premise-form routine with a proved premise is passed the proof), `Floor` in `FPROVED`, `__muldf3` in `FCALLS`, `OP_MUL`/`OP_MULK` in `FLOAT_ARMS` |
| `scripts/gen_lua_arms.py` | +4 python | `__muldf3` in `FLOAT_CALLS`; MUL and MULK in `FLOAT_ARMS`. This regenerates `Segs/G31–G34, G49, G53`: the call node keeps `s6`/`a0` live. `Kit.sim_MUL` and `Kit.sim_MULK` still build. |
| `Kit/AtJoinMul.lean` (new) | 13 | `model_mul_comm`; the stored-float `at_new_ext` rule for `__muldf3`, whose operands are commuted (`__muldf3(c, b)`) |
| `Kit/AtFloat.lean` | +1 | imports `Lua.Vm.Fn.Muldf3`, for the irreducible attribute line |
| `Kit/AtJoinF2I.lean`, `Kit/AtJoinShift.lean`, `Kit/AtFlt{Bandk,Bork,Bxork,Bnot,F2I}.lean` | −(hfl) | the `(hfl : FloorSpec)` parameters are removed from the macros and the arms |

## How

1. **Floor.**
   - `floorSpec_proved : FloorSpec` already existed (lane float-sf3).
   - The generator now emits `Floor.sum Lua.Vm.Sim.floorSpec_proved …` and `f<k>_eq` with no hypothesis.
   - It keeps the premise-form statement: the model's `Lua.Num.floor`, through `Floor.spec`.
   - The arms lose the parameter, and `armTable` loses `hF.floor`.
2. **MUL and MULK.**
   - The machine's float path is `op_arithf(K)` with the shape of ADD/ADDK. Its float conversion of an integer operand runs through `__floatdidf`, with `R[B]` spilled at `16(sp)`, followed by one `__muldf3` with commuted operands.
   - The arms are F2's `at_jarith`/`at_jarithK` unchanged, plus one stored-float rule.
   - The integer×integer path (`__muldi3`) is not followed on this route. The float predicate refutes it.
3. **EQI.** `EqiFlt_Statement` is a pure model fact. It says that `δ .eq` of a float and an 8-bit immediate (`F2Ieq`, then integer equality) is `Float.Model.beq` with the immediate's conversion.
   - **The `F64` view (`f2iEqW`).** `floor` is `SfRef.floor` (`floor_model`), `==` is `F64.eq` (`eq_eq_model`), `(lua_Integer)` is `__fixdfdi` (`fixdfdi_model`), and the range constants are `toModel_min`/`toModel_max`.
   - **From `==` to `F2Ieq`.**
     - `F64.eq X Y` means one non-NaN class, or two zeros (`eq_cls`).
     - A non-NaN word is its class (`cls_inj`, from `pack_cls`).
     - So `X` is `ofInt sB` or `±0`. Each of the 256 immediates is decided once (`ImmFacts`, five `decide +kernel` facts).
   - **From `F2Ieq` to `==`.**
     - `X == floor X` gives `floor X = X`.
     - By `floor_cls`, an exponent `≥ 0` gives `|X| ≥ 2^52`, whose conversion is no immediate.
     - Otherwise `X = normalize n 0` with `|n| ≤ m < 2^53`. `ofInt_exact` then gives `X = ofInt sB`.

## Open

- **DIV, DIVK, IDIV, IDIVK** need `__divdf3` (level (a) blocked; see `float-sf3.md`).
- **POW, POWK, MOD, MODK** need newlib `pow` and `fmod`, which have no summaries.
- **EQ, EQK** are lane F4's: `luaV_equalobj`'s float paths.
- **FORPREP**'s `FpCoerce_Statement` needs `strtod`.

## Builds

- **Lake parallelism.** `lake build Lua.Vm.Sim.Fold` was killed twice under the 12 GB cap, because lake runs about 32 jobs in parallel and `SfRefFloor{A..D}` was uncached. Lake has no `-j` option. The float arms were therefore built two modules at a time (`scratchpad/f5_batches.sh`).
- **Module builds.** Every float arm, `Lua.Vm.Sim.Kit` and `Lua.Vm.Sim.Fold` build with exit 0.
- **Gate.** `python3 abstractions/gate.py` is ok: `a1-float-arm` 26 cases (first 3.0, last 1.7); `a1-kit-arm` ok.

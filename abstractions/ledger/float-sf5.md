# Lane float-sf5: libm `__ieee754_fmod` on the `SfRef` route; loops in lifted functions

The base is main `28628a7`.

`__ieee754_fmod` (`e_fmod.c`, `0x8002bdb4`, 317 instructions, 6 loops) is
proved at both levels:

- **Level (a).** `Ieee754Fmod.sum` is the routine's summary: 142 segments
  folded into 90 nodes, with 6 cycles. `__muldf3` is a call node.
  `__divdf3` is a call node of the proved `Divdf3.sum_div` (since the
  integration with lane float-sf4; see the end).
- **(b1).** `Ieee754Fmod.F_eq_ref` gives `F = SfRef.fmod` and `T = true` on
  every pair of operands.
- **(b2).** `SfRef.fmod_model` shows `SfRef.fmod = Lua.Num.fmod` on the model.
- **Level-2 equation.** `Ieee754Fmod.spec_proved : F m s r a b = S a b`, with
  `S = SfRef.fmod`, takes `FnSp s 128` and `RodataRead m` (for the `Zero[]`
  table).
- **Summary on the reference.** `Ieee754Fmod.sum_ref` takes no premise.

`Ieee754Fmod` is in `gen_lua_at.py`'s `FPROVED`. `FCALLS`, the call node and
the MOD/MODK arm wiring are left to an arm lane.

## What is proved

| level | theorem | file |
|---|---|---|
| (a) | `Ieee754Fmod.sum (hdiv : DivSpec) … (hT : T … = true)` | `Lua/Vm/Fn/Ieee754Fmod/L2.lean` (generated) |
| (b2) | `SfRef.fmodLoop_spec`, `fmodLoop_rem`, `fmodPack_eq`, `fmodFields_fin`, `fmod_cls` | `Lua/Num/SfRefFmod.lean` |
| (b2) | `SfRef.fmod_model : toModel (fmod x y) = Lua.Num.fmod (toModel x) (toModel y)` | `Lua/Vm/Fn/SfRefFmodModel.lean` |
| (b1) | `F_eq_ref`, `spec_proved`, `T_true`, `sum_ref` | `Lua/Vm/Fn/FmodSpec.lean` |

Axioms, from `#print axioms`: `sum`, `F_eq_ref`, `spec_proved`, `sum_ref` and
`fmod_model` each depend on `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` stage 6 lists them. There are no `sorry`, `axiom`,
`native_decide` or `bv_decide`, and no raised limits.

### The (b1) proof

The proof goes bottom-up. Each stage lemma states `N_<pc> … = outv sx iy R ∧ T_<pc> … = true`.

- **Pack and conversion back.** The pack is `pack_c118`, built from
  `fm_psub_chambers` and `fm_psub_cover`, plus `pack_c020`. Normalisation is
  the cycle `norm_c008`. The zero test and conversion are `fin_bff0` and
  `fin_bfd8`.
- **The fix-point loop** is `loop_bf60`, by induction on the remaining count
  (`LoopClaim`).
- **Loop entries:** `entry_bf24`, `entry_bf28`, `entry_bfd0`, `entry_bea4`.
- **`ilogb` cycles:** `ilog_be34`, `ilog_bee0`, `ilog_be5c`, `ilog_c088`, all
  from one induction macro, `fm_ilog`.
- **Set-ups:** per-exponent chambers from the generators
  `fm_yc0b4_chambers`, `fm_ybe94_chambers`, `fm_xbe78_chambers`,
  `fm_dc0e8_chambers` and `fm_dc0d8_chambers`. One tactic, `fm_cover`, joins
  each chamber list by a balanced split. Rule R18 rejects a hand-written
  chamber in `Fmod*.lean`.
- **Operand tests:** `pre_nan` (`(x*y)/(x*y)` is `qnan` by `nan_beb0` and
  `divmul_nan`), `pre_lt`, `pre_eq` and `pre_be1c`.
- **Classes:** `ilg`, `sig` and `frem` are the operand's `ilogb`, its
  normalised significand and the remainder. The class lemmas are `L_be68`,
  `L_c080`, `L_be58`, `L_c1bc`, `L_be40`, `L_c22c`, `L_bf94` and `L_be1c`.
- **Bridge to the fields:**
  - `lens_eq` and `LensOk` give the word lens.
  - `ilg_fields`, `sig_fields` and `frem_fields` show that `ilg` is `normExp`
    and `sig` is `normSig`.
  - `outv_pack` shows that `outv` is `fmodPack`.
  - `fmodFields_gt` gives the main case of the reference.
  - `lowOk_of` and `fmod_dvd` show the result exponent is in range: the
    remainder is a multiple of `2^(-1022-iy)`.

## Abstractions built

- **Loops in `gen_lua_fn.py` (the lane's new capability).**
  - Tarjan SCCs are computed on the node graph.
  - A cycle's nodes take `fuel : Nat` in a `mutual` block. The entry fuel is
    `fnFuel = 2^64`, and fuel 0 gives junk.
  - Every node has a termination function `T_<pc> : Bool`. The summary takes
    `hT : T … = true`.
  - A cycle lemma is an `induction` over the structure `Cyc_<h>`. Mutual
    theorem recursion timed out, so it is not used.
  - Side conditions the generator cannot discharge (`SIDE`) become `decide`
    conjuncts of `T`. They are read back by `fn_and_l` and `fn_and_r`.
  - Other additions: premise callees (`Callee.premise`: `DivSpec`), `MEMLESS`
    (memory is a parameter only where it is read), and `DISCH` (`fn_disch`).
  - The existing routines regenerate byte-identically.
- **The Int word lens.** `Lua/Vm/Fn/FmodLens.lean` writes every register as
  `BitVec.ofInt 64 (Int expr)`.
  - `fm_nf` normalises, with `fm_disch`: `omega`, or `decide` on ground goals.
  - Guards become `decide` over `Int`.
  - `bmod` is removed by range lemmas.
  - `fm_close` closes the remaining equations.
- **Per-literal-shift chamber generators and `fm_cover`.** Each variable shift
  becomes one chamber per literal, and a balanced cover joins them.
- **The step-equation pattern.** First prove `N_x … = N_y (normal-form args)`
  by unfolding, so the right-hand side's `outv` argument is never normalised.

## Tests

`Lua/Vm/Fn/FmodTest.lean` checks 7,600 operand pairs. The pairs cover every
class pair (normal, subnormal at each depth, ±0, ±∞, NaN), signs, and nearby
or equal magnitudes. Four checks run, and each prints `[]` (no mismatches):

1. `T` is true on every pair.
2. The machine's `Ieee754Fmod.F` equals the model's `Lua.Num.fmod`.
3. The machine equals `SfRef.fmod` bit for bit.
4. `SfRef.fmod` equals the model.

## Numbers

- **Lines** are non-blank and non-comment, with doc blocks excluded.
- **CPU** is the user seconds of one `lake env lean <file>`, with its imports
  built and the default thread count.
- **Peak** is the maximum RSS.

| file | lines | CPU s | peak MB |
|---|---|---|---|
| `Lua/Vm/Sim/Kit/FnLoop.lean` | 18 | 1.2 | 1827 |
| `Lua/Vm/Fn/DivSpec.lean` (removed at integration) | 27 | 1.2 | 1831 |
| `Lua/Vm/Fn/Ieee754Fmod/Defs.lean` (gen) | 1118 | 4.9 | 1954 |
| `Lua/Vm/Fn/Ieee754Fmod/L0.lean` (gen) | 841 | 77.6 | 2395 |
| `Lua/Vm/Fn/Ieee754Fmod/L1.lean` (gen) | 850 | 83.4 | 2323 |
| `Lua/Vm/Fn/Ieee754Fmod/L2.lean` (gen) | 237 | 25.0 | 2075 |
| `Lua/Num/SfRefFmod.lean` (b2) | 398 | 4.2 | 821 |
| `Lua/Vm/Fn/SfRefFmodModel.lean` (b2) | 27 | 1.5 | 2295 |
| `Lua/Vm/Fn/FmodLens.lean` | 473 | 5.0 | 1924 |
| `Lua/Vm/Fn/FmodPack.lean` | 90 | 69.3 | 2390 |
| `Lua/Vm/Fn/FmodNorm.lean` | 64 | 5.4 | 1973 |
| `Lua/Vm/Fn/FmodFin.lean` | 171 | 6.6 | 2016 |
| `Lua/Vm/Fn/FmodLoop.lean` | 360 | 11.1 | 2032 |
| `Lua/Vm/Fn/FmodEntry.lean` | 85 | 3.1 | 1953 |
| `Lua/Vm/Fn/FmodIlogb.lean` | 82 | 8.4 | 2007 |
| `Lua/Vm/Fn/FmodSetY.lean` | 121 | 69.6 | 2338 |
| `Lua/Vm/Fn/FmodSetX.lean` | 106 | 110.8 | 2383 |
| `Lua/Vm/Fn/FmodSetN.lean` | 114 | 5.5 | 1996 |
| `Lua/Vm/Fn/FmodDeep.lean` | 166 | 42.9 | 2203 |
| `Lua/Vm/Fn/FmodPre.lean` | 174 | 33.9 | 2627 |
| `Lua/Vm/Fn/FmodTop.lean` | 423 | 17.2 | 2202 |
| `Lua/Vm/Fn/FmodSpec.lean` | 258 | 3.8 | 2431 |
| `Lua/Vm/Fn/FmodTest.lean` | 52 | 36.5 | 1908 |

Totals:

- **Hand-written (b1):** 2,687 lines, 393 CPU s.
- **(b2):** 425 lines.
- **Generated level (a):** 3,046 lines, 191 CPU s.
- **Peak:** 2.6 GB for any one file.
- **Generators:** the `gen_lua_fn.py` diff is +383/−60.

## Open, with evidence

- **The `fmod` wrapper** (`w_fmod.c`, `0x8002b964`, 38 instructions) is not
  lifted. Its value is `__ieee754_fmod(x, y)`, or `0/0 = qnan` when `y = ±0`
  and `x` is not NaN; the routine already returns `qnan` there. Lifting it
  needs:
  - callee-saved `s0`/`s1`/`s2` held across four calls (float-sf4's mid-body
    saves, on main);
  - call nodes for `__eqdf2`, `__unorddf2`, `__errno` and `__divdf3`;
  - a store `sw 33, 0(a0)` through `__errno()`'s pointer (`ld a0, 1224(gp)`),
    which is a write outside the frame that `gen_lua_fn.py`'s `Fm` does not
    model.
  An arm lane on main should do this, together with the call node in
  `FCALLS`.
- **`pow` was not started.** Forecast:
  - `Lua/Num/Pow.lean` already transcribes `e_pow.c` over `Float.Model`, so
    (b2) is that transcription's equality to an `F64` transcription, one stage
    per soft-float call.
  - Level (a) for `__ieee754_pow` (893 instructions) needs call nodes for
    `__adddf3`, `__subdf3`, `__muldf3`, `__divdf3`, `__floatsidf`, `scalbn`,
    `fabs`, `__math_oflow`/`__math_uflow` and `__ieee754_sqrt`. All but
    `scalbn`/`sqrt` are proved.
  - `__ieee754_sqrt` (209 instructions, 4 loops) uses this lane's loop
    support, with bit-by-bit cycles like `ilog_*`.
  - (b1) follows the C branch structure, about 30 class branches, on
    `FmodLens`.
  - Estimate, from this lane's cost: about 4–5k hand lines and 2–3 lane
    sessions, plus `sqrt` (about 1.5k).

## Integration with lane float-sf4 (`DivSpec` removed)

- **`DivSpec` was unsatisfiable as stated.** `Div.Sum Fm` asked for frame
  contents `Fm m s r a b` that do not depend on the caller's frame `g`. But
  `__divdf3` saves the caller's `s0`-`s3` to its frame mid-body (lane
  float-sf4's `saves`), so the patched memory depends on `g`. `sum` and
  `sum_ref` under it were vacuous.
- **The call node is now `Divdf3.sum_div`** (`Lua/Vm/Fn/DivSum.lean`):
  `Divdf3.sum` with its result rewritten by `Divdf3.spec_proved`, so the
  value is `F64.div` of the arguments. Every value function `N_<pc>` is
  unchanged, and so is every (b1) lemma. The memory is
  `Divdf3.Fm m s r g a b`.
- **Generator change.** A callee's `Fm` format may take `{g}`, and its
  summary's arguments may take `{g}` in place of `sframe?`. The caller's
  memory functions then take `g` (`Fn.mem_g`). A call where the caller's
  callee-saved registers are spilled is refused (`call_g`). The `premise`
  and `noncomp` fields of `Callee` remain, unused.
- **`saves` runs on cyclic graphs.** Lane float-sf4's save-slot dataflow is
  now a fixpoint, so it runs on `__ieee754_fmod`'s cycles. On the acyclic
  routines its result is unchanged.
- **Results.** `Ieee754Fmod.sum_ref` takes no premise. `Lua/Vm/Fn/DivSpec.lean`
  is deleted. `FmodTest` still prints `[]` four times.

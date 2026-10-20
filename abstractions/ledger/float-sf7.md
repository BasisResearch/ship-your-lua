# Lane float-sf7: `__ieee754_pow` at level (b)

Base: main `b5f43e8`.

**`PowR.Ieee754PowSpec_Statement` is proved** (`Ieee754Pow.spec_proved`,
`Lua/Vm/Fn/PowSpec.lean`). On quiet operands, the lifted `Ieee754Pow.F` is the
canonical datum of `e_pow.c`'s transcription `Lua.Num.Pow.ieee754Pow`. This
covers every NaN result too: soft-fp's `0x7ff8000000000000`.

`FloatArms.pow_spec` is discharged. `armTable`'s `POW` and `POWK` pass
`spec_proved` (`Lua/Vm/Sim/Fold.lean`), so `FloatArms` keeps two fields:
`soft` (empty) and `FORPREP`.

## What is proved

| region (`e_pow.c`) | lemma(s) | file |
|---|---|---|
| `scalbn` (`s_scalbn.c`) | `Scalbn.F_model` (`tail_d104`) | `Lua/Vm/Fn/ScalbnSpec.lean` |
| `__math_oflow`/`__math_uflow`, `__ledf2`/`__gedf2` tests, `fabs`, `__floatsidf`, the signalling tests | `oflow_v`, `uflow_v`, `oflow_0`, `uflow_0`, `ledf2_lt0`, `gedf2_gt0`, `gedf2_lt0`, `fabs_l`, `floatsidf_l`, `sig_ge_l`, `sig_lt_l`, `sig_ge_int`, `sig_lt_int`, `negW_l`, `notNaN_div_one`, `W_nan`, `W_ofInt_nan` | `Lua/Vm/Fn/PowLeaves.lean` |
| stage equations | `exp2Tail_stage`, `exp2Tail_split` (`PowStage.lean`); `log2Exp_eq`, `ieee754Pow_stage : ieee754Pow = powTop`, `powAx_neg0` | `Lua/Vm/Fn/{PowStage,PowLeaves}.lean` |
| `:292-318` (`exp2`) | `fin_ccd0`, `poly_cb60`, `n_cf98` (12 chambers + cover), `e_cf88`, `e_caf4`, `e_cd38`, `e_caa4`, `exp2_ca2c` | `Lua/Vm/Fn/PowExp.lean` |
| `:198-266` (`log2`) | `e_ce14`, `e_cfc4`, `e_c708` (`logExp`, one tactic `pw_logexp`), `e_c6d4`, `e_c69c`, `e_ce40` (`logNear`), `e_c458` (`log2Exp`) | `Lua/Vm/Fn/PowLog.lean` |
| `:172-196` | `e_c444` (`powSign`), `e_c418` (`powNY`), `e_c620`, `e_c61c` (`powXZn`, `powXZ`), `e_c618`, `e_c600` (`powAx0`), `e_c3c4`, `e_c4fc` (`powAx`), `e_cd9c` (`powAxN`), `e_c5a4` | `Lua/Vm/Fn/PowSpecial.lean` |
| `:137-170` (`yisint`, special `y`) | `e_c580` (53 chambers + cover), `e_c3b4`, `e_c578`, `e_c3ac`, `e_c37c`, `e_c374` | `Lua/Vm/Fn/PowYi.lean` |
| `:115-130`, the whole | `e_c31c` (`powNaN`), `e_c308`, **`F_model`**, `F_nan_nn`, `F_nan_nx`, `F_nan_ny`, **`spec_proved`** | `Lua/Vm/Fn/PowSpec.lean` |

Axioms, from `#print axioms`:
- `spec_proved`, `F_model`, `exp2_ca2c`, `e_c458`, `e_c580`, `e_c374`,
  `Scalbn.F_model`, `ieee754Pow_stage` and `log2Exp_eq` all depend on
  `[propext, Classical.choice, Quot.sound]`.
- They are listed in `scripts/check.sh` stage 6.

There are no `sorry`, `axiom`, `native_decide` or `bv_decide`, and no raised
limits.

`Lua/Num/Pow.lean` is unchanged. The stages restate its tails, checked by
`rfl` or `pw_ite_cases`.

## The shape: one walk, one lemma per join

The proof is a structural correspondence, `pw_walk using [cuts]`
(`Lua/Vm/Fn/PowLens.lean`). It runs the machine's fork tree beside the
model:

- **Machine lens (`pw_lens`).** Words become `BitVec.ofInt 64 e`, and
  soft-float results become `ofInt (W d)` with `d` a model term.
- **Model lens (`pw_mlens`).** It produces `Int32.ofInt` and `UInt32.ofInt`
  normal forms, with conditions as `Int` propositions.
- **Generalisation (`pwGen`).** A value both sides compute is generalised.
  A commuted `*` or `+` is retried.
- **Splits.** The machine's `if` is split with `byCases`. A branch the
  context refutes is closed by `omega`. The model's frontier `if`s are
  decided by the split facts (`pw_front`).
- **Cuts.** A join is cut by one lemma whose right side is a stage of
  `PowStage.lean`. Its premises are discharged by
  `pw_disch`/`pw_notnan`/`fn_sp_in`.
- **Leaves.** At a leaf, the coarser stage is unfolded on the side that has
  it (`pwLeaf`), shift amounts the context pins are fixed (`pw_shift_fix`),
  and the leaf closes by `rfl` or `pw_close`.

Abstractions:
- **`pw_chambers nm [lo, hi] (k) binders : stmt := by tac`.** A chamber
  generator: one declaration per value of the shift amount `k`, plus their
  cover.
  - It is used twice: `n_cf98` (`exp2`'s `n`, `k ∈ [-1, 10]`) and `e_c580`
    (`yisint`, `k ∈ [0, 52]`).
  - Rule R18 (`R18-hand-pow-chamber`) catches a hand chamber.
- **`pw_ite_cases`.** Proves stage equations: it case-splits every `if` over
  its Boolean atoms and closes by `rfl` or refutation.
- **`scripts/gen_pow_rod.py`** (generated `PowRod.lean`). Gives one
  `decide +kernel` lemma per `.rodata` word the routines read. `pw_rod`
  applies them by name. It is checked in check.sh stage 1.
- **`gen_lua_fn.py` `FORWARD`** for `__ieee754_pow` and `scalbn`: their
  frame reloads are forwarded.

## Measurements

The host was shared, with a load average of about 130 during the lane.
Times are CPU (user) from `/usr/bin/time` for `lake env lean <file>`.
`LEAN_NUM_THREADS=1` was requested, but elaboration tasks still run in
parallel, so user time can exceed wall time.

| module | hand lines | user s | wall s | peak RSS MB |
|---|---|---|---|---|
| `PowAttr` | 29 | 0.8 | 1.3 | 1508 |
| `PowRod` (generated) | 131 | 1.2 | 2.0 | 2082 |
| `PowStage` | 318 | 1.9 | 2.5 | 1524 |
| `PowLens` | 1939 | 18.0 | 11.2 | 2996 |
| `ScalbnSpec` | 45 | 12.8 | 10.0 | 2796 |
| `PowLeaves` | 311 | 13.1 | 10.4 | 2802 |
| `PowFacts` | 42 | 1.5 | 2.6 | 2648 |
| `PowExp` | 134 | 357.8 | 142.0 | 6542 |
| `PowLog` | 110 | 30.6 | 13.7 | 3130 |
| `PowSpecial` | 183 | 26.5 | 11.6 | 3105 |
| `PowYi` | 143 | 756.5 | 110.8 | 7905 |
| `PowSpec` | 141 | 34.3 | 21.3 | 3401 |

- **Hand lines.** 3,395 Lean lines plus 83 of `scripts/gen_pow_rod.py`.
  `PowLens.lean`'s 1,939 are the lenses and the walk (meta code).
- **Generated lines.** 131 in `PowRod.lean`. Regenerating with `FORWARD`
  rewrote 9 files under `Lua/Vm/Fn/{Ieee754Pow,Scalbn}` (+998 −800).
- **Largest declaration.** `F_model` (the whole function over its cuts)
  needs between 25,000 and 50,000 heartbeats: it fails at 25k and passes at
  50k. `exp2_ca2c` passes at 25k. Every declaration fits the default 200,000.
- **Per-case cost.** The 35 hand join lemmas each take a statement of 6–12
  lines and a proof of 4–6 tactic lines:
  `fn_sp_factsW; unfold <stage>; pw_lens_r | pw_model_r; pw_front; pw_walk using [cuts]`.
  The 65 chambers cost no hand lines (`pw_chambers`). The heavy modules
  (`PowExp`, `PowYi`) are heavy because of their chamber counts: 12 and 53
  walks.
- **Gate.** `abstractions/gate.py` passes.

## Obstacles met (and the construction that replaced them)

- **Heartbeats per declaration.** The function has 20,282 paths, and the
  `log2` series is 55 operations. The fixes:
  - cuts at the joins;
  - the per-interval `logExp` lemmas;
  - chambers for every shift by a register;
  - a cheaper `pw_front` (`omega` first, `pw_omega` only when a `bmod` occurs);
  - the NaN cases with the disjunctive facts left out, since every `omega`
    would split them.
- **Mismatched normal forms.** Each was closed by one lens rule:
  - the high half (`insertWords_l`, `mul32_lo`);
  - `setLow` by a mask (`setLow0_l'`, `and_np32'`);
  - `x + -c` (`Int.add_neg_eq_sub`);
  - `| 2^29` (`or_k29'`);
  - `| -2^30` (`or_np30`);
  - `Int32` literals.
- **The sign of `-z` (`e_pow.c:183`).** The machine `xor`s bit 63, while
  the model's `neg` canonicalises NaN. `negW_l` holds off NaN. Its premise
  at the cut is `pw_notnan`: `|x|` or `1/|x|` of `x ∈ {±0, ±∞, ±1}`, by
  `notNaN_div_one` (`decide` on three `F64.div` literals).
- **NaN payloads.** The model has one NaN. A quiet NaN operand of any payload
  is walked by its words, with the model's word canonical (`W_ofInt_nan`), in
  three cases (`F_nan_nn`, `F_nan_nx`, `F_nan_ny`).

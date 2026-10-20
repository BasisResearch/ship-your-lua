# Lane float-sf6: libm `__ieee754_sqrt` and `pow` on the `SfRef` route

The base is main `c4470a0`, with main merged at `40137f8` (lanes F1-F7 and
F1-FMT).

- **`__ieee754_sqrt`** (`e_sqrt.c`, `0x8002d448`, 209 instructions, 4 loops)
  is proved at both levels and is correctly rounded: `F = F64.sqrt =
  Float.Model.sqrt`.
- **`pow`** (`w_pow.c`, `e_pow.c`, `s_scalbn.c`, `math_err.c`) is proved at
  level (a): every routine it reaches has a generated summary.
- **Level (b) for `pow`**:
  - `__unorddf2` is proved.
  - The wrapper's value is proved on the model (`PowR.model`), given one
    named obligation, `PowR.Ieee754PowSpec_Statement`.
  - That obligation is `__ieee754_pow`'s own level (b). It is open, with
    evidence on 16,900 operand pairs.

`Ieee754Sqrt` and `Unorddf2` are added to `gen_lua_at.py`'s `FPROVED`. **`FCALLS`
is not changed.** The POW/POWK call nodes and arms are left to an arm lane
(`FloatArms`' `POW`, `POWK` fields stay open).

## What is proved

| level | theorem | file |
|---|---|---|
| (a) | `Ieee754Sqrt.sum (hT : T … = true)`: 77 segments, 53 nodes, 4 cycles | `Lua/Vm/Fn/Ieee754Sqrt/L1.lean` (generated) |
| (b2) | `SfRef.sqRun_spec`, `sqrt_unique`, `sqrtCore_norm`, `sqWords_spec`, `sqNorm_spec`, **`SfRef.sqrt_eq : SfRef.sqrt = F64.sqrt`** | `Lua/Num/SfRefSqrt.lean` |
| (b1) | `l2_claim` (the second root loop, 32 bits of `q1`), `l1_claim` (the first, 21 bits of `q`), `core_478` (`= SfRef.sqCore`) | `Lua/Vm/Fn/SqrtLoop{,1,2}.lean` |
| (b1) | the subnormal normalisation `st_5cc`, `l5b8`, `sub_5b0`, `sub_5a0`, `sub_590` | `Lua/Vm/Fn/SqrtNorm.lean` |
| (b1) | **`F_eq_ref`** (`F = SfRef.sqrt ∧ T = true`), `T_true`, **`spec_proved : F = F64.sqrt`**, `sum_ref` (no premise), `spec_model : F = Float.Model.sqrt` | `Lua/Vm/Fn/SqrtSpec.lean` |
| (a) | `Fabs.sum`, `Finite.sum`, `WithErrno.sum`, `Xflow.sum`, `MathOflow.sum`, `MathUflow.sum`, `Scalbn.sum` | `Lua/Vm/Fn/{Fabs,Finite,WithErrno,Xflow,MathOflow,MathUflow,Scalbn}.lean` (generated) |
| (a) | `Ieee754Pow.sum`: 320 segments, 247 nodes; tail jumps to `__ieee754_sqrt`, `__math_oflow` and `__math_uflow` | `Lua/Vm/Fn/Ieee754Pow/L6.lean` (generated) |
| (a) | `Pow.sum`, the wrapper, with its `errno` stores (`OUTER`) | `Lua/Vm/Fn/Pow.lean` (generated) |
| (b) | `Unorddf2.spec_proved : F = S` (`1` on a NaN operand) | `Lua/Vm/Fn/PowR.lean` |
| (b) | `PowR.n_wrap` (the wrapper's value over `z = __ieee754_pow(x, y)`), `wrap_model`, **`PowR.model : Ieee754PowSpec_Statement → … → toModel (Pow.F m s r g x y) = Lua.Num.pow (toModel x) (toModel y)`** | `Lua/Vm/Fn/PowR.lean` |
| — | `Adddf3.sum_add`, `Subdf3.sum_sub`, `Muldf3.sum_mul`, `Ledf2.sum_le`, `Gedf2.sum_ge` (summaries whose result is the `F64` operation) | `Lua/Vm/Fn/FSum.lean` |

Axioms, from `#print axioms`: every theorem above depends on `[propext,
Classical.choice, Quot.sound]`, and `scripts/check.sh` stage 6 lists them.
There are no `sorry`, `axiom`, `native_decide` or `bv_decide`, and no raised
limits. `scripts/check.sh` passes all stages, and `gen_lua_fn.py --check`
shows no drift.

### The `sqrt` proof

- **(b2): `SfRef.sqrt`.** This is `e_sqrt.c` over the fields: a normalised
  significand, a bit-by-bit root (`sqBit`, `sqRun`) and the rounding tail.
  - The loop invariant `SqInv` gives `sqRun_spec`: the result is the integer
    square root, with the remainder.
  - `sqrt_unique` and `sqrt4` give the rounding.
  - `sqrtPack_eq` and `sqrtCore_norm` show it is `F64.sqrt`'s
    `roundPack` of the exact root.
- **(b1): the machine.**
  - The two root loops are proved by induction on the remaining bit count
    (`L2Inv`/`L2Claim`, `L1Inv`/`L1Claim`), over `FmodLens`'s Int lens.
  - The facts lemmas (`l2_*`, `l1_*`) keep `omega` out of large contexts.
  - The set-up is `core_478`, the subnormal shifts are `SqrtNorm`, and the
    class tests are `mid_464`.
- **Evidence.** `Lua/Vm/Fn/SqrtTest.lean` checks 4,054 operands: `T` is
  true, `F = F64.sqrt`, and `F64.sqrt` equals the host's `Float.sqrt`. All
  three checks print `[]`.

## Abstractions built (`scripts/gen_lua_fn.py`, additive)

- **`F64`-valued call nodes** (`CALLEES_FOR`, `Lua/Vm/Fn/FSum.lean`). A
  routine's own callee table can name a proved summary whose result is the
  `F64` operation. The routine's lifted value is then memory-free across the
  call.
- **`val_g`.** A value function whose body mentions the caller's frame `g`
  (through a callee's frame contents) takes `g`.
- **`CYC_SPLIT`.** A cycle block too large for one declaration is split into
  one declaration per node, `cs_<pc>`.
- **`forward()` as a fixpoint** over cyclic graphs.
- **Tail nodes** (`TERM = ("ret", "tail")`, `TAILS`, `Lua/Vm/Sim/Kit/FnTail.lean`).
  A `j <callee>` with the frame popped is a node whose value and memory are
  the callee summary's. Its proof is by:
  - `memPatch_tail` (the callee's window inside the routine's);
  - `memPatch_tail_outer` (both have an outer word);
  - `memPatch_tail_outer0` (only the routine has one: `pow`'s `sqrt`);
  - `fn_sp_le` (the callee's room at the routine's `sp`);
  - the `{fsp}` and `{hr}` argument placeholders.
- **Outer stores**, on top of lane F1-F7's `OUTER`:
  - a store in the returning segment (`memPatch_ret_wm4`, `with_errno`);
  - frame reads past the store (`bytesT8_wm4_far`);
  - outer callees (`Callee.outer`). A call edge carries the callee's outer
    patch, and `memPatch_patch_outer_in` folds it into the caller's.
- **Joins of spilled registers.** A register spilled on some paths into a
  join only (`__ieee754_pow`'s `s4`, `s5` at its `log(x)` join) is spilled at
  the join, provided its save slot is stored on every path in.
- **Wide windows** (`fn_sp_factsW`). `omega` hits the recursion limit on
  `tohostAddr + 16 + 288 ≤ s`, which is a definition plus a literal of about
  250 or more (it unfolds `Nat.add` on the literal). The bound is therefore
  stated by its literal (`FnSp.lo_lit`), and the `errno` facts are written
  literal-first (`8 + W + symImpurePtr ≤ s`).
- **Imports.** Each callee module is imported once.

## Tests

- **`Lua/Vm/Fn/SqrtTest.lean`**: 4,054 operands, three checks, each `[]`.
- **`Lua/Vm/Fn/PowTest.lean`**: 130 operands are 70 edges (±0, ±1, ±∞, the
  NaN, subnormals, near-1, integers, overflow and underflow thresholds) and
  60 pseudo-random values. Their 16,900 ordered pairs are checked, with
  signalling NaNs left out. Each check prints `[]`:
  1. The machine's `Ieee754Pow.F` equals `Lua.Num.Pow.ieee754Pow` (`e_pow.c`'s
     transcription), up to the NaN class.
  2. The machine's `Pow.F` equals `Lua.Num.pow` (`w_pow.c`).
  3. The machine's `Scalbn.F` equals `Lua.Num.Pow.scalbn` for
     `n ∈ {-1100, …, 1100}` (12 values).

## Numbers

- **Lines** are non-blank and non-comment, with doc blocks excluded.
- **CPU** is the user seconds of one `lake env lean <file>`, with its imports
  built and the default thread count.
- **Peak** is the maximum RSS.

| file | lines | CPU s | peak MB |
|---|---|---|---|
| `Lua/Num/SfRefSqrt.lean` | 474 | 3.9 | 793 |
| `Lua/Vm/Fn/FSum.lean` | 47 | 0.8 | 1974 |
| `Lua/Vm/Sim/Kit/FnTail.lean` | 61 | 0.9 | 1793 |
| `Lua/Vm/Fn/SqrtLoop.lean` | 522 | 38.3 | 2340 |
| `Lua/Vm/Fn/SqrtLoop2.lean` | 378 | 5.3 | 2239 |
| `Lua/Vm/Fn/SqrtLoop1.lean` | 245 | 9.8 | 2191 |
| `Lua/Vm/Fn/SqrtNorm.lean` | 214 | 9.8 | 2180 |
| `Lua/Vm/Fn/SqrtSpec.lean` | 206 | 8.1 | 2224 |
| `Lua/Vm/Fn/SqrtTest.lean` | 42 | 3.8 | 2053 |
| `Lua/Vm/Fn/PowR.lean` | 133 | 1.6 | 2262 |
| `Lua/Vm/Fn/PowTest.lean` | 49 | 124.3 | 2238 |
| `Lua/Vm/Fn/Ieee754Sqrt/Defs.lean` (gen) | 653 | 2.9 | 2084 |
| `Lua/Vm/Fn/Ieee754Sqrt/L0.lean` (gen) | 1002 | 92.6 | 2572 |
| `Lua/Vm/Fn/Ieee754Sqrt/L1.lean` (gen) | 322 | 17.8 | 2218 |
| `Lua/Vm/Fn/Fabs.lean` (gen) | 20 | 1.3 | 1794 |
| `Lua/Vm/Fn/Finite.lean` (gen) | 20 | 1.4 | 1796 |
| `Lua/Vm/Fn/WithErrno.lean` (gen) | 60 | 4.7 | 1855 |
| `Lua/Vm/Fn/Xflow.lean` (gen) | 126 | 7.2 | 2100 |
| `Lua/Vm/Fn/MathOflow.lean` (gen) | 34 | 1.8 | 2009 |
| `Lua/Vm/Fn/MathUflow.lean` (gen) | 34 | 1.8 | 2011 |
| `Lua/Vm/Fn/Scalbn.lean` (gen) | 651 | 49.4 | 2332 |
| `Lua/Vm/Fn/Ieee754Pow/Defs.lean` (gen) | 1445 | 10.2 | 2329 |
| `Lua/Vm/Fn/Ieee754Pow/L0.lean` (gen) | 997 | 115.7 | 2819 |
| `Lua/Vm/Fn/Ieee754Pow/L1.lean` (gen) | 1166 | 126.2 | 2919 |
| `Lua/Vm/Fn/Ieee754Pow/L2.lean` (gen) | 1281 | 163.5 | 3183 |
| `Lua/Vm/Fn/Ieee754Pow/L3.lean` (gen) | 1285 | 154.9 | 3230 |
| `Lua/Vm/Fn/Ieee754Pow/L4.lean` (gen) | 1135 | 150.8 | 3070 |
| `Lua/Vm/Fn/Ieee754Pow/L5.lean` (gen) | 961 | 168.8 | 3058 |
| `Lua/Vm/Fn/Ieee754Pow/L6.lean` (gen) | 191 | 19.0 | 2378 |
| `Lua/Vm/Fn/Pow.lean` (gen) | 1044 | 56.6 | 2628 |

Totals:

- **`sqrt`, hand-written ((b2) and (b1), with `FSum`):** 2,086 lines, 76 CPU s.
- **`sqrt`, generated level (a):** 1,977 lines, 113 CPU s.
- **`pow`, generated level (a)** (nine routines): 10,450 lines, 1033 CPU s.
- **`pow`, hand-written (`PowR`, `FnTail`):** 194 lines, 3 CPU s.
- **Tests:** 91 lines, 128 CPU s.
- **Peak:** 3.2 GB for any one file.
- **Generators:** the `gen_lua_fn.py` diff from `c4470a0` is +509/−73.

## Open, precisely

- **`PowR.Ieee754PowSpec_Statement`** is `__ieee754_pow`'s level (b):
  `toModel (Ieee754Pow.F m s r g x y) = Lua.Num.Pow.ieee754Pow (toModel x)
  (toModel y)`, under `RodataRead m`, `FnSp s 288`, and quiet (non-signalling)
  operands. It is the one premise of `PowR.model`. The route:
  - **(b2).** Write an `F64` transcription of `e_pow.c` (an `SfRef.pow`, with
    `F64` operations at each soft-float call) and prove it equals
    `Lua.Num.Pow.ieee754Pow` on the model. Each step follows from
    `add/sub/mul/div/sqrt_eq_model`, `eq_eq_model` and the word lemmas of
    `hiW`/`loW`/`setHigh`/`setLow`. The transcription's NaN inputs need care:
    `issignaling` is false on the model.
  - **(b1).** Show `Ieee754Pow.F` equals that transcription. There are 247
    nodes, and the callees' values are already the `F64` operations
    (`CALLEES_FOR`), so the proof is the C's branch structure: about 30
    classes for the special `x`/`y` cases, then `log2Split` and
    `exp2Tail`. It goes on the Int word lens (`FmodLens`), with one
    lemma per branch node:
    - the `hiW`/`loW` word arithmetic of `yisint`;
    - the `ix` thresholds;
    - `n`, `k`, `j` in `log2Split`;
    - `exp2Tail`'s `j`/`i` tests.
    `scalbn` (26 nodes) needs its own (b), against `Lua.Num.Pow.scalbn` (the
    test above agrees). So do `fabs` and `finite` (one node each), and the
    error exits (`xflow`'s value is `F64.mul` of a sign flip).
  - **Estimate**, from this lane's cost for `sqrt` (about 2,100 hand lines
    for 53 nodes): 5–8k hand lines.
- **POW/POWK.** `gen_lua_at.py`'s `FCALLS`, the call nodes and the arms
  (`FloatArms.POW`, `POWK`) are an arm lane's work. They use `Pow.sum`
  (premises: `gp`, the stack above `_impure_ptr`, `_impure_ptr`'s target,
  `RodataRead`, `FnSp s 320`). The value is then `PowR.model`'s, and `errno`
  is a second window, as for `fmod` (`FOUTER`).

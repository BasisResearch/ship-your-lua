# Lane float-s0a: `F64`, the binary64 proof library, bridged to `Float.Model`

Base: main `7c625a0` (FLOAT-DESIGN §1 revised: δ's float spec is core
`Float.Model`; `F64` is the proof library proved equal to it). Lines are
non-blank, non-comment lines. CPU and peak memory are one `lake env lean
<file>` each (`/usr/bin/time -v`).

## Result

| target | status | where |
|---|---|---|
| `F64` over `BitVec 64`: `cls`, `bits`, `packFin`, `round` (closed-form `shr`/`rne`/`finish`), `add`, `sub`, `mul`, `div` (`divCore`), `sqrt` (`sqrtCore`), `ofInt`, `neg`, `compare`/`lt`/`le`/`eq`, `qnan` | defined | `Lua/Num/F64.lean` |
| decode and re-pack are the model's | **proved** | `unpack_eq`, `pack_cls`, `toModel_unpack` |
| `round` is the model's `roundWithAccuracy` (when no bits are shifted in) / `round` | **proved** | `round_eq_model`, `roundExact_eq_model`, `normalize_eq_model` |
| bridges, bit-equal, NaN included | **proved** | `ofInt_eq_model`, `add_eq_model`, `sub_eq_model`, `mul_eq_model`, `div_eq_model`, `sqrt_eq_model`, `compare_eq_model`, `lt_eq_model`, `le_eq_model`, `eq_eq_model` |
| `neg` against the model | **proved off NaN** | `neg_eq_model` (`x.cls ≠ .nan`): Lua's `-x` flips a NaN's sign (ELF: `-(0/0)` = `0xfff8000000000000`), the model's `neg` canonicalises |
| sanity lemmas | **proved** | `add_comm`, `mul_comm`, `neg_neg`, `compare_swap`, `trichotomy` (off NaN), `lt_irrefl`, `ofInt_exact` (`|i| ≤ 2^53`, read back by `truncInt?`) |
| Lua's numeric functions the model lacks, over `Float.Model` | defined | `Lua/Num/Arith.lean`: `floor` (`l_floor`), `fmod`, `numberToInteger` (`lua_numbertointeger`), `F2Imod`, `flttointeger` (`luaV_flttointeger`), `numidiv`, `nummod` |
| `F64` versions of `floor`/`fmod` and their bridges | open | (bonus in the brief; not attempted) |

Axioms of every theorem: `[propext, Classical.choice, Quot.sound]` or a
subset (check.sh stage 6 lists 16 of them).

## Numbers

| file | lines | CPU (user) / peak |
|---|---|---|
| `Lua/Num/F64.lean` | 861 (definitions ~150, bridge ~630, sanity ~110) | 7.7 s / 0.83 GB |
| `Lua/Num/Arith.lean` | 53 | 0.4 s / 0.83 GB |
| `Lua/Num/F64Test.lean` (not imported by `Lua`) | 114 | 10.5 s / 0.83 GB |
| `c/tests/float/` (`gen_vectors.py`, `run_sail.sh`, `nan_probe.lua`) | 59 + 11 + 10 | the Sail run of `vectors.lua`: ~25 min |

The bridge's shape: one decode lemma, one re-pack lemma, one rounding lemma
(`shiftRight_succ`: the model's `Nat.repeat shiftRightOne` equals the closed
form; `first_stage`/`second_stage`), then per operation only the class case
split (`f64_special`, shared) plus a mantissa-width fact for `mul`/`div`/`sqrt`
(`mul_target`, `div_target`, `sqrt_target`). After `add` (≈50 lines with the
rounding lemmas it first needed), `sub` 30, `mul` 15, `div` 60 (`divCore_eq`,
`div_target`), `sqrt` 70 (`sqrtCore_eq`, `sqrt_target`), compare 10.

Obstacle met and its fix: `unfold` of a function whose result the kernel must
then evaluate on a symbolic sign (`truncInt? (roundExact neg (2^53) 0)`)
timed out in the kernel (elaboration was instant); splitting `neg` first so
each case is closed (`decide +kernel`) fixed it.

## Tests

* **Host `Float` oracle** (`F64Test.lean`, `#eval`): 3,844 edge pairs (±0,
  subnormal bounds, `2^52`/`2^53` ties, max finite, ∞, NaNs with payload and
  sign) and 100,000 pseudo-random pairs (same exponent, nearby exponents,
  small exponents, full range): `add`, `sub`, `mul`, `div`, `sqrt`, `neg`,
  `lt`/`le`/`eq`, `ofInt` — 0 mismatches (NaN by class: x86's default NaN is
  negative). `floor` against `Float.floor`, and the three F2I modes against
  `floor`/`ceil` + the C range guard: 0 mismatches. A negative control
  (`add` against host `-`) reports mismatches.
* **Host `lua` oracle** (glibc `fmod`, exact): `Arith.fmod` on 6,844 pairs, 0
  mismatches (NaN by class).
* **The ELF on Sail** (`c/tests/float/vectors.lua`, generated, run by
  `run_sail.sh` on an ELF with that chunk; same libgcc/newlib code as the
  proof ELF): 396 float pairs × `+ − × / % //`, `< <= ==`, `x|0` (F2Ieq through
  `luaV_tointegerns`), and 32 `i + 0.0` (`__floatdidf`), output
  `vectors.sail.out`: 428 lines, **0 mismatches bit for bit, NaN sign
  included**. Host `lua` differs from the ELF on 45 of those lines, all NaN
  sign.
* **NaN** (`c/tests/float/nan_probe.lua` on Sail): `0/0`, `1%0.0`, `inf-inf`,
  `0*inf`, and `+ × ÷ %` with a signalling or negative NaN operand all give
  `0x7ff8000000000000` (= `Float.Model.nan`, = `F64.qnan`); `-(0/0)` gives
  `0xfff8000000000000`; printed `nan` and `-nan`.

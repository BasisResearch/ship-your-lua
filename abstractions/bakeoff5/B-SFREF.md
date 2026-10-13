# Round-5 bake-off, axis B (level (b)): contender B-SFREF (soft-fp-shaped reference)

The base is main `eb982c0`. The branch is `worktree-agent-a1420e9fa920cd6f5`;
this file's commit is the head.

## Summary row

| setup | held-out hand lines (per case) | generated | CPU (user s) | peak mem | largest decl heartbeats | refactor | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 1,317 Lean: `SfRef` 153, (b2) `SfRefSpec` 692, lens and exploration `SfLens` 472 | **`__adddf3` 644**, **`__subdf3` 695** | 0 (580 of `__subdf3`'s lines were emitted by a scratch template from `__adddf3`'s chamber list, then hand-edited; counted as hand lines) | `SfRefAdd` 274 (32 wall), `SfRefSub` 286 (34 wall), `SfRefSpec` 11, `SfLens` 8, `SfRef` 0.9 | 3.35 GB (`SfRefSub`) | `g_da50`/`g_ec00` (renormalised round): 100k–150k; every other declaration < 100k | none on axis B | ≈ 75 failed single-file compiles of ≈ 120 (4 of them OOM kills at 6–12 GB caps); 0 failed `lake build` | ≈ 3 h 30 min |

Lines are non-blank, non-comment lines, `/- … -/` blocks and `--` lines
dropped. CPU and memory are one `lake env lean <file>` per module with its
imports built, under `/usr/bin/time` (user time counts Lean's parallel
elaboration; wall is the second figure). Heartbeats: the files were
re-elaborated with `maxHeartbeats` lowered to 100k (only `g_da50` and
`g_ec00` fail) and to 150k (none fails).

## What is proved

**Both held-out `SoftFloatSpec` fields are theorems**, under the field's exact
hypotheses:

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Fn.Adddf3.spec_proved` | `Lua/Vm/Fn/SfRefAdd.lean` | `FnSp s 48 → Adddf3.F m s r a b = F64.add a b` (= `SoftFloatSpec.adddf3`) |
| `Lua.Vm.Fn.Subdf3.spec_proved` | `Lua/Vm/Fn/SfRefSub.lean` | `FnSp s 48 → Subdf3.F m s r a b = F64.sub a b` (= `SoftFloatSpec.subdf3`) |
| `Lua.Num.SfRef.add_eq` | `Lua/Num/SfRefSpec.lean` | (b2) `SfRef.add a b = F64.add a b`, in `Nat` |
| `Lua.Num.SfRef.sub_eq` | `Lua/Num/SfRefSpec.lean` | (b2) `SfRef.sub a b = F64.sub a b` (`sub_eq_add_neg` + `add_eq`: no second proof) |
| `Lua.Vm.Fn.Adddf3.F_eq_sfref` | `Lua/Vm/Fn/SfRefAdd.lean` | (b1) `FnSp s 48 → Adddf3.F m s r a b = SfRef.add a b` |
| `Lua.Vm.Fn.Subdf3.F_eq_sfref` | `Lua/Vm/Fn/SfRefSub.lean` | (b1) `FnSp s 48 → Subdf3.F m s r a b = SfRef.sub a b` |

Axioms of all six: `[propext, Classical.choice, Quot.sound]` (check.sh
stage 6 lists the first four). `lake build Lua Vsa VsaIris` passes.
`scripts/check.sh --static-only` passes stages 1–3b; 3c fails on
`a1-float-arm` (the pre-existing stop signal, axis A's cluster). Stage 6 run
by hand on its own heredoc: 409 theorems, all within the allowed axioms.
No `sorry`, `axiom`, `native_decide`, `bv_decide` or raised limit.
`SoftFloatSpec` itself is untouched (the coordinator decides whether the two
fields leave the structure).

## The route

1. **`SfRef` (`Lua/Num/SfRef.lean`, 153).** soft-fp's `_FP_ADD_INTERNAL`
   (semiraw) over the operands' fields, in `Nat`, with round to odd:
   - `rto n k` (`_FP_FRAC_SRS`), `roundPack` (`_FP_ROUND` + `_FP_PACK_SEMIRAW`
     as the field value `(E-1)·2^52 + rne3 F / 8`, ±∞ on overflow);
   - `carryPack`, `addAligned` (same signs), `subPack`, `normPack` (clz
     renormalisation, subnormal below the least exponent), `subMag`;
   - `addFields`: 16 branches (sign × exponent order × NaN/∞ × subnormal);
   - `SfRef.sub a b := add a (F64.neg b)` (soft-fp's `_FP_SUB`).
   `abstractions/bakeoff5/SfRefEval.lean` checked it against `F64` and the
   lifted `F` on 26,726 pairs before any proof (no disagreement).
2. **(b2) `SfRefSpec` (692).** Three laws of `F64.round` on an exact value:
   - `roundPack_eq`: the machine's round and pack is `F64.round` of the
     working mantissa at scale `max E 1 − 1078` (shift 3, the carry, the
     subnormal-to-normal carry, overflow);
   - `round_scale`: `n·2^j` at `e − j` rounds as `n` at `e`;
   - `round_rto` (W1): round to odd two or more bits below the rounding
     position rounds as the exact value (`shr_rto`, `target_rto`).
   Then `addAligned_eq`, `subMag_eq` (the cancellation through `normPack`;
   `k ≤ 3` exact by `round_scale`, `k ≥ 4` by W1 with `S ≥ 2^54`),
   `addFields_fin` (finite × finite, one zero allowed), the special
   operands (`addFields_nan_l/_r`, `_inf_*`, `_zero_*`), `round_fields`
   (a representable value rounds to itself), and `add_eq` by `F64.cls`.
3. **The `Nat` lens and exploration (`Lua/Vm/Fn/SfLens.lean`, 472).**
   - Every node argument is kept as `BitVec.ofNat 64 n` of a `Nat`
     expression; `sf_nf` pushes the machine's operations onto `n` (side
     conditions by `omega`) and turns guards into `decide`s over `n`.
   - soft-fp idioms as named facts: `nf_srs` (`srl`/`sll 64−k`/`snez`/`or`
     is `rto`), `nf_sticky`, `nf_clr55`/`nf_clr54` (`&= ~IMPLBIT`),
     `nf_or_low` (the jam bit), `nf_clz` (`clz64`), `pack_eq`.
   - `sf_go [cuts]` explores a DAG under the chamber's facts: unfold the head
     node, or split its guard and drop a side `omega` refutes; it stops at
     pack leaves and at cut nodes.
   - `sf_close [packs]` closes a leaf: pack lemma, the reference's branches
     (`sf_ref`, `sf_ref2`), `omega`.
   - `sf_reload`: the frame reloads across `__clzdi2` forwarded through the
     routine's own stores (`frame_addr`: `s − 48 + o`, from `FnSp`).
4. **(b1) per routine (`SfRefAdd` 644, `SfRefSub` 695).**
   - `F_unpack`: the entry's arguments as field naturals (`__subdf3` adds the
     NaN test of `b`, `flag_eq`, and the sign flip, `ea38_step`).
   - Stage lemmas at the machine's round sites (one per site, `sf_go` +
     `sf_close`): the join, `dc60`/`efc8` (equal exponents), `dd48`/`ee98`
     (round, carry after round), `dbcc`/`ed4c` (carry renormalisation),
     `dbb8`/`ed38` (the aligned sum), `db28`/`ecd4` (the difference),
     `d820`/`eaf4` (clz + frame), `da50`/`ec00`, `d854`/`eb28` (the
     renormalised normal and subnormal rounds).
   - 33–34 chambers per routine: a chamber is an `addFields` branch split by
     the classes the machine distinguishes (operand zero, subnormal, `k = 0`,
     `ea = 1`), each `sf_go [cuts]` + the stage lemmas + `sf_close`.
   - `cover`: the chamber case split; its leaves close by `sf_rhs`
     (`addFields` reduced under the chamber's facts).

## The falsifier's facts (ROUND-5 §2b)

| fact | how B-SFREF handles it |
|---|---|
| 1. hidden bit kept out of the value at 7 of 10 points | the stage lemmas take the machine's semiraw `f` and state `roundPack E (2^55 + f)`; no rewriting of the machine value |
| 2. the renormalised site is `rto M (k+1) · 2` | it falls out: `subMag`'s `S = A − rto B k` is round to odd at the pre-shift scale, and `normPack` multiplies by `2^z`; (b2) proves it with W1 at `S ≥ 2^54` and `round_scale` for the shift |
| 3. W1 split by result class | `round_rto` needs two bits below the rounding position at the round-to-odd scale; subnormal results go through `normPack`'s exact branch and `round_scale`; `subMag_eq` takes `k ≤ 3` (exact, `B ≡ 0 mod 8`) by `round_scale` |
| 4. folded sites (`x+5`, `x+4`) | explored like any other leaf, with the chamber fact `57 ≤ k → rto B k = 1`; the arithmetic closes them (no node to rewrite, none needed) |
| 5. per-site exponents | not an input: the chamber's hypotheses fix them, and the stage lemmas take the exponent as an argument |

## What the route could not express, and what it cost

- **Two routines, two chamber lists.** `__subdf3` is separately compiled with
  different node names and parameter orders (pack `(S, F, E)` against
  `(E, F, S)`), so every stage and chamber statement was restated. The
  proofs are the same three tactic lines. A generator emitting the chamber
  list from the `SfRef` branch table and the node map would remove the
  statement lines (≈ 400 of each file).
- **More chambers than forecast.** R5-R2-3 #5 forecast ≈ 10 chambers per
  routine. The machine distinguishes zero and subnormal operands, `k = 0`
  and `ea = 1`, so `addFields`' 16 branches became 33–34 chambers.
- **The declaration budget forces cuts.** One chamber explored to its pack
  leaves exceeds 200k heartbeats. Cutting at the round sites (stage lemmas)
  keeps every declaration under 150k.
- **`omega` limits.**
  - `omega` hits the recursion limit on `(1 − 1) · 2^52` (or `(0 − 1)`) next
    to a large bound. The workaround is `sf_omega`, which evaluates
    literals first, and `sf_close0`. `g_eb50` closes its three leaves by
    hand.
  - Discharging bounds on terms with atoms (`rto B k`, `2^k`) needs explicit
    chamber facts (`rto_le_half`, `rto_pos`, `rto_big`, `norm_bounds`): 3–5
    lines in 12 of the chambers.
- **Simp hygiene.** Lemmas named inside a `macro` must be fully qualified.
  `rfl` attempts on `BitVec.ofNat` with big literals recurse (`with_reducible
  rfl`, `ofNat_congr`). `BitVec` literal simprocs loop with
  `BitVec.ofNat_eq_ofNat` in one pass, so they sit in separate passes.
- **No `bv_decide`, no bit-blasting.** Every `BitVec` fact goes through the
  `ofNat` normal form plus `omega`. Masks with holes (`~IMPLBIT`) needed a
  `testBit` lemma (`land_clear`).

## Forecast

**`__muldf3`, `__divdf3`.**
- (a) Neither has level (a) yet. `gen_lua_fn.py` must lift them first, with
  call nodes for `__muldi3`/`__udivdi3`/`__umoddi3` (limb arithmetic).
- (b2) reuses `roundPack_eq`, `round_scale` and `round_rto` unchanged.
  - New: `SfRef.mul`/`div` in soft-fp's shape (one finite branch each).
  - The product collapse is `rto p 53`-like, and the quotient's sticky is a
    remainder (`jam` over a divisor, R5-R2-3 #4).
  - Estimate: ≈ 150 lines per routine (one `addFields_fin`-like lemma and
    the special operands), about a quarter of `SfRefSpec`.
- (b1): ≈ 20 chambers each (no exponent alignment, so fewer than add/sub,
  but zero/subnormal/∞ pairs), plus 6–8 stage lemmas.
  - New lens facts are needed for the 128-bit product limbs and the
    divide's remainder test (`umul_ppmm`, the `q |= r ≠ 0` idiom).
  - Estimate: ≈ 500–600 lines each, and ≈ 300 s CPU per module, at today's
    hand-written statement cost. A chamber generator would make it ≈ 150.

**The other `FloatArms` fields (axis A)** are untouched by this route. It
discharges two `SoftFloatSpec` fields; the arms consume the fields as
before.

## Files

- `Lua/Num/SfRef.lean`, `Lua/Num/SfRefSpec.lean`: the reference, (b2).
- `Lua/Vm/Fn/SfLens.lean`: the lens and exploration tactics.
- `Lua/Vm/Fn/SfRefAdd.lean`, `Lua/Vm/Fn/SfRefSub.lean`: (b1) and the two
  `spec_proved` theorems.
- `abstractions/bakeoff5/SfRefEval.lean`: the evaluation check (not
  imported by `Lua`).
- `Lua.lean` imports the new modules; `scripts/check.sh` stage 6 lists the
  new theorems.

# Round-5 bake-off, axis B: contender B-RTO (round to odd, value-guarded)

Base `5d5c5cb` (main); branch `worktree-agent-a13bc98e01eecc2fc`. Held out: the
`SoftFloatSpec` fields for `__adddf3` and `__subdf3`. **Both are proved as
theorems**, for every pair of operands (all classes, NaN payloads included),
on any memory, under the fields' exact hypotheses (`FnSp s 48`), with no
premise and no `sorry`. There is no refactor on axis B.

## Summary row

| setup | held-out hand lines (per case) | generated | CPU | peak | largest decl | refactor before → after | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| 1,025: `Lua/Num/Rto.lean` 581 (round-to-odd algebra, W1, `round_scale`, `roundPack_exact`, the aligned add/subtract stage rules, `F64.add` by fields and classes, `sub_eq_add_neg`) + `Lua/Vm/Fn/SfView.lean` 444 (the word view `sf_norm`, `srs_rto`, `clz64_log2`, `reload_forward`, masks, operand unpacking) | `__adddf3` **972** (35 declarations); `__subdf3` **988** (33 declarations); mean 980 | 0 (no generator change) | setup 10.4 s + 6.3 s; `Adddf3Spec` 48.7 s, `Subdf3Spec` 44.9 s (user) | 2.38 GB | 73.0k (`Adddf3.t_d96c`); `Subdf3.t_ed8c` 70.5k; library `roundPack_exact` 52.5k | n/a (axis B) | ≈ 80 failing single-file compiles, plus ≈ 85 scripted bisection runs (the `omega` recursion, below); 0 failing `lake build` | 2 h 22 min to both theorems (23:24–01:46), 2 h 36 min with measurement and report (to 02:00) |

Lines are non-blank, non-comment lines: `--` lines and `/- … -/` blocks
(docstrings included) are dropped. CPU and peak memory are `/usr/bin/time -v`
of `lake env lean <file>` with its imports built, under a 12 GB cap.
Heartbeats are in `maxHeartbeats` units, per declaration, measured with
`Elab.async false` around each command; nothing comes near the 200k default
and no limit is raised.

## What is proved

`#print axioms` of every theorem below is `[propext, Classical.choice,
Quot.sound]`; the first four are in `scripts/check.sh` stage 6.

| theorem | file | statement |
|---|---|---|
| `Lua.Vm.Fn.Adddf3.F_spec` | `Lua/Vm/Fn/Adddf3Spec.lean` | `FnSp s 48 → Adddf3.F m s r a b = F64.add a b` (the `SoftFloatSpec.adddf3` field) |
| `Lua.Vm.Fn.Subdf3.F_spec` | `Lua/Vm/Fn/Subdf3Spec.lean` | `FnSp s 48 → Subdf3.F m s r a b = F64.sub a b` (the `SoftFloatSpec.subdf3` field) |
| `Lua.Num.F64.round_rto` (W1) | `Lua/Num/Rto.lean` | `2^54 ≤ rto n k → roundExact neg (rto n k) (e + k) = roundExact neg n e` |
| `Lua.Num.F64.roundPack_exact` | `Lua/Num/Rto.lean` | soft-fp's semi-raw round and pack (`+4` unless exact or an even tie, carry, overflow to ∞) is `F64.round` |
| `Lua.Num.F64.round_scale`, `shr_rto`, `rto_add_even`, `rto_sub_even`, `log2_rto` | `Lua/Num/Rto.lean` | the round-to-odd rules (`shr_rto` needs `s ≥ 2`, the add/sub anchors need parity) |
| `Lua.Num.F64.add_aligned`, `add_folded`, `sub_core`, `sub_folded`, `sub_hex` | `Lua/Num/Rto.lean` | the aligned sum/difference stages, the folded `d ≥ 57` sites, the renormalisation's exactness |
| `Lua.Num.F64.sub_eq_add_neg` | `Lua/Num/Rto.lean` | `sub x y = add x (neg y)` for every class (L5-comm on the spec) |
| `Lua.Vm.Fn.SfView.srs_rto` | `Lua/Vm/Fn/SfView.lean` | the machine's `_FP_FRAC_SRS` idiom is `rto x k`, `1 ≤ k ≤ 63` |
| `Lua.Vm.Fn.SfView.clz64_log2` | `Lua/Vm/Fn/SfView.lean` | `__clzdi2`'s answer is `63 − log2 x` on `x ≠ 0` |
| `reload_forward` (a `simp` set) | `Lua/Vm/Fn/SfView.lean` | the three reloads of the routine's own spills across `__clzdi2` read the spilled values |

`SoftFloatSpec` (`Lua/Vm/Fn/Spec.lean`) is unchanged: its two fields are now
theorems, and dropping them (and proving `Adddf3.spec`/`Subdf3.spec` from
`F_spec`) is a merge-time edit that touches the structure every float arm
takes. PHASES.md's float-M0 row records it.

## The route

1. **Round to odd as a function** (`F64.rto n k = n / 2^k`, bit 0 jammed). The
   machine's sticky shift is `srs_rto`, rewritten on the raw generated term
   before normalisation, at every SRS site (5 per routine).
2. **W1, value-guarded** (`round_rto`): a collapsed value `≥ 2^54` rounds as
   the exact value. No margin or `log2` bookkeeping reaches a use site: the
   guard is a literal bound on the machine-scale value, which `omega` gets
   from the stage's own bounds.
3. **The stage cut at the per-pc joins.** One lemma per join node, stated as
   `N_<pc> … (W x) … = F64.roundExact sg N E` (or a pack): the round sites
   (`dd48`, `dbc0`, `dc60` inline, `db30`, `da50`, `d854`), the carry test
   (`dbb8`), the aligned add and subtract (`d920`, `dc44`, `d800`, `da00`),
   the renormalisation test (`db28`) and `__clzdi2` (`d820`), and the pack
   joins (`d92c`, `d934`, `dacc`, `d89c`). The chambers above them only
   compose these and match `F64.add`'s class cases.
4. **`roundPack_exact`** closes every round site against `F64.round`.
5. **The word view** `sf_norm`: every argument as `W n` of a `Nat`
   expression, every guard as a decided `Nat` proposition, side conditions by
   `omega`.

How the falsifier's five facts were handled:

| fact (ROUND-5 §2b) | where |
|---|---|
| the hidden bit (`v + 2^55 = rto M k`) | the site lemmas take the semi-raw fraction and state the value with `+ 2^55`; `roundPack_exact` is stated on it |
| the renormalised site is `rto` one bit coarser, then doubled | no new rule: `t_d820` turns the clz shift into `round_scale`, and the caller applies W1 at the coarser scale (`sub_core`: `k = 1` exact by parity, `k ≥ 2` under W1 from the machine-scale bound `A + 2^55 − rto B k ≥ 2^54`) |
| W1 split by result class | `t_d820`'s two branches: normal → `t_da50` + `round_scale`; subnormal → `t_d854`, exact, its exactness side condition discharged once by `sub_hex` |
| folded sites (`x+5`, `x+4` after `A−1`) | arithmetic, not a rewrite: `add_folded`/`sub_folded` (`rto_small`: the smaller operand collapses to the jam bit, then W1 and `roundPack_exact`); the `A = 0` subtract case renormalises `2^55 − 1` |
| per-site exponents | the exponent is an argument of each site lemma; no table |

`__subdf3` adds no new rule: its prologue flips `b`'s sign unless `b` is a
NaN (`F_eq`, `t_ea38`), the spec is rewritten by `sub_eq_add_neg` and
`neg_fields`, and its 33 declarations are the add ones at its own nodes.

## Per-case cost, by role

| | sites and joins | chambers (classes, spec matching) | entry and top |
|---|---|---|---|
| `__adddf3` | 311 | 611 | 50 |
| `__subdf3` | 293 | 653 | 60 |

The round-to-odd rules close the hard part, the inexact sites, in about a
third of each routine. Two thirds are the chambers: zero, subnormal, infinite
and NaN operands against `F64.add`'s nine class cases, and the scale-3
bridges between the machine's semi-raw mantissas and the spec's.

## What the route could not express

- **The stage cut is per routine, by hand.** The pre-round value is not a
  node of the lifted DAG, so each routine's join lemmas are written at its
  own `N_<pc>` names and parameter orders. `__subdf3`'s 33 declarations are
  `__adddf3`'s proofs with the nodes renamed: the second held-out case cost
  as much as the first (988 against 972 lines). CLAUDE.md law 3 names this
  duplication. The missing abstraction is a generated stage cut: emit, per
  routine, the role of each join node (pack join, round site, carry test,
  aligned add/subtract, renormalisation) with its parameter map from
  `gen_lua_fn.py`, so that the site lemmas are instances of one statement
  per role. The proofs are already uniform (`sf_norm`, the child lemmas,
  one stage rule), so most of the 300 site lines per routine would become
  generated.
- **No shared statement for "the pack join returns `x` or the canonical
  NaN".** It is restated against each class case in each chamber (the
  `add_inf_l`/`add_nan_l`/`add_fin_zero` blocks). That is most of the
  chamber lines.
- **`omega` inside the normaliser is fragile on 64-bit literals.** Measured
  obstructions, all reproduced in isolation:
  - `example (A B : Nat) (hB : B < 2 ^ 56) : B < (A + 2 ^ 55) * 2 := by omega`
    fails with "maximum recursion depth" (`B < 2 * A + 2 ^ 56` and the
    `Nat.lt_of_lt_of_le` form succeed);
  - `omega` as a `simp` discharger deep in a nested `if` exceeded the
    recursion limit on `0 * 2 ^ 63 < 2` (found by bisecting the simp set over
    ≈ 85 runs); fixed by keeping lemmas whose side condition can only fail
    out of the global set (`w_or_low` is local);
  - a signed comparison stated with `↔` in a hypothesis made `omega` lose
    facts; the normal form is now `↔`-free (`w_sge_r`, `w_slt_r`, …);
  - adding `decide_eq_true`/`decide_eq_false` (`omega`-discharged) to the
    global normaliser made `Adddf3Spec` grow to 16 GB in 6 minutes (killed);
    they are local to `__subdf3`'s entry now;
  - `unfold F64.sub; cases c <;> rfl` on a `BitVec.ofNat` literal goal ran
    into the 12 GB cap (terminated); replaced by `sub_nan_r`;
  - `congr 1` on `BitVec.ofNat`-literal equalities hits the kernel's deep
    recursion; every pack is closed by `bits_congr` and `omega` per field.
- **`rw [if_pos]` picks the first `ite`.** In goals with the machine's `if`
  on the left and the spec's on the right the rewrites must be ordered by
  hand (one failure cost several runs before it was diagnosed).

## Forecast

**`__muldf3`, `__divdf3`.** Neither has level (a) yet (ROUND-5 §1.5), so the
first cost is `gen_lua_fn.py` on them. For level (b):
- reused unchanged: `roundPack_exact`, W1 (`round_rto`), `round_scale`, the
  pack joins' statements, `sf_norm`, `clz64_log2`, the class lemmas (a
  `mul_fin` analogue of `add_same` is a few lines: `F64.mul` is
  `roundExact (a ^^ b) (m₁ m₂) (e₁ + e₂)`);
- new for `__muldf3`: the double-word product (`__muldi3` or inline
  `mul`/`mulhu`) as one `Nat` product, and its collapse to 56 bits by a
  constant SRS with the low word as sticky (`rto` at a literal scale: W1
  applies directly). About 3 round sites and 2 clz sites; 60–70 % of add's
  site work and far fewer chambers (no alignment, no cancellation): about
  500–650 lines;
- new for `__divdf3`: the sticky is `rem ≠ 0` against a divisor, not against
  `2^k`. It needs `rtoQ N D = N / D ||| [N % D ≠ 0]` and its W1 (`shr` of
  `rtoQ` ≡ `shr` of the exact quotient at margin ≥ 2), about 80 lines, plus
  the `__udivdi3`/`__umoddi3` spec at its call sites: about 650–850 lines.
- With a generated stage cut (above), each would drop by about 40 %.

**The other six `SoftFloatSpec` fields** (not in the pilot): `__floatdidf`
has one SRS, one round site and one clz: the same rules, about 250 lines.
`__floatsidf` is exact (no round site). `__fixdfdi`, `__eqdf2`, `__ledf2`,
`__gedf2` have no rounding; they need only `sf_norm` and the class lemmas.

## Files

- `Lua/Num/Rto.lean` (new): the round-to-odd library and the `F64` facts by
  fields.
- `Lua/Vm/Fn/SfView.lean` (new): the word view, `srs_rto`, `clz64_log2`,
  `reload_forward`, the macros `sf_norm`, `omg`, `bits_eq`.
- `Lua/Vm/Fn/Adddf3Spec.lean`, `Lua/Vm/Fn/Subdf3Spec.lean` (new): the stage
  cut and the chambers; `F_spec`.
- `Lua.lean` imports the three; `scripts/check.sh` stage 6 lists the
  theorems; PHASES.md's float-M0 row.

## Gate

- `scripts/check.sh --static-only`: stages 1, 2, 3 and 3b pass; 3c fails only
  on `a1-float-arm` (the round's trigger, unchanged).
- `lake build Lua Vsa VsaIris` (once, at the end): OK, 1,884 jobs, 3 min 15 s
  wall, 3,035 s CPU (mostly modules stale in the copied build cache), 3.7 GB
  peak RSS. Under a 12 GB scope it was stopped twice by the scope's memory
  accounting (mapped `.olean` pages count against the cgroup), so the final
  run used the common rules' 30 GB cap.
- Stage 6 run by hand on the built tree (check.sh stops at 3c): 407 of 407
  `#print axioms` reports, all within {propext, Classical.choice,
  Quot.sound}, including the six new names.

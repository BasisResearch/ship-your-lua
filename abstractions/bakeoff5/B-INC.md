# Round-5 bake-off, axis B: contender B-INC (direct proof over the lifted function)

B-INC proves `SoftFloatSpec.adddf3`/`subdf3` straight over the generated
lifted functions `Lua.Vm.Fn.{Adddf3,Subdf3}.F`. It uses case analysis and
`simp`/`omega` over the DAG, with no new algebra: no round-to-odd, no stage
vocabulary and no reference program. It is time-boxed. The base is main
`eb982c0`, on branch `worktree-agent-aea6a68a249d7c477`.

**Result: did not close.**
- Both fields are proved **off the finite chamber**: the 21 class pairs with a
  NaN, an infinity or a zero operand, for each routine.
- The four finite pairs (each operand subnormal or normal) remain one named
  premise per routine, `FinChamber_Statement`.
- Inside it, the route closed `d = 0` with both operands normal and the same
  sign (32 cells), plus one `d = 1` cell. It stopped there, for the reasons in
  "What the route could not express".

## Summary row

| setup | held-out lines (per case) | generated | CPU (user s) | peak | largest decl | refactor before → after | failed builds | wall |
|---|---|---|---|---|---|---|---|---|
| **325** (`IReg` 253, `Chamber` 60, `NodeAttr` 12) | `__adddf3` **123** + 141 finite (partial); `__subdf3` **123** (finite open in both). Per case: 4 lines per special class pair; ≈5 lines per finite cell family plus ≈30 lines per finite chamber shape | 0 | 39.3 (add) / 35.1 (sub) / 49.1 (add finite) / 5.6 (setup) | 2.21 / 2.23 / 2.50 GB | **100k–125k** (`add_d0_true_nov`, 8 cells); special chambers ≤ 50k; the one `d = 1` cell 75k–100k | n/a (axis B) | 3 runs OOM-killed at the 12 GB cap (1 `lake build`, 2 `lake env lean`, all the same `d = 0` closer, see below), ≈ 40 `lake env lean` error iterations | ≈ 95 min, plus 15 min measuring |

How the numbers were measured:
- **Lines** are non-blank, non-comment lines (`/- … -/` blocks and `--` lines
  dropped), counted by `scratchpad/binc/loc.py`.
- **The two `<R>Spec.lean` files** were written once by a 40-line scratch
  script (`gen_spec.py`, not committed), one chamber per class pair. They are
  counted as hand lines.
- **CPU and peak** come from one `lake env lean <module>` each, under
  `/usr/bin/time` and a 12 GB scope.
- **Heartbeats** are bracketed by recompiling a scratch copy under a lowered
  global `maxHeartbeats` (25k/50k/75k/100k/125k/150k). No limit is raised in
  the repository.

## What is proved

The full `lake build Lua Vsa VsaIris` passes. `scripts/check.sh --static-only`
passes every stage but 3c, which fails as expected (`a1-float-arm`). Stage 6's
axioms file was run by hand with the four new lines: every new theorem depends
on `[propext, Classical.choice, Quot.sound]`.

| theorem | file | statement |
|---|---|---|
| `Adddf3.spec_of_fin` | `Lua/Vm/Fn/Adddf3Spec.lean` | `FinChamber_Statement → ∀ m s r a b, FnSp s 48 → F m s r a b = F64.add a b`: the `SoftFloatSpec.adddf3` field from the finite chamber |
| `Subdf3.spec_of_fin` | `Lua/Vm/Fn/Subdf3Spec.lean` | the same for `F64.sub` |
| `Adddf3.add_<ca>_<cb>`, `Subdf3.sub_<ca>_<cb>` (21 + 21) | same | `F = F64.add`/`F64.sub` for the class pairs with a NaN, ∞ or zero operand, all four sign cases |
| `Adddf3.add_d0_nn` | `Lua/Vm/Fn/Adddf3Fin.lean` | `bexp a = bexp b`, both normal, same sign: `F = F64.add` (32 cells, overflow to ∞ included) |
| `Adddf3.add_d1_cell` | same | one `d = 1` cell: positive, no carry before rounding, round bit set, odd quotient |
| `spec_d0`, `spec_dpos`, `round_d0`, `round_hi` | same | spec-side shapes: `F64.add` on two normals with exponent offset `d` is `F64.round` of `m₁·2^d + m₂`; `F64.round` at a known `log2` is `finish ∘ rne` of a literal shift |
| `IReg.*` (55 lemmas) | `Lua/Vm/Fn/IReg.lean` | `R z = BitVec.ofInt 64 z`: literals, `+ − ^^^`, shifts, masks (`0x7ff`, `0x7fe`, `0xf`, `7`, `1`, the 52-bit frac, bit 55 clear), disjoint `or` (52/55/63/1), the sticky flag, `sext.w`, `subw`, signed/unsigned guards as `decide` of an `Int` fact; the operand fields `fld_sign/exp/frac`; the classes `cls_*`, `cls5`, `self_R` |

New open premises, recorded in PHASES.md's Float M0 row:
- `Lua.Vm.Fn.Adddf3.FinChamber_Statement`;
- `Lua.Vm.Fn.Subdf3.FinChamber_Statement`.

## The route

1. **`fn_eval`** (`Chamber.lean`):
   - rewrites `F`'s operand fields to `R (sgnI x)`, `R (bexp x)`,
     `R (frac x)`;
   - unfolds every node (`#tag_fn_nodes` tags `N_<pc>`/`F` with the simp set
     `fn_node`; no node is named by hand);
   - turns every literal and operation into `R` of an `Int` expression;
   - decides each guard by `omega` from the chamber's hypotheses
     (`dec_t`/`dec_f`, discharger `omega`), so `↓reduceIte` keeps one branch.
2. **`spec_eval`** evaluates `F64.add`/`F64.sub` through `cls_*`. It closes by
   `R_eq_iff` + `omega`, or by `self_R` when the answer is an operand.
3. **`chamber`** does the four sign cases. One special class pair costs
   0.4–0.6 s CPU and at most 50k heartbeats.
4. **Finite cells** (`Adddf3Fin.lean`):
   - `spec_dpos` + `round_hi` bring the spec to `finish (rne (n / 2^s) rb st) T`
     with `s` a literal;
   - the cell's hypotheses fix the residues and carries the machine branches
     on;
   - `fin_cell`/`fin_close` evaluate both sides and close by `omega` over
     div/mod by literals.

**The falsifier facts (§2b) under this route.** All five are absorbed into
`omega` arithmetic inside a cell, except where noted.
- **The hidden bit** (`v + 2^55 = rto M k`): `or_55` turns the machine's
  `| 1<<55` into `+ 2^55`. A cell never names the pre-round value.
- **Folded sites** (`x+5`/`x+4`): plain arithmetic in a cell. Nothing has to
  locate them.
- **The renormalised site** (`rto M (k+1) · 2`): not reached; the cancellation
  chambers were not attempted. Under this route it is a cell with a literal
  `clz`, so no `rto` statement is needed. The price is the split described
  below.
- **W1 by result class**: shows up as a second spec shape.
  - `round_hi` covers normal results (`T = e + L − 52`).
  - Subnormal results (`T = −1074`) need their own shape. It was not written.
- **Per-site exponents**: the chamber's hypotheses (`E`, literal `d`).

## What the route could not express

1. **Symbolic shift amounts.**
   - `F`'s alignment `x >> d` and its sticky `x << (64−d) ≠ 0`, and the
     renormalisation `x << clz`, are `x / 2^d`, `x · 2^d` and `x · 2^c` with
     `d`, `c` symbolic. `omega` cannot handle these.
   - A cell must fix `d` (0…57) and `c` (0…55) as literals.
   - `d ≥ 58` is one chamber on the machine side (sticky only). On the spec
     side it needs `(m₁·2^d + m₂)/2^d = m₁` with `d` symbolic, which is a
     division lemma, so new algebra.
2. **Residue enumeration is hand work, and the budget forces it.**
   - A cell needs hypotheses that decide the machine's branches: the round
     bit, sticky, quotient parity, carry before rounding, carry after rounding
     and overflow.
   - Letting the closer split instead (`repeat' split` + `fn_norm`) fails:
     - one `d = 1` chamber with only the carry fixed exceeds 200k heartbeats;
     - on the `d = 0` cells the same closer exceeded the 12 GB cap: three runs
       were OOM-killed (`journalctl`: "oom-kill").
   - So each cell family is its own declaration, at 2–8 cells per declaration.
   - The hypotheses are the round-to-odd facts (which bits are the round bit
     and the sticky) restated per `d` by hand. B-INC re-derives per cell what
     B-RTO states once.
3. **Cost per cell grows with `d`.**
   - A `d = 0` cell: ≈ 1 s CPU, ≈ 14k heartbeats.
   - The `d = 1` cell: ≈ 13 s, 75k–100k heartbeats. Its expressions nest one
     more div/mod pair (the SRS by `d` and its sticky), and `omega`'s cost
     grows with the number of div/mod atoms.
4. **Special chambers are cheap and complete.**
   - All 42 close with one 3-line macro.
   - `__subdf3` needed three additions: `R_xor_1` (`xori 1`), `or_odd_flag`
     (the odd sticky `or`) and `BitVec.or_self`/`and_self` in the simp set.
     After those it was a second instance, with no per-routine work beyond
     the 21 statements.

## Forecast

**The rest of `__adddf3`/`__subdf3` by this route.** Counts are per routine.

| | count |
|---|---|
| alignment chambers, same sign: (nn, ns, sn) × 2 operand orders × `d` ∈ 0…57 | ≈ 350 |
| alignment chambers, different sign | ≈ 350 |
| cancellation (`d ≤ 1`) × a literal `clz` count | ≈ 110 |
| subnormal-result chambers | ≈ 60 |
| `d ≥ 58` chambers, each with a spec-side division lemma | ≈ 10 |
| cells per chamber (measured: 32 at `d = 0`; raw 2^6 per sign at `d ≥ 1`, some infeasible) | ≈ 30 |

That gives **≈ 25,000 cells per routine**:
- **CPU:** 7 to 90 CPU-hours at 1–13 s per cell.
- **Declarations:** ≈ 5,000–12,000 under the 200k-heartbeat budget, with the
  residue hypotheses per cell written by a new generator that knows soft-fp's
  round positions.
- **Hand:** ≈ 8 spec-shape lemmas (≈ 30 lines each), the frame forwarding for
  the 14 reloads around `__clzdi2` (`bytesT8_wm8_same/far`, a few lines), and
  that generator.

This does not fit a pilot, and it scales linearly in cells: there is no
abstraction to amortise.

**`__muldf3`, `__divdf3`.** They have no level (a) yet. Once `F` exists:
- **Special chambers:** transfer as is: 21 × 4 lines per routine, ≈ 40 s CPU.
- **Finite chamber:** the direct route fails at the core. The spec has `m₁·m₂`
  (and `m₁ / m₂` with a remainder), a product of two variables. `omega`
  cannot reason about it, and no literal split helps, because the operands
  are 53-bit symbolic values.
  - It needs limb lemmas over `mulhu`/`__muldi3`/`__udivdi3`, which are new
    algebra.
  - So B-INC forecasts **specials only** for `__muldf3`/`__divdf3`.

## Files

| file | contents |
|---|---|
| `Lua/Vm/Fn/IReg.lean` | setup: the `R` register library |
| `Lua/Vm/Fn/NodeAttr.lean` | setup: `fn_node`, `#tag_fn_nodes` |
| `Lua/Vm/Fn/Chamber.lean` | setup: `fn_eval`, `fn_norm`, `spec_eval`, `chamber` |
| `Lua/Vm/Fn/Adddf3Spec.lean` | 21 special chambers, `FinChamber_Statement`, `spec_of_fin` |
| `Lua/Vm/Fn/Subdf3Spec.lean` | 21 special chambers, `FinChamber_Statement`, `spec_of_fin` |
| `Lua/Vm/Fn/Adddf3Fin.lean` | finite cells: `add_d0_nn`, `add_d1_cell`, the spec shapes |

The other changes:
- `Lua.lean` imports the three new proof modules;
- `scripts/check.sh` stage 6 gains 4 lines;
- PHASES.md's Float M0 row notes the two new premises.

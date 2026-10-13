import Lua.Num.F64

/-!
# `SfRef`: a soft-fp-shaped reference for `__adddf3`/`__subdf3` (round 5, B-SFREF)

Level (b) of the soft-float routines (`SoftFloatSpec.adddf3`/`subdf3`) is
split at a reference program written as libgcc soft-fp's
`_FP_ADD_INTERNAL` reads in its semiraw form (`op-common.h`): unpack, `<< 3`
(three work bits), align the smaller operand by a sticky shift
(`_FP_FRAC_SRS`, here `rto`: round to odd), add or subtract, renormalise
(`__FP_CLZ`), then `_FP_ROUND` to nearest even on the three work bits and
`_FP_PACK_SEMIRAW` (`roundPack`).

* (b2) `SfRef.add = F64.add` is proved once, in `Nat`, in this module.
* (b1) the lifted machine function (`Lua.Vm.Fn.Adddf3.F`) equals `SfRef.add`
  by chambers (`Lua/Vm/Fn/SfRefAdd.lean`).
* `SfRef.sub a b = SfRef.add a (b ^^^ 2^63)` by definition (soft-fp's
  `_FP_SUB`), and `F64.sub_eq_add_neg` carries (b2) to `F64.sub`.

The semiraw mantissa of a field pair `(e, f)` is `mant e f`: `8 f` with the
hidden bit `2^55` when `e ≥ 1`; its exponent is `max e 1` (a subnormal has
the exponent of the least normal). A working mantissa `F < 2^56` at biased
exponent `E` denotes `F · 2^(max E 1 - 1078)`.
-/

namespace Lua.Num.SfRef

open F64

/-- Round to odd (von Neumann's jamming, soft-fp's sticky shift
`_FP_FRAC_SRS`): drop `k` bits of `n`, or-ing "a dropped bit was set" into
the last kept bit. -/
def rto (n k : Nat) : Nat := if n % 2 ^ k = 0 then n / 2 ^ k else 2 * (n / 2 ^ (k + 1)) + 1

/-- `_FP_ROUND_NEAREST` on three work bits (`(X & 15) != 4` then `X += 4`,
skipped when `X & 7 = 0`). -/
def rne3 (f : Nat) : Nat := if f % 8 = 0 ∨ f % 16 = 4 then f else f + 4

/-- `_FP_ROUND` then `_FP_PACK_SEMIRAW` of a working mantissa `F < 2^56`
(hidden bit `2^55` included when `E ≥ 1`) at biased exponent `E`: the field
value `(E - 1) · 2^52 + rne3 F / 8` (a carry out of the mantissa or out of a
subnormal moves into the exponent field by itself), ±∞ on overflow. -/
def roundPack (neg : Bool) (E F : Nat) : F64 :=
  let v := (E - 1) * 2 ^ 52 + rne3 F / 8
  if 2047 * 2 ^ 52 ≤ v then infty neg else bits neg 0 v

/-- The semiraw mantissa of fields `(e, f)`, three work bits. -/
def mant (e f : Nat) : Nat := if e = 0 then 8 * f else 2 ^ 55 + 8 * f

/-- Same signs: `A` at `E` plus `B` aligned by a sticky shift of `k`
(`_FP_FRAC_SRS`), then the carry renormalisation (`_FP_FRAC_SRS (R, 1)`). -/
def addAligned (neg : Bool) (E A B k : Nat) : F64 :=
  let S := A + rto B k
  if 2 ^ 56 ≤ S then roundPack neg (E + 1) (rto S 1) else roundPack neg E S

/-- Different signs, `|A| > |B|`: `A − rto B k`, renormalised by the count
of leading zeros (`__FP_CLZ`, `_FP_FRAC_SLL`); below the least normal
exponent the result is subnormal (`R_e <= diff`). -/
def subMag (neg : Bool) (E A B k : Nat) : F64 :=
  let S := A - rto B k
  if 2 ^ 55 ≤ S then roundPack neg E S
  else
    let z := 55 - S.log2
    if z < E then roundPack neg (E - z) (S * 2 ^ z) else roundPack neg 0 (S * 2 ^ (E - 1))

/-- `__adddf3` as soft-fp's `_FP_ADD_INTERNAL` (semiraw) computes it, over the
operands' fields. NaN results are the canonical `qnan` (RISC-V
`_FP_CHOOSENAN`). -/
def addFields (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat) : F64 :=
  let A := mant ea fa
  let B := mant eb fb
  let Ea := max ea 1
  let Eb := max eb 1
  if sa = sb then
    if ea = eb then
      if ea = 2047 then (if fa = 0 ∧ fb = 0 then infty sa else qnan)
      else addAligned sa Ea A B 0
    else if eb < ea then
      if ea = 2047 then (if fa = 0 then infty sa else qnan)
      else addAligned sa Ea A B (Ea - Eb)
    else
      if eb = 2047 then (if fb = 0 then infty sb else qnan)
      else addAligned sb Eb B A (Eb - Ea)
  else
    if ea = eb then
      if ea = 2047 then qnan
      else if A = B then zero false
      else if B < A then subMag sa Ea A B 0
      else subMag sb Eb B A 0
    else if eb < ea then
      if ea = 2047 then (if fa = 0 then infty sa else qnan)
      else subMag sa Ea A B (Ea - Eb)
    else
      if eb = 2047 then (if fb = 0 then infty sb else qnan)
      else subMag sb Eb B A (Eb - Ea)

/-- `SfRef.add`. -/
def add (a b : F64) : F64 := addFields a.sign a.bexp a.frac b.sign b.bexp b.frac

/-- `SfRef.sub`: soft-fp's `_FP_SUB` is `_FP_ADD_INTERNAL` with `Y`'s sign
flipped (a NaN's sign is irrelevant: every NaN result is `qnan`). -/
def sub (a b : F64) : F64 := add a (b ^^^ 0x8000000000000000#64)

/-! ## Rewriting the reference by cases (side conditions by `omega`) -/

theorem rto_zero (n : Nat) : rto n 0 = n := by simp [rto]; omega
theorem rto_exact {n k : Nat} (h : n % 2 ^ k = 0) : rto n k = n / 2 ^ k := by simp [rto, h]
theorem rto_jam {n k : Nat} (h : n % 2 ^ k ≠ 0) : rto n k = 2 * (n / 2 ^ (k + 1)) + 1 := by simp [rto, h]
theorem rto_one_even {n : Nat} (h : n % 2 = 0) : rto n 1 = n / 2 := by simp [rto, h]
theorem rto_one_odd {n : Nat} (h : n % 2 = 1) : rto n 1 = 2 * (n / 4) + 1 := by
  simp [rto]; omega
theorem rne3_keep {f : Nat} (h : f % 8 = 0 ∨ f % 16 = 4) : rne3 f = f := by simp [rne3, h]
theorem rne3_up {f : Nat} (h1 : f % 8 ≠ 0) (h2 : f % 16 ≠ 4) : rne3 f = f + 4 := by simp [rne3, h1, h2]
theorem roundPack_fin {neg : Bool} {E F : Nat} (h : (E - 1) * 2 ^ 52 + rne3 F / 8 < 2047 * 2 ^ 52) :
    roundPack neg E F = bits neg 0 ((E - 1) * 2 ^ 52 + rne3 F / 8) := by
  simp only [roundPack]; rw [ite_eq_right (by omega)]
theorem roundPack_inf {neg : Bool} {E F : Nat} (h : 2047 * 2 ^ 52 ≤ (E - 1) * 2 ^ 52 + rne3 F / 8) :
    roundPack neg E F = infty neg := by
  simp only [roundPack]; rw [ite_eq_left h]
theorem addAligned_carry {neg : Bool} {E A B k : Nat} (h : 2 ^ 56 ≤ A + rto B k) :
    addAligned neg E A B k = roundPack neg (E + 1) (rto (A + rto B k) 1) := by
  simp only [addAligned]; rw [ite_eq_left h]
theorem addAligned_nocarry {neg : Bool} {E A B k : Nat} (h : A + rto B k < 2 ^ 56) :
    addAligned neg E A B k = roundPack neg E (A + rto B k) := by
  simp only [addAligned]; rw [ite_eq_right (by omega)]

theorem roundPack_keep {neg : Bool} {E F : Nat} (h0 : F % 8 = 0 ∨ F % 16 = 4)
    (h : (E - 1) * 2 ^ 52 + F / 8 < 2047 * 2 ^ 52) :
    roundPack neg E F = bits neg 0 ((E - 1) * 2 ^ 52 + F / 8) := by
  rw [roundPack_fin (by rw [rne3_keep h0]; exact h), rne3_keep h0]
theorem roundPack_up {neg : Bool} {E F : Nat} (h1 : F % 8 ≠ 0) (h2 : F % 16 ≠ 4)
    (h : (E - 1) * 2 ^ 52 + (F + 4) / 8 < 2047 * 2 ^ 52) :
    roundPack neg E F = bits neg 0 ((E - 1) * 2 ^ 52 + (F + 4) / 8) := by
  rw [roundPack_fin (by rw [rne3_up h1 h2]; exact h), rne3_up h1 h2]
theorem roundPack_inf_keep {neg : Bool} {E F : Nat} (h0 : F % 8 = 0 ∨ F % 16 = 4)
    (h : 2047 * 2 ^ 52 ≤ (E - 1) * 2 ^ 52 + F / 8) : roundPack neg E F = infty neg := by
  rw [roundPack_inf (by rw [rne3_keep h0]; exact h)]
theorem roundPack_inf_up {neg : Bool} {E F : Nat} (h1 : F % 8 ≠ 0) (h2 : F % 16 ≠ 4)
    (h : 2047 * 2 ^ 52 ≤ (E - 1) * 2 ^ 52 + (F + 4) / 8) : roundPack neg E F = infty neg := by
  rw [roundPack_inf (by rw [rne3_up h1 h2]; exact h)]

theorem roundPack_inf_any {neg : Bool} {E F : Nat} (h : 2047 * 2 ^ 52 ≤ (E - 1) * 2 ^ 52 + F / 8) :
    roundPack neg E F = infty neg := by
  apply roundPack_inf
  have : F ≤ rne3 F := by unfold rne3; split <;> omega
  have := Nat.div_le_div_right (c := 8) this
  omega

end Lua.Num.SfRef

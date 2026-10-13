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

/-- The carry renormalisation of a sum `S < 2^57` (`_FP_FRAC_SRS (R, 1)`
when bit 56 is set), then `roundPack`. -/
def carryPack (neg : Bool) (E S : Nat) : F64 :=
  if 2 ^ 56 ≤ S then roundPack neg (E + 1) (rto S 1) else roundPack neg E S

/-- Same signs: `A` at `E` plus `B` aligned by a sticky shift of `k`
(`_FP_FRAC_SRS`), then the carry renormalisation. -/
def addAligned (neg : Bool) (E A B k : Nat) : F64 := carryPack neg E (A + rto B k)

/-- The renormalisation of a working mantissa `0 < S < 2^55` at `E ≥ 1` by
its count of leading zeros (`__FP_CLZ`, `_FP_FRAC_SLL`); below the least
normal exponent the result is subnormal (`R_e <= diff`). -/
def normPack (neg : Bool) (E S : Nat) : F64 :=
  let z := 55 - S.log2
  if z < E then roundPack neg (E - z) (S * 2 ^ z) else roundPack neg 0 (S * 2 ^ (E - 1))

/-- A difference `0 < S < 2^56` at `E`: round it, or renormalise it when the
hidden bit cancelled. -/
def subPack (neg : Bool) (E S : Nat) : F64 :=
  if 2 ^ 55 ≤ S then roundPack neg E S else normPack neg E S

/-- Different signs, `|A| > |B|`: `A − rto B k`. -/
def subMag (neg : Bool) (E A B k : Nat) : F64 := subPack neg E (A - rto B k)

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
theorem rto_one (n : Nat) : rto n 1 = if n % 2 = 0 then n / 2 else 2 * (n / 4) + 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [rto_one_even h, if_pos h]
  · rw [rto_one_odd h, if_neg (by omega)]
theorem rne3_keep {f : Nat} (h : f % 8 = 0 ∨ f % 16 = 4) : rne3 f = f := by simp [rne3, h]
theorem rne3_up {f : Nat} (h1 : f % 8 ≠ 0) (h2 : f % 16 ≠ 4) : rne3 f = f + 4 := by simp [rne3, h1, h2]
theorem roundPack_fin {neg : Bool} {E F : Nat} (h : (E - 1) * 2 ^ 52 + rne3 F / 8 < 2047 * 2 ^ 52) :
    roundPack neg E F = bits neg 0 ((E - 1) * 2 ^ 52 + rne3 F / 8) := by
  simp only [roundPack]; rw [ite_eq_right (by omega)]
theorem roundPack_inf {neg : Bool} {E F : Nat} (h : 2047 * 2 ^ 52 ≤ (E - 1) * 2 ^ 52 + rne3 F / 8) :
    roundPack neg E F = infty neg := by
  simp only [roundPack]; rw [ite_eq_left h]
theorem np_congr {n : Bool} {E E' S S' : Nat} (h1 : E = E') (h2 : S = S') :
    normPack n E S = normPack n E' S' := by rw [h1, h2]
theorem sp_congr {n : Bool} {E E' S S' : Nat} (h1 : E = E') (h2 : S = S') :
    subPack n E S = subPack n E' S' := by rw [h1, h2]
theorem cp_congr {n : Bool} {E E' S S' : Nat} (h1 : E = E') (h2 : S = S') :
    carryPack n E S = carryPack n E' S' := by rw [h1, h2]

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

theorem rto_big {n k : Nat} (h0 : 0 < n) (h : n < 2 ^ k) : rto n k = 1 := by
  have h1 : n / 2 ^ (k + 1) = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
  unfold rto; rw [Nat.mod_eq_of_lt h, if_neg (by omega), h1]
theorem rto_le (n k : Nat) : rto n k ≤ n / 2 ^ k + 1 := by
  unfold rto; split
  · omega
  · have : 2 * (n / 2 ^ (k + 1)) ≤ n / 2 ^ k := by
      rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega
    omega
theorem rto_lt_of {n k m : Nat} (hk : 1 ≤ k) (h : n < 2 ^ (m + 1)) : rto n k < 2 ^ m + 1 := by
  have h1 := rto_le n k
  have h2 : n / 2 ^ k < 2 ^ m := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
    calc n < 2 ^ (m + 1) := h
      _ = 2 ^ m * 2 := by rw [Nat.pow_succ]
      _ ≤ 2 ^ m * 2 ^ k := Nat.mul_le_mul_left _ (by
          calc 2 = 2 ^ 1 := rfl
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk)
  omega

theorem rto_zero_n (k : Nat) : rto 0 k = 0 := by simp [rto]

theorem rto_le_self (n k : Nat) : rto n k ≤ n := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; rw [rto_zero]; exact Nat.le_refl _
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [rto_zero_n]; exact Nat.le_refl _
    · have h1 := rto_le n k
      have h2 : n / 2 ^ k ≤ n / 2 := Nat.div_le_div_left (by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk) (by decide)
      omega

theorem rto_mul_pow (f z k : Nat) (h : k ≤ z) : rto (f * 2 ^ z) k = f * 2 ^ (z - k) := by
  have e : f * 2 ^ z = f * 2 ^ (z - k) * 2 ^ k := by rw [Nat.mul_assoc, ← Nat.pow_add, Nat.sub_add_cancel h]
  rw [rto_exact (by rw [e]; exact Nat.mul_mod_left _ _), e, Nat.mul_div_cancel _ (Nat.two_pow_pos k)]

/-- The clz-normalised mantissa of `0 < S < 2^56` has its top bit at 55. -/
theorem norm_bounds {S : Nat} (h0 : 0 < S) (h : S < 2 ^ 56) :
    2 ^ 55 ≤ S * 2 ^ (55 - S.log2) ∧ S * 2 ^ (55 - S.log2) < 2 ^ 56 := by
  have hL : S.log2 < 56 := (Nat.log2_lt (by omega)).2 h
  have h1 : 2 ^ S.log2 ≤ S := Nat.log2_self_le (by omega)
  have h2 : S < 2 ^ (S.log2 + 1) := Nat.lt_log2_self
  constructor
  · calc 2 ^ 55 = 2 ^ S.log2 * 2 ^ (55 - S.log2) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ S * 2 ^ (55 - S.log2) := Nat.mul_le_mul_right _ h1
  · calc S * 2 ^ (55 - S.log2) < 2 ^ (S.log2 + 1) * 2 ^ (55 - S.log2) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ 56 := by rw [← Nat.pow_add]; congr 1; omega

end Lua.Num.SfRef

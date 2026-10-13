import Lua.Num.SfRefSpec

/-!
# `SfRef.mul`: soft-fp's `__muldf3` over the fields (lane float-sf3, (b2))

libgcc's `__muldf3` (`soft-fp/muldf3.c`: `FP_UNPACK_D`, `FP_MUL_D`,
`FP_PACK_D`; `soft-fp/op-common.h` `_FP_MUL`, `_FP_UNPACK_CANONICAL`,
`_FP_PACK_CANONICAL`; `soft-fp/op-1.h` `_FP_MUL_MEAT_1_wide` with
`umul_ppmm`), transcribed over the operands' fields:

* `unpackF`/`unpackE`: `_FP_UNPACK_CANONICAL` of a nonzero finite operand,
  the working mantissa `X_f ∈ [2^55, 2^56)` (three work bits; a subnormal
  normalised by its count of leading zeros) and the unbiased exponent;
* `mulNorm`: `_FP_MUL`'s normal case: `R_e = X_e + Y_e + 1`, the 112-bit
  product (`umul_ppmm`) shifted right by `55` with a sticky bit
  (`_FP_FRAC_SRS_2`, `rto`), renormalised by one more sticky bit when bit 56
  is set (`_FP_FRAC_OVERP`), else `R_e - 1`;
* `packCanon`: `_FP_PACK_CANONICAL`: `_FP_ROUND` and the pack at the biased
  exponent `E = R_e + 1023 ≥ 1` (`roundPack`), or, at `E ≤ 0`, the sticky
  shift by `1 - E` first (a deep underflow, `1 - E > 56`, gives zero either
  way: `rto` leaves `1`, which rounds to `0`).

(b2) `mul_eq : mul a b = F64.mul a b`, by the round laws of B-SFREF
(`roundPack_eq`, `round_rto` (W1) three times at most, `round_scale`).
-/

namespace Lua.Num.SfRef

set_option linter.deprecated false

open F64

/-- `_FP_UNPACK_CANONICAL`'s working mantissa of a nonzero finite operand. -/
def unpackF (e f : Nat) : Nat := if e = 0 then f * 2 ^ (55 - f.log2) else 2 ^ 55 + 8 * f

/-- `_FP_UNPACK_CANONICAL`'s unbiased exponent of a nonzero finite operand. -/
def unpackE (e f : Nat) : Int := if e = 0 then -1074 + (f.log2 : Int) else (e : Int) - 1023

/-- `_FP_PACK_CANONICAL` of a normal working value `R ∈ [2^55, 2^56)` at the
unbiased exponent `e`. -/
def packCanon (neg : Bool) (e : Int) (R : Nat) : F64 :=
  if 0 < e + 1023 then roundPack neg (e + 1023).toNat R
  else roundPack neg 0 (rto R (1 - (e + 1023)).toNat)

/-- `_FP_MUL` of two normal unpacked operands, packed. -/
def mulNorm (neg : Bool) (X : Nat) (Xe : Int) (Y : Nat) (Ye : Int) : F64 :=
  if 2 ^ 56 ≤ rto (X * Y) 55 then packCanon neg (Xe + Ye + 1) (rto (rto (X * Y) 55) 1)
  else packCanon neg (Xe + Ye) (rto (X * Y) 55)

/-- `__muldf3` over the fields (`_FP_MUL`'s class cases; a NaN result is
the canonical `qnan`, `_FP_CHOOSENAN` on RISC-V). -/
def mulFields (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat) : F64 :=
  if (ea = 2047 ∧ fa ≠ 0) ∨ (eb = 2047 ∧ fb ≠ 0) then qnan
  else if ea = 2047 then (if eb = 0 ∧ fb = 0 then qnan else infty (sa ^^ sb))
  else if eb = 2047 then (if ea = 0 ∧ fa = 0 then qnan else infty (sa ^^ sb))
  else if (ea = 0 ∧ fa = 0) ∨ (eb = 0 ∧ fb = 0) then zero (sa ^^ sb)
  else mulNorm (sa ^^ sb) (unpackF ea fa) (unpackE ea fa) (unpackF eb fb) (unpackE eb fb)

/-- `SfRef.mul`. -/
def mul (a b : F64) : F64 := mulFields a.sign a.bexp a.frac b.sign b.bexp b.frac

/-! ## The round laws at the machine's shifts -/

theorem target_ge (n : Nat) (e : Int) : (n.log2 : Int) + 1 + e - 53 ≤ target n e := by
  unfold target; omega
theorem target_ge' (n : Nat) (e : Int) : -1074 ≤ target n e := by
  unfold target; omega

/-- A sticky shift keeps the top bit's range. -/
theorem rto_ge {n k a : Nat} (ha : 1 ≤ a) (h : 2 ^ (a + k) ≤ n) : 2 ^ a ≤ rto n k := by
  have h1 : 2 ^ a ≤ n / 2 ^ k := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos k), ← Nat.pow_add]; exact h
  have h2 : 2 ^ (a - 1) ≤ n / 2 ^ (k + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) h
  have h3 : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  unfold rto; split <;> omega

theorem rto_lt {n k a : Nat} (ha : 1 ≤ a) (h : n < 2 ^ (a + k)) : rto n k < 2 ^ a := by
  have h1 : n / 2 ^ k < 2 ^ a := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← Nat.pow_add]; exact h
  have h2 : n / 2 ^ (k + 1) < 2 ^ (a - 1) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega))
  have h3 : 2 ^ a = 2 * 2 ^ (a - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  unfold rto; split <;> omega

/-- `_FP_PACK_CANONICAL` of a normal working value is `F64.round` of it. -/
theorem packCanon_eq (neg : Bool) (e : Int) (R : Nat) (h1 : 2 ^ 55 ≤ R) (h2 : R < 2 ^ 56) :
    packCanon neg e R = round neg R (e - 55) false false := by
  unfold packCanon
  split
  · rename_i hE
    rw [roundPack_eq neg _ R h2 (fun _ => h1)]
    congr 1; omega
  · rename_i hE
    have hk : 1 ≤ (1 - (e + 1023)).toNat := by omega
    rw [roundPack_eq neg 0 _ (Nat.lt_of_le_of_lt (rto_le_self _ _) h2) (by omega)]
    have := round_rto neg R (1 - (e + 1023)).toNat (-1077 - (1 - (e + 1023)).toNat)
      (by have := target_ge' (rto R (1 - (e + 1023)).toNat) (-1077 - ((1 - (e + 1023)).toNat : Int) +
            ((1 - (e + 1023)).toNat : Int)); omega)
    rw [show ((max 0 1 : Nat) : Int) - 1078 = -1077 - ((1 - (e + 1023)).toNat : Int) +
      ((1 - (e + 1023)).toNat : Int) by omega, this]
    congr 1; omega

/-- `_FP_MUL`'s normal case, packed, is `F64.round` of the exact product. -/
theorem mulNorm_eq (neg : Bool) (X Y : Nat) (Xe Ye : Int) (hX1 : 2 ^ 55 ≤ X) (hX2 : X < 2 ^ 56)
    (hY1 : 2 ^ 55 ≤ Y) (hY2 : Y < 2 ^ 56) :
    mulNorm neg X Xe Y Ye = round neg (X * Y) (Xe + Ye - 110) false false := by
  have hP1 : 2 ^ 110 ≤ X * Y := by
    have := Nat.mul_le_mul hX1 hY1; rwa [← Nat.pow_add] at this
  have hP2 : X * Y < 2 ^ 112 := by
    have := Nat.mul_lt_mul_of_lt_of_le hX2 (Nat.le_of_lt hY2) (by omega)
    rwa [← Nat.pow_add] at this
  have hR1 : 2 ^ 55 ≤ rto (X * Y) 55 := rto_ge (by decide) (by simpa using hP1)
  have hR2 : rto (X * Y) 55 < 2 ^ 57 := rto_lt (by decide) (by simpa using hP2)
  have hL : 55 ≤ (rto (X * Y) 55).log2 := le_log2_of hR1
  -- W1 at the product's sticky shift by 55
  have w55 := round_rto neg (X * Y) 55 (Xe + Ye - 110)
    (by have := target_ge (rto (X * Y) 55) (Xe + Ye - 110 + (55 : Nat)); omega)
  unfold mulNorm
  split
  · rename_i hov
    have hS1 : 2 ^ 55 ≤ rto (rto (X * Y) 55) 1 := rto_ge (by decide) (by simpa using hov)
    have hS2 : rto (rto (X * Y) 55) 1 < 2 ^ 56 := rto_lt (by decide) (by simpa using hR2)
    have hL1 : 55 ≤ (rto (rto (X * Y) 55) 1).log2 := le_log2_of hS1
    have w1 := round_rto neg (rto (X * Y) 55) 1 (Xe + Ye - 110 + (55 : Nat))
      (by have := target_ge (rto (rto (X * Y) 55) 1) (Xe + Ye - 110 + (55 : Nat) + (1 : Nat)); omega)
    rw [packCanon_eq neg _ _ hS1 hS2, show Xe + Ye + 1 - 55 = Xe + Ye - 110 + (55 : Nat) + (1 : Nat) by omega,
      w1, w55]
  · rename_i hov
    rw [packCanon_eq neg _ _ hR1 (by omega), show Xe + Ye - 55 = Xe + Ye - 110 + (55 : Nat) by omega, w55]

/-! ## The unpacked operands -/

theorem unpack_bounds (e f : Nat) (hf : f < 2 ^ 52) (h0 : e ≠ 0 ∨ f ≠ 0) :
    2 ^ 55 ≤ unpackF e f ∧ unpackF e f < 2 ^ 56 := by
  unfold unpackF
  split
  · have hf0 : 0 < f := by omega
    exact norm_bounds hf0 (by omega)
  · omega

/-- The unpacked operand is the decoded one, scaled: `X_f = cm · 2^j` at
`X_e - 55 = ce - j`. -/
theorem unpack_scale (e f : Nat) (hf : f < 2 ^ 52) (h0 : e ≠ 0 ∨ f ≠ 0) :
    ∃ j : Nat, unpackF e f = cm e f * 2 ^ j ∧ unpackE e f - 55 = ce e - j := by
  unfold unpackF unpackE cm ce
  by_cases h : e = 0
  · have hf0 : 0 < f := by omega
    have hl : f.log2 < 52 := (Nat.log2_lt (by omega)).2 hf
    refine ⟨55 - f.log2, ?_, ?_⟩
    · simp only [h, if_true]
    · simp only [h, if_true]; omega
  · refine ⟨3, ?_, ?_⟩
    · simp only [h, if_false]; omega
    · simp only [h, if_false]; omega

/-! ## (b2) -/

theorem mulFields_fin (sa sb : Bool) (ea fa eb fb : Nat) (hea : ea ≤ 2046) (heb : eb ≤ 2046)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha0 : ea ≠ 0 ∨ fa ≠ 0) (hb0 : eb ≠ 0 ∨ fb ≠ 0) :
    mulFields sa ea fa sb eb fb = roundExact (sa ^^ sb) (cm ea fa * cm eb fb) (ce ea + ce eb) := by
  unfold mulFields
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have ⟨ha1, ha2⟩ := unpack_bounds ea fa hfa ha0
  have ⟨hb1, hb2⟩ := unpack_bounds eb fb hfb hb0
  rw [mulNorm_eq _ _ _ _ _ ha1 ha2 hb1 hb2]
  obtain ⟨ja, hja, hea'⟩ := unpack_scale ea fa hfa ha0
  obtain ⟨jb, hjb, heb'⟩ := unpack_scale eb fb hfb hb0
  rw [hja, hjb, show cm ea fa * 2 ^ ja * (cm eb fb * 2 ^ jb) = cm ea fa * cm eb fb * 2 ^ (ja + jb) by
    rw [Nat.pow_add]; ac_rfl,
    show unpackE ea fa + unpackE eb fb - 110 = (ce ea + ce eb) - ((ja + jb : Nat) : Int) by omega,
    round_scale]

/-- **(b2) for `__muldf3`**: the soft-fp-shaped reference is the `F64`
specification. -/
theorem mul_eq (a b : F64) : mul a b = F64.mul a b := by
  have hfa : a.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hea : a.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfb : b.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have heb : b.bexp < 2048 := Nat.mod_lt _ (by decide)
  unfold mul F64.mul
  by_cases han : a.bexp = 2047 ∧ a.frac ≠ 0
  · rw [cls_nan' han.1 han.2]; unfold mulFields; rw [if_pos (Or.inl han)]
  by_cases hbn : b.bexp = 2047 ∧ b.frac ≠ 0
  · rw [cls_nan' hbn.1 hbn.2]; unfold mulFields; rw [if_pos (Or.inr hbn)]
    cases a.cls <;> rfl
  unfold mulFields; rw [if_neg (by omega)]
  by_cases hai : a.bexp = 2047
  · have hfa0 : a.frac = 0 := by omega
    rw [cls_inf' hai hfa0, if_pos hai]
    by_cases hbi : b.bexp = 2047
    · have hfb0 : b.frac = 0 := by omega
      rw [cls_inf' hbi hfb0, if_neg (by omega)]
    by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
    · rw [cls_zero' hb0.1 hb0.2, if_pos hb0]
    · rw [cls_fin' (by omega) hbi, if_neg hb0]
  rw [if_neg hai]
  by_cases hbi : b.bexp = 2047
  · have hfb0 : b.frac = 0 := by omega
    rw [cls_inf' hbi hfb0, if_pos hbi]
    by_cases ha0 : a.bexp = 0 ∧ a.frac = 0
    · rw [cls_zero' ha0.1 ha0.2, if_pos ha0]
    · rw [cls_fin' (by omega) hai, if_neg ha0]
  rw [if_neg hbi]
  by_cases ha0 : a.bexp = 0 ∧ a.frac = 0
  · rw [if_pos (Or.inl ha0), cls_zero' ha0.1 ha0.2]
    by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
    · rw [cls_zero' hb0.1 hb0.2]
    · rw [cls_fin' (by omega) hbi]
  by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
  · rw [if_pos (Or.inr hb0), cls_zero' hb0.1 hb0.2, cls_fin' (by omega) hai]
  rw [if_neg (by omega), cls_fin' (by omega) hai, cls_fin' (by omega) hbi]
  have := mulFields_fin a.sign b.sign a.bexp a.frac b.bexp b.frac (by omega) (by omega) hfa hfb
    (by omega) (by omega)
  unfold mulFields at this
  rw [if_neg (by omega), if_neg hai, if_neg hbi, if_neg (by omega)] at this
  exact this

end Lua.Num.SfRef

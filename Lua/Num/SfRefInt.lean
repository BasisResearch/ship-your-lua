import Lua.Num.SfRefSpec

/-!
# `SfRef` conversions: `__fixdfdi`, `__floatdidf`, `__floatsidf` (lane float-sf2)

The soft-fp-shaped references of the integer conversions, over `Nat` fields,
and (b2): each is its `F64` specification.

* `toIntFields`: libgcc `soft-fp/op-common.h` `_FP_TO_INT (r, X, 64, 1)`
  (through `soft-fp/fixdfdi.c`'s `FP_TO_INT_D`): below the bias the result is
  `0`; at or above `2^63` it saturates by the sign (`r = 1 << 63`,
  `r -= 1 - X_s`); otherwise the mantissa with its hidden bit is shifted to
  the integer position and negated by the sign. No rounding: truncation.
* `fromNat`: `_FP_FROM_INT (X, r, 64, UDItype)` (through
  `soft-fp/floatdidf.c`/`floatsidf.c`'s `FP_FROM_INT_D`): the magnitude's
  count of leading zeros `z` (`__FP_CLZ`) gives the exponent `1086 - z`;
  a magnitude of at most 53 bits is shifted into place exactly, a longer one
  is shifted right to the 56-bit working mantissa by a sticky shift
  (`_FP_FRAC_SRS`, here `rto`), then `_FP_ROUND` and the pack (`roundPack`).
  (b2) reuses B-SFREF's round laws unchanged: `roundPack_eq`, `round_scale`
  (the exact path), `round_rto` (W1, the sticky path).
-/

namespace Lua.Num.SfRef

open F64

/-! ## `__fixdfdi` -/

/-- `_FP_TO_INT (r, X, 64, 1)` over the fields `(s, e, f)`. -/
def toIntFields (s : Bool) (e f : Nat) : Int :=
  if e < 1023 then 0
  else if 1086 ≤ e then (if s then -2 ^ 63 else 2 ^ 63 - 1)
  else sgnApply s (if 1075 ≤ e then (2 ^ 52 + f) * 2 ^ (e - 1075) else (2 ^ 52 + f) / 2 ^ (1075 - e))

/-- `__fixdfdi`. -/
def toInt (x : F64) : BitVec 64 := BitVec.ofInt 64 (toIntFields x.sign x.bexp x.frac)

theorem div_small {m k : Nat} (hm : m < 2 ^ 53) (hk : 53 ≤ k) : m / 2 ^ k = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) hk))
theorem mul_pow_lt {m k : Nat} (hm : m < 2 ^ 53) (hk : k ≤ 10) : m * 2 ^ k < 2 ^ 63 := by
  calc m * 2 ^ k < 2 ^ 53 * 2 ^ k := Nat.mul_lt_mul_of_pos_right hm (Nat.two_pow_pos k)
    _ = 2 ^ (53 + k) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
theorem mul_pow_ge {m k : Nat} (hm : 2 ^ 52 ≤ m) (hk : 11 ≤ k) : 2 ^ 63 ≤ m * 2 ^ k := by
  calc 2 ^ 63 ≤ 2 ^ (52 + k) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2 ^ 52 * 2 ^ k := Nat.pow_add _ _ _
    _ ≤ m * 2 ^ k := Nat.mul_le_mul_right _ hm
theorem sat_true : BitVec.ofInt 64 (-2 ^ 63) = BitVec.ofNat 64 (2 ^ 63) := by decide
theorem sat_false : BitVec.ofInt 64 (2 ^ 63 - 1) = BitVec.ofNat 64 (2 ^ 63 - 1) := by decide

/-- **(b2) for `__fixdfdi`**: `_FP_TO_INT` is truncation toward zero,
saturated by the sign (the body of `Lua.Vm.Fn.Fixdfdi.S`). -/
theorem toInt_eq (x : F64) :
    toInt x = match F64.truncInt? x with
      | some i => if -(2 ^ 63 : Int) ≤ i ∧ i < 2 ^ 63 then BitVec.ofInt 64 i
                  else if F64.sign x then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1)
      | none => if F64.sign x then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1) := by
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have he : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  unfold toInt truncInt?
  by_cases hi : x.bexp = 2047
  · have hc : x.cls = .nan ∨ x.cls = .inf x.sign := by
      by_cases h0 : x.frac = 0
      · exact Or.inr (cls_inf' hi h0)
      · exact Or.inl (cls_nan' hi h0)
    have hT : toIntFields x.sign x.bexp x.frac = if x.sign then -2 ^ 63 else 2 ^ 63 - 1 := by
      unfold toIntFields; rw [if_neg (by omega), if_pos (by omega)]
    rcases hc with hc | hc <;> rw [hc, hT] <;> cases x.sign <;> decide
  by_cases hz : x.bexp = 0 ∧ x.frac = 0
  · rw [cls_zero' hz.1 hz.2]
    dsimp only
    unfold toIntFields; rw [if_pos (by omega), if_pos (by decide)]
  rw [cls_fin' (by omega) hi]
  dsimp only
  generalize x.sign = s
  generalize hE : x.bexp = e at *
  generalize hF : x.frac = f at *
  -- the truncated magnitude `V` and the reference, region by region
  have key : ∀ (n : Nat) (T : Int), toIntFields s e f = T →
      (if 0 ≤ ce e then cm e f <<< (ce e).toNat else cm e f / 2 ^ (-ce e).toNat) = n →
      (if -(2 ^ 63 : Int) ≤ sgnApply s n ∧ sgnApply s n < 2 ^ 63 then BitVec.ofInt 64 (sgnApply s n)
        else if s then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1)) = BitVec.ofInt 64 T →
      BitVec.ofInt 64 (toIntFields s e f) =
        if -(2 ^ 63 : Int) ≤ sgnApply s (if 0 ≤ ce e then cm e f <<< (ce e).toNat else cm e f / 2 ^ (-ce e).toNat) ∧
            sgnApply s (if 0 ≤ ce e then cm e f <<< (ce e).toNat else cm e f / 2 ^ (-ce e).toNat) < 2 ^ 63 then
          BitVec.ofInt 64 (sgnApply s (if 0 ≤ ce e then cm e f <<< (ce e).toNat else cm e f / 2 ^ (-ce e).toNat))
        else if s then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1) := by
    intro n T h1 h2 h3; rw [h1, h2, h3]
  have hsg0 : ∀ s : Bool, sgnApply s 0 = 0 := fun s => by cases s <;> rfl
  by_cases hlo : e < 1023
  · -- below the bias (subnormals included): zero
    apply key 0 0
    · unfold toIntFields; rw [if_pos hlo]
    · unfold cm ce
      by_cases h0 : e = 0
      · subst h0; simp only [ite_true]
        rw [if_neg (by decide), show (-(-1074 : Int)).toNat = 1074 by rfl, div_small (by omega) (by omega)]
      · simp only [h0, ite_false]
        rw [if_neg (by omega), show (-((e : Int) - 1075)).toNat = 1075 - e by omega,
          div_small (by omega) (by omega)]
    · rw [hsg0, if_pos (by decide)]
  have h0 : e ≠ 0 := by omega
  have hcm : cm e f = f + 2 ^ 52 := by unfold cm; simp [h0]
  have hce : ce e = (e : Int) - 1075 := by unfold ce; simp [h0]
  by_cases hhi : 1086 ≤ e
  · -- at or above `2^63`: saturated by the sign
    have hge := mul_pow_ge (m := f + 2 ^ 52) (k := e - 1075) (by omega) (by omega)
    apply key ((f + 2 ^ 52) * 2 ^ (e - 1075)) (if s then -2 ^ 63 else 2 ^ 63 - 1)
    · unfold toIntFields; rw [if_neg hlo, if_pos hhi]
    · rw [hcm, hce, if_pos (by omega), show ((e : Int) - 1075).toNat = e - 1075 by omega, Nat.shiftLeft_eq]
    · cases s
      · simp only [sgnApply, Bool.false_eq_true, ite_false]
        rw [if_neg (by omega)]; exact sat_false.symm
      · simp only [sgnApply, ite_true]
        by_cases heq : (f + 2 ^ 52) * 2 ^ (e - 1075) = 2 ^ 63
        · rw [heq, if_pos (by decide)]; decide
        · rw [if_neg (by omega)]; exact sat_true.symm
  by_cases hmid : 1075 ≤ e
  · -- an exact left shift, below `2^63`
    have hlt := mul_pow_lt (m := f + 2 ^ 52) (k := e - 1075) (by omega) (by omega)
    apply key ((f + 2 ^ 52) * 2 ^ (e - 1075)) (sgnApply s ((f + 2 ^ 52) * 2 ^ (e - 1075)))
    · unfold toIntFields; rw [if_neg hlo, if_neg hhi, if_pos hmid, Nat.add_comm (2 ^ 52) f]
    · rw [hcm, hce, if_pos (by omega), show ((e : Int) - 1075).toNat = e - 1075 by omega, Nat.shiftLeft_eq]
    · rw [if_pos (by cases s <;> simp only [sgnApply, Bool.false_eq_true, ite_true, ite_false] <;> omega)]
  · -- a truncating right shift
    have hle : (f + 2 ^ 52) / 2 ^ (1075 - e) ≤ f + 2 ^ 52 := Nat.div_le_self _ _
    apply key ((f + 2 ^ 52) / 2 ^ (1075 - e)) (sgnApply s ((f + 2 ^ 52) / 2 ^ (1075 - e)))
    · unfold toIntFields; rw [if_neg hlo, if_neg hhi, if_neg hmid, Nat.add_comm (2 ^ 52) f]
    · rw [hcm, hce, if_neg (by omega), show (-((e : Int) - 1075)).toNat = 1075 - e by omega]
    · generalize (f + 2 ^ 52) / 2 ^ (1075 - e) = q at hle ⊢
      rw [if_pos (by cases s <;> simp only [sgnApply, Bool.false_eq_true, ite_true, ite_false] <;> omega)]

/-! ## `__floatdidf`, `__floatsidf` -/

/-- `_FP_FROM_INT` on a magnitude `n < 2^64` with sign `neg`: `z` leading
zeros, exponent `1086 - z`; the 56-bit working mantissa is `n` shifted left
(at most 53 significant bits: exact) or right by a sticky shift. -/
def fromNat (neg : Bool) (n : Nat) : F64 :=
  if n = 0 then zero false
  else if 8 ≤ 63 - n.log2 then roundPack neg (1086 - (63 - n.log2)) (n * 2 ^ (63 - n.log2 - 8))
  else roundPack neg (1086 - (63 - n.log2)) (rto n (8 - (63 - n.log2)))

/-- `__floatdidf` (and `__floatsidf` on a sign-extended `int`). -/
def ofInt (i : BitVec 64) : F64 := fromNat (decide (i.toInt < 0)) i.toInt.natAbs

theorem log2_bounds {n : Nat} (h0 : 0 < n) : 2 ^ n.log2 ≤ n ∧ n < 2 ^ (n.log2 + 1) :=
  ⟨Nat.log2_self_le (by omega), Nat.lt_log2_self⟩

/-- `_FP_FROM_INT` rounds the magnitude exactly as `F64.round` does. -/
theorem fromNat_eq (neg : Bool) (n : Nat) (h0 : 0 < n) (h : n < 2 ^ 64) :
    fromNat neg n = round neg n 0 false false := by
  have hL : n.log2 < 64 := (Nat.log2_lt (by omega)).2 h
  have ⟨hb1, hb2⟩ := log2_bounds h0
  unfold fromNat
  rw [if_neg (by omega)]
  by_cases hz : 8 ≤ 63 - n.log2
  · rw [if_pos hz]
    have hj : 63 - n.log2 - 8 = 55 - n.log2 := by omega
    rw [hj]
    have hF1 : 2 ^ 55 ≤ n * 2 ^ (55 - n.log2) := by
      calc 2 ^ 55 = 2 ^ n.log2 * 2 ^ (55 - n.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ n * 2 ^ (55 - n.log2) := Nat.mul_le_mul_right _ hb1
    have hF2 : n * 2 ^ (55 - n.log2) < 2 ^ 56 := by
      calc n * 2 ^ (55 - n.log2) < 2 ^ (n.log2 + 1) * 2 ^ (55 - n.log2) :=
            Nat.mul_lt_mul_of_pos_right hb2 (Nat.two_pow_pos _)
        _ = 2 ^ 56 := by rw [← Nat.pow_add]; congr 1; omega
    rw [roundPack_eq neg _ _ hF2 (fun _ => hF1)]
    have he : (((max (1086 - (63 - n.log2)) 1 : Nat) : Int) - 1078) = 0 - ((55 - n.log2 : Nat) : Int) := by omega
    rw [he, round_scale]
  · rw [if_neg hz]
    have hk : 8 - (63 - n.log2) = n.log2 - 55 := by omega
    rw [hk]
    have hkn : 2 ^ (n.log2 - 55) ≤ n :=
      Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hb1
    have hlr := log2_rto hkn
    have hr0 : 0 < rto n (n.log2 - 55) := rto_pos h0
    have ⟨hr1, hr2⟩ := log2_bounds hr0
    have hr55 : (rto n (n.log2 - 55)).log2 = 55 := by omega
    rw [hr55] at hr1 hr2
    rw [roundPack_eq neg _ _ hr2 (fun _ => hr1)]
    have he : (((max (1086 - (63 - n.log2)) 1 : Nat) : Int) - 1078) = 0 + ((n.log2 - 55 : Nat) : Int) := by omega
    rw [he, round_rto]
    unfold target; rw [hr55]; omega

/-- **(b2) for `__floatdidf`**: `_FP_FROM_INT` is `F64.ofInt`. -/
theorem ofInt_eq (i : BitVec 64) : ofInt i = F64.ofInt i := by
  unfold ofInt F64.ofInt normalize
  by_cases h0 : i.toInt = 0
  · rw [if_pos h0, h0]; rfl
  rw [if_neg h0]
  have h1 := i.toInt_lt
  have h2 := i.le_toInt
  rw [fromNat_eq _ _ (by omega) (by omega)]

end Lua.Num.SfRef

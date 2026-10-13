import Lua.Num.SfRef

/-!
# (b2): `SfRef.add = F64.add`, in `Nat` (round 5, B-SFREF)

The soft-fp-shaped reference (`Lua/Num/SfRef.lean`) is the `F64`
specification. The rounding half is three laws of `F64.round` on an exact
value (`rb = st = false`):

* `roundPack_eq`: soft-fp's `_FP_ROUND` + `_FP_PACK_SEMIRAW` on a working
  mantissa `F < 2^56` at biased exponent `E` is `F64.round` of `F · 2^(max E 1 - 1078)`;
* `round_scale`: an exact value's representation does not matter
  (`n · 2^j` at `e - j` is `n` at `e`);
* `round_rto`: round to odd at a position two or more bits below the
  rounding position does not change the rounding (W1).
-/

namespace Lua.Num.SfRef

set_option linter.deprecated false

open F64

theorem bits_zero (neg : Bool) (be f : Nat) : bits neg be f = bits neg 0 (be * 2 ^ 52 + f) := by
  unfold bits; exact congrArg (BitVec.ofNat 64) (by omega)

/-- `rne3` is `rne` on the three work bits. -/
theorem rne3_div (F : Nat) :
    rne3 F / 8 = rne (F / 8) (decide (F / 4 % 2 = 1)) (decide (F % 4 ≠ 0)) := by
  unfold rne3 rne
  by_cases h1 : F % 8 = 0
  · rw [if_pos (Or.inl h1)]
    have : ¬ (F / 4 % 2 = 1) := by omega
    simp [this]
  by_cases h2 : F % 16 = 4
  · rw [if_pos (Or.inr h2)]
    have : F / 4 % 2 = 1 := by omega
    have : F % 4 = 0 := by omega
    have : F / 8 % 2 = 0 := by omega
    simp [*]
  rw [if_neg (by omega)]
  by_cases h3 : F / 4 % 2 = 1
  · have : decide (F % 4 ≠ 0) || F / 8 % 2 == 1 := by
      by_cases h4 : F % 4 = 0
      · have : F / 8 % 2 = 1 := by omega
        simp [this]
      · simp [h4]
    simp only [h3, decide_true, Bool.true_and, this, ite_true]; omega
  · simp only [h3, decide_false, Bool.false_and]; simp; omega

theorem log2_55 {F : Nat} (h1 : 2 ^ 55 ≤ F) (h2 : F < 2 ^ 56) : F.log2 = 55 :=
  (Nat.log2_eq_iff (by omega)).2 ⟨h1, h2⟩

theorem log2_le_55 {F : Nat} (h2 : F < 2 ^ 56) : F.log2 ≤ 55 := by
  rcases Nat.eq_zero_or_pos F with h | h
  · subst h; simp
  · have := (Nat.log2_lt (by omega)).2 h2; omega

/-- The rounding position of a working mantissa is three bits up. -/
theorem target_work {E F : Nat} (hF0 : 0 < F) (hF : F < 2 ^ 56) (hn : 2 ≤ E → 2 ^ 55 ≤ F) :
    target F ((max E 1 : Nat) - 1078 : Int) = ((max E 1 : Nat) - 1078 : Int) + 3 := by
  unfold target
  by_cases hE : 2 ≤ E
  · rw [log2_55 (hn hE) hF]; omega
  · have := log2_le_55 hF; omega

/-- `F64.round` of an exact working mantissa: three bits shifted out, `rne`, `finish`. -/
theorem round_work (neg : Bool) (E F : Nat) (hF0 : 0 < F) (hF : F < 2 ^ 56) (hn : 2 ≤ E → 2 ^ 55 ≤ F) :
    round neg F ((max E 1 : Nat) - 1078 : Int) false false =
      finish neg (rne3 F / 8) (((max E 1 : Nat) - 1078 : Int) + 3) := by
  unfold round
  rw [target_work hF0 hF hn, if_pos (by omega)]
  have h3 : (((max E 1 : Nat) - 1078 : Int) + 3 - ((max E 1 : Nat) - 1078 : Int)).toNat = 3 := by omega
  simp only [h3, shr, rne3_div]
  simp

theorem rne3_le (F : Nat) : F ≤ rne3 F ∧ rne3 F ≤ F + 4 := by unfold rne3; split <;> omega

/-- Close a case of two packs: the same constant, or the same word. -/
macro "rp_close" : tactic => `(tactic| first
  | (with_reducible rfl)
  | (exfalso; omega)
  | (unfold infty bits; exact congrArg (BitVec.ofNat 64) (by omega))
  | (unfold zero bits; exact congrArg (BitVec.ofNat 64) (by omega))
  | (unfold bits; exact congrArg (BitVec.ofNat 64) (by omega)))

/-- **`_FP_ROUND` then `_FP_PACK_SEMIRAW` is `F64.round`** of the working
mantissa at its scale. -/
theorem roundPack_eq (neg : Bool) (E F : Nat) (hF : F < 2 ^ 56) (hn : 2 ≤ E → 2 ^ 55 ≤ F) :
    roundPack neg E F = round neg F ((max E 1 : Nat) - 1078 : Int) false false := by
  rcases Nat.eq_zero_or_pos F with h0 | h0
  · subst h0
    have hE : E ≤ 1 := by
      by_cases h : 2 ≤ E
      · have := hn h; omega
      · omega
    have hT : target 0 ((max E 1 : Nat) - 1078 : Int) = -1074 := by unfold target; simp; omega
    have hL : roundPack neg E 0 = bits neg 0 0 := by
      unfold roundPack
      rw [show rne3 0 = 0 by decide, if_neg (by omega)]
      congr 1; omega
    have hR : round neg 0 ((max E 1 : Nat) - 1078 : Int) false false = zero neg := by
      unfold round
      rw [hT, if_pos (by omega)]
      simp [shr, rne, finish, packFin]
    rw [hL, hR]; rfl
  · rw [round_work neg E F h0 hF hn]
    have hq := rne3_le F
    have hq1 : rne3 F / 8 ≤ 2 ^ 53 := by omega
    have hq2 : 2 ≤ E → 2 ^ 52 ≤ rne3 F / 8 := fun h => by have := hn h; omega
    unfold roundPack finish packFin
    dsimp only
    by_cases hm : rne3 F / 8 = 2 ^ 53
    · rw [if_pos hm]
      (repeat' split) <;> rp_close
    · rw [if_neg hm]
      (repeat' split) <;> rp_close

/-! ## The representation of an exact value does not matter -/

theorem div_scale (n j s : Nat) : n * 2 ^ j / 2 ^ (s + j) = n / 2 ^ s := by
  rw [Nat.pow_add, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos j)]
theorem mod_scale (n j s : Nat) : n * 2 ^ j % 2 ^ (s + j) = n % 2 ^ s * 2 ^ j := by
  rw [Nat.pow_add, Nat.mul_mod_mul_right]

theorem shr_scale (n j s : Nat) : shr (n * 2 ^ j) false false (s + j) = shr n false false s := by
  unfold shr
  by_cases h0 : s + j = 0
  · have : s = 0 := by omega
    have : j = 0 := by omega
    subst_vars; simp
  rw [if_neg h0]
  by_cases hs : s = 0
  · subst hs
    rw [if_pos rfl]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have ee : n * 2 ^ (j' + 1) = (2 * n) * 2 ^ j' := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ j') 2, ← Nat.mul_assoc, Nat.mul_comm n 2]
    have e1 : n * 2 ^ (j' + 1) / 2 ^ (0 + (j' + 1) - 1) = 2 * n := by
      rw [ee, show 0 + (j' + 1) - 1 = 0 + j' by omega, div_scale]; simp
    have e2 : n * 2 ^ (j' + 1) % 2 ^ (0 + (j' + 1) - 1) = 0 := by
      rw [ee, show 0 + (j' + 1) - 1 = 0 + j' by omega, mod_scale]; simp [Nat.mod_one]
    rw [div_scale, e1, e2]; simp
  · rw [if_neg hs, div_scale, show s + j - 1 = (s - 1) + j by omega, div_scale, mod_scale]
    have : (n % 2 ^ (s - 1) * 2 ^ j ≠ 0) ↔ (n % 2 ^ (s - 1) ≠ 0) := by
      constructor
      · intro h h'; rw [h'] at h; simp at h
      · intro h; exact Nat.mul_ne_zero h (Nat.ne_of_gt (Nat.two_pow_pos j))
    simp only [Bool.or_false, decide_eq_decide.mpr this]

theorem round_zero (neg : Bool) (e : Int) : round neg 0 e false false = zero neg := by
  unfold round
  dsimp only
  split
  · simp [shr, rne, finish, packFin]
  · simp [packFin]

theorem target_scale (n j : Nat) (e : Int) (hn : 0 < n) : target (n * 2 ^ j) (e - j) = target n e := by
  unfold target
  rw [← Nat.shiftLeft_eq, log2_shiftLeft j hn]; omega

theorem round_scale (neg : Bool) (n j : Nat) (e : Int) :
    round neg (n * 2 ^ j) (e - j) false false = round neg n e false false := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp only [Nat.zero_mul, round_zero]
  have hT := target_scale n j e hn
  have ht : ((n.log2 : Int) + 1 + e - 53) ≤ target n e := by unfold target; omega
  unfold round
  rw [hT]
  by_cases h1 : e ≤ target n e
  · rw [if_pos (by omega), if_pos h1,
      show (target n e - (e - j)).toNat = (target n e - e).toNat + j by omega, shr_scale]
  · rw [if_neg h1]
    obtain ⟨d, hd⟩ : ∃ d : Nat, (e - target n e) = (d : Int) := ⟨(e - target n e).toNat, by omega⟩
    have hd1 : 1 ≤ d := by omega
    have hlt : n * 2 ^ d < 2 ^ 53 := by
      rw [← Nat.shiftLeft_eq]
      apply lt_two_pow_of_log2
      rw [log2_shiftLeft d hn]; omega
    by_cases h2 : e - j ≤ target n e
    · rw [if_pos h2]
      have hs : j = (target n e - (e - j)).toNat + d := by omega
      have e1 : n * 2 ^ j = (n * 2 ^ d) * 2 ^ (target n e - (e - j)).toNat := by
        rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
      have hss := shr_scale (n * 2 ^ d) ((target n e - (e - j)).toNat) 0
      rw [Nat.zero_add] at hss
      rw [e1, hss]
      simp only [shr, if_true, rne, Bool.false_and, Bool.false_eq_true, ite_false, finish]
      rw [if_neg (by omega), show (e - target n e).toNat = d by omega, Nat.shiftLeft_eq]
    · rw [if_neg h2, Nat.shiftLeft_eq, Nat.shiftLeft_eq, Nat.mul_assoc, ← Nat.pow_add]
      congr 3; omega

/-! ## Round to odd two bits below the rounding position (W1) -/

theorem div_pow_add (n a b : Nat) : n / 2 ^ a / 2 ^ b = n / 2 ^ (a + b) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem shr_rto (n k s : Nat) (hs : 2 ≤ s) :
    shr (rto n k) false false s = shr n false false (s + k) := by
  unfold shr
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [Bool.or_false]
  unfold rto
  split
  · rename_i h
    obtain ⟨q, hq⟩ : ∃ q, n = q * 2 ^ k := ⟨n / 2 ^ k, by
      have := Nat.div_add_mod n (2 ^ k); rw [h] at this; rw [Nat.mul_comm]; omega⟩
    subst hq
    rw [Nat.mul_div_cancel _ (Nat.two_pow_pos k), div_scale, show s + k - 1 = (s - 1) + k by omega,
      div_scale, mod_scale]
    have : (q % 2 ^ (s - 1) * 2 ^ k ≠ 0) ↔ (q % 2 ^ (s - 1) ≠ 0) := by
      constructor
      · intro h h'; rw [h'] at h; simp at h
      · intro h; exact Nat.mul_ne_zero h (Nat.ne_of_gt (Nat.two_pow_pos k))
    simp only [decide_eq_decide.mpr this]
  · rename_i h
    have hq := Nat.div_add_mod n (2 ^ (k + 1))
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
    have hA : ∀ a b : Nat, a / 2 ^ (b + 1) = a / 2 / 2 ^ b := by
      intro a b; rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]
    have hq2 : (2 * (n / 2 ^ (k + 1)) + 1) / 2 = n / 2 ^ (k + 1) := by omega
    have e1 : (2 * (n / 2 ^ (k + 1)) + 1) / 2 ^ (s' + 2) = n / 2 ^ (s' + 2 + k) := by
      have l : (2 * (n / 2 ^ (k + 1)) + 1) / 2 ^ (s' + 2) = n / 2 ^ (k + 1) / 2 ^ (s' + 1) := by
        rw [hA, hq2]
      have r : n / 2 ^ (s' + 2 + k) = n / 2 ^ (k + 1) / 2 ^ (s' + 1) := by
        rw [div_pow_add]; congr 2; omega
      rw [l, r]
    have e2 : (2 * (n / 2 ^ (k + 1)) + 1) / 2 ^ (s' + 2 - 1) = n / 2 ^ (s' + 2 + k - 1) := by
      have l : (2 * (n / 2 ^ (k + 1)) + 1) / 2 ^ (s' + 2 - 1) = n / 2 ^ (k + 1) / 2 ^ s' := by
        rw [show s' + 2 - 1 = s' + 1 by omega, hA, hq2]
      have r : n / 2 ^ (s' + 2 + k - 1) = n / 2 ^ (k + 1) / 2 ^ s' := by
        rw [div_pow_add]; congr 2; omega
      rw [l, r]
    have e3 : (2 * (n / 2 ^ (k + 1)) + 1) % 2 ^ (s' + 2 - 1) ≠ 0 := by
      rw [show s' + 2 - 1 = s' + 1 by omega]
      intro h0
      have hd : 2 ∣ 2 ^ (s' + 1) := ⟨2 ^ s', by rw [Nat.pow_succ, Nat.mul_comm]⟩
      have := Nat.mod_mod_of_dvd (2 * (n / 2 ^ (k + 1)) + 1) hd
      rw [h0, Nat.zero_mod] at this
      omega
    have e4 : n % 2 ^ (s' + 2 + k - 1) ≠ 0 := by
      intro h0
      apply h
      have hd : 2 ^ k ∣ 2 ^ (s' + 2 + k - 1) := Nat.pow_dvd_pow 2 (by omega)
      rw [← Nat.mod_mod_of_dvd n hd, h0, Nat.zero_mod]
    rw [e1, e2]
    simp only [e3, e4, ne_eq, not_false_eq_true, decide_true]

end Lua.Num.SfRef

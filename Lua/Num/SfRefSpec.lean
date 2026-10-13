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

end Lua.Num.SfRef

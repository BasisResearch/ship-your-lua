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

theorem log2_of_bounds {n L : Nat} (h1 : 2 ^ L ≤ n) (h2 : n < 2 ^ (L + 1)) : n.log2 = L :=
  (Nat.log2_eq_iff (by have := Nat.two_pow_pos L; omega)).2 ⟨h1, h2⟩

/-- Round to odd keeps the top bit: `log2 (rto n k) + k = log2 n` once `2^k ≤ n`. -/
theorem log2_rto {n k : Nat} (h : 2 ^ k ≤ n) : (rto n k).log2 + k = n.log2 := by
  have hq1 : 1 ≤ n / 2 ^ k := (Nat.le_div_iff_mul_le (Nat.two_pow_pos k)).2 (by omega)
  have hL1 := Nat.log2_self_le (n := n / 2 ^ k) (by omega)
  have hL2 := Nat.lt_log2_self (n := n / 2 ^ k)
  have hp : 2 ^ ((n / 2 ^ k).log2 + 1) = 2 * 2 ^ (n / 2 ^ k).log2 := by rw [Nat.pow_succ, Nat.mul_comm]
  have hR : (rto n k).log2 = (n / 2 ^ k).log2 := by
    apply log2_of_bounds
    · unfold rto; split
      · exact hL1
      · have : n / 2 ^ (k + 1) = n / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
        omega
    · unfold rto; split
      · exact hL2
      · have : n / 2 ^ (k + 1) = n / 2 ^ k / 2 := by rw [Nat.pow_succ, Nat.div_div_eq_div_mul]
        omega
  have hn : n.log2 = (n / 2 ^ k).log2 + k := by
    apply log2_of_bounds
    · rw [Nat.pow_add]
      exact Nat.le_trans (Nat.mul_le_mul_right _ hL1) (Nat.div_mul_le_self n (2 ^ k))
    · rw [show (n / 2 ^ k).log2 + k + 1 = ((n / 2 ^ k).log2 + 1) + k by omega, Nat.pow_add]
      have := Nat.lt_mul_div_succ n (Nat.two_pow_pos k)
      have h3 : (n / 2 ^ k + 1) * 2 ^ k ≤ 2 ^ ((n / 2 ^ k).log2 + 1) * 2 ^ k := Nat.mul_le_mul_right _ hL2
      rw [Nat.mul_comm (2 ^ k) (n / 2 ^ k + 1)] at this
      omega
  omega

theorem target_rto {n k : Nat} {e : Int} (hn : 0 < n) (h : e + k + 2 ≤ target (rto n k) (e + k)) :
    target n e = target (rto n k) (e + k) := by
  by_cases hk : 2 ^ k ≤ n
  · have := log2_rto hk
    unfold target; omega
  · have h1 : rto n k = 1 := rto_big hn (by omega)
    rw [h1] at h ⊢
    have hl : n.log2 < k := (Nat.log2_lt (by omega)).2 (by omega)
    unfold target at h ⊢
    have : (1 : Nat).log2 = 0 := by decide
    rw [this] at h ⊢
    omega

/-- **W1**: round to odd at `k` bits, two or more bits below the rounding
position, rounds as the exact value. -/
theorem round_rto (neg : Bool) (n k : Nat) (e : Int) (h : e + k + 2 ≤ target (rto n k) (e + k)) :
    round neg (rto n k) (e + k) false false = round neg n e false false := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; rw [rto_zero_n, round_zero, round_zero]
  have hT := target_rto hn h
  unfold round
  rw [← hT, if_pos (by omega), if_pos (by omega),
    shr_rto n k _ (by omega), show (target n e - (e + k)).toNat + k = (target n e - e).toNat by omega]

/-! ## The aligned sum and difference -/

theorem rto_add_even (A B k : Nat) (hA : A % 2 = 0) : A + rto B k = rto (A * 2 ^ k + B) k := by
  have h1 : (A * 2 ^ k + B) % 2 ^ k = B % 2 ^ k := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  have h2 : (A * 2 ^ k + B) / 2 ^ k = A + B / 2 ^ k := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k), Nat.add_comm]
  have h3 : (A * 2 ^ k + B) / 2 ^ (k + 1) = A / 2 + B / 2 ^ (k + 1) := by
    have : A * 2 ^ k = (A / 2) * 2 ^ (k + 1) := by
      rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm (A / 2) (2 ^ k), Nat.mul_assoc, Nat.mul_comm]
      congr 1; omega
    rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos (k + 1)), Nat.add_comm]
  unfold rto
  rw [h1]
  split
  · rw [h2]
  · rw [h3]; omega

/-- The machine's working scale of a biased exponent. -/
abbrev wsc (E : Nat) : Int := ((max E 1 : Nat) : Int) - 1078

/-- Same signs: `addAligned` rounds the exact aligned sum `A · 2^k + B` at the
smaller operand's scale. -/
theorem addAligned_eq (neg : Bool) (E A B k : Nat) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hAe : A % 2 = 0)
    (hA : A < 2 ^ 56) (hB : B < 2 ^ 56) (hk : k = 0 → A + B < 2 ^ 57) (hk1 : 1 ≤ k → 2 ^ 55 ≤ A)
    (hA2 : 2 ≤ E → 2 ^ 55 ≤ A) :
    addAligned neg E A B k = round neg (A * 2 ^ k + B) (wsc E - k) false false := by
  have hS := rto_add_even A B k hAe
  have hSlt : A + rto B k < 2 ^ 57 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; rw [rto_zero]; exact hk rfl
    · have := rto_le_half (n := B) h; omega
  unfold addAligned carryPack
  split
  · rename_i hc
    have hr1 : rto (A + rto B k) 1 < 2 ^ 56 := by rw [rto_one]; split <;> omega
    have hr2 : 2 ^ 55 ≤ rto (A + rto B k) 1 := by rw [rto_one]; split <;> omega
    rw [roundPack_eq neg (E + 1) _ hr1 (fun _ => hr2)]
    have e1 : ((max (E + 1) 1 : Nat) : Int) - 1078 = wsc E + 1 := by simp only [wsc]; omega
    have hw := target_work (E := E + 1) (by omega) hr1 (fun _ => hr2)
    rw [e1] at hw
    have h1 := round_rto neg (A + rto B k) 1 (wsc E) (by rw [Int.natCast_one, hw]; omega)
    rw [Int.natCast_one] at h1
    rw [e1, h1]
    rw [hS, show wsc E = (wsc E - k) + k by omega, round_rto neg _ k _ (by
      rw [← hS, show wsc E - k + k = wsc E by omega]
      have hl : (A + rto B k).log2 = 56 := log2_of_bounds hc (by omega)
      unfold target; omega)]
    try rw [show wsc E - (k : Int) + k - k = wsc E - k by omega]
  · rename_i hc
    rw [roundPack_eq neg E _ (by omega) (fun h => by have := hA2 h; omega)]
    rw [hS, show ((max E 1 : Nat) : Int) - 1078 = (wsc E - k) + k by simp only [wsc]; omega,
      round_rto neg _ k _ (by
        rw [← hS, show wsc E - k + k = ((max E 1 : Nat) : Int) - 1078 by simp only [wsc]; omega]
        rcases Nat.eq_zero_or_pos (A + rto B k) with h0 | h0
        · unfold target; omega
        · rw [target_work h0 (by omega) (fun h => by have := hA2 h; omega)]; omega)]
    try rw [show wsc E - (k : Int) + k - k = wsc E - k by omega]

theorem round_scale' (neg : Bool) (n j : Nat) (e : Int) :
    round neg n e false false = round neg (n * 2 ^ j) (e - j) false false := (round_scale neg n j e).symm

/-- A difference, rounded or renormalised, is `F64.round` of it. -/
theorem subPack_eq (neg : Bool) (E S : Nat) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS0 : 0 < S) (hS : S < 2 ^ 56) :
    subPack neg E S = round neg S (wsc E) false false := by
  unfold subPack
  split
  · rename_i h
    rw [roundPack_eq neg E S hS (fun _ => h)]
  · rename_i h
    have hL : S.log2 < 55 := (Nat.log2_lt (by omega)).2 (by omega)
    have hN := norm_bounds hS0 hS
    unfold normPack
    dsimp only
    split
    · rename_i hz
      rw [roundPack_eq neg (E - (55 - S.log2)) _ hN.2 (fun _ => hN.1),
        round_scale' neg S (55 - S.log2) (wsc E)]
      congr 1; simp only [wsc]; omega
    · rename_i hz
      have hlt : S * 2 ^ (E - 1) < 2 ^ 56 := by
        have h1 : S < 2 ^ (S.log2 + 1) := Nat.lt_log2_self
        have h2 : S * 2 ^ (E - 1) < 2 ^ (S.log2 + 1) * 2 ^ (E - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 (Nat.two_pow_pos _)
        rw [← Nat.pow_add] at h2
        exact Nat.lt_of_lt_of_le h2 (Nat.pow_le_pow_right (by decide) (by omega))
      rw [roundPack_eq neg 0 _ hlt (fun h => by omega), round_scale' neg S (E - 1) (wsc E)]
      congr 1; simp only [wsc]; omega

theorem rto_sub_even (A B k : Nat) (hA : A % 2 = 0) (hAB : B < A * 2 ^ k) :
    A - rto B k = rto (A * 2 ^ k - B) k := by
  have hP := Nat.two_pow_pos k
  have hB := Nat.div_add_mod B (2 ^ k)
  have hr := Nat.mod_lt B hP
  have hq : B / 2 ^ k < A := by
    rw [Nat.div_lt_iff_lt_mul hP]; exact hAB
  have hP1 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [Nat.pow_succ]
  by_cases h0 : B % 2 ^ k = 0
  · have hN : A * 2 ^ k - B = (A - B / 2 ^ k) * 2 ^ k := by
      rw [Nat.sub_mul]; rw [h0, Nat.add_zero] at hB; rw [Nat.mul_comm (B / 2 ^ k)]; omega
    have h1 : rto B k = B / 2 ^ k := rto_exact h0
    have h2 : rto (A * 2 ^ k - B) k = A - B / 2 ^ k := by
      rw [rto_exact (by rw [hN]; exact Nat.mul_mod_left _ _), hN, Nat.mul_div_cancel _ hP]
    rw [h1, h2]
  · have hN : A * 2 ^ k - B = (A - B / 2 ^ k - 1) * 2 ^ k + (2 ^ k - B % 2 ^ k) := by
      have e : (A - B / 2 ^ k - 1) * 2 ^ k + 2 ^ k = (A - B / 2 ^ k) * 2 ^ k := by
        rw [← Nat.succ_mul]; congr 1; omega
      have e2 : (A - B / 2 ^ k) * 2 ^ k + B / 2 ^ k * 2 ^ k = A * 2 ^ k := by
        rw [← Nat.add_mul]; congr 1; omega
      rw [Nat.mul_comm (2 ^ k) (B / 2 ^ k)] at hB
      omega
    have hm : (A * 2 ^ k - B) % 2 ^ k = 2 ^ k - B % 2 ^ k := by
      rw [hN, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    have hd1 : (A * 2 ^ k - B) / 2 ^ k = A - B / 2 ^ k - 1 := by
      rw [hN, Nat.add_comm, Nat.add_mul_div_right _ _ hP,
        Nat.div_eq_of_lt (by omega : 2 ^ k - B % 2 ^ k < 2 ^ k), Nat.zero_add]
    have hd : (A * 2 ^ k - B) / 2 ^ (k + 1) = (A - B / 2 ^ k - 1) / 2 := by
      rw [hP1, ← Nat.div_div_eq_div_mul, hd1]
    have hdB : B / 2 ^ (k + 1) = B / 2 ^ k / 2 := by rw [hP1, Nat.div_div_eq_div_mul]
    unfold rto
    rw [if_neg h0, if_neg (by omega), hd, hdB]
    omega

/-- Different signs, `A · 2^k > B`: `subMag` rounds the exact aligned difference. -/
theorem subMag_eq (neg : Bool) (E A B k : Nat) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hAe : A % 2 = 0)
    (hB8 : B % 8 = 0) (hA : A < 2 ^ 56) (hB : B < 2 ^ 56) (hAB : B < A * 2 ^ k)
    (hk1 : 1 ≤ k → 2 ^ 55 ≤ A) :
    subMag neg E A B k = round neg (A * 2 ^ k - B) (wsc E - k) false false := by
  unfold subMag
  have hS := rto_sub_even A B k hAe hAB
  by_cases hk : k ≤ 3
  · have hex : B % 2 ^ k = 0 := by
      have : 2 ^ k ∣ 8 := ⟨2 ^ (3 - k), by rw [← Nat.pow_add, show k + (3 - k) = 3 by omega]⟩
      rw [← Nat.mod_mod_of_dvd B this, hB8, Nat.zero_mod]
    have h1 : rto B k = B / 2 ^ k := rto_exact hex
    have hS0 : 0 < A - B / 2 ^ k := by
      have : B / 2 ^ k < A := by rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]; exact hAB
      omega
    rw [h1, subPack_eq neg E _ hE1 hE hS0 (by omega), round_scale' neg _ k (wsc E)]
    congr 2
    rw [Nat.sub_mul, Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hex)]
  · have hR := rto_le_half (n := B) (k := k) (by omega)
    have hR4 : rto B k ≤ B / 16 + 1 := by
      have := rto_le B k
      have : B / 2 ^ k ≤ B / 16 := Nat.div_le_div_left (by
        calc 16 = 2 ^ 4 := rfl
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)) (by decide)
      omega
    have hA55 := hk1 (by omega)
    have hS0 : 2 ^ 54 ≤ A - rto B k := by omega
    rw [subPack_eq neg E _ hE1 hE (by omega) (by omega), hS,
      show wsc E = (wsc E - k) + k by omega]
    rw [round_rto neg _ k _ (by
      rw [← hS, show wsc E - k + k = wsc E by omega]
      have hl : 54 ≤ (A - rto B k).log2 := by
        by_cases hc : (A - rto B k).log2 < 54
        · have := (Nat.log2_lt (n := A - rto B k) (k := 54) (by omega)).1 hc; omega
        · omega
      unfold target; omega)]
    try rw [show wsc E - (k : Int) + k - k = wsc E - k by omega]

/-! ## Finite operands: the reference is `normalize` of the aligned sum -/

/-- The decoded mantissa and exponent of fields `(e, f)` (`F64.cls`). -/
abbrev cm (e f : Nat) : Nat := if e = 0 then f else f + 2 ^ 52
abbrev ce (e : Nat) : Int := if e = 0 then -1074 else (e : Int) - 1075

theorem mant_cm (e f : Nat) : mant e f = cm e f * 2 ^ 3 := by unfold mant cm; split <;> omega
theorem ce_wsc (e : Nat) : ce e = wsc e + 3 := by unfold ce wsc; split <;> omega

theorem sgn_add (s : Bool) (x y : Nat) : sgnApply s x + sgnApply s y = sgnApply s (x + y) := by
  unfold sgnApply; cases s <;> simp <;> omega
theorem sgn_sub (s : Bool) (x y : Nat) (h : y < x) : sgnApply s x + sgnApply (!s) y = sgnApply s (x - y) := by
  unfold sgnApply; cases s <;> simp <;> omega
theorem sgn_sub' (s : Bool) (x y : Nat) (h : x < y) : sgnApply s x + sgnApply (!s) y = sgnApply (!s) (y - x) := by
  unfold sgnApply; cases s <;> simp <;> omega
theorem norm_sgn (s : Bool) (x : Nat) (hx : 0 < x) (t : Int) :
    normalize (sgnApply s x) t false = round s x t false false := by
  unfold normalize sgnApply
  cases s
  · simp only [Bool.false_eq_true, ite_false]
    rw [if_neg (by omega)]
    have : decide ((x : Int) < 0) = false := by simp
    rw [this]; simp
  · simp only [ite_true]
    rw [if_neg (by omega)]
    have : decide (-(x : Int) < 0) = true := by simp; omega
    rw [this]; simp
theorem align_eq (m : Nat) (e t : Int) : align m e t = m * 2 ^ (e - t).toNat := by
  unfold align; rw [Nat.shiftLeft_eq]

theorem cm_bounds (e f : Nat) (hf : f < 2 ^ 52) : cm e f < 2 ^ 53 ∧ (e ≠ 0 → 2 ^ 52 ≤ cm e f) := by
  unfold cm; split <;> omega

/-- Same signs, `eb ≤ ea`: the reference rounds the exact sum at `b`'s exponent. -/
theorem add_ge (s : Bool) (ea fa eb fb : Nat) (hea : ea ≤ 2046) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52)
    (h : eb ≤ ea) :
    addAligned s (max ea 1) (mant ea fa) (mant eb fb) (max ea 1 - max eb 1) =
      round s (cm ea fa * 2 ^ (ce ea - ce eb).toNat + cm eb fb) (ce eb) false false := by
  have ha := cm_bounds ea fa hfa
  have hb := cm_bounds eb fb hfb
  rw [addAligned_eq s _ _ _ _ (by omega) (by omega) (by rw [mant_cm]; omega) (by rw [mant_cm]; omega)
    (by rw [mant_cm]; omega) (fun _ => by rw [mant_cm, mant_cm]; omega)
    (fun hk => by rw [mant_cm]; have := ha.2 (by omega); omega)
    (fun hk => by rw [mant_cm]; have := ha.2 (by omega); omega)]
  rw [mant_cm, mant_cm, show cm ea fa * 2 ^ 3 * 2 ^ (max ea 1 - max eb 1) + cm eb fb * 2 ^ 3 =
      (cm ea fa * 2 ^ (max ea 1 - max eb 1) + cm eb fb) * 2 ^ 3 by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (2 ^ 3) (2 ^ (max ea 1 - max eb 1))],
    show wsc (max ea 1) - ((max ea 1 - max eb 1 : Nat) : Int) = ce eb - ((3 : Nat) : Int) by
      rw [ce_wsc]; unfold wsc; omega,
    round_scale, show (ce ea - ce eb).toNat = max ea 1 - max eb 1 by unfold ce; split <;> split <;> omega]

/-- Different signs, `|b| < |a|` (aligned at `b`'s exponent): the reference
rounds the exact difference, with `a`'s sign. -/
theorem sub_gt (s : Bool) (ea fa eb fb : Nat) (hea : ea ≤ 2046) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52)
    (h : eb ≤ ea) (hm : cm eb fb < cm ea fa * 2 ^ (max ea 1 - max eb 1)) :
    subMag s (max ea 1) (mant ea fa) (mant eb fb) (max ea 1 - max eb 1) =
      round s (cm ea fa * 2 ^ (ce ea - ce eb).toNat - cm eb fb) (ce eb) false false := by
  have ha := cm_bounds ea fa hfa
  have hb := cm_bounds eb fb hfb
  rw [subMag_eq s _ _ _ _ (by omega) (by omega) (by rw [mant_cm]; omega) (by rw [mant_cm]; omega)
    (by rw [mant_cm]; omega) (by rw [mant_cm]; omega)
    (by rw [mant_cm, mant_cm, Nat.mul_assoc, Nat.mul_comm (2 ^ 3), ← Nat.mul_assoc]; exact Nat.mul_lt_mul_of_pos_right hm (by decide))
    (fun hk => by rw [mant_cm]; have := ha.2 (by omega); omega)]
  rw [mant_cm, mant_cm, show cm ea fa * 2 ^ 3 * 2 ^ (max ea 1 - max eb 1) - cm eb fb * 2 ^ 3 =
      (cm ea fa * 2 ^ (max ea 1 - max eb 1) - cm eb fb) * 2 ^ 3 by
      rw [Nat.sub_mul, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm (2 ^ 3) (2 ^ (max ea 1 - max eb 1))],
    show wsc (max ea 1) - ((max ea 1 - max eb 1 : Nat) : Int) = ce eb - ((3 : Nat) : Int) by
      rw [ce_wsc]; unfold wsc; omega,
    round_scale, show (ce ea - ce eb).toNat = max ea 1 - max eb 1 by unfold ce; split <;> split <;> omega]

theorem ce_le {ea eb : Nat} (h : ea ≤ eb) : ce ea ≤ ce eb := by unfold ce; split <;> split <;> omega
theorem cm_pos {e f : Nat} (h : e ≠ 0 ∨ f ≠ 0) : 0 < cm e f := by unfold cm; split <;> omega

/-- The aligned sum of two finite operands, at the smaller exponent `ce eb ≤ ce ea`. -/
theorem fin_rhs (sa sb : Bool) (ea fa eb fb : Nat) (h : eb ≤ ea) :
    sgnApply sa (align (cm ea fa) (ce ea) (min (ce ea) (ce eb))) +
        sgnApply sb (align (cm eb fb) (ce eb) (min (ce ea) (ce eb))) =
      sgnApply sa (cm ea fa * 2 ^ (ce ea - ce eb).toNat) + sgnApply sb (cm eb fb) := by
  rw [Int.min_eq_right (ce_le h), align_eq, align_eq, Int.sub_self]; simp

theorem fin_rhs' (sa sb : Bool) (ea fa eb fb : Nat) (h : ea ≤ eb) :
    sgnApply sa (align (cm ea fa) (ce ea) (min (ce ea) (ce eb))) +
        sgnApply sb (align (cm eb fb) (ce eb) (min (ce ea) (ce eb))) =
      sgnApply sb (cm eb fb * 2 ^ (ce eb - ce ea).toNat) + sgnApply sa (cm ea fa) := by
  rw [Int.min_eq_left (ce_le h), align_eq, align_eq, Int.sub_self, Int.add_comm]; simp

theorem pow_ce (ea eb : Nat) (h : eb ≤ ea) : (ce ea - ce eb).toNat = max ea 1 - max eb 1 := by
  unfold ce; split <;> split <;> omega

theorem cm_zero (f : Nat) : cm 0 f = f := by simp [cm]

/-- **(b2) on finite operands**: the reference is `F64.add`'s `normalize` of the
exact aligned sum. -/
theorem addFields_fin (sa sb : Bool) (ea fa eb fb : Nat) (hea : ea ≤ 2046) (heb : eb ≤ 2046)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h0 : (ea ≠ 0 ∨ fa ≠ 0) ∨ (eb ≠ 0 ∨ fb ≠ 0)) :
    addFields sa ea fa sb eb fb =
      normalize (sgnApply sa (align (cm ea fa) (ce ea) (min (ce ea) (ce eb))) +
        sgnApply sb (align (cm eb fb) (ce eb) (min (ce ea) (ce eb)))) (min (ce ea) (ce eb)) false := by
  have hp : 0 < cm ea fa ∨ 0 < cm eb fb := by
    rcases h0 with h | h
    · exact Or.inl (cm_pos h)
    · exact Or.inr (cm_pos h)
  have hpk : ∀ x k : Nat, 0 < x → 0 < x * 2 ^ k := fun x k hx => Nat.mul_pos hx (Nat.two_pow_pos k)
  have hpa := fun h => hpk (cm ea fa) ((ce ea - ce eb).toNat) h
  have hpb := fun h => hpk (cm eb fb) ((ce eb - ce ea).toNat) h
  have hba := cm_bounds ea fa hfa
  have hbb := cm_bounds eb fb hfb
  unfold addFields; dsimp only
  by_cases hs : sa = sb
  · subst hs; rw [if_pos rfl]
    rcases Nat.lt_trichotomy ea eb with h | h | h
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), add_ge _ _ _ _ _ heb hfb hfa (by omega),
        fin_rhs' _ _ _ _ _ _ (by omega), sgn_add, norm_sgn _ _ (by omega), Nat.add_comm,
        Int.min_eq_left (ce_le (by omega))]
    · subst h
      rw [if_pos rfl, if_neg (by omega), show (0 : Nat) = max ea 1 - max ea 1 by omega,
        add_ge _ _ _ _ _ hea hfa hfb (by omega), fin_rhs _ _ _ _ _ _ (by omega), sgn_add,
        norm_sgn _ _ (by omega), Int.min_self]
    · rw [if_neg (by omega), if_pos h, if_neg (by omega), add_ge _ _ _ _ _ hea hfa hfb (by omega),
        fin_rhs _ _ _ _ _ _ (by omega), sgn_add, norm_sgn _ _ (by omega), Int.min_eq_right (ce_le (by omega))]
  · rw [if_neg hs]
    have hsb : sb = !sa := by cases sa <;> cases sb <;> simp_all
    subst hsb
    rcases Nat.lt_trichotomy ea eb with h | h | h
    · have hm : cm ea fa < cm eb fb * 2 ^ (max eb 1 - max ea 1) := by
        have hb52 := hbb.2 (by omega)
        rcases Nat.eq_zero_or_pos (max eb 1 - max ea 1) with hk | hk
        · have h0 : ea = 0 := by omega
          subst h0
          rw [hk, Nat.pow_zero, Nat.mul_one, cm_zero]; omega
        · have h2 : 2 ≤ 2 ^ (max eb 1 - max ea 1) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ _ := Nat.pow_le_pow_right (by decide) hk
          have h3 : cm eb fb * 2 ≤ cm eb fb * 2 ^ (max eb 1 - max ea 1) := Nat.mul_le_mul_left _ h2
          omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), sub_gt _ _ _ _ _ heb hfb hfa (by omega) hm,
        fin_rhs' _ _ _ _ _ _ (by omega), Int.add_comm, sgn_sub' _ _ _ (by rw [pow_ce _ _ (by omega)]; exact hm),
        norm_sgn _ _ (by rw [pow_ce _ _ (by omega)]; omega), Int.min_eq_left (ce_le (by omega))]
    · subst h
      rw [if_pos rfl, if_neg (by omega)]
      have hmant : ∀ f g, mant ea f = mant ea g ↔ f = g := fun f g => by unfold mant; split <;> omega
      have hmant2 : ∀ f g, mant ea f < mant ea g ↔ f < g := fun f g => by unfold mant; split <;> omega
      have hcm2 : ∀ f g, cm ea f < cm ea g ↔ f < g := fun f g => by unfold cm; split <;> omega
      rcases Nat.lt_trichotomy fa fb with hf | hf | hf
      · rw [if_neg (by rw [hmant]; omega), if_neg (by rw [hmant2]; omega),
          show (0 : Nat) = max ea 1 - max ea 1 by omega,
          sub_gt _ _ _ _ _ hea hfb hfa (by omega) (by rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one, hcm2]; exact hf),
          fin_rhs' _ _ _ _ _ _ (by omega), Int.add_comm,
          sgn_sub' _ _ _ (by rw [Int.sub_self]; simp; rw [hcm2]; exact hf),
          norm_sgn _ _ (by rw [Int.sub_self]; simp; have := (hcm2 fa fb).2 hf; omega), Int.min_self]
      · subst hf
        rw [if_pos rfl, fin_rhs _ _ _ _ _ _ (by omega)]
        unfold normalize
        rw [if_pos (by unfold sgnApply; cases sa <;> simp <;> omega)]
      · rw [if_neg (by rw [hmant]; omega), if_pos (by rw [hmant2]; omega),
          show (0 : Nat) = max ea 1 - max ea 1 by omega,
          sub_gt _ _ _ _ _ hea hfa hfb (by omega) (by rw [Nat.sub_self, Nat.pow_zero, Nat.mul_one, hcm2]; exact hf),
          fin_rhs _ _ _ _ _ _ (by omega),
          sgn_sub _ _ _ (by rw [Int.sub_self]; simp; rw [hcm2]; exact hf),
          norm_sgn _ _ (by rw [Int.sub_self]; simp; have := (hcm2 fb fa).2 hf; omega), Int.min_self]
    · have hm : cm eb fb < cm ea fa * 2 ^ (max ea 1 - max eb 1) := by
        have ha52 := hba.2 (by omega)
        rcases Nat.eq_zero_or_pos (max ea 1 - max eb 1) with hk | hk
        · have h0 : eb = 0 := by omega
          subst h0
          rw [hk, Nat.pow_zero, Nat.mul_one, cm_zero]; omega
        · have h2 : 2 ≤ 2 ^ (max ea 1 - max eb 1) := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ _ := Nat.pow_le_pow_right (by decide) hk
          have h3 : cm ea fa * 2 ≤ cm ea fa * 2 ^ (max ea 1 - max eb 1) := Nat.mul_le_mul_left _ h2
          omega
      rw [if_neg (by omega), if_pos h, if_neg (by omega), sub_gt _ _ _ _ _ hea hfa hfb (by omega) hm,
        fin_rhs _ _ _ _ _ _ (by omega), sgn_sub _ _ _ (by rw [pow_ce _ _ (by omega)]; exact hm),
        norm_sgn _ _ (by rw [pow_ce _ _ (by omega)]; omega), Int.min_eq_right (ce_le (by omega))]

end Lua.Num.SfRef

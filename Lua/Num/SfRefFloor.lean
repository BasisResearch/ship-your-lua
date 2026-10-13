import Lua.Num.SfRefSpec

/-!
# `SfRef.floor`: newlib's fdlibm `floor` over the fields (lane float-sf3, (b2))

libm's `floor` (newlib 4.5.0 `libm/math/s_floor.c`, entry `0x8002bb14` in
the ELF) works on the two 32-bit halves `i0:i1` of its argument with
`j0 = e - 1023`, the unbiased exponent:

* `j0 = 0x400` (`e = 2047`): `x + x` (`__adddf3`: `∞` stays, a NaN is the
  canonical `qnan`);
* `j0 > 51` (`1075 ≤ e`): `x` is integral, returned;
* `j0 < 0` (`e < 1023`): `+0` for `x ≥ +0`, `-0` for `-0`, `-1` for a
  negative nonzero `x` (behind `huge + x > 0`, which holds:
  `Lua/Vm/Fn/SfRefFloor.lean`);
* `0 ≤ j0 ≤ 51`: the `k = 52 - j0 = 1075 - e` fraction bits below the binary
  point are cleared, after adding `2^k` when `x < 0` (the carry moves into
  the exponent field by itself); an integral `x` is returned.

`floorFields` transcribes it over the fields `(s, e, f)`; the cleared word is
the field value `e · 2^52 + f` with its low `k` bits cleared. (b2) is
`floor_cls`: the reference is `x` itself, `qnan`, or the exact integer
`normalize (±⌊|x|⌋ or -⌈|x|⌉) 0`, which `Lua.Num.floor` names on the model
(`Lua/Vm/Fn/SfRefFloor.lean`, `floor_model`).
-/

namespace Lua.Num.SfRef

set_option linter.deprecated false

open F64

/-- fdlibm `floor` (`s_floor.c`) over the fields of its argument. -/
def floorFields (s : Bool) (e f : Nat) : F64 :=
  if e = 2047 then (if f = 0 then infty s else qnan)
  else if 1075 ≤ e then bits s e f
  else if e < 1023 then
    (if s then (if e = 0 ∧ f = 0 then bits true 0 0 else bits true 1023 0) else bits false 0 0)
  else if f % 2 ^ (1075 - e) = 0 then bits s e f
  else if s then bits true 0 ((e * 2 ^ 52 + f) / 2 ^ (1075 - e) * 2 ^ (1075 - e) + 2 ^ (1075 - e))
  else bits false 0 ((e * 2 ^ 52 + f) / 2 ^ (1075 - e) * 2 ^ (1075 - e))

/-- `SfRef.floor`. -/
def floor (x : F64) : F64 := floorFields x.sign x.bexp x.frac

/-- A normal datum whose value is the integer `c` (`(2^52 + fr) = c · 2^j` at
`be - 1075 = -j`) is `c` rounded exactly. -/
theorem bits_round (s : Bool) (be fr c j : Nat) (hbe1 : 1 ≤ be) (hbe : be ≤ 2046) (hfr : fr < 2 ^ 52)
    (hc : fr + 2 ^ 52 = c * 2 ^ j) (hj : be + j = 1075) : bits s be fr = roundExact s c 0 := by
  have ⟨h1, h2, h3⟩ := fields_bits s be fr (by omega) hfr
  have hr := round_fields (bits s be fr) (by omega) (by omega)
  rw [h1, h2, h3] at hr
  have hs := round_scale s c j 0
  have ecm : cm be fr = fr + 2 ^ 52 := by unfold cm; rw [if_neg (by omega)]
  have ece : ce be = 0 - (j : Int) := by unfold ce; rw [if_neg (by omega)]; omega
  rw [ecm, ece, hc, hs] at hr
  exact hr.symm

theorem normalize_pos (s : Bool) (c : Nat) (hc : 0 < c) :
    normalize (sgnApply s c) 0 false = roundExact s c 0 := by
  unfold normalize sgnApply
  cases s
  · simp only [Bool.false_eq_true, ite_false]
    rw [if_neg (by omega)]
    congr 1
  · simp only [ite_true]
    rw [if_neg (by omega)]
    congr 1
    · simp; omega
    · omega

/-- The integer the cleared word denotes (`1023 ≤ e ≤ 1074`, `k = 1075 - e`). -/
theorem floor_mid (s : Bool) (e f : Nat) (he1 : 1023 ≤ e) (he2 : e < 1075) (hf : f < 2 ^ 52) :
    floorFields s e f = normalize (sgnApply s ((f + 2 ^ 52) / 2 ^ (1075 - e) +
      (if s = true ∧ (f + 2 ^ 52) % 2 ^ (1075 - e) ≠ 0 then 1 else 0))) 0 false := by
  unfold floorFields
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  obtain ⟨k, hk⟩ : ∃ k, 1075 - e = k := ⟨_, rfl⟩
  rw [hk]
  have hk1 : 1 ≤ k := by omega
  have hk52 : k ≤ 52 := by omega
  obtain ⟨K, hKe⟩ : ∃ K, 2 ^ k = K := ⟨_, rfl⟩
  obtain ⟨Q, hQe⟩ : ∃ Q, 2 ^ (52 - k) = Q := ⟨_, rfl⟩
  have hKQ : 2 ^ 52 = K * Q := by rw [← hKe, ← hQe, ← Nat.pow_add]; congr 1; omega
  have hK : 0 < K := hKe ▸ Nat.two_pow_pos k
  have hQ : 0 < Q := hQe ▸ Nat.two_pow_pos (52 - k)
  rw [hKe]
  have hm : (f + 2 ^ 52) / K = f / K + Q := by rw [hKQ, Nat.add_mul_div_left _ _ hK]
  have hmod : (f + 2 ^ 52) % K = f % K := by rw [hKQ, Nat.add_mul_mod_self_left]
  have hw : (e * 2 ^ 52 + f) / K = f / K + e * Q := by
    rw [hKQ, show e * (K * Q) + f = f + K * (e * Q) by rw [Nat.mul_left_comm, Nat.add_comm],
      Nat.add_mul_div_left _ _ hK]
  have hfK : K * (f / K) + f % K = f := Nat.div_add_mod f K
  have hfQ : f / K < Q := by
    rw [Nat.div_lt_iff_lt_mul hK, Nat.mul_comm, ← hKQ]; exact hf
  have hQK : (f / K + Q) * K = K * (f / K) + 2 ^ 52 := by
    rw [hKQ, Nat.add_mul, Nat.mul_comm (f / K) K, Nat.mul_comm Q K]
  rw [hm, hmod]
  have hpos : 0 < f / K + Q := Nat.lt_of_lt_of_le hQ (Nat.le_add_left _ _)
  by_cases hi : f % K = 0
  · -- integral: `x` itself
    rw [if_pos hi]
    simp only [hi, ne_eq, not_true_eq_false, and_false, ite_false, Nat.add_zero]
    rw [normalize_pos _ _ hpos]
    exact bits_round s e f _ k (by omega) (by omega) hf (by rw [hKe, hQK]; omega) (by omega)
  · rw [if_neg hi]
    have hKK : K * (f / K) < 2 ^ 52 := by omega
    cases s
    · -- positive: the low `k` bits cleared
      simp only [Bool.false_eq_true, ite_false, false_and, Nat.add_zero]
      rw [normalize_pos _ _ hpos, hw]
      rw [show (f / K + e * Q) * K = e * 2 ^ 52 + K * (f / K) by
        rw [hKQ, Nat.add_mul, Nat.mul_comm (f / K) K, Nat.mul_assoc, Nat.mul_comm Q K]; omega]
      rw [← bits_zero]
      exact bits_round false e (K * (f / K)) _ k (by omega) (by omega) hKK
        (by rw [hKe, hQK]) (by omega)
    · -- negative: one more, the carry into the exponent field when it overflows the fraction
      simp only [ite_true, ne_eq, hi, not_false_eq_true, and_self]
      rw [normalize_pos _ _ (by omega), hw]
      have hle : K * (f / K) + K ≤ 2 ^ 52 := by
        rw [hKQ]
        have : K * (f / K + 1) ≤ K * Q := Nat.mul_le_mul_left K hfQ
        rw [Nat.mul_add, Nat.mul_one] at this; exact this
      rw [show (f / K + e * Q) * K + K = e * 2 ^ 52 + (K * (f / K) + K) by
        rw [hKQ, Nat.add_mul, Nat.mul_comm (f / K) K, Nat.mul_assoc, Nat.mul_comm Q K]; omega]
      by_cases hc : K * (f / K) + K < 2 ^ 52
      · rw [← bits_zero]
        exact bits_round true e (K * (f / K) + K) _ k (by omega) (by omega) hc
          (by rw [hKe, Nat.add_mul, hQK, Nat.one_mul]; omega) (by omega)
      · -- `f / K + 1 = Q`: the word is `(e + 1) · 2^52`, the value `2 Q = 2^(53 - k)`
        have he : K * (f / K) + K = 2 ^ 52 := by omega
        rw [he, show e * 2 ^ 52 + 2 ^ 52 = (e + 1) * 2 ^ 52 + 0 by rw [Nat.add_mul, Nat.one_mul, Nat.add_zero],
          ← bits_zero]
        have hq : f / K + 1 = Q := by
          have h2 : K * (f / K + 1) = K * Q := by rw [Nat.mul_add, Nat.mul_one, he, hKQ]
          exact Nat.eq_of_mul_eq_mul_left hK h2
        have hk2 : 2 ^ k = 2 * 2 ^ (k - 1) := by
          rw [← Nat.pow_succ']; congr 1; omega
        exact bits_round true (e + 1) 0 _ (k - 1) (by omega) (by omega) (by decide)
          (by
            rw [show f / K + Q + 1 = 2 * Q by omega, Nat.zero_add, hKQ, ← hKe, hk2]
            exact Nat.mul_right_comm _ _ _)
          (by omega)

/-- **(b2) for `floor`**, by the argument's class: `x` itself (`±∞`, `±0`, an
integral value), `qnan`, or the exact integer `±⌊|x|⌋` (`x ≥ 0`) or
`-⌈|x|⌉` (`x < 0`), which is `Lua.Num.floor` on the model. -/
theorem floor_cls (x : F64) : floor x = match x.cls with
    | .nan => qnan
    | .inf _ => x
    | .zero _ => x
    | .fin s m e => if 0 ≤ e then x else
        normalize (sgnApply s (m / 2 ^ (-e).toNat +
          (if s = true ∧ m % 2 ^ (-e).toNat ≠ 0 then 1 else 0))) 0 false := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hx := bits_self x
  unfold floor
  by_cases h2047 : x.bexp = 2047
  · unfold floorFields cls
    rw [if_pos h2047, if_pos h2047]
    by_cases hf0 : x.frac = 0
    · rw [if_pos hf0, if_pos hf0]
      simp only []
      unfold infty; rw [← h2047, ← hf0, hx]
    · rw [if_neg hf0, if_neg hf0]
  by_cases hhi : 1075 ≤ x.bexp
  · unfold floorFields cls
    rw [if_neg h2047, if_pos hhi, if_neg h2047, if_neg (by omega)]
    simp only []
    rw [if_pos (by omega), hx]
  by_cases hlo : x.bexp < 1023
  · by_cases hz : x.bexp = 0 ∧ x.frac = 0
    · unfold floorFields cls
      rw [if_neg h2047, if_neg hhi, if_pos hlo, if_neg h2047, if_pos hz.1, if_pos hz.2]
      simp only []
      cases hs : x.sign
      · rw [hz.1, hz.2, hs] at hx; simp only [Bool.false_eq_true, ite_false]; exact hx
      · rw [hz.1, hz.2, hs] at hx; simp only [ite_true]; rw [if_pos hz]; exact hx
    · -- `0 < |x| < 1`
      have hm : ∀ m : Nat, ∀ e : Int, x.cls = .fin x.sign m e → m < 2 ^ 53 ∧ 0 < m ∧ e ≤ -53 := by
        intro m e hc
        have ⟨ok, _⟩ := cls_fin hc
        refine ⟨ok.lt, ok.pos, ?_⟩
        unfold cls at hc
        rw [if_neg h2047] at hc
        split at hc
        · split at hc
          · cases hc
          · cases hc; omega
        · cases hc; omega
      have hcls : ∃ m e, x.cls = .fin x.sign m e := by
        unfold cls; rw [if_neg h2047]
        split
        · rw [if_neg (by omega)]; exact ⟨_, _, rfl⟩
        · exact ⟨_, _, rfl⟩
      obtain ⟨m, e, hc⟩ := hcls
      obtain ⟨hm1, hm0, he⟩ := hm m e hc
      rw [hc]
      simp only []
      rw [if_neg (by omega)]
      have hk : 2 ^ 53 ≤ 2 ^ (-e).toNat := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      unfold floorFields
      rw [if_neg h2047, if_neg hhi, if_pos hlo]
      cases x.sign
      · simp only [Bool.false_eq_true, ite_false, false_and, Nat.add_zero]
        rfl
      · simp only [ite_true, ne_eq, true_and, if_neg hz]
        rw [if_pos (by omega), Nat.zero_add, normalize_pos _ _ (by decide)]
        exact bits_round true 1023 0 1 52 (by decide) (by decide) (by decide) (by decide) (by decide)
  · -- `1 ≤ |x| < 2^52`, not integral in general
    have hc : x.cls = .fin x.sign (x.frac + 2 ^ 52) ((x.bexp : Int) - 1075) := by
      unfold cls; rw [if_neg h2047, if_neg (by omega)]
    rw [hc]
    simp only []
    rw [if_neg (by omega), floor_mid _ _ _ (by omega) (by omega) hf,
      show (-((x.bexp : Int) - 1075)).toNat = 1075 - x.bexp by omega]

end Lua.Num.SfRef

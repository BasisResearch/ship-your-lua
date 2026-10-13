import Lua.Num.SfRefMul

/-!
# `SfRef.div`: soft-fp's `__divdf3` over the fields (lane float-sf4, (b2))

libgcc's `__divdf3` (`soft-fp/divdf3.c`: `FP_UNPACK_D`, `FP_DIV_D`,
`FP_PACK_D`; `soft-fp/op-common.h` `_FP_DIV`, `_FP_UNPACK_CANONICAL`,
`_FP_PACK_CANONICAL`; `soft-fp/op-1.h` `_FP_DIV_MEAT_1_udiv_norm`;
`longlong.h` `__udiv_qrnnd_c`, the generic `udiv_qrnnd` of a target without
a hardware divide), transcribed over the operands' fields:

* `qrHalf`/`udivQrnnd`: `__udiv_qrnnd_c`, Knuth's algorithm D on two 32-bit
  digits of a normalised 64-bit divisor, every word operation mod `2^64` as
  the machine performs it (the estimate `u / d1`, the product `q · d0`, at
  most two corrections, the carry test `r ≥ d`);
* `divMeat`: `_FP_DIV_MEAT_1_udiv_norm`: the divisor `Y · 2^8` normalised,
  the dividend `X · 2^64` (`X < Y`, `R_e` one lower) or `X · 2^63`, and
  `R_f = q | (r != 0)`: the quotient with a remainder sticky bit;
* `divNorm`: `_FP_DIV`'s normal case, then `_FP_PACK_CANONICAL`
  (`packCanon`, shared with `__muldf3`);
* `divFields`: `_FP_DIV`'s class cases (a NaN result is the canonical `qnan`,
  `_FP_CHOOSENAN` on RISC-V).

(b2) `div_eq : div a b = F64.div a b`:

* `udivQrnnd_eq`: Knuth D computes the quotient and remainder
  (`qrHalf_eq`: the estimate is at most two too large for a normalised
  divisor);
* `jam n d`: the quotient with the remainder sticky bit, `rto`'s
  generalisation to any divisor (`rto_jam`); `round_jam` (W1 for a
  quotient): two or more bits below the rounding position it rounds as the
  exact quotient with its round and sticky bits;
* `shr_quot`, `quot_cross`, `round_refine`: `F64.round` of a quotient
  depends only on the rational it denotes, so `F64.divCore`'s coarse
  quotient and `_FP_DIV`'s fine one round alike;
* the unpacked operands and `packCanon_eq` are `__muldf3`'s.
-/

namespace Lua.Num.SfRef

set_option linter.deprecated false

open F64

/-! ## `udiv_qrnnd` (`longlong.h` `__udiv_qrnnd_c`) -/

/-- One digit of `__udiv_qrnnd_c`: `u · 2^32 + t` by the normalised divisor
`d` (`__q = u / __d1`, `__r = u % __d1`, `__m = __q * __d0`, `__r = __r *
__ll_B | t`; `__r += d` and `__q--` while `__r < __m`, at most twice, the
second time only without a carry), every word operation mod `2^64`. -/
def qrHalf (u t d : Nat) : Nat × Nat :=
  let q := u / (d / 2 ^ 32)
  let m := q * (d % 2 ^ 32) % 2 ^ 64
  let r := (u % (d / 2 ^ 32) * 2 ^ 32 % 2 ^ 64) ||| t
  if r < m then
    let r' := (r + d) % 2 ^ 64
    if d ≤ r' ∧ r' < m then ((q + 2 ^ 64 - 2) % 2 ^ 64, ((r' + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64)
    else ((q + 2 ^ 64 - 1) % 2 ^ 64, (r' + 2 ^ 64 - m) % 2 ^ 64)
  else (q, (r + 2 ^ 64 - m) % 2 ^ 64)

/-- `__udiv_qrnnd_c (q, r, n1, n0, d)`: the high digit from `n1` and
`n0`'s high half, the low digit from its remainder and `n0`'s low half,
`q = __q1 * __ll_B | __q0`. -/
def udivQrnnd (n1 n0 d : Nat) : Nat × Nat :=
  let h := qrHalf n1 (n0 / 2 ^ 32) d
  let l := qrHalf h.2 (n0 % 2 ^ 32) d
  ((h.1 * 2 ^ 32 % 2 ^ 64) ||| l.1, l.2)

/-- `x | t` on a word whose low 32 bits are clear. -/
theorem or_low32 (a t : Nat) (ht : t < 2 ^ 32) : a * 2 ^ 32 ||| t = a * 2 ^ 32 + t := by
  rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt ht a).symm

/-- Division with remainder from `N = q · d + r`, `r < d`. -/
theorem divmod_of {N d q r : Nat} (hd : 0 < d) (h : N = q * d + r) (hr : r < d) :
    (N / d, N % d) = (q, r) := by
  obtain ⟨e1, e2⟩ := (Nat.div_mod_unique hd).2 (⟨by rw [h, Nat.mul_comm]; omega, hr⟩ : r + d * q = N ∧ r < d)
  rw [e1, e2]

/-- The corrections of a digit estimate `q` at most two too large (`N + m =
q · d + R`, `R < d`, `m < 2^64 ≤ 2 d`), word arithmetic mod `2^64`. -/
theorem qr_fix {N d q R m : Nat} (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hR : R < d) (hm : m < 2 ^ 64)
    (hq : q < 2 ^ 64) (hNq : N + m = q * d + R) :
    (if R < m then
      (if d ≤ (R + d) % 2 ^ 64 ∧ (R + d) % 2 ^ 64 < m then
        ((q + 2 ^ 64 - 2) % 2 ^ 64, (((R + d) % 2 ^ 64 + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64)
      else ((q + 2 ^ 64 - 1) % 2 ^ 64, ((R + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64))
    else (q, (R + 2 ^ 64 - m) % 2 ^ 64)) = (N / d, N % d) := by
  have hd : 0 < d := by omega
  by_cases h1 : R < m
  · rw [if_pos h1]
    have hq1 : 1 ≤ q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; simp at hNq; omega
      · exact h
    by_cases h2 : d ≤ (R + d) % 2 ^ 64 ∧ (R + d) % 2 ^ 64 < m
    · rw [if_pos h2]
      have hnc : R + d < 2 ^ 64 := by
        refine Classical.byContradiction fun hc => ?_
        have : (R + d) % 2 ^ 64 = R + d - 2 ^ 64 := by omega
        omega
      rw [Nat.mod_eq_of_lt hnc] at h2 ⊢
      have hq2 : 2 ≤ q := by
        refine Classical.byContradiction fun hc => ?_
        have : q = 1 := by omega
        subst this; simp at hNq; omega
      have e2 : (q - 2) * d = q * d - 2 * d := by rw [Nat.sub_mul]
      have e3 : 2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
      rw [divmod_of hd (show N = (q - 2) * d + (R + 2 * d - m) by omega) (by omega), Prod.mk.injEq]
      exact ⟨by omega, by omega⟩
    · rw [if_neg h2]
      have e2 : (q - 1) * d = q * d - 1 * d := by rw [Nat.sub_mul]
      have e3 : 1 * d ≤ q * d := Nat.mul_le_mul_right d hq1
      have hge : m ≤ R + d := by
        refine Classical.byContradiction fun hc => ?_
        apply h2
        rw [Nat.mod_eq_of_lt (show R + d < 2 ^ 64 by omega)]; omega
      rw [divmod_of hd (show N = (q - 1) * d + (R + d - m) by omega) (by omega), Prod.mk.injEq]
      refine ⟨by omega, ?_⟩
      by_cases hc : R + d < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hc]; omega
      · rw [show (R + d) % 2 ^ 64 = R + d - 2 ^ 64 by omega]; omega
  · rw [if_neg h1, divmod_of hd (show N = q * d + (R - m) by omega) (by omega), Prod.mk.injEq]
    exact ⟨rfl, by omega⟩

theorem knuth_num {u t q d d1 d0 ρ : Nat} (hqd : q * d = q * d1 * 2 ^ 32 + q * d0)
    (hu32 : u * 2 ^ 32 = q * d1 * 2 ^ 32 + ρ * 2 ^ 32) :
    u * 2 ^ 32 + t + q * d0 = q * d + (ρ * 2 ^ 32 + t) := by
  rw [hqd, hu32]; ac_rfl

/-- **The facts of one digit's estimate** (`__udiv_qrnnd_c`'s `__q`, `__r`,
`__m` for `u < d`, `d` normalised): what the corrections need, and what a
machine transcription of them reads (lane float-sf4, (b1)). -/
structure QrSetup (u t d : Nat) : Prop where
  /-- `__r = __r * __ll_B | t` is below the divisor. -/
  hR : (u % (d / 2 ^ 32) * 2 ^ 32 % 2 ^ 64 ||| t) < d
  /-- The estimate is a word. -/
  hq : u / (d / 2 ^ 32) < 2 ^ 64
  /-- `__m` does not wrap. -/
  hm : u / (d / 2 ^ 32) * (d % 2 ^ 32) < 2 ^ 64
  /-- The remainder estimate is a 32-bit digit. -/
  hρ : u % (d / 2 ^ 32) < 2 ^ 32
  /-- `N + __m = __q · d + __r`. -/
  hNq : u * 2 ^ 32 + t + u / (d / 2 ^ 32) * (d % 2 ^ 32) % 2 ^ 64 =
    u / (d / 2 ^ 32) * d + (u % (d / 2 ^ 32) * 2 ^ 32 % 2 ^ 64 ||| t)
  /-- The digit is a 32-bit digit. -/
  hlt : (u * 2 ^ 32 + t) / d < 2 ^ 32

theorem qr_setup {u t d : Nat} (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hu : u < d) (ht : t < 2 ^ 32) :
    QrSetup u t d := by
  -- the divisor's digits
  have hdd := Nat.div_add_mod d (2 ^ 32)
  obtain ⟨d1, hD1⟩ : ∃ d1, d / 2 ^ 32 = d1 := ⟨_, rfl⟩
  obtain ⟨d0, hD0⟩ : ∃ d0, d % 2 ^ 32 = d0 := ⟨_, rfl⟩
  rw [hD1, hD0] at hdd
  have hd0 : d0 < 2 ^ 32 := by rw [← hD0]; exact Nat.mod_lt _ (by decide)
  have hd1lo : 2 ^ 31 ≤ d1 := by omega
  -- the estimate
  have huu := Nat.div_add_mod u d1
  obtain ⟨q, hQ⟩ : ∃ q, u / d1 = q := ⟨_, rfl⟩
  obtain ⟨ρ, hR⟩ : ∃ ρ, u % d1 = ρ := ⟨_, rfl⟩
  rw [hQ, hR] at huu
  have hρ : ρ < d1 := by rw [← hR]; exact Nat.mod_lt _ (by omega)
  have hq : q ≤ 2 ^ 32 + 1 := by
    refine Classical.byContradiction fun hc => ?_
    have := Nat.mul_le_mul_left d1 (show 2 ^ 32 + 2 ≤ q by omega)
    omega
  have hm : q * d0 ≤ 2 ^ 64 - 1 := by
    have := Nat.mul_le_mul hq (show d0 ≤ 2 ^ 32 - 1 by omega)
    omega
  have hrr : ρ * 2 ^ 32 % 2 ^ 64 ||| t = ρ * 2 ^ 32 + t := by
    rw [Nat.mod_eq_of_lt (by omega), or_low32 _ _ ht]
  -- `N + m = q · d + R`
  have hqd : q * d = q * d1 * 2 ^ 32 + q * d0 := by
    rw [← hdd, Nat.mul_add, Nat.mul_comm (2 ^ 32) d1, ← Nat.mul_assoc]
  have hu32 : u * 2 ^ 32 = q * d1 * 2 ^ 32 + ρ * 2 ^ 32 := by
    rw [← huu, Nat.add_mul, Nat.mul_comm d1 q]
  have hNq : u * 2 ^ 32 + t + q * d0 = q * d + (ρ * 2 ^ 32 + t) := knuth_num hqd hu32
  have hNlt : u * 2 ^ 32 + t < 2 ^ 32 * d := by
    have := Nat.mul_le_mul_right (2 ^ 32) (show u + 1 ≤ d by omega)
    rw [Nat.add_mul, Nat.mul_comm d] at this; omega
  have hm' : q * d0 % 2 ^ 64 = q * d0 := Nat.mod_eq_of_lt (by omega)
  have hR' : ρ * 2 ^ 32 % 2 ^ 64 ||| t < d := by
    rw [hrr]
    have h1 := Nat.mul_le_mul_right (2 ^ 32) (show ρ + 1 ≤ d1 by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    rw [← hdd, Nat.mul_comm (2 ^ 32) d1]
    obtain ⟨X, hX⟩ : ∃ X, ρ * 2 ^ 32 = X := ⟨_, rfl⟩
    obtain ⟨Y, hY⟩ : ∃ Y, d1 * 2 ^ 32 = Y := ⟨_, rfl⟩
    rw [hX, hY] at h1; rw [hX, hY]
    omega
  rw [← hm', ← hrr] at hNq
  rw [← hQ, ← hR, ← hD1, ← hD0] at hNq
  rw [← hR, ← hD1] at hR'
  have hm2 : u / (d / 2 ^ 32) * (d % 2 ^ 32) < 2 ^ 64 := by rw [hD1, hD0, hQ]; omega
  exact ⟨hR', by rw [hD1, hQ]; omega, hm2, by rw [hD1, hR]; omega, hNq,
    (Nat.div_lt_iff_lt_mul (by omega)).2 hNlt⟩

/-- **One digit of Knuth's algorithm D** (`__udiv_qrnnd_c`'s half): for a
normalised divisor and `u < d`, the estimate `u / d1` is at most two too
large and the corrections leave the exact digit and remainder. -/
theorem qrHalf_eq {u t d : Nat} (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hu : u < d) (ht : t < 2 ^ 32) :
    qrHalf u t d = ((u * 2 ^ 32 + t) / d, (u * 2 ^ 32 + t) % d) ∧ (u * 2 ^ 32 + t) / d < 2 ^ 32 := by
  have k := qr_setup hd1 hd2 hu ht
  exact ⟨qr_fix hd1 hd2 k.hR (Nat.mod_lt _ (by decide)) k.hq k.hNq, k.hlt⟩

/-- `n1 · 2^64 + n0` by 32-bit digits. -/
theorem split64 (n1 n0 : Nat) : n1 * 2 ^ 64 + n0 = (n1 * 2 ^ 32 + n0 / 2 ^ 32) * 2 ^ 32 + n0 % 2 ^ 32 := by
  have := Nat.div_add_mod n0 (2 ^ 32)
  omega

/-- The two digits recombined: `(A·2^32 + b)` by `d` from `A` by `d`. -/
theorem div_digits {A b d : Nat} (hd : 0 < d) :
    A * 2 ^ 32 + b = (A / d * 2 ^ 32 + (A % d * 2 ^ 32 + b) / d) * d + (A % d * 2 ^ 32 + b) % d := by
  have hA := Nat.div_add_mod A d
  have hB := Nat.div_add_mod (A % d * 2 ^ 32 + b) d
  have e : A * 2 ^ 32 = A / d * 2 ^ 32 * d + A % d * 2 ^ 32 := by
    conv => lhs; rw [← hA]
    rw [Nat.add_mul, Nat.mul_comm d, Nat.mul_assoc, Nat.mul_comm d, ← Nat.mul_assoc]
  rw [Nat.add_mul, e, Nat.mul_comm ((A % d * 2 ^ 32 + b) / d) d]
  omega

/-- **Knuth's algorithm D** (`__udiv_qrnnd_c`): for a normalised divisor
and `n1 < d`, the quotient and remainder of `n1 · 2^64 + n0` by `d`. -/
theorem udivQrnnd_eq {n1 n0 d : Nat} (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64) (hn1 : n1 < d)
    (hn0 : n0 < 2 ^ 64) :
    udivQrnnd n1 n0 d = ((n1 * 2 ^ 64 + n0) / d, (n1 * 2 ^ 64 + n0) % d) := by
  have ht1 : n0 / 2 ^ 32 < 2 ^ 32 := by omega
  have ht0 : n0 % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  obtain ⟨e1, hq1⟩ := qrHalf_eq hd1 hd2 hn1 ht1
  have hr1 : (n1 * 2 ^ 32 + n0 / 2 ^ 32) % d < d := Nat.mod_lt _ (by omega)
  obtain ⟨e0, hq0⟩ := qrHalf_eq hd1 hd2 hr1 ht0
  unfold udivQrnnd
  simp only [e1, e0]
  rw [split64 n1 n0, divmod_of (by omega) (div_digits (by omega))
    (Nat.mod_lt _ (by omega)), Nat.mod_eq_of_lt (by omega), or_low32 _ _ hq0]

/-! ## The quotient's sticky bit and its rounding -/

/-- **The quotient with a remainder sticky bit** (soft-fp's `R_f = q | (r !=
0)`): round to odd over any divisor (`rto_eq_jam`). -/
def jam (n d : Nat) : Nat := if n % d = 0 then n / d else 2 * (n / d / 2) + 1

theorem rto_eq_jam (n k : Nat) : rto n k = jam n (2 ^ k) := by
  unfold rto jam
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]

theorem lor_one (q : Nat) : q ||| 1 = 2 * (q / 2) + 1 := by
  have e : 2 * (q / 2) + 1 = 2 * (q / 2) ||| 1 := by
    have := Nat.two_pow_add_eq_or_of_lt (show 1 < 2 ^ 1 by decide) (q / 2)
    simpa using this
  rcases Nat.mod_two_eq_zero_or_one q with h | h
  · conv => lhs; rw [show q = 2 * (q / 2) by omega]
    exact e.symm
  · have hq : q = 2 * (q / 2) ||| 1 := by rw [← e]; omega
    calc q ||| 1 = (2 * (q / 2) ||| 1) ||| 1 := by rw [← hq]
      _ = 2 * (q / 2) ||| 1 := by rw [Nat.or_assoc, Nat.or_self]
      _ = 2 * (q / 2) + 1 := e.symm

/-- `q | (r != 0)` is `jam`. -/
theorem lor_sticky (n d : Nat) : n / d ||| (if n % d = 0 then 0 else 1) = jam n d := by
  unfold jam
  split
  · simp
  · exact lor_one _

/-- `_FP_ROUND`'s round bit of a quotient: the remainder is at least half the divisor. -/
def rbOf (N D : Nat) : Bool := decide (D ≤ 2 * (N % D))
/-- Its sticky bit: the remainder is neither zero nor half the divisor. -/
def stOf (N D : Nat) : Bool := decide (N % D ≠ 0 ∧ 2 * (N % D) ≠ D)

theorem rb_or_st {N D : Nat} (hD : 0 < D) : (rbOf N D || stOf N D) = decide (N % D ≠ 0) := by
  unfold rbOf stOf
  by_cases h : N % D = 0
  · simp [h]; omega
  · simp only [h, ne_eq, not_false_eq_true, true_and, decide_true]
    by_cases h2 : 2 * (N % D) = D
    · simp [h2]
    · simp [h2]

/-- **`shr` of a quotient with its round and sticky bits** is the quotient
by the divisor scaled, with its own. -/
theorem shr_quot {N D : Nat} (hD : 0 < D) (s : Nat) :
    shr (N / D) (rbOf N D) (stOf N D) s = (N / (D * 2 ^ s), rbOf N (D * 2 ^ s), stOf N (D * 2 ^ s)) := by
  rcases s with _ | s
  · simp [shr]
  unfold shr
  rw [if_neg (by omega), show s + 1 - 1 = s by omega, Nat.div_div_eq_div_mul]
  have hK : 0 < D * 2 ^ s := Nat.mul_pos hD (Nat.two_pow_pos s)
  have e2 : D * 2 ^ (s + 1) = (D * 2 ^ s) * 2 := by rw [Nat.pow_succ, Nat.mul_assoc]
  rw [e2, Nat.div_div_eq_div_mul]
  -- `N % 2K = N % K + K · ((N / K) % 2)`
  have hmod : N % (D * 2 ^ s * 2) = N % (D * 2 ^ s) + D * 2 ^ s * (N / (D * 2 ^ s) % 2) := Nat.mod_mul
  have hmodK : N % (D * 2 ^ s) = N % D + D * (N / D % 2 ^ s) := Nat.mod_mul
  have hlt := Nat.mod_lt N hK
  obtain ⟨K, hKd⟩ : ∃ K, D * 2 ^ s = K := ⟨_, rfl⟩
  rw [hKd] at hmod hlt hK hmodK ⊢
  rw [Bool.or_assoc, rb_or_st hD]
  unfold rbOf stOf
  rcases Nat.mod_two_eq_zero_or_one (N / K) with hb | hb
  · rw [hb, Nat.mul_zero, Nat.add_zero] at hmod
    rw [hmod, hb]
    simp only [Prod.mk.injEq, true_and]
    constructor
    · simp; omega
    · by_cases hz : N % K = 0
      · have : N % D = 0 ∧ N / D % 2 ^ s = 0 := by
          constructor
          · omega
          · rcases Nat.eq_zero_or_pos (N / D % 2 ^ s) with h | h
            · exact h
            · have := Nat.mul_pos hD h; omega
        simp [hz, this.1, this.2] <;> omega
      · have : N % D ≠ 0 ∨ N / D % 2 ^ s ≠ 0 := by
          by_cases h : N % D = 0
          · right; intro h'; rw [h, h', Nat.mul_zero] at hmodK; omega
          · left; exact h
        simp only [hz, ne_eq, not_false_eq_true, true_and]
        rcases this with h | h <;> simp [h] <;> omega
  · rw [hb, Nat.mul_one] at hmod
    rw [hmod, hb]
    simp only [Prod.mk.injEq, true_and]
    constructor
    · simp; omega
    · by_cases hz : N % K = 0
      · have : N % D = 0 ∧ N / D % 2 ^ s = 0 := by
          constructor
          · omega
          · rcases Nat.eq_zero_or_pos (N / D % 2 ^ s) with h | h
            · exact h
            · have := Nat.mul_pos hD h; omega
        simp [hz, this.1, this.2] <;> omega
      · have : N % D ≠ 0 ∨ N / D % 2 ^ s ≠ 0 := by
          by_cases h : N % D = 0
          · right; intro h'; rw [h, h', Nat.mul_zero] at hmodK; omega
          · left; exact h
        rcases this with h | h <;> simp [h] <;> omega

/-- **Two quotients of one rational** (`N1 / D1 = N2 / D2`) have the same
floor, round bit and sticky bit. -/
theorem quot_cross {N1 D1 N2 D2 : Nat} (h : N1 * D2 = N2 * D1) (hD1 : 0 < D1) (hD2 : 0 < D2) :
    N1 / D1 = N2 / D2 ∧ rbOf N1 D1 = rbOf N2 D2 ∧ stOf N1 D1 = stOf N2 D2 := by
  have hq : N1 / D1 = N2 / D2 := by
    rw [← Nat.mul_div_mul_right N1 D1 hD2, ← Nat.mul_div_mul_right N2 D2 hD1, h, Nat.mul_comm D1 D2]
  have hr : N1 % D1 * D2 = N2 % D2 * D1 := by
    rw [← Nat.mul_mod_mul_right, ← Nat.mul_mod_mul_right, h, Nat.mul_comm D1 D2]
  refine ⟨hq, ?_, ?_⟩
  · unfold rbOf
    apply decide_eq_decide.mpr
    constructor
    · intro h1
      apply Nat.le_of_mul_le_mul_right (c := D1) _ hD1
      have := Nat.mul_le_mul_right D2 h1
      rw [Nat.mul_assoc, hr, Nat.mul_comm D1 D2] at this
      rw [Nat.mul_assoc]; exact this
    · intro h1
      apply Nat.le_of_mul_le_mul_right (c := D2) _ hD2
      have := Nat.mul_le_mul_right D1 h1
      rw [Nat.mul_assoc, ← hr, Nat.mul_comm D2 D1] at this
      rw [Nat.mul_assoc]; exact this
  · unfold stOf
    apply decide_eq_decide.mpr
    have z : N1 % D1 = 0 ↔ N2 % D2 = 0 := by
      constructor
      · intro h1; rw [h1, Nat.zero_mul] at hr
        exact (Nat.mul_eq_zero.mp hr.symm).resolve_right (by omega)
      · intro h1; rw [h1, Nat.zero_mul] at hr
        exact (Nat.mul_eq_zero.mp hr).resolve_right (by omega)
    have w : 2 * (N1 % D1) = D1 ↔ 2 * (N2 % D2) = D2 := by
      constructor
      · intro h1
        apply Nat.eq_of_mul_eq_mul_right hD1
        rw [Nat.mul_assoc, ← hr, ← Nat.mul_assoc, h1, Nat.mul_comm]
      · intro h1
        apply Nat.eq_of_mul_eq_mul_right hD2
        rw [Nat.mul_assoc, hr, ← Nat.mul_assoc, h1, Nat.mul_comm]
    simp only [ne_eq, z, w]

/-- A quotient refined by `k` more bits: `shr` by `k` more gives the same. -/
theorem shr_refine {N D : Nat} (hD : 0 < D) (s k : Nat) :
    shr (N * 2 ^ k / D) (rbOf (N * 2 ^ k) D) (stOf (N * 2 ^ k) D) (s + k) =
      shr (N / D) (rbOf N D) (stOf N D) s := by
  rw [shr_quot hD, shr_quot hD]
  obtain ⟨e1, e2, e3⟩ := quot_cross (N1 := N * 2 ^ k) (D1 := D * 2 ^ (s + k)) (N2 := N) (D2 := D * 2 ^ s)
    (by rw [Nat.pow_add]; ac_rfl) (Nat.mul_pos hD (Nat.two_pow_pos _)) (Nat.mul_pos hD (Nat.two_pow_pos _))
  rw [e1, e2, e3]

/-- The rounding position of a refined quotient (in the `shr` branch). -/
theorem target_refine {N D : Nat} (hD : 0 < D) (E : Int) (k : Nat) (hE : E ≤ target (N / D) E) :
    target (N * 2 ^ k / D) (E - k) = target (N / D) E := by
  unfold target at *
  rcases Nat.eq_zero_or_pos (N / D) with hq | hq
  · rw [hq] at hE ⊢
    have hE' : E ≤ -1074 := by simp at hE; omega
    have hN : N < D := by
      refine Classical.byContradiction fun hc => ?_
      have := Nat.div_pos (show D ≤ N by omega) hD; omega
    have hx : N * 2 ^ k / D < 2 ^ k :=
      (Nat.div_lt_iff_lt_mul hD).2 (by rw [Nat.mul_comm (2 ^ k) D]; exact Nat.mul_lt_mul_of_pos_right hN (Nat.two_pow_pos k))
    have hl : (N * 2 ^ k / D).log2 ≤ k := by
      rcases Nat.eq_zero_or_pos (N * 2 ^ k / D) with h0 | h0
      · rw [h0]; simp
      · exact Nat.le_of_lt ((Nat.log2_lt (by omega)).2 hx)
    simp; omega
  · have hL1 := Nat.log2_self_le (n := N / D) (by omega)
    have hL2 := Nat.lt_log2_self (n := N / D)
    have hlo : N / D * 2 ^ k ≤ N * 2 ^ k / D := by
      rw [Nat.le_div_iff_mul_le hD, Nat.mul_right_comm]
      exact Nat.mul_le_mul_right _ (Nat.div_mul_le_self N D)
    have hhi : N * 2 ^ k / D < (N / D + 1) * 2 ^ k := by
      rw [Nat.div_lt_iff_lt_mul hD, Nat.mul_right_comm]
      exact Nat.mul_lt_mul_of_pos_right (by have := Nat.lt_mul_div_succ N hD; rw [Nat.mul_comm] at this; exact this)
        (Nat.two_pow_pos k)
    have e : (N * 2 ^ k / D).log2 = (N / D).log2 + k := by
      apply log2_of_bounds
      · rw [Nat.pow_add]; exact Nat.le_trans (Nat.mul_le_mul_right _ hL1) hlo
      · rw [show (N / D).log2 + k + 1 = ((N / D).log2 + 1) + k by omega, Nat.pow_add]
        exact Nat.lt_of_lt_of_le hhi (Nat.mul_le_mul_right _ hL2)
    rw [e]; omega

/-- **`F64.round` of a quotient refined by `k` bits** rounds as the quotient:
its value is the same rational. -/
theorem round_refine (neg : Bool) {N D : Nat} (hD : 0 < D) (E : Int) (k : Nat) (hE : E ≤ target (N / D) E) :
    round neg (N * 2 ^ k / D) (E - k) (rbOf (N * 2 ^ k) D) (stOf (N * 2 ^ k) D) =
      round neg (N / D) E (rbOf N D) (stOf N D) := by
  have hT := target_refine hD E k hE
  unfold round
  rw [hT, if_pos (by omega), if_pos hE,
    show (target (N / D) E - (E - k)).toNat = (target (N / D) E - E).toNat + k by omega, shr_refine hD]

/-- `jam` keeps the top bit of a quotient `≥ 2`. -/
theorem log2_jam {N D : Nat} (hq : 2 ≤ N / D) : (jam N D).log2 = (N / D).log2 := by
  have hL1 := Nat.log2_self_le (n := N / D) (by omega)
  have hL2 := Nat.lt_log2_self (n := N / D)
  rw [Nat.pow_succ] at hL2
  apply log2_of_bounds
  · unfold jam; split <;> omega
  · rw [Nat.pow_succ]; unfold jam; split <;> omega

theorem target_jam {N D : Nat} (hq : 2 ≤ N / D) (E : Int) : target (jam N D) E = target (N / D) E := by
  unfold target; rw [log2_jam hq]

theorem div_pow_succ (a b : Nat) : a / 2 ^ (b + 1) = a / 2 / 2 ^ b := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-- `jam` two or more bits below the rounding position shifts as the
quotient with its round and sticky bits. -/
theorem shr_jam {N D : Nat} (hD : 0 < D) (s : Nat) (hs : 2 ≤ s) :
    shr (jam N D) false false s = shr (N / D) (rbOf N D) (stOf N D) s := by
  obtain ⟨s, rfl⟩ : ∃ s', s = s' + 2 := ⟨s - 2, by omega⟩
  unfold shr
  rw [if_neg (by omega), if_neg (by omega), show s + 2 - 1 = s + 1 by omega]
  simp only [Bool.or_false]
  rw [Bool.or_assoc, rb_or_st hD]
  unfold jam
  split
  · rename_i h; simp [h]
  · rename_i h
    have hJ : (2 * (N / D / 2) + 1) / 2 = N / D / 2 := by omega
    have e1 : (2 * (N / D / 2) + 1) / 2 ^ (s + 2) = N / D / 2 ^ (s + 2) := by
      rw [div_pow_succ, hJ, ← div_pow_succ]
    have e2 : (2 * (N / D / 2) + 1) / 2 ^ (s + 1) = N / D / 2 ^ (s + 1) := by
      rw [div_pow_succ, hJ, ← div_pow_succ]
    have e3 : (2 * (N / D / 2) + 1) % 2 ^ (s + 1) ≠ 0 := by
      intro h0
      have hd : 2 ∣ 2 ^ (s + 1) := ⟨2 ^ s, by rw [Nat.pow_succ, Nat.mul_comm]⟩
      have := Nat.mod_mod_of_dvd (2 * (N / D / 2) + 1) hd
      rw [h0, Nat.zero_mod] at this
      omega
    rw [e1, e2]
    simp [e3, h]

/-- **W1 for a quotient**: the quotient with its remainder sticky bit
(`jam`), two or more bits below the rounding position, rounds as the
quotient with its round and sticky bits. -/
theorem round_jam (neg : Bool) {N D : Nat} (hD : 0 < D) (hq : 2 ≤ N / D) (E : Int)
    (hE : E + 2 ≤ target (N / D) E) :
    round neg (jam N D) E false false = round neg (N / D) E (rbOf N D) (stOf N D) := by
  unfold round
  rw [target_jam hq, if_pos (by omega), if_pos (by omega), shr_jam hD _ (by omega)]

/-! ## `_FP_DIV_MEAT_1_udiv_norm`, `_FP_DIV` -/

/-- `_FP_DIV_MEAT_1_udiv_norm` (`op-1.h`) on two normal working mantissas:
`Y <<= _FP_WFRACXBITS_D` (8 bits, the divisor normalised), the dividend
`X : 0` when `X < Y` (`R_e--`) else `(X >> 1) : (X << 63)`, `udiv_qrnnd`, and
`R_f = q | (r != 0)`. -/
def divMeat (X Y : Nat) : Nat :=
  let d := Y * 2 ^ 8 % 2 ^ 64
  let qr := if X < Y then udivQrnnd X 0 d else udivQrnnd (X / 2) (X * 2 ^ 63 % 2 ^ 64) d
  qr.1 ||| (if qr.2 = 0 then 0 else 1)

/-- `_FP_DIV`'s normal case: `R_e = X_e - Y_e` (one lower when `X < Y`),
`_FP_DIV_MEAT_D`, then `_FP_PACK_CANONICAL`. -/
def divNorm (neg : Bool) (X : Nat) (Xe : Int) (Y : Nat) (Ye : Int) : F64 :=
  packCanon neg (if X < Y then Xe - Ye - 1 else Xe - Ye) (divMeat X Y)

/-- `__divdf3` over the fields (`_FP_DIV`'s class cases; a NaN result is the
canonical `qnan`, `_FP_CHOOSENAN` on RISC-V). -/
def divFields (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat) : F64 :=
  if (ea = 2047 ∧ fa ≠ 0) ∨ (eb = 2047 ∧ fb ≠ 0) then qnan
  else if ea = 2047 then (if eb = 2047 then qnan else infty (sa ^^ sb))
  else if eb = 2047 then zero (sa ^^ sb)
  else if ea = 0 ∧ fa = 0 then (if eb = 0 ∧ fb = 0 then qnan else zero (sa ^^ sb))
  else if eb = 0 ∧ fb = 0 then infty (sa ^^ sb)
  else divNorm (sa ^^ sb) (unpackF ea fa) (unpackE ea fa) (unpackF eb fb) (unpackE eb fb)

/-- `SfRef.div`. -/
def div (a b : F64) : F64 := divFields a.sign a.bexp a.frac b.sign b.bexp b.frac

/-! ## (b2) -/

/-- The dividend of `_FP_DIV_MEAT_1_udiv_norm` over the divisor, both
scaled by `2^8`. -/
theorem quot_scale (N Y : Nat) (hY : 0 < Y) :
    N * 2 ^ 8 / (Y * 2 ^ 8) = N / Y ∧ (N * 2 ^ 8 % (Y * 2 ^ 8) = 0 ↔ N % Y = 0) := by
  refine ⟨Nat.mul_div_mul_right N Y (Nat.two_pow_pos 8), ?_⟩
  rw [Nat.mul_mod_mul_right]
  constructor
  · intro h; exact (Nat.mul_eq_zero.mp h).resolve_right (by decide)
  · intro h; rw [h, Nat.zero_mul]

/-- **`_FP_DIV_MEAT_1_udiv_norm`** is the quotient with its sticky bit,
`X · 2^56 / Y` (`X < Y`) or `X · 2^55 / Y`. -/
theorem divMeat_eq {X Y : Nat} (hX1 : 2 ^ 55 ≤ X) (hX2 : X < 2 ^ 56) (hY1 : 2 ^ 55 ≤ Y) (hY2 : Y < 2 ^ 56) :
    divMeat X Y = jam (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) Y := by
  have hY0 : 0 < Y := by omega
  have hd : Y * 2 ^ 8 % 2 ^ 64 = Y * 2 ^ 8 := Nat.mod_eq_of_lt (by omega)
  unfold divMeat
  simp only [hd]
  rw [← lor_sticky]
  by_cases h : X < Y
  · rw [if_pos h, if_pos h, udivQrnnd_eq (by omega) (by omega) (by omega) (by omega)]
    have e : X * 2 ^ 64 + 0 = X * 2 ^ 56 * 2 ^ 8 := by rw [Nat.add_zero, Nat.mul_assoc, ← Nat.pow_add]
    obtain ⟨q1, q2⟩ := quot_scale (X * 2 ^ 56) Y hY0
    simp only [e, q1]
    by_cases hr : X * 2 ^ 56 % Y = 0
    · rw [if_pos (q2.2 hr), if_pos hr]
    · rw [if_neg (fun h' => hr (q2.1 h')), if_neg hr]
  · rw [if_neg h, if_neg h, udivQrnnd_eq (by omega) (by omega) (by omega) (by omega)]
    have e : X / 2 * 2 ^ 64 + X * 2 ^ 63 % 2 ^ 64 = X * 2 ^ 55 * 2 ^ 8 := by
      have h1 : X * 2 ^ 63 % 2 ^ 64 = X % 2 * 2 ^ 63 := by
        rw [show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from by rw [← Nat.pow_succ'], Nat.mul_mod_mul_right]
      rw [h1, Nat.mul_assoc, ← Nat.pow_add,
        show (2 : Nat) ^ 64 = 2 * 2 ^ 63 from by rw [← Nat.pow_succ'], ← Nat.mul_assoc, ← Nat.add_mul]
      congr 1; omega
    obtain ⟨q1, q2⟩ := quot_scale (X * 2 ^ 55) Y hY0
    simp only [e, q1]
    by_cases hr : X * 2 ^ 55 % Y = 0
    · rw [if_pos (q2.2 hr), if_pos hr]
    · rw [if_neg (fun h' => hr (q2.1 h')), if_neg hr]

/-- The quotient of two normal working mantissas lies in `[2^55, 2^56)`. -/
theorem quot_bounds {X Y : Nat} (hX1 : 2 ^ 55 ≤ X) (hX2 : X < 2 ^ 56) (hY1 : 2 ^ 55 ≤ Y) (hY2 : Y < 2 ^ 56) :
    2 ^ 55 ≤ (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) / Y ∧
      (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) / Y < 2 ^ 56 := by
  have hY0 : 0 < Y := by omega
  split
  · rename_i h
    refine ⟨(Nat.le_div_iff_mul_le hY0).2 ?_, (Nat.div_lt_iff_lt_mul hY0).2 ?_⟩
    · have := Nat.mul_le_mul_left (2 ^ 55) (show Y ≤ 2 * X by omega)
      rw [show (2 : Nat) ^ 56 = 2 ^ 55 * 2 by decide, ← Nat.mul_assoc, Nat.mul_comm X]; omega
    · rw [Nat.mul_comm X]; exact Nat.mul_lt_mul_of_pos_left h (Nat.two_pow_pos 56)
  · rename_i h
    refine ⟨(Nat.le_div_iff_mul_le hY0).2 ?_, (Nat.div_lt_iff_lt_mul hY0).2 ?_⟩
    · rw [Nat.mul_comm X]; exact Nat.mul_le_mul_left _ (by omega)
    · have := Nat.mul_lt_mul_of_pos_left (show X < 2 * Y by omega) (Nat.two_pow_pos 55)
      rw [show (2 : Nat) ^ 56 = 2 ^ 55 * 2 by decide, Nat.mul_assoc, Nat.mul_comm X]; omega

theorem jam_bounds {N D : Nat} (h1 : 2 ^ 55 ≤ N / D) (h2 : N / D < 2 ^ 56) :
    2 ^ 55 ≤ jam N D ∧ jam N D < 2 ^ 56 := by
  unfold jam; split <;> omega

/-- **`_FP_DIV`'s normal case, packed, is `F64.round` of the quotient** with
its round and sticky bits, at the scale of the 56-bit working quotient. -/
theorem divNorm_eq (neg : Bool) {X Y : Nat} (Xe Ye : Int) (hX1 : 2 ^ 55 ≤ X) (hX2 : X < 2 ^ 56)
    (hY1 : 2 ^ 55 ≤ Y) (hY2 : Y < 2 ^ 56) :
    divNorm neg X Xe Y Ye =
      round neg ((if X < Y then X * 2 ^ 56 else X * 2 ^ 55) / Y)
        ((if X < Y then Xe - Ye - 1 else Xe - Ye) - 55)
        (rbOf (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) Y) (stOf (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) Y) := by
  have hY0 : 0 < Y := by omega
  obtain ⟨hq1, hq2⟩ := quot_bounds hX1 hX2 hY1 hY2
  obtain ⟨hj1, hj2⟩ := jam_bounds hq1 hq2
  unfold divNorm
  rw [divMeat_eq hX1 hX2 hY1 hY2, packCanon_eq neg _ _ hj1 hj2]
  generalize (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) = N at hq1 hq2 ⊢
  generalize (if X < Y then Xe - Ye - 1 else Xe - Ye) = Re
  have hL : (N / Y).log2 = 55 := log2_of_bounds hq1 (by simpa using hq2)
  exact round_jam neg hY0 (by omega) _ (by unfold target; rw [hL]; omega)

/-! ## `F64.divCore`'s quotient refined to the working scale -/

/-- **`F64.div`'s rounding of `divCore`** is the rounding of the quotient
at any finer exponent `E` (`round_refine`): `divCore` shifts the dividend
just far enough that its quotient is in `round`'s `shr` branch. -/
theorem divCore_round (s : Bool) {m1 m2 : Nat} (e1 e2 : Int) (hm1 : 0 < m1) (hm2 : 0 < m2) (E : Int)
    (hE : E ≤ min (e1 - e2) (max (((m1.log2 : Int) + 1 + e1) - ((m2.log2 : Int) + 1 + e2) - 53) (-1074))) :
    (match divCore m1 e1 m2 e2 with | (q, t, rb, st) => round s q t rb st) =
      round s (m1 * 2 ^ (e1 - e2 - E).toNat / m2) E (rbOf (m1 * 2 ^ (e1 - e2 - E).toNat) m2)
        (stOf (m1 * 2 ^ (e1 - e2 - E).toNat) m2) := by
  unfold divCore
  dsimp only
  rw [Nat.shiftLeft_eq]
  obtain ⟨t, ht⟩ : ∃ t, min (e1 - e2) (max (((m1.log2 : Int) + 1 + e1) - ((m2.log2 : Int) + 1 + e2) - 53)
      (-1074)) = t := ⟨_, rfl⟩
  rw [ht] at hE ⊢
  -- the coarse quotient is in `round`'s `shr` branch
  have hT : t ≤ target (m1 * 2 ^ (e1 - e2 - t).toNat / m2) t := by
    unfold target
    by_cases h1 : t ≤ -1074
    · omega
    · have hL1 := Nat.log2_self_le (n := m1) (by omega)
      have hL2 := Nat.lt_log2_self (n := m2)
      have hj : m2.log2 + 1 + 52 ≤ m1.log2 + (e1 - e2 - t).toNat := by omega
      have hq : 2 ^ 52 ≤ m1 * 2 ^ (e1 - e2 - t).toNat / m2 := by
        rw [Nat.le_div_iff_mul_le hm2]
        calc 2 ^ 52 * m2 ≤ 2 ^ 52 * 2 ^ (m2.log2 + 1) := Nat.mul_le_mul_left _ (Nat.le_of_lt hL2)
          _ = 2 ^ (m2.log2 + 1 + 52) := by rw [← Nat.pow_add, Nat.add_comm 52]
          _ ≤ 2 ^ (m1.log2 + (e1 - e2 - t).toNat) := Nat.pow_le_pow_right (by decide) hj
          _ = 2 ^ m1.log2 * 2 ^ (e1 - e2 - t).toNat := Nat.pow_add _ _ _
          _ ≤ m1 * 2 ^ (e1 - e2 - t).toNat := Nat.mul_le_mul_right _ hL1
      have := le_log2_of hq
      omega
  have hr := round_refine s (N := m1 * 2 ^ (e1 - e2 - t).toNat) hm2 t (t - E).toNat hT
  rw [Nat.mul_assoc, ← Nat.pow_add, show (e1 - e2 - t).toNat + (t - E).toNat = (e1 - e2 - E).toNat by omega,
    show t - ((t - E).toNat : Int) = E by omega] at hr
  rw [hr]
  rfl

/-- The unpacked operand of `_FP_UNPACK_CANONICAL` from the decoded one:
`X_f = m · 2^(55 - log2 m)`, `X_e = e + log2 m`. -/
theorem unpack_log (e f : Nat) (hf : f < 2 ^ 52) (h0 : e ≠ 0 ∨ f ≠ 0) :
    0 < cm e f ∧ (cm e f).log2 ≤ 52 ∧ unpackF e f = cm e f * 2 ^ (55 - (cm e f).log2) ∧
      unpackE e f = ce e + (cm e f).log2 := by
  unfold unpackF unpackE cm ce
  by_cases h : e = 0
  · rw [if_pos h, if_pos h, if_pos h, if_pos h]
    have hl : f.log2 < 52 := (Nat.log2_lt (by omega)).2 hf
    exact ⟨by omega, by omega, rfl, by omega⟩
  · rw [if_neg h, if_neg h, if_neg h, if_neg h]
    have hl : (f + 2 ^ 52).log2 = 52 := log2_of_bounds (by omega) (by omega)
    rw [hl]
    exact ⟨by omega, by omega, by omega, by omega⟩

theorem pow_cross {m1 m2 a b c d : Nat} (h : a + c = b + d) :
    m1 * 2 ^ a * 2 ^ c * m2 = m1 * 2 ^ b * (m2 * 2 ^ d) :=
  calc m1 * 2 ^ a * 2 ^ c * m2 = m1 * m2 * (2 ^ a * 2 ^ c) := by ac_rfl
    _ = m1 * m2 * 2 ^ (b + d) := by rw [← Nat.pow_add, h]
    _ = m1 * 2 ^ b * (m2 * 2 ^ d) := by rw [Nat.pow_add]; ac_rfl

/-- `__divdf3` on two finite nonzero operands is `F64.div`'s rounding of
`divCore`. -/
theorem divFields_fin (sa sb : Bool) (ea fa eb fb : Nat) (hea : ea ≤ 2046) (heb : eb ≤ 2046)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha0 : ea ≠ 0 ∨ fa ≠ 0) (hb0 : eb ≠ 0 ∨ fb ≠ 0) :
    divFields sa ea fa sb eb fb =
      (match divCore (cm ea fa) (ce ea) (cm eb fb) (ce eb) with | (q, t, rb, st) => round (sa ^^ sb) q t rb st) := by
  unfold divFields
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  have ⟨ha1, ha2⟩ := unpack_bounds ea fa hfa ha0
  have ⟨hb1, hb2⟩ := unpack_bounds eb fb hfb hb0
  rw [divNorm_eq _ _ _ ha1 ha2 hb1 hb2]
  obtain ⟨hma, hla, hXa, hXe⟩ := unpack_log ea fa hfa ha0
  obtain ⟨hmb, hlb, hYa, hYe⟩ := unpack_log eb fb hfb hb0
  generalize unpackF ea fa = X at ha1 ha2 hXa ⊢
  generalize unpackF eb fb = Y at hb1 hb2 hYa ⊢
  rw [hXe, hYe]
  generalize cm ea fa = m1 at hma hla hXa ⊢
  generalize cm eb fb = m2 at hmb hlb hYa ⊢
  generalize ce ea = e1
  generalize ce eb = e2
  have hY0 : 0 < Y := by omega
  -- the exponent `R_e - 55` and the dividend's shift `c`
  obtain ⟨c, hc, hN, hRe⟩ : ∃ c : Nat, (c = 55 ∨ c = 56) ∧
      (if X < Y then X * 2 ^ 56 else X * 2 ^ 55) = X * 2 ^ c ∧
      (if X < Y then e1 + m1.log2 - (e2 + m2.log2) - 1 else e1 + m1.log2 - (e2 + m2.log2)) =
        e1 + m1.log2 - (e2 + m2.log2) + 55 - c := by
    by_cases h : X < Y
    · exact ⟨56, Or.inr rfl, by rw [if_pos h], by rw [if_pos h]; omega⟩
    · exact ⟨55, Or.inl rfl, by rw [if_neg h], by rw [if_neg h]; omega⟩
  rw [hN, hRe]
  rw [divCore_round _ _ _ hma hmb (e1 + m1.log2 - (e2 + m2.log2) + 55 - c - 55) (by omega)]
  have hJ : (e1 - e2 - (e1 + ↑m1.log2 - (e2 + ↑m2.log2) + 55 - ↑c - 55)).toNat = c - m1.log2 + m2.log2 := by
    omega
  rw [hJ]
  obtain ⟨q1, q2, q3⟩ := quot_cross (N1 := X * 2 ^ c) (D1 := Y) (N2 := m1 * 2 ^ (c - m1.log2 + m2.log2))
    (D2 := m2) (by rw [hXa, hYa]; exact pow_cross (by omega)) hY0 hmb
  rw [q1, q2, q3]

/-- **(b2) for `__divdf3`**: the soft-fp-shaped reference is the `F64`
specification. -/
theorem div_eq (a b : F64) : div a b = F64.div a b := by
  have hfa : a.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hea : a.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfb : b.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have heb : b.bexp < 2048 := Nat.mod_lt _ (by decide)
  unfold div F64.div
  by_cases han : a.bexp = 2047 ∧ a.frac ≠ 0
  · rw [cls_nan' han.1 han.2]; unfold divFields; rw [if_pos (Or.inl han)]
  by_cases hbn : b.bexp = 2047 ∧ b.frac ≠ 0
  · rw [cls_nan' hbn.1 hbn.2]; unfold divFields; rw [if_pos (Or.inr hbn)]
    cases a.cls <;> rfl
  unfold divFields; rw [if_neg (by omega)]
  by_cases hai : a.bexp = 2047
  · have hfa0 : a.frac = 0 := by omega
    rw [cls_inf' hai hfa0, if_pos hai]
    by_cases hbi : b.bexp = 2047
    · have hfb0 : b.frac = 0 := by omega
      rw [cls_inf' hbi hfb0, if_pos hbi]
    by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
    · rw [cls_zero' hb0.1 hb0.2, if_neg hbi]
    · rw [cls_fin' (by omega) hbi, if_neg hbi]
  rw [if_neg hai]
  by_cases hbi : b.bexp = 2047
  · have hfb0 : b.frac = 0 := by omega
    rw [cls_inf' hbi hfb0, if_pos hbi]
    by_cases ha0 : a.bexp = 0 ∧ a.frac = 0
    · rw [cls_zero' ha0.1 ha0.2]
    · rw [cls_fin' (by omega) hai]
  rw [if_neg hbi]
  by_cases ha0 : a.bexp = 0 ∧ a.frac = 0
  · rw [if_pos ha0, cls_zero' ha0.1 ha0.2]
    by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
    · rw [if_pos hb0, cls_zero' hb0.1 hb0.2]
    · rw [if_neg hb0, cls_fin' (by omega) hbi]
  rw [if_neg ha0]
  by_cases hb0 : b.bexp = 0 ∧ b.frac = 0
  · rw [if_pos hb0, cls_zero' hb0.1 hb0.2, cls_fin' (by omega) hai]
  rw [if_neg hb0, cls_fin' (by omega) hai, cls_fin' (by omega) hbi]
  have := divFields_fin a.sign b.sign a.bexp a.frac b.bexp b.frac (by omega) (by omega) hfa hfb
    (by omega) (by omega)
  unfold divFields at this
  rw [if_neg (by omega), if_neg hai, if_neg hbi, if_neg ha0, if_neg hb0] at this
  exact this

end Lua.Num.SfRef

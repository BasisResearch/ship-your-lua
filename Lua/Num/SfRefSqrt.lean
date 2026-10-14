import Lua.Num.SfRefFmod

/-!
# `SfRef.sqrt`: newlib's fdlibm `__ieee754_sqrt` over the fields (lane float-sf6, (b2))

libm's `__ieee754_sqrt` (newlib 4.5.0 `libm/math/e_sqrt.c`, entry
`0x8002d448` in the ELF) works on the 32-bit halves `ix0:ix1` of its operand:

* `ix0 & 0x7ff00000 == 0x7ff00000` (∞, NaN): `x*x+x` (`e_sqrt.c:102-104`);
* `±0`: `x`; a negative: `(x-x)/(x-x)` (`e_sqrt.c:106-110`);
* a subnormal is normalised: whole words of 21 bits while `ix0 == 0`, then
  bit by bit to bit 20 (`e_sqrt.c:112-121`: `sqWords`, `sqClz`, `sqNorm`);
* `m -= 1023`, the hidden bit set, an odd `m` doubles `ix0:ix1`, `m >>= 1`
  (`e_sqrt.c:122-128`), and one more doubling (`e_sqrt.c:131-132`): the
  radicand `Y = 2 · 2^(m&1) · (ix0:ix1)`;
* the root bit by bit (`e_sqrt.c:133-171`): 22 bits of `q`, then 32 bits of
  `q1`, each a test `t ≤ ix0:ix1` of the doubled remainder against
  `s0:s1 + r` (`sqBit`, `sqRun`), the remainder doubled every step;
* a nonzero remainder rounds up by one unit of the 54-bit root (`e_sqrt.c:
  174-186`: with round to nearest, `one-tiny` and `one+tiny` are `one`, so
  `q1 += (q1&1)` after the `q1 == 0xffffffff` carry), then the halved root is
  packed at the halved exponent (`e_sqrt.c:187-191`: `sqrtPack`).

(b2) is `sqrt_eq : SfRef.sqrt x = F64.sqrt x`: the loop is `Nat.sqrt` with
its remainder (`sqRun_spec`), the rounding is `F64.round` (round to nearest:
a root is never a tie).
-/

namespace Lua.Num.SfRef

open F64

/-! ## The root, bit by bit -/

/-- One bit `ρ` of the root (`e_sqrt.c:135-144`, `:149-163`): the remainder
`W` (the doubled `ix0:ix1`), the root `Q` (`q:q1`; `s0:s1 = 2Q`). -/
def sqBit (ρ : Nat) (st : Nat × Nat) : Nat × Nat :=
  if 2 * st.2 + ρ ≤ st.1 then (2 * (st.1 - (2 * st.2 + ρ)), st.2 + ρ) else (2 * st.1, st.2)

/-- `n` bits, `2^(sh + n - 1)` down to `2^sh`. -/
def sqRun : Nat → Nat → Nat × Nat → Nat × Nat
  | 0, _, st => st
  | n + 1, sh, st => sqRun n sh (sqBit (2 ^ (sh + n)) st)

/-- The loop invariant before the bits below `2^p`: `Q` is `√N` to `2^p`,
`W` its remainder scaled. -/
structure SqInv (N p W Q : Nat) : Prop where
  le : Q * Q ≤ N
  rem : W * 2 ^ p = 2 * (N - Q * Q)
  lt : N < (Q + 2 ^ p) * (Q + 2 ^ p)
  dvd : 2 ^ p ∣ Q

theorem sq_add (a b : Nat) : (a + b) * (a + b) = a * a + (2 * a + b) * b := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.add_mul, Nat.two_mul, Nat.add_mul, Nat.mul_comm b a]
  omega

/-- The invariant with the bit `ρ` explicit. -/
theorem sqBit_inv' {N W Q ρ : Nat} (hρ : 0 < ρ) (hle : Q * Q ≤ N) (hrem : W * (2 * ρ) = 2 * (N - Q * Q))
    (hlt : N < (Q + 2 * ρ) * (Q + 2 * ρ)) (hdvd : 2 * ρ ∣ Q) :
    (sqBit ρ (W, Q)).2 * (sqBit ρ (W, Q)).2 ≤ N ∧
    (sqBit ρ (W, Q)).1 * ρ = 2 * (N - (sqBit ρ (W, Q)).2 * (sqBit ρ (W, Q)).2) ∧
    N < ((sqBit ρ (W, Q)).2 + ρ) * ((sqBit ρ (W, Q)).2 + ρ) ∧ ρ ∣ (sqBit ρ (W, Q)).2 := by
  have hW : W * ρ = N - Q * Q := by
    have : W * (2 * ρ) = 2 * (W * ρ) := by rw [Nat.mul_left_comm]
    omega
  have e1 : (Q + ρ) * (Q + ρ) = Q * Q + (2 * Q + ρ) * ρ := sq_add Q ρ
  have e2 : (Q + 2 * ρ) * (Q + 2 * ρ) = (Q + ρ) * (Q + ρ) + (2 * (Q + ρ) + ρ) * ρ := by
    rw [show Q + 2 * ρ = (Q + ρ) + ρ by omega, sq_add]
  have hdQ : ρ ∣ Q := Nat.dvd_trans (Nat.dvd_mul_left ρ 2) hdvd
  unfold sqBit
  dsimp only
  by_cases ht : 2 * Q + ρ ≤ W
  · rw [if_pos ht]
    dsimp only
    have hm : (2 * Q + ρ) * ρ ≤ W * ρ := Nat.mul_le_mul_right _ ht
    refine ⟨by omega, ?_, ?_, Nat.dvd_add hdQ (Nat.dvd_refl ρ)⟩
    · rw [Nat.mul_assoc, Nat.sub_mul, hW]; omega
    · rw [show Q + ρ + ρ = Q + 2 * ρ by omega]; exact hlt
  · rw [if_neg ht]
    dsimp only
    have hm : W * ρ < (2 * Q + ρ) * ρ := Nat.mul_lt_mul_of_pos_right (by omega) hρ
    refine ⟨hle, ?_, by omega, hdQ⟩
    rw [Nat.mul_assoc, hW]

theorem sqBit_inv {N p W Q : Nat} (h : SqInv N (p + 1) W Q) :
    SqInv N p (sqBit (2 ^ p) (W, Q)).1 (sqBit (2 ^ p) (W, Q)).2 := by
  obtain ⟨hle, hrem, hlt, hdvd⟩ := h
  have hP : 2 ^ (p + 1) = 2 * 2 ^ p := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hP] at hrem hlt hdvd
  obtain ⟨a, b, c, d⟩ := sqBit_inv' (Nat.two_pow_pos p) hle hrem hlt hdvd
  exact ⟨a, b, c, d⟩

theorem sqRun_inv (N sh : Nat) : ∀ n W Q, SqInv N (sh + n) W Q →
    SqInv N sh (sqRun n sh (W, Q)).1 (sqRun n sh (W, Q)).2 := by
  intro n
  induction n with
  | zero => intro W Q h; exact h
  | succ n ih =>
    intro W Q h
    unfold sqRun
    rw [show sh + (n + 1) = (sh + n) + 1 by omega] at h
    have := sqBit_inv h
    exact ih _ _ this

/-- `Nat.sqrt` by its bounds. -/
theorem sqrt_unique {N s : Nat} (h1 : s * s ≤ N) (h2 : N < (s + 1) * (s + 1)) : N.sqrt = s := by
  have a1 := Nat.sqrt_le N
  have a2 := Nat.lt_succ_sqrt N
  simp only [Nat.succ_eq_add_one] at a2
  rcases Nat.lt_trichotomy N.sqrt s with h | h | h
  · have : (N.sqrt + 1) * (N.sqrt + 1) ≤ s * s := Nat.mul_le_mul h h
    omega
  · exact h
  · have : (s + 1) * (s + 1) ≤ N.sqrt * N.sqrt := Nat.mul_le_mul h h
    omega

/-- The invariant before the first bit: `W = Y`, `Q = 0`. -/
theorem sqInv_init (Y : Nat) (hY : Y < 2 ^ 55) : SqInv (Y * 2 ^ 53) (32 + 22) Y 0 := by
  refine ⟨by simp, ?_, ?_, Nat.dvd_zero _⟩
  · rw [show (32 + 22 : Nat) = 53 + 1 by rfl, Nat.pow_succ]; simp; omega
  · simp only [Nat.zero_add]
    have : Y * 2 ^ 53 < 2 ^ 108 := by
      calc Y * 2 ^ 53 < 2 ^ 55 * 2 ^ 53 := Nat.mul_lt_mul_of_pos_right hY (Nat.two_pow_pos _)
        _ = 2 ^ 108 := by rw [← Nat.pow_add]
    calc Y * 2 ^ 53 < 2 ^ 108 := this
      _ = 2 ^ (32 + 22) * 2 ^ (32 + 22) := by rw [← Nat.pow_add]

/-- **The loop computes the root** (`e_sqrt.c:133-171`): from `(Y, 0)`, the
54 bits give `Q = √(Y·2^53)` and the remainder `W = 2 (Y·2^53 - Q²)`. -/
theorem sqRun_spec (Y : Nat) (hY : Y < 2 ^ 55) :
    sqRun 32 0 (sqRun 22 32 (Y, 0)) =
      (2 * (Y * 2 ^ 53 - (Y * 2 ^ 53).sqrt * (Y * 2 ^ 53).sqrt), (Y * 2 ^ 53).sqrt) := by
  have h0 := sqInv_init Y hY
  have h1 := sqRun_inv (Y * 2 ^ 53) 32 22 Y 0 h0
  generalize sqRun 22 32 (Y, 0) = st at h1 ⊢
  rcases st with ⟨W0, Q0⟩
  have h2 := sqRun_inv (Y * 2 ^ 53) 0 32 W0 Q0 (by simpa using h1)
  generalize sqRun 32 0 (W0, Q0) = st' at h2 ⊢
  obtain ⟨hle, hrem, hlt, _⟩ := h2
  simp only [Nat.pow_zero, Nat.mul_one] at hrem hlt
  have hs := sqrt_unique hle hlt
  rcases st' with ⟨W, Q⟩
  dsimp only at hle hrem hlt hs ⊢
  rw [hs, hrem]


/-! ## The reference -/

/-- The halved root packed at the halved exponent (`e_sqrt.c:174-191`): the
54-bit root `Q = q:q1` rounded up by one unit when the remainder is not zero
(round to nearest: `one-tiny` and `one+tiny` are `one`), halved, at the
biased exponent `k + 1023` (`(q>>1) + 0x3fe00000 + (m<<20)`, the hidden bit
of `q>>1` adding the last `1`). -/
def sqrtPack (Y : Nat) (k : Int) : F64 :=
  let st := sqRun 32 0 (sqRun 22 32 (Y, 0))
  BitVec.ofInt 64 ((k + 1022) * 2 ^ 52 + (((st.2 + if st.1 = 0 then 0 else 1) / 2 : Nat) : Int))

/-- A normalised `ix0:ix1` (bit 20 of `ix0` set, or masked in) at biased
exponent `m` (`e_sqrt.c:122-191`): `m -= 1023`, the hidden bit, an odd `m`
doubles, the pre-loop doubling, the root at `m >> 1`. -/
def sqCore (h l : Nat) (m : Int) : F64 :=
  let W := (h % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 + l
  sqrtPack (if (m - 1023) % 2 = 1 then 4 * W else 2 * W) ((m - 1023) / 2)

/-- A subnormal's whole-word shifts (`e_sqrt.c:113-116`: while `ix0 == 0`,
`m -= 21`, `ix0 |= ix1 >> 11`, `ix1 <<= 21`). -/
def sqWords : Nat → Nat → Nat → Int → Nat × Nat × Int
  | 0, h, l, m => (h, l, m)
  | n + 1, h, l, m => if h = 0 then sqWords n (l / 2 ^ 11) (l * 2 ^ 21 % 2 ^ 32) (m - 21) else (h, l, m)

/-- The shifts of `ix0` to bit 20 (`e_sqrt.c:117`, compiled as a do-while: at
least one when bit 20 is clear). -/
def sqClz : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, h => if 2 * h < 2 ^ 20 then sqClz n (2 * h) + 1 else 1

/-- The bit shifts (`e_sqrt.c:117-120`): `ix0 <<= i`, `m -= i - 1`,
`ix0 |= ix1 >> (32 - i)`, `ix1 <<= i` (`i = 0` when bit 20 is set). -/
def sqNorm (h l : Nat) (m : Int) : Nat × Nat × Int :=
  if 2 ^ 20 ≤ h then (h, l, m + 1)
  else
    let i := sqClz 20 h
    (h * 2 ^ i + l / 2 ^ (32 - i), l * 2 ^ i % 2 ^ 32, m - ((i - 1 : Nat) : Int))

/-- `__ieee754_sqrt` (`e_sqrt.c`) over the fields of `x`. -/
def sqrtFields (s : Bool) (e f : Nat) (x : F64) : F64 :=
  if e = 2047 then F64.add (F64.mul x x) x
  else if e = 0 ∧ f = 0 then x
  else if s then F64.div (F64.sub x x) (F64.sub x x)
  else if e = 0 then
    let w := sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0
    let n := sqNorm w.1 w.2.1 w.2.2
    sqCore n.1 n.2.1 n.2.2
  else sqCore (f / 2 ^ 32) (f % 2 ^ 32) e

/-- `SfRef.sqrt`. -/
def sqrt (x : F64) : F64 := sqrtFields x.sign x.bexp x.frac x

/-! ## The rounding is `F64.round` -/

theorem sqA (r : Nat) : (2 * r + 1) * (2 * r + 1) = 4 * (r * r) + 4 * r + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  rw [Nat.mul_mul_mul_comm]; omega
theorem sqB (r : Nat) : (2 * r) * (2 * r) = 4 * (r * r) := by
  rw [Nat.mul_mul_mul_comm]
theorem sqC (r : Nat) : (r + 1) * (r + 1) = r * r + 2 * r + 1 := by
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]; omega
theorem sqD (r : Nat) : (2 * r + 2) * (2 * r + 2) = 4 * ((r + 1) * (r + 1)) := by
  rw [show 2 * r + 2 = 2 * (r + 1) by omega, Nat.mul_mul_mul_comm]

/-- The root of `4a` from the root of `a` and its remainder: one more bit,
set when the remainder exceeds the root; exact iff `a`'s is. -/
theorem sqrt4 (a : Nat) :
    (4 * a).sqrt = 2 * a.sqrt + (if a.sqrt < a - a.sqrt * a.sqrt then 1 else 0) ∧
    (4 * a - (4 * a).sqrt * (4 * a).sqrt = 0 ↔ a - a.sqrt * a.sqrt = 0) := by
  have h1 := Nat.sqrt_le a
  have h2 := Nat.lt_succ_sqrt a
  simp only [Nat.succ_eq_add_one] at h2
  generalize a.sqrt = r at *
  have c := sqC r
  have A := sqA r
  have B := sqB r
  have D := sqD r
  by_cases h : r < a - r * r
  · rw [if_pos h]
    have hs : (4 * a).sqrt = 2 * r + 1 :=
      sqrt_unique (by omega) (by rw [show 2 * r + 1 + 1 = 2 * r + 2 by omega, D]; omega)
    rw [hs, A]; exact ⟨rfl, by omega⟩
  · rw [if_neg h]
    have hs : (4 * a).sqrt = 2 * r := sqrt_unique (by omega) (by rw [A]; omega)
    rw [hs, B]; exact ⟨by omega, by omega⟩

/-- A root of `a ∈ [2^104, 2^106)` has 53 bits. -/
theorem sqrt_bits {a : Nat} (h1 : 2 ^ 104 ≤ a) (h2 : a < 2 ^ 106) : 2 ^ 52 ≤ a.sqrt ∧ a.sqrt < 2 ^ 53 := by
  have s1 := Nat.sqrt_le a
  have s2 := Nat.lt_succ_sqrt a
  simp only [Nat.succ_eq_add_one] at s2
  constructor
  · refine Nat.le_of_not_lt fun hc => ?_
    have : (a.sqrt + 1) * (a.sqrt + 1) ≤ 2 ^ 52 * 2 ^ 52 := Nat.mul_le_mul hc hc
    rw [← Nat.pow_add] at this; omega
  · refine Nat.lt_of_not_le fun hc => ?_
    have : 2 ^ 53 * 2 ^ 53 ≤ a.sqrt * a.sqrt := Nat.mul_le_mul hc hc
    rw [← Nat.pow_add] at this; omega

theorem ofInt_pack (X : Int) (Z : Nat) (h : X = (Z : Int)) : BitVec.ofInt 64 X = BitVec.ofNat 64 Z := by
  rw [h, BitVec.ofInt_natCast]

/-- **The pack is `F64.round`** of `√a` at `2^(k-52)`, `a = W · 2^(o+52)`. -/
theorem sqrtPack_eq (W o : Nat) (k : Int) (hW1 : 2 ^ 52 ≤ W) (hW2 : W < 2 ^ 53) (ho : o ≤ 1)
    (hk1 : -600 ≤ k) (hk2 : k ≤ 600) :
    sqrtPack (2 ^ (o + 1) * W) k =
      round false (W * 2 ^ (o + 52)).sqrt (k - 52)
        (decide (W * 2 ^ (o + 52) - (W * 2 ^ (o + 52)).sqrt * (W * 2 ^ (o + 52)).sqrt ≠ 0 ∧
          (W * 2 ^ (o + 52)).sqrt < W * 2 ^ (o + 52) - (W * 2 ^ (o + 52)).sqrt * (W * 2 ^ (o + 52)).sqrt))
        (decide (W * 2 ^ (o + 52) - (W * 2 ^ (o + 52)).sqrt * (W * 2 ^ (o + 52)).sqrt ≠ 0)) := by
  have hY : 2 ^ (o + 1) * W < 2 ^ 55 := by
    have : 2 ^ (o + 1) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) (by omega)
    calc 2 ^ (o + 1) * W < 2 ^ 2 * 2 ^ 53 := Nat.mul_lt_mul_of_le_of_lt this hW2 (by decide)
      _ = 2 ^ 55 := by rw [← Nat.pow_add]
  have hN : 2 ^ (o + 1) * W * 2 ^ 53 = 4 * (W * 2 ^ (o + 52)) := by
    rw [Nat.mul_comm (2 ^ (o + 1)) W, Nat.mul_assoc, ← Nat.pow_add, Nat.mul_left_comm,
      show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add, show o + 1 + 53 = 2 + (o + 52) by omega]
  have ha1 : 2 ^ 104 ≤ W * 2 ^ (o + 52) := by
    calc 2 ^ 104 = 2 ^ 52 * 2 ^ 52 := by rw [← Nat.pow_add]
      _ ≤ W * 2 ^ (o + 52) := Nat.mul_le_mul hW1 (Nat.pow_le_pow_right (by decide) (by omega))
  have ha2 : W * 2 ^ (o + 52) < 2 ^ 106 := by
    calc W * 2 ^ (o + 52) < 2 ^ 53 * 2 ^ (o + 52) := Nat.mul_lt_mul_of_pos_right hW2 (Nat.two_pow_pos _)
      _ ≤ 2 ^ 53 * 2 ^ 53 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
      _ = 2 ^ 106 := by rw [← Nat.pow_add]
  unfold sqrtPack
  rw [sqRun_spec _ hY]
  dsimp only
  rw [hN]
  generalize W * 2 ^ (o + 52) = a at ha1 ha2 ⊢
  obtain ⟨e4, ex4⟩ := sqrt4 a
  have hr := sqrt_bits ha1 ha2
  have s1 := Nat.sqrt_le a
  generalize hr0 : a.sqrt = r at e4 ex4 hr s1 ⊢
  generalize hrem : a - r * r = rem at e4 ex4 ⊢
  generalize hs : (4 * a).sqrt = s at e4 ex4 ⊢
  -- the halved, rounded-up root is `r + [r < rem]`
  have hq : (s + (if 2 * (4 * a - s * s) = 0 then 0 else 1)) / 2 = r + (if r < rem then 1 else 0) := by
    by_cases h : r < rem
    · rw [if_pos h] at e4 ⊢
      have : 4 * a - s * s ≠ 0 := fun h' => by have := ex4.1 h'; omega
      rw [if_neg (by omega)]; omega
    · rw [if_neg h] at e4 ⊢
      by_cases h0 : rem = 0
      · have := ex4.2 h0
        rw [if_pos (by omega)]; omega
      · have : 4 * a - s * s ≠ 0 := fun h' => h0 (ex4.1 h')
        rw [if_neg (by omega)]; omega
  rw [hq]
  have hrne : rne r (decide (rem ≠ 0 ∧ r < rem)) (decide (rem ≠ 0)) = r + (if r < rem then 1 else 0) := by
    unfold rne
    by_cases h : r < rem
    · rw [if_pos h]; simp [h, show rem ≠ 0 by omega]
    · rw [if_neg h]; simp [h]
  have hlog : r.log2 = 52 := (Nat.log2_eq_iff (by omega)).2 ⟨hr.1, hr.2⟩
  have hT : target r (k - 52) = k - 52 := by unfold target; rw [hlog]; omega
  unfold round
  rw [hT, if_pos (Int.le_refl _), Int.sub_self, Int.toNat_zero]
  simp only [shr, if_true]
  rw [hrne]
  have hM1 : 2 ^ 52 ≤ r + (if r < rem then 1 else 0) := by split <;> omega
  have hM2 : r + (if r < rem then 1 else 0) ≤ 2 ^ 53 := by split <;> omega
  generalize r + (if r < rem then 1 else 0) = M at hM1 hM2 ⊢
  unfold finish packFin bits
  simp only [Bool.false_eq_true, if_false, Nat.zero_add]
  by_cases hc : M = 2 ^ 53
  · rw [if_pos hc, if_neg (by decide), if_neg (by omega), if_pos (Nat.le_refl _), ofInt_pack]
    omega
  · rw [if_neg hc, if_neg (by omega), if_neg (by omega), if_pos hM1, ofInt_pack]
    omega

/-- **`F64.sqrtCore` of a normalisable mantissa** `mant · 2^j = W ∈ [2^52, 2^53)`
at the biased exponent `mx` (`x = W · 2^(mx - 1075)`): the root of
`a = W · 2^(o + 52)` at `2^(k - 52)`, `mx - 1023 = 2k + o`. -/
theorem sqrtCore_norm (mant j : Nat) (mx : Int) (h1 : 2 ^ 52 ≤ mant * 2 ^ j) (h2 : mant * 2 ^ j < 2 ^ 53)
    (hmx1 : -51 ≤ mx) (hmx2 : mx ≤ 2046) :
    sqrtCore mant (mx - 1075 + j) =
      ((mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt, (mx - 1023) / 2 - 52,
        decide (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52) -
            (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt *
              (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt ≠ 0 ∧
          (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt <
            mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52) -
              (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt *
                (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt),
        decide (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52) -
            (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt *
              (mant * 2 ^ j * 2 ^ (((mx - 1023) % 2).toNat + 52)).sqrt ≠ 0)) := by
  have hm0 : 0 < mant := by
    rcases Nat.eq_zero_or_pos mant with h | h
    · subst h; simp at h1
    · exact h
  have hj : j ≤ 52 := by
    refine Nat.le_of_not_lt fun hc => ?_
    have : 2 ^ 53 ≤ mant * 2 ^ j :=
      calc 2 ^ 53 ≤ 1 * 2 ^ j := by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) hc
        _ ≤ mant * 2 ^ j := Nat.mul_le_mul_right _ hm0
    omega
  have hl1 : 2 ^ (52 - j) ≤ mant := by
    refine Nat.le_of_mul_le_mul_right (c := 2 ^ j) ?_ (Nat.two_pow_pos j)
    rw [← Nat.pow_add, show 52 - j + j = 52 by omega]; exact h1
  have hl2 : mant < 2 ^ (52 - j + 1) := by
    refine Nat.lt_of_mul_lt_mul_right (a := 2 ^ j) ?_
    rw [← Nat.pow_add, show 52 - j + 1 + j = 53 by omega]; exact h2
  have hlog : mant.log2 = 52 - j := (Nat.log2_eq_iff (by omega)).2 ⟨hl1, hl2⟩
  unfold sqrtCore
  simp only [show ∀ a : Int, a.ediv 2 = a / 2 from fun _ => rfl, hlog]
  have ht : min ((mx - 1075 + (j : Int)) / 2)
      (max ((((52 - j : Nat) : Int) + 1 + (mx - 1075 + (j : Int)) + 1) / 2 - 53) (-1074)) =
      (mx - 1023) / 2 - 52 := by omega
  rw [ht]
  have hsh : (mx - 1075 + (j : Int) - 2 * ((mx - 1023) / 2 - 52)).toNat = j + (((mx - 1023) % 2).toNat + 52) := by
    omega
  rw [hsh, Nat.shiftLeft_eq, Nat.pow_add, Nat.mul_assoc]

/-- **The core is `F64`'s rounded root** of `mant · 2^(mx - 1075 + j)`, for
the normalised words `(h % 2^20 + 2^20) : l = mant · 2^j`. -/
theorem sqCore_eq (h l mant j : Nat) (mx : Int) (hW : (h % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 + l = mant * 2 ^ j)
    (h1 : 2 ^ 52 ≤ mant * 2 ^ j) (h2 : mant * 2 ^ j < 2 ^ 53) (hmx1 : -51 ≤ mx) (hmx2 : mx ≤ 2046) :
    sqCore h l mx =
      round false (sqrtCore mant (mx - 1075 + j)).1 (sqrtCore mant (mx - 1075 + j)).2.1
        (sqrtCore mant (mx - 1075 + j)).2.2.1 (sqrtCore mant (mx - 1075 + j)).2.2.2 := by
  rw [sqrtCore_norm mant j mx h1 h2 hmx1 hmx2]
  unfold sqCore
  dsimp only
  rw [hW]
  have hk1 : -600 ≤ (mx - 1023) / 2 := by omega
  have hk2 : (mx - 1023) / 2 ≤ 600 := by omega
  by_cases ho : (mx - 1023) % 2 = 1
  · rw [if_pos ho, ho, show (4 : Nat) = 2 ^ (1 + 1) from rfl,
      sqrtPack_eq _ 1 _ h1 h2 (by decide) hk1 hk2]
    rfl
  · have ho0 : (mx - 1023) % 2 = 0 := by omega
    rw [if_neg ho, ho0, show (2 : Nat) * (mant * 2 ^ j) = 2 ^ (0 + 1) * (mant * 2 ^ j) from rfl,
      sqrtPack_eq _ 0 _ h1 h2 (by decide) hk1 hk2]
    rfl

/-! ## The subnormal normalisation -/

/-- A two-word left shift by `i ≤ 32`: `(l >> (32 - i)) : (l << i)` is `l · 2^i`. -/
theorem shl_words (l i : Nat) (hi : i ≤ 32) :
    l / 2 ^ (32 - i) * 2 ^ 32 + l * 2 ^ i % 2 ^ 32 = l * 2 ^ i := by
  have e : 2 ^ 32 = 2 ^ (32 - i) * 2 ^ i := by rw [← Nat.pow_add, Nat.sub_add_cancel hi]
  have hd : l * 2 ^ i / 2 ^ 32 = l / 2 ^ (32 - i) := by
    rw [e, Nat.mul_div_mul_right _ _ (Nat.two_pow_pos i)]
  rw [← hd]
  exact Nat.div_add_mod' _ _

/-- The bit shifts to bit 20 (`e_sqrt.c:117`). -/
theorem sqClz_spec : ∀ (n h : Nat), 0 < h → h < 2 ^ 20 → 2 ^ 20 ≤ h * 2 ^ n →
    1 ≤ sqClz n h ∧ sqClz n h ≤ n ∧ 2 ^ 20 ≤ h * 2 ^ sqClz n h ∧ h * 2 ^ sqClz n h < 2 ^ 21 := by
  intro n
  induction n with
  | zero => intro h _ h2 h3; simp at h3; omega
  | succ n ih =>
    intro h h1 h2 h3
    unfold sqClz
    by_cases hc : 2 * h < 2 ^ 20
    · rw [if_pos hc]
      have h3' : 2 ^ 20 ≤ 2 * h * 2 ^ n := by
        rw [Nat.pow_succ] at h3; rw [Nat.mul_comm 2 h, Nat.mul_assoc, Nat.mul_comm 2]; exact h3
      obtain ⟨a1, a2, a3, a4⟩ := ih (2 * h) (by omega) hc h3'
      have e : h * 2 ^ (sqClz n (2 * h) + 1) = 2 * h * 2 ^ sqClz n (2 * h) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [e]; exact ⟨by omega, by omega, a3, a4⟩
    · rw [if_neg hc]; simp only [Nat.pow_one]; omega

/-- `a · 2^i + b` below `2^21` when `a · 2^i` is and `b < 2^i`. -/
theorem add_below (a b i : Nat) (hi : i ≤ 21) (ha : a * 2 ^ i < 2 ^ 21) (hb : b < 2 ^ i) :
    a * 2 ^ i + b < 2 ^ 21 := by
  have e : 2 ^ 21 = 2 ^ (21 - i) * 2 ^ i := by rw [← Nat.pow_add, Nat.sub_add_cancel hi]
  rw [e] at ha ⊢
  have h1 : a < 2 ^ (21 - i) := Nat.lt_of_mul_lt_mul_right ha
  have h2 : (a + 1) * 2 ^ i ≤ 2 ^ (21 - i) * 2 ^ i := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-- The whole-word shifts (`e_sqrt.c:113-116`) of a nonzero 52-bit fraction:
`c` words of 21 bits. -/
theorem sqWords_spec (f : Nat) (hf0 : 0 < f) (hf : f < 2 ^ 52) :
    ∃ c : Nat, (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 * 2 ^ 32 + (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1 =
        f * 2 ^ (21 * c) ∧ (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2 = -21 * (c : Int) ∧
      0 < (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 ∧ (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 < 2 ^ 21 ∧
      (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1 < 2 ^ 32 := by
  have hl : f % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  by_cases h0 : f / 2 ^ 32 = 0
  · have hf32 : f < 2 ^ 32 := by omega
    have hfl : f % 2 ^ 32 = f := Nat.mod_eq_of_lt hf32
    unfold sqWords
    rw [if_pos h0, hfl]
    have s21 := shl_words f 21 (by decide)
    by_cases h1 : f / 2 ^ 11 = 0
    · -- two words: `f < 2^11`
      have hf11 : f < 2 ^ 11 := by omega
      have e1 : f * 2 ^ 21 % 2 ^ 32 = f * 2 ^ 21 := Nat.mod_eq_of_lt (by
        calc f * 2 ^ 21 < 2 ^ 11 * 2 ^ 21 := Nat.mul_lt_mul_of_pos_right hf11 (Nat.two_pow_pos _)
          _ = 2 ^ 32 := by rw [← Nat.pow_add])
      unfold sqWords
      rw [if_pos h1, e1]
      have e2 : f * 2 ^ 21 / 2 ^ 11 = f * 2 ^ 10 := by
        rw [show (2 : Nat) ^ 21 = 2 ^ 10 * 2 ^ 11 by rw [← Nat.pow_add], ← Nat.mul_assoc,
          Nat.mul_div_cancel _ (Nat.two_pow_pos 11)]
      have e3 : f * 2 ^ 21 * 2 ^ 21 % 2 ^ 32 = 0 := by
        rw [Nat.mul_assoc, ← Nat.pow_add, show (2 : Nat) ^ (21 + 21) = 2 ^ 10 * 2 ^ 32 by rw [← Nat.pow_add],
          ← Nat.mul_assoc]
        exact Nat.mul_mod_left _ _
      have hpos : 0 < f * 2 ^ 10 := Nat.mul_pos hf0 (Nat.two_pow_pos _)
      unfold sqWords
      rw [e2, if_neg (by omega), e3]
      refine ⟨2, ?_, by simp <;> omega, hpos, ?_, by simp⟩
      · rw [Nat.add_zero, Nat.mul_assoc, ← Nat.pow_add]
      · calc f * 2 ^ 10 < 2 ^ 11 * 2 ^ 10 := Nat.mul_lt_mul_of_pos_right hf11 (Nat.two_pow_pos _)
          _ = 2 ^ 21 := by rw [← Nat.pow_add]
    · unfold sqWords
      rw [if_neg h1]
      refine ⟨1, by rw [s21], by simp <;> omega, by omega, ?_, Nat.mod_lt _ (by decide)⟩
      exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; omega)
  · unfold sqWords
    rw [if_neg h0]
    refine ⟨0, ?_, by simp, by omega, ?_, hl⟩
    · simp only [Nat.mul_zero, Nat.pow_zero, Nat.mul_one]; exact Nat.div_add_mod' f _
    · exact Nat.div_lt_of_lt_mul (by rw [← Nat.pow_add]; omega)

/-- **The normalisation of a subnormal** (`e_sqrt.c:112-121`): the words are
`f · 2^j ∈ [2^52, 2^53)` at `m = 1 - j`, bit 20 of `ix0` set. -/
theorem sqNorm_spec (f : Nat) (hf0 : 0 < f) (hf : f < 2 ^ 52) :
    ∃ j : Nat,
      ((sqNorm (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
          (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2).1 % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 +
        (sqNorm (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
          (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2).2.1 = f * 2 ^ j ∧
      (sqNorm (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
          (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2).2.2 = 1 - (j : Int) ∧
      2 ^ 52 ≤ f * 2 ^ j ∧ f * 2 ^ j < 2 ^ 53 := by
  obtain ⟨c, hw, hm, h0, h21, hl⟩ := sqWords_spec f hf0 hf
  generalize sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0 = w at hw hm h0 h21 hl ⊢
  obtain ⟨h, l, m⟩ := w
  dsimp only at hw hm h0 h21 hl ⊢
  subst hm
  unfold sqNorm
  by_cases hb : 2 ^ 20 ≤ h
  · rw [if_pos hb]
    dsimp only
    refine ⟨21 * c, ?_, by omega, ?_, ?_⟩
    · rw [← hw]; congr 2; omega
    · rw [← hw]; omega
    · rw [← hw]; omega
  · rw [if_neg hb]
    dsimp only
    obtain ⟨i1, i2, i3, i4⟩ := sqClz_spec 20 h h0 (by omega)
      (calc 2 ^ 20 = 1 * 2 ^ 20 := by rw [Nat.one_mul]
        _ ≤ h * 2 ^ 20 := Nat.mul_le_mul_right _ h0)
    generalize sqClz 20 h = i at i1 i2 i3 i4 ⊢
    have sw := shl_words l i (by omega)
    have hlo : l / 2 ^ (32 - i) < 2 ^ i := by
      refine Nat.div_lt_of_lt_mul ?_
      rw [← Nat.pow_add, show 32 - i + i = 32 by omega]; exact hl
    have hh := add_below h (l / 2 ^ (32 - i)) i (by omega) i4 hlo
    have hmask : (h * 2 ^ i + l / 2 ^ (32 - i)) % 2 ^ 20 + 2 ^ 20 = h * 2 ^ i + l / 2 ^ (32 - i) := by omega
    have e : (h * 2 ^ i + l / 2 ^ (32 - i)) * 2 ^ 32 + l * 2 ^ i % 2 ^ 32 = f * 2 ^ (21 * c + i) := by
      rw [Nat.pow_add, ← Nat.mul_assoc, ← hw, Nat.add_mul, Nat.add_mul, ← sw]
      rw [Nat.mul_assoc h, Nat.mul_comm (2 ^ i) (2 ^ 32), ← Nat.mul_assoc]
      omega
    refine ⟨21 * c + i, by rw [hmask, e], by omega, ?_, ?_⟩
    · rw [← e]; omega
    · rw [← e]; omega

/-! ## Assembly: `SfRef.sqrt = F64.sqrt` -/

theorem cls_qnan : qnan.cls = .nan := by decide
theorem cls_infty_false : (infty false).cls = .inf false := by decide
theorem cls_zero_false : (zero false).cls = .zero false := by decide

/-- The rounded root of a positive finite value, as `F64.sqrt` takes it. -/
theorem sqrt_fin (x : F64) {m : Nat} {e : Int} (h : x.cls = .fin false m e) :
    F64.sqrt x = round false (sqrtCore m e).1 (sqrtCore m e).2.1 (sqrtCore m e).2.2.1 (sqrtCore m e).2.2.2 := by
  unfold F64.sqrt; rw [h]

/-- **(b2)**: `SfRef.sqrt` is `F64.sqrt`, so `Float.Model.sqrt` (`F64.sqrt_eq_model`). -/
theorem sqrt_eq (x : F64) : sqrt x = F64.sqrt x := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold sqrt sqrtFields
  by_cases h1 : x.bexp = 2047
  · rw [if_pos h1]
    by_cases h2 : x.frac = 0
    · have hc := cls_inf' h1 h2
      unfold F64.sqrt F64.mul
      rw [hc]
      dsimp only
      rw [Bool.xor_self]
      unfold F64.add
      rw [hc, cls_infty_false]
      cases x.sign <;> rfl
    · have hc := cls_nan' h1 h2
      unfold F64.sqrt F64.mul
      rw [hc]
      unfold F64.add
      rw [hc, cls_qnan]
  · rw [if_neg h1]
    by_cases h0 : x.bexp = 0 ∧ x.frac = 0
    · rw [if_pos h0]
      unfold F64.sqrt
      rw [cls_zero' h0.1 h0.2]
      dsimp only
      have := bits_self x
      rw [h0.1, h0.2] at this
      exact this.symm
    · rw [if_neg h0]
      have h0' : x.bexp ≠ 0 ∨ x.frac ≠ 0 := by omega
      have hc := cls_fin' h0' h1
      by_cases hs : x.sign = true
      · rw [if_pos hs]
        rw [hs] at hc
        unfold F64.sqrt F64.sub
        rw [hc]
        dsimp only
        unfold normalize
        rw [if_pos (Int.sub_self _)]
        unfold F64.div
        rw [cls_zero_false]
      · rw [if_neg hs]
        rw [show x.sign = false by simpa using hs] at hc
        rw [sqrt_fin x hc]
        by_cases he : x.bexp = 0
        · rw [if_pos he]
          have hf0 : 0 < x.frac := by omega
          obtain ⟨j, hw, hm, hj1, hj2⟩ := sqNorm_spec x.frac hf0 hf
          have hj : j ≤ 52 := by
            refine Nat.le_of_not_lt fun hc' => ?_
            have : 2 ^ 53 ≤ x.frac * 2 ^ j :=
              calc 2 ^ 53 ≤ 1 * 2 ^ j := by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) hc'
                _ ≤ x.frac * 2 ^ j := Nat.mul_le_mul_right _ hf0
            omega
          dsimp only
          rw [sqCore_eq _ _ x.frac j _ hw hj1 hj2 (by omega) (by omega), hm]
          unfold cm ce
          rw [if_pos he, if_pos he, show (1 - (j : Int)) - 1075 + j = -1074 by omega]
        · rw [if_neg he]
          rw [sqCore_eq _ _ (2 ^ 52 + x.frac) 0 x.bexp (by omega) (by omega) (by omega) (by omega)
            (by omega)]
          unfold cm ce
          rw [if_neg he, if_neg he, Nat.add_comm (2 ^ 52), show ((x.bexp : Int) - 1075 + ((0 : Nat) : Int)) =
            (x.bexp : Int) - 1075 by omega]

end Lua.Num.SfRef

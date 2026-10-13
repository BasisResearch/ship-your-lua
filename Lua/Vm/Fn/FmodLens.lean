import Lua.Vm.Fn.SfLens

/-!
# The signed-integer lens on `__ieee754_fmod`'s lifted function (lane float-sf5, (b1))

fdlibm's `e_fmod.c` works on 32-bit halves held sign-extended in 64-bit
registers (`sext.w`, `addw`, `subw`, `slliw`, `srliw`, `sraiw`, `sllw`,
`srlw`, `sraw`) and on small signed integers (`ix`, `iy`, `n`). Every
register value is kept in one normal form, `BitVec.ofInt 64 i` of an `Int`
expression `i` (`omega`'s domain: linear, with `/` and `%` by literals), and
every guard a `decide` over `Int`:

* a word operation is `BitVec.ofInt 32` arithmetic (`ofInt` is a ring
  homomorphism), its sign extension `Int.bmod`, dropped when the word is in
  range (`bmod_small`);
* a literal is `ofInt` of its signed value (`lit_pos`, `lit_neg`);
* a comparison is one on `toInt`/`toNat`, which `ofInt` gives back in range.

The lemmas are conditional rewrites; `fm_nf` applies them with `omega` as the
discharger.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.FmodLens

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- Powers of two are monotone (in `Int`). -/
theorem ipow_mono {k j : Nat} (h : k ≤ j) : (2 : Int) ^ k ≤ 2 ^ j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Int.le_refl _
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 : (0 : Int) < 2 ^ (k + d) := Int.pow_pos (by decide)
    rw [show k + (d + 1) = (k + d) + 1 by omega, Int.pow_succ]
    omega

/-! ## Literals and the normal form -/

theorem lit_pos (n : Nat) (h : n < 2 ^ 63) : BitVec.ofNat 64 n = BitVec.ofInt 64 (n : Int) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem lit_neg (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    BitVec.ofNat 64 n = BitVec.ofInt 64 ((n : Int) - 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem lit_pos' (n : Nat) (h : n < 2 ^ 63) : (OfNat.ofNat n : BitVec 64) = BitVec.ofInt 64 (n : Int) :=
  lit_pos n h

theorem lit_neg' (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    (OfNat.ofNat n : BitVec 64) = BitVec.ofInt 64 ((n : Int) - 2 ^ 64) :=
  lit_neg n h1 h2

theorem ofInt_toInt (i : Int) (h1 : -2 ^ 63 ≤ i) (h2 : i < 2 ^ 63) : (BitVec.ofInt 64 i).toInt = i := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod]; split <;> omega

theorem ofInt_toNat (i : Int) : ((BitVec.ofInt 64 i).toNat : Int) = i % 2 ^ 64 := by
  rw [BitVec.toNat_ofInt]; have : 0 ≤ i % 2 ^ 64 := Int.emod_nonneg _ (by decide); omega

theorem bmod_small (z : Int) (h1 : -2 ^ 31 ≤ z) (h2 : z < 2 ^ 31) : z.bmod (2 ^ 32) = z := by
  simp only [Int.bmod]; split <;> omega

/-- A word with bit 31 set, sign-extended. -/
theorem bmod_high' (z : Int) (h1 : 2147483648 ≤ z) (h2 : z < 4294967296) : z.bmod 4294967296 = z - 4294967296 := by
  simp only [Int.bmod]; split <;> omega

/-- `bmod_small` on the evaluated modulus. -/
theorem bmod_small' (z : Int) (h1 : -2147483648 ≤ z) (h2 : z < 2147483648) : z.bmod 4294967296 = z :=
  bmod_small z (by omega) (by omega)

theorem bmod64_small (z : Int) (h1 : -2 ^ 63 ≤ z) (h2 : z < 2 ^ 63) : z.bmod (2 ^ 64) = z := by
  simp only [Int.bmod]; split <;> omega

/-- `ofInt 64` is periodic: an out-of-range argument by its signed residue. -/
theorem ofInt_bmod (z : Int) : BitVec.ofInt 64 z = BitVec.ofInt 64 (z.bmod (2 ^ 64)) := by
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt, Int.bmod_bmod]

/-! ## Words -/

/-- The low word. -/
theorem lo_ofInt (i : Int) : Sail.BitVec.extractLsb (BitVec.ofInt 64 i) 31 0 = BitVec.ofInt (31 - 0 + 1) i := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    Nat.shiftRight_zero]
  have h1 : 0 ≤ i % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h2 : 0 ≤ i % 2 ^ (31 - 0 + 1) := Int.emod_nonneg _ (by decide)
  omega

/-- `sext.w`: the low word sign-extended. -/
theorem sext_ofInt (z : Int) :
    sign_extend (m := 64) (BitVec.ofInt (31 - 0 + 1) z) = BitVec.ofInt 64 (z.bmod (2 ^ 32)) := by
  apply BitVec.eq_of_toInt_eq
  rw [SfLens.sext_eq, BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  have h1 := Int.bmod_lt (x := z) (m := 2 ^ 32) (by decide)
  have h2 := Int.le_bmod (x := z) (m := 2 ^ 32) (by decide)
  rw [bmod64_small _ (by omega) (by omega)]

theorem sub32 (a b : Int) :
    BitVec.ofInt (31 - 0 + 1) a - BitVec.ofInt (31 - 0 + 1) b = BitVec.ofInt (31 - 0 + 1) (a - b) := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

theorem add32 (a b : Int) :
    BitVec.ofInt (31 - 0 + 1) a + BitVec.ofInt (31 - 0 + 1) b = BitVec.ofInt (31 - 0 + 1) (a + b) := by
  rw [BitVec.ofInt_add]

theorem twoPow_ofInt (w n : Nat) : BitVec.twoPow w n = BitVec.ofInt w ((2 : Int) ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_twoPow, BitVec.toNat_ofInt]
  have : ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) := by simp
  rw [this, ← Int.natCast_emod, Int.toNat_natCast]

/-- `slliw`/`sllw`: a shift left. -/
theorem sll32 {m : Nat} (a : Int) (k : BitVec m) :
    shift_bits_left (BitVec.ofInt (31 - 0 + 1) a) k = BitVec.ofInt (31 - 0 + 1) (a * 2 ^ k.toNat) := by
  unfold shift_bits_left
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow, twoPow_ofInt, ← BitVec.ofInt_mul]

/-- `srliw`/`srlw`: a logical shift right of the unsigned word. -/
theorem srl32 {m : Nat} (a : Int) (k : BitVec m) :
    shift_bits_right (BitVec.ofInt (31 - 0 + 1) a) k =
      BitVec.ofInt (31 - 0 + 1) ((a % 2 ^ 32) / 2 ^ k.toNat) := by
  unfold shift_bits_right
  rw [BitVec.ushiftRight_eq']
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  have e32 : ((2 ^ (31 - 0 + 1) : Nat) : Int) = 2 ^ 32 := by decide
  rw [e32]
  have h0 : 0 ≤ a % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have hl : a % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  obtain ⟨u, hu⟩ : ∃ u : Nat, a % 2 ^ 32 = (u : Int) := ⟨_, (Int.toNat_of_nonneg h0).symm⟩
  rw [hu, Int.toNat_natCast]
  have hP : ((2 : Int) ^ k.toNat) = ((2 ^ k.toNat : Nat) : Int) := by simp
  rw [hP, ← Int.natCast_ediv]
  have : u / 2 ^ k.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  generalize u / 2 ^ k.toNat = q at this ⊢
  omega

/-- `sraiw`/`sraw`: an arithmetic shift right of the signed word. -/
theorem sra32 {m : Nat} (a : Int) (k : BitVec m) :
    shift_bits_right_arith (BitVec.ofInt (31 - 0 + 1) a) k =
      BitVec.ofInt (31 - 0 + 1) (a.bmod (2 ^ 32) >>> k.toNat) := by
  unfold shift_bits_right_arith
  rw [BitVec.sshiftRight_eq, BitVec.toInt_ofInt]
  simp [BitVec.toNatInt]

/-- Any sign extension to 64 bits, by the signed value. -/
theorem sext64 {n : Nat} (x : BitVec n) (h : n ≤ 64) : sign_extend (m := 64) x = BitVec.ofInt 64 x.toInt := by
  apply BitVec.eq_of_toInt_eq
  rw [SfLens.sext_eq, BitVec.toInt_signExtend_of_le h, BitVec.toInt_ofInt]
  have h1 := BitVec.toInt_lt (x := x)
  have h2 := BitVec.le_toInt (x := x)
  have : (2 : Int) ^ (n - 1) ≤ 2 ^ 63 := by
    have : (2 : Nat) ^ (n - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast this
  rw [bmod64_small _ (by omega) (by omega)]

/-- A field of a word's low bits (a shift amount, `extractLsb 4 0`). -/
theorem lo5_ofInt (i : Int) :
    Sail.BitVec.extractLsb (BitVec.ofInt (31 - 0 + 1) i) 4 0 = BitVec.ofInt (4 - 0 + 1) i := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, BitVec.toNat_ofInt,
    Nat.shiftRight_zero]
  have h1 : 0 ≤ i % 2 ^ (31 - 0 + 1) := Int.emod_nonneg _ (by decide)
  have h2 : 0 ≤ i % 2 ^ (4 - 0 + 1) := Int.emod_nonneg _ (by decide)
  omega

theorem toNat_ofInt5 (i : Int) : (BitVec.ofInt (4 - 0 + 1) i).toNat = (i % 32).toNat := by
  rw [BitVec.toNat_ofInt]; rfl

theorem toNat_ofInt32 (i : Int) : (BitVec.ofInt (31 - 0 + 1) i).toNat = (i % 2 ^ 32).toNat := by
  rw [BitVec.toNat_ofInt]; rfl

theorem toInt_ofInt32 (i : Int) : (BitVec.ofInt (31 - 0 + 1) i).toInt = i.bmod (2 ^ 32) := by
  rw [BitVec.toInt_ofInt]

theorem add64 (a b : Int) : BitVec.ofInt 64 a + BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) := by
  rw [BitVec.ofInt_add]

theorem sub64 (a b : Int) : BitVec.ofInt 64 a - BitVec.ofInt 64 b = BitVec.ofInt 64 (a - b) := by
  rw [Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg, BitVec.sub_eq_add_neg]

/-- `slli` by a literal. -/
theorem sll64 {m : Nat} (a : Int) (k : BitVec m) :
    shift_bits_left (BitVec.ofInt 64 a) k = BitVec.ofInt 64 (a * 2 ^ k.toNat) := by
  unfold shift_bits_left
  rw [BitVec.shiftLeft_eq', BitVec.shiftLeft_eq_mul_twoPow, twoPow_ofInt, ← BitVec.ofInt_mul]

/-- `srli` by a literal: of the unsigned value. -/
theorem srl64 {m : Nat} (a : Int) (k : BitVec m) :
    shift_bits_right (BitVec.ofInt 64 a) k = BitVec.ofInt 64 ((a % 2 ^ 64) / 2 ^ k.toNat) := by
  unfold shift_bits_right
  rw [BitVec.ushiftRight_eq']
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofInt, BitVec.toNat_ofInt, Nat.shiftRight_eq_div_pow]
  have e64 : ((2 ^ 64 : Nat) : Int) = 2 ^ 64 := by decide
  rw [e64]
  have h0 : 0 ≤ a % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have hl : a % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  obtain ⟨u, hu⟩ : ∃ u : Nat, a % 2 ^ 64 = (u : Int) := ⟨_, (Int.toNat_of_nonneg h0).symm⟩
  rw [hu, Int.toNat_natCast]
  have hP : ((2 : Int) ^ k.toNat) = ((2 ^ k.toNat : Nat) : Int) := by simp
  rw [hP, ← Int.natCast_ediv]
  have : u / 2 ^ k.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  generalize u / 2 ^ k.toNat = q at this ⊢
  omega

/-! ## Comparisons -/

theorem slt_ofInt (a b : Int) (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    zopz0zI_s (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a < b) := by
  rw [SfLens.slt_int', ofInt_toInt a ha1 ha2, ofInt_toInt b hb1 hb2]

theorem sge_ofInt (a b : Int) (ha1 : -2 ^ 63 ≤ a) (ha2 : a < 2 ^ 63) (hb1 : -2 ^ 63 ≤ b) (hb2 : b < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (b ≤ a) := by
  rw [SfLens.sge_int, ofInt_toInt a ha1 ha2, ofInt_toInt b hb1 hb2]

theorem ult_ofInt (a b : Int) :
    zopz0zI_u (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (a % 2 ^ 64 < b % 2 ^ 64) := by
  unfold zopz0zI_u
  simp only [BitVec.toNatInt, Int.ofNat_eq_coe, ofInt_toNat]

theorem uge_ofInt (a b : Int) :
    zopz0zKzJ_u (BitVec.ofInt 64 a) (BitVec.ofInt 64 b) = decide (b % 2 ^ 64 ≤ a % 2 ^ 64) := by
  unfold zopz0zKzJ_u
  simp only [BitVec.toNatInt, Int.ofNat_eq_coe, ofInt_toNat]

theorem beq_ofInt (a b : Int) :
    (BitVec.ofInt 64 a == BitVec.ofInt 64 b) = decide (a % 2 ^ 64 = b % 2 ^ 64) := by
  rw [SfLens.beq_toNat]
  apply decide_eq_decide.2
  rw [← ofInt_toNat a, ← ofInt_toNat b]
  omega

theorem bne_ofInt (a b : Int) :
    (BitVec.ofInt 64 a != BitVec.ofInt 64 b) = !decide (a % 2 ^ 64 = b % 2 ^ 64) := by
  simp only [bne, beq_ofInt]

/-! ## Bitwise operations -/

theorem ofInt_ofNat (n : Nat) : BitVec.ofInt 64 (n : Int) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq; simp

/-- A field mask: `a & ((2^l - 1) · 2^j)` keeps bits `[j, j + l)`. -/
theorem land_field (a j l : Nat) : a &&& ((2 ^ l - 1) * 2 ^ j) = (a / 2 ^ j % 2 ^ l) * 2 ^ j := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow]
  by_cases hi : j ≤ i
  · simp only [hi, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
      Nat.testBit_div_two_pow]
    rw [show i - j + j = i by omega]
    by_cases hl : i - j < l <;> simp [hl]
  · simp [hi]

/-- `and` with a field mask, on a non-negative value. -/
theorem and_field (a : Int) (m j l : Nat) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) (hm : m = (2 ^ l - 1) * 2 ^ j)
    (hm2 : m < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 (m : Int) = BitVec.ofInt 64 (a / 2 ^ j % 2 ^ l * 2 ^ j) := by
  obtain ⟨u, rfl⟩ : ∃ u : Nat, a = (u : Int) := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
  rw [ofInt_ofNat, ofInt_ofNat]
  have e : ((u : Int) / 2 ^ j % 2 ^ l * 2 ^ j) = ((u / 2 ^ j % 2 ^ l * 2 ^ j : Nat) : Int) := by
    simp [Int.natCast_ediv, Int.natCast_emod, Int.natCast_mul, Int.natCast_pow]
  rw [e, ofInt_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), Nat.mod_eq_of_lt (by omega : m < 2 ^ 64), hm, land_field]
  have : u / 2 ^ j % 2 ^ l * 2 ^ j ≤ u := by
    have h1 : u / 2 ^ j % 2 ^ l ≤ u / 2 ^ j := Nat.mod_le _ _
    have h2 : u / 2 ^ j * 2 ^ j ≤ u := Nat.div_mul_le_self _ _
    exact Nat.le_trans (Nat.mul_le_mul_right _ h1) h2
  omega

theorem and_2047 (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2047 = BitVec.ofInt 64 (a % 2048) := by
  have := and_field a 2047 0 11 ha ha2 (by decide) (by decide)
  simp only [Int.pow_zero, Int.ediv_one, Int.mul_one] at this
  exact this
theorem and_fffff (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 1048575 = BitVec.ofInt 64 (a % 1048576) := by
  have := and_field a 1048575 0 20 ha ha2 (by decide) (by decide)
  simp only [Int.pow_zero, Int.ediv_one, Int.mul_one] at this
  exact this
theorem and_7fffffff (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2147483647 = BitVec.ofInt 64 (a % 2147483648) := by
  have := and_field a 2147483647 0 31 ha ha2 (by decide) (by decide)
  simp only [Int.pow_zero, Int.ediv_one, Int.mul_one] at this
  exact this
theorem and_7ff00000 (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2146435072 = BitVec.ofInt 64 (a / 1048576 % 2048 * 1048576) :=
  and_field a 2146435072 20 11 ha ha2 (by decide) (by decide)
/-- `and` with the sign-extended `0x80000000` (the sign word of a high word). -/
theorem and_hi31 (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 32) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2147483648) = BitVec.ofInt 64 (a / 2147483648 * 2147483648) := by
  obtain ⟨u, rfl⟩ : ∃ u : Nat, a = (u : Int) := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
  have hu : u < 2 ^ 32 := by omega
  have h1 : BitVec.ofInt 64 (-2147483648) = BitVec.ofNat 64 ((2 ^ 33 - 1) * 2 ^ 31) := by decide
  have e : ((u : Int) / 2147483648 * 2147483648) = ((u / 2 ^ 31 % 2 ^ 33 * 2 ^ 31 : Nat) : Int) := by
    have : u / 2 ^ 31 % 2 ^ 33 = u / 2 ^ 31 := Nat.mod_eq_of_lt (by omega)
    rw [this]; omega
  rw [h1, ofInt_ofNat, e, ofInt_ofNat, ← land_field]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), Nat.mod_eq_of_lt (by decide : (2 ^ 33 - 1) * 2 ^ 31 < 2 ^ 64)]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left (by omega))).symm

/-- `or` of disjoint non-negative values: the sum (`b` below `2^k`, `a` a multiple). -/
theorem or_disj (a b : Int) (k : Nat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 2 ^ k = 0) (hbk : b < 2 ^ k)
    (hab : a + b < 2 ^ 64) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) := by
  obtain ⟨u, rfl⟩ : ∃ u : Nat, a = (u : Int) := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
  obtain ⟨v, rfl⟩ : ∃ v : Nat, b = (v : Int) := ⟨b.toNat, (Int.toNat_of_nonneg hb).symm⟩
  rw [ofInt_ofNat, ofInt_ofNat, show ((u : Int) + v) = ((u + v : Nat) : Int) by simp, ofInt_ofNat]
  have hk : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by simp
  rw [hk] at hak hbk
  have hu : u % 2 ^ k = 0 := by exact_mod_cast hak
  have hv : v < 2 ^ k := by exact_mod_cast hbk
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), Nat.mod_eq_of_lt (by omega : v < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : u + v < 2 ^ 64)]
  obtain ⟨q, rfl⟩ : ∃ q, u = 2 ^ k * q := ⟨u / 2 ^ k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hu)).symm⟩
  rw [Nat.mul_comm, SfLens.or_add _ _ _ hv]

theorem or_disj' (a b : Int) (k : Nat) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 2 ^ k = 0) (hbk : b < 2 ^ k)
    (hab : a + b < 2 ^ 64) : BitVec.ofInt 64 b ||| BitVec.ofInt 64 a = BitVec.ofInt 64 (a + b) := by
  rw [BitVec.or_comm]; exact or_disj a b k ha hb hak hbk hab

/-- `or_disj` at the bit positions the routine packs at (`k` fixed, so a
`simp` lemma with `omega` discharging the rest). -/
theorem or_k20 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 1048576 = 0) (hbk : b < 1048576)
    (hab : a + b < 18446744073709551616) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) :=
  or_disj a b 20 ha hb (by omega) (by omega) (by omega)
theorem or_k31 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 2147483648 = 0) (hbk : b < 2147483648)
    (hab : a + b < 18446744073709551616) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) :=
  or_disj a b 31 ha hb (by omega) (by omega) (by omega)
theorem or_k32 (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 4294967296 = 0) (hbk : b < 4294967296)
    (hab : a + b < 18446744073709551616) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) :=
  or_disj a b 32 ha hb (by omega) (by omega) (by omega)
theorem or_k20' (a b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hak : a % 1048576 = 0) (hbk : b < 1048576)
    (hab : a + b < 18446744073709551616) : BitVec.ofInt 64 b ||| BitVec.ofInt 64 a = BitVec.ofInt 64 (a + b) :=
  or_disj' a b 20 ha hb (by omega) (by omega) (by omega)

/-- The sign word or-ed into a packed high word: `a | (sx + b)` (`sx` bit 31). -/
theorem or_sx (a sx b : Int) (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : sx = 0 ∨ sx = 2147483648)
    (hak : a % 1048576 = 0) (hbk : b < 1048576) (hab : a + b < 2147483648) :
    BitVec.ofInt 64 a ||| BitVec.ofInt 64 (sx + b) = BitVec.ofInt 64 (sx + (a + b)) := by
  rw [← or_k31 sx b (by omega) hb (by omega) (by omega) (by omega), ← BitVec.or_assoc,
    BitVec.or_comm (BitVec.ofInt 64 a), BitVec.or_assoc,
    or_k20 a b ha hb hak hbk (by omega), or_k31 sx (a + b) (by omega) (by omega) (by omega) hab (by omega)]

/-- `or` of a value whose low `k` bits are zero and a non-negative value below
`2^k` (any sign for the first: two's complement keeps the low bits). -/
theorem or_low (a b : Int) (k : Nat) (hk : k ≤ 64) (hak : a % 2 ^ k = 0) (hb : 0 ≤ b) (hbk : b < 2 ^ k) :
    BitVec.ofInt 64 a ||| BitVec.ofInt 64 b = BitVec.ofInt 64 (a + b) := by
  have hK : (2 : Int) ^ k = ((2 ^ k : Nat) : Int) := by simp
  have h64 : (2 ^ k : Nat) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hk
  obtain ⟨c, hc⟩ := h64
  -- the unsigned values
  have hu := ofInt_toNat a
  have hv := ofInt_toNat b
  have huv := ofInt_toNat (a + b)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  generalize hU : (BitVec.ofInt 64 a).toNat = U at hu
  generalize hV : (BitVec.ofInt 64 b).toNat = V at hv
  generalize hW : (BitVec.ofInt 64 (a + b)).toNat = W at huv
  have hPk : (0 : Int) < 2 ^ k := by rw [hK]; exact_mod_cast Nat.two_pow_pos k
  -- `U` is a multiple of `2^k`, `V = b < 2^k`, `W = U + V`
  have hdvd : (2 : Int) ^ k ∣ 2 ^ 64 := by
    rw [hK, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by simp, hc]
    exact Int.natCast_dvd_natCast.2 (Nat.dvd_mul_right _ _)
  have hUk : U % 2 ^ k = 0 := by
    have : (U : Int) % 2 ^ k = 0 := by rw [hu, Int.emod_emod_of_dvd _ hdvd]; exact hak
    rw [hK] at this; exact_mod_cast this
  have hk64 : (2 : Int) ^ k ≤ 2 ^ 64 := by
    rw [hK, show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by simp]
    exact_mod_cast Nat.pow_le_pow_right (by decide) hk
  have hVb : (V : Int) = b := by rw [hv]; exact Int.emod_eq_of_lt hb (by omega)
  have hVk : V < 2 ^ k := by rw [hK] at hbk; omega
  have hWUV : W = U + V := by
    have h1 : ((U + V : Nat) : Int) % 2 ^ 64 = (a + b) % 2 ^ 64 := by
      push_cast; rw [hu, hVb]; omega
    have h2 : U + V < 2 ^ 64 := by
      have : U < 2 ^ 64 := by rw [← hU]; exact BitVec.isLt _
      have hUc : U ≤ 2 ^ 64 - 2 ^ k := by
        obtain ⟨q, rfl⟩ : ∃ q, U = 2 ^ k * q := ⟨U / 2 ^ k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hUk)).symm⟩
        rw [hc] at this ⊢
        have hq : q < c := Nat.lt_of_mul_lt_mul_left this
        have := Nat.mul_le_mul_left (2 ^ k) (show q + 1 ≤ c by omega)
        rw [Nat.mul_add, Nat.mul_one] at this; omega
      have := Nat.two_pow_pos k
      omega
    have : ((U + V : Nat) : Int) = (a + b) % 2 ^ 64 := by
      rw [← h1]; exact (Int.emod_eq_of_lt (by omega) (by exact_mod_cast h2)).symm
    omega
  rw [hWUV]
  obtain ⟨q, rfl⟩ : ∃ q, U = 2 ^ k * q := ⟨U / 2 ^ k, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hUk)).symm⟩
  rw [Nat.mul_comm, SfLens.or_add _ _ _ hVk]

/-- The machine's two-word right shift: `(h << (32 - n)) | (l >>> n)` as
words, `P = 2^(32 - n)`, `Q = 2^n` (literals once `n` is; the side
conditions by `decide`). -/
theorem or_shr (a l : Int) (P Q : Int) (k : Nat) (hP : P = 2 ^ k) (hk : k ≤ 32) (hPQ : P * Q = 4294967296) :
    BitVec.ofInt 64 ((a * P).bmod 4294967296) ||| BitVec.ofInt 64 (l % 4294967296 / Q) =
      BitVec.ofInt 64 ((a * P).bmod 4294967296 + l % 4294967296 / Q) := by
  subst hP
  have hQ : 0 < Q := by
    rcases Int.lt_trichotomy Q 0 with h | h | h
    · have : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
      have : 2 ^ k * Q < 0 := Int.mul_neg_of_pos_of_neg this h
      omega
    · subst h; simp at hPQ
    · exact h
  have hPpos : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)
  apply or_low _ _ k (by omega)
  · -- the low `k` bits of `a·2^k` stay zero through `bmod 2^32`
    have hd : (2 : Int) ^ k ∣ ((4294967296 : Nat) : Int) := ⟨Q, hPQ.symm⟩
    simp only [Int.bmod]
    split
    · rw [Int.emod_emod_of_dvd _ hd]; exact Int.mul_emod_left _ _
    · rw [Int.sub_emod, Int.emod_emod_of_dvd _ hd, Int.mul_emod_left, Int.emod_eq_zero_of_dvd hd]; simp
  · exact Int.ediv_nonneg (Int.emod_nonneg _ (by decide)) (by omega)
  · have hl : l % 4294967296 < 2 ^ k * Q := by rw [hPQ]; exact Int.emod_lt_of_pos _ (by decide)
    exact Int.ediv_lt_of_lt_mul hQ hl

/-- `or_shr` with its exponent read off the literal `P` (a `simp` lemma). -/
theorem or_shr' (a l : Int) (P Q : Int) (hP : P = 2 ^ P.toNat.log2) (hk : P.toNat.log2 ≤ 32)
    (hPQ : P * Q = 4294967296) :
    BitVec.ofInt 64 ((a * P).bmod 4294967296) ||| BitVec.ofInt 64 (l % 4294967296 / Q) =
      BitVec.ofInt 64 ((a * P).bmod 4294967296 + l % 4294967296 / Q) :=
  or_shr a l P Q _ hP hk hPQ

/-- `or_shr'` when the high part did not wrap (`bmod` already dropped). -/
theorem or_shr0 (a l : Int) (P Q : Int) (hP : P = 2 ^ P.toNat.log2) (hk : P.toNat.log2 ≤ 32)
    (hPQ : P * Q = 4294967296) :
    BitVec.ofInt 64 (a * P) ||| BitVec.ofInt 64 (l % 4294967296 / Q) =
      BitVec.ofInt 64 (a * P + l % 4294967296 / Q) := by
  have hQ : 0 < Q := by
    have hP0 : (0 : Int) < P := by rw [hP]; exact Int.pow_pos (by decide)
    rcases Int.lt_trichotomy Q 0 with h | h | h
    · have : P * Q < 0 := Int.mul_neg_of_pos_of_neg hP0 h
      omega
    · subst h; simp at hPQ
    · exact h
  apply or_low _ _ P.toNat.log2 (by omega)
  · rw [← hP]; exact Int.mul_emod_left _ _
  · exact Int.ediv_nonneg (Int.emod_nonneg _ (by decide)) (by omega)
  · have hl : l % 4294967296 < P * Q := by rw [hPQ]; exact Int.emod_lt_of_pos _ (by decide)
    rw [← hP]
    exact Int.ediv_lt_of_lt_mul hQ hl

/-- A sign-extended word is zero exactly when the word is. -/
theorem sext_beq0 (x : BitVec (31 - 0 + 1)) :
    (sign_extend (m := 64) x == BitVec.ofInt 64 0) = decide (x.toNat = 0) := by
  rw [sext64 x (by decide)]
  have h1 := BitVec.le_toInt (x := x)
  have h2 := BitVec.toInt_lt (x := x)
  rw [beq_ofInt]
  apply decide_eq_decide.2
  have e : (2 : Int) ^ (31 - 0 + 1 - 1) = 2 ^ 31 := by decide
  rw [e] at h1 h2
  constructor
  · intro h
    have : x.toInt = 0 := by omega
    have : x = 0#_ := BitVec.eq_of_toInt_eq (by rw [this]; rfl)
    rw [this]; rfl
  · intro h
    have : x = 0#_ := BitVec.eq_of_toNat_eq (by rw [h]; rfl)
    rw [this]; decide

/-- `sext.w (a | b) == 0`: both low words zero. -/
theorem or_lo_beq0 (a b : Int) :
    (sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofInt 64 a ||| BitVec.ofInt 64 b) 31 0) ==
      BitVec.ofInt 64 0) = decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  rw [sext_beq0]
  apply decide_eq_decide.2
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero,
    BitVec.toNat_or]
  rw [show 31 - 0 + 1 = 32 from rfl, Nat.or_mod_two_pow, Nat.or_eq_zero_iff]
  have ha := ofInt_toNat a
  have hb := ofInt_toNat b
  have ea : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := Int.emod_emod_of_dvd _ (by decide)
  have eb : b % 2 ^ 64 % 2 ^ 32 = b % 2 ^ 32 := Int.emod_emod_of_dvd _ (by decide)
  omega

/-- `or_lo_beq0` in the normal form `fm_nf` reaches (the sign extension by `sext64`). -/
theorem or_lo_toInt0 (a b : Int) :
    ((Sail.BitVec.extractLsb (BitVec.ofInt 64 a ||| BitVec.ofInt 64 b) 31 0).toInt % 18446744073709551616 = 0) =
      (a % 4294967296 = 0 ∧ b % 4294967296 = 0) := by
  have h := or_lo_beq0 a b
  rw [sext64 _ (by decide), beq_ofInt] at h
  have e : ∀ p q : Prop, [Decidable p] → [Decidable q] → decide p = decide q → p = q := by
    intro p q _ _ hpq; exact propext (decide_eq_decide.1 hpq)
  have := e _ _ h
  rw [show (0 : Int) % 2 ^ 64 = 0 by decide] at this
  simpa using this

theorem add_ofInt0 (x : BitVec 64) : x + BitVec.ofInt 64 0 = x := by
  rw [show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.add_zero]

theorem or_zero_ofInt (a : Int) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 0 = BitVec.ofInt 64 a := by
  rw [show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.or_zero]

theorem zero_or_ofInt (a : Int) : BitVec.ofInt 64 0 ||| BitVec.ofInt 64 a = BitVec.ofInt 64 a := by
  rw [show BitVec.ofInt 64 0 = 0#64 by decide, BitVec.zero_or]

/-- `(a | b) == 0`: both zero. -/
theorem or_beq0 (a b : Int) :
    ((BitVec.ofInt 64 a ||| BitVec.ofInt 64 b) == BitVec.ofInt 64 0) =
      decide (a % 2 ^ 64 = 0 ∧ b % 2 ^ 64 = 0) := by
  rw [SfLens.beq_toNat]
  apply decide_eq_decide.2
  rw [BitVec.toNat_or, show (BitVec.ofInt 64 0).toNat = 0 by decide, Nat.or_eq_zero_iff]
  have ha := ofInt_toNat a
  have hb := ofInt_toNat b
  omega

theorem or_bne0 (a b : Int) :
    ((BitVec.ofInt 64 a ||| BitVec.ofInt 64 b) != BitVec.ofInt 64 0) =
      !decide (a % 2 ^ 64 = 0 ∧ b % 2 ^ 64 = 0) := by
  simp only [bne, or_beq0]

theorem ext6_toNat (k : BitVec 6) : (Sail.BitVec.extractLsb k 5 0).toNat = k.toNat := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat, Nat.shiftRight_zero]
  omega

/-! ## The normal form -/

open Lean Elab Tactic Meta in
/-- Fail unless the goal is closed (no free variable): `decide` only there. -/
elab "fm_ground" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  if t.hasFVar || t.hasMVar then throwError "fm_ground: an open goal"

/-- The side conditions of `fm_nf`'s rewrites. -/
macro "fm_disch" : tactic => `(tactic| first | omega | (fm_ground; decide))

/-- **The normal form**, to its fixpoint: literals to `ofInt`, words through
`ofInt (31 - 0 + 1)` and back by `sext64`, the operations on `Int`, the guards
to `decide` over `Int` (side conditions by `omega`). -/
syntax "fm_nf" (Lean.Parser.Tactic.location)? : tactic
macro_rules | `(tactic| fm_nf $[$loc]?) => `(tactic| (
  simp (config := { failIfUnchanged := false }) (disch := fm_disch) only [
    Lua.Vm.Fn.FmodLens.sext64, Lua.Vm.Fn.FmodLens.lo_ofInt, Lua.Vm.Fn.FmodLens.lo5_ofInt,
    Lua.Vm.Fn.FmodLens.sub32, Lua.Vm.Fn.FmodLens.add32, Lua.Vm.Fn.FmodLens.sll32,
    Lua.Vm.Fn.FmodLens.srl32, Lua.Vm.Fn.FmodLens.sra32, Lua.Vm.Fn.FmodLens.add64,
    Lua.Vm.Fn.FmodLens.sub64, Lua.Vm.Fn.FmodLens.sll64, Lua.Vm.Fn.FmodLens.srl64,
    Lua.Vm.Fn.FmodLens.toNat_ofInt5, Lua.Vm.Fn.FmodLens.toNat_ofInt32, Lua.Vm.Fn.FmodLens.toInt_ofInt32,
    Lua.Vm.Fn.FmodLens.ext6_toNat, Lua.Vm.Fn.FmodLens.bmod_small, Lua.Vm.Fn.FmodLens.bmod_small',
    BitVec.toInt_ofInt, Int.reduceNatCast, Int.cast_ofNat_Int,
    Lua.Vm.Fn.FmodLens.lit_pos, Lua.Vm.Fn.FmodLens.lit_neg,
    Lua.Vm.Fn.FmodLens.lit_pos', Lua.Vm.Fn.FmodLens.lit_neg',
    Lua.Vm.Fn.FmodLens.slt_ofInt, Lua.Vm.Fn.FmodLens.sge_ofInt, Lua.Vm.Fn.FmodLens.ult_ofInt,
    Lua.Vm.Fn.FmodLens.uge_ofInt, Lua.Vm.Fn.FmodLens.beq_ofInt, Lua.Vm.Fn.FmodLens.bne_ofInt,
    Lua.Vm.Fn.FmodLens.or_beq0, Lua.Vm.Fn.FmodLens.or_bne0,
    Lua.Vm.Fn.FmodLens.or_zero_ofInt, Lua.Vm.Fn.FmodLens.zero_or_ofInt,
    Lua.Vm.Fn.FmodLens.or_k20, Lua.Vm.Fn.FmodLens.or_k31, Lua.Vm.Fn.FmodLens.or_k32, Lua.Vm.Fn.FmodLens.or_sx,
    Lua.Vm.Fn.FmodLens.or_k20', Lua.Vm.Fn.FmodLens.and_2047, Lua.Vm.Fn.FmodLens.and_fffff,
    Lua.Vm.Fn.FmodLens.and_7fffffff, Lua.Vm.Fn.FmodLens.and_7ff00000, Lua.Vm.Fn.FmodLens.and_hi31,
    Lua.Vm.Fn.FmodLens.or_shr', Lua.Vm.Fn.FmodLens.or_shr0, Lua.Vm.Fn.FmodLens.or_lo_beq0, Lua.Vm.Fn.FmodLens.or_lo_toInt0,
    Lua.Vm.Fn.FmodLens.add_ofInt0, if_pos, if_neg,
    Int.shiftRight_eq_div_pow,
    BitVec.reduceToInt, BitVec.reduceToNat, BitVec.reduceAppend, BitVec.reduceSignExtend,
    BitVec.reduceAdd, BitVec.reduceXOr, BitVec.reduceAnd, BitVec.reduceOr,
    BitVec.reduceNot, BitVec.reduceExtractLsb,
    Int.reducePow, Int.reduceMul, Int.reduceAdd, Int.reduceSub, Int.reduceNeg, Int.reduceMod,
    Int.reduceDiv, Int.reduceToNat, Nat.reducePow, Nat.reduceMod, Nat.reduceAdd, Nat.reduceSub,
    Nat.reduceMul, Int.add_zero, Int.zero_add, Int.mul_one, Int.sub_zero,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true,
    Bool.not_true, Bool.not_false, Bool.not_not, decide_true, decide_false,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, ite_true, ite_false] $[$loc]?))

/-- Close an equation of normal forms: the `ofInt`s' arguments in `omega`,
a remaining sign extension (`Int.bmod`) split by cases. -/
macro "fm_close" : tactic => `(tactic| (
  first
  | rfl
  | (congr 1
     try simp only [Int.bmod]
     (repeat' split) <;> omega)))

end Lua.Vm.Fn.FmodLens

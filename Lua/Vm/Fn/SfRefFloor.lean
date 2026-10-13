import Lua.Vm.Fn.FloorFn
import Lua.Vm.Fn.SfRefAdd
import Lua.Vm.Fn.SfRefCmp
import Lua.Vm.Sim.Kit.FltVal
import Lua.Num.SfRefFloor
import Lua.Vm.Sim.Kit.FnCall

/-!
# libm's `floor` against `SfRef.floor` (lane float-sf3, (b1))

`floor`'s lifted function (`Lua.Vm.Fn.FloorFn.F`, generated with its
callees `__adddf3` and `__gedf2` as call nodes) is the soft-fp-shaped
reference `SfRef.floor` (`Lua/Num/SfRefFloor.lean`, fdlibm's `s_floor.c`
over the fields); with (b2) (`SfRef.floor_cls`, then `floor_model` here)
the named premise `FloorSpec` is a theorem (`floorSpec_proved`).

* **The 32-bit lens.** fdlibm works on the halves `i0:i1` of its argument:
  `srai 32`, `sext.w`, `addiw`, `sraw`/`srlw`/`sllw`, `addw`, `subw`. Each
  is one lemma on the `ofNat` normal form (`fl_hi`, `fl_e`, `nf_sextw`,
  `nf_sraw`, …); a mask `0xfffff >> j0` is a literal once `j0` is.
* **Chambers.** The reference's branches (`floorFields`), with the mask
  range `1023 ≤ e ≤ 1074` split into one chamber per exponent (the machine's
  variable shifts become literal), emitted by the one-operand chamber
  generator `fl_chambers` and its cover `fl_cover` (never a hand chamber
  list); the chambers are `Lua/Vm/Fn/SfRefFloor{A,B,C,D}.lean`, the cover
  and the premise `Lua/Vm/Fn/SfRefFloorSpec.lean`.
* **The call nodes.** `huge + x > 0` (`__adddf3` then `__gedf2` against
  `0`) is `1` on every argument the machine asks it of (`bexp < 1075`):
  `fl_inexact`, from (b2) of `__adddf3` (`SfRef.add`, the operand far below
  `huge`'s exponent jams to one sticky bit); `x + x` on `±∞`/NaN is
  `fl_twice`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Lua.Vm.Fn.SfLens Lua.Vm.Fn.SfCmpLens Lua.Vm.Sim

namespace Lua.Vm.Fn.FloorLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The halves of the argument -/

theorem nf_sextw' (a : Nat) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0) =
      BitVec.ofNat 64 (a % 2 ^ 32 + if a % 2 ^ 32 < 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_zero, Nat.reduceAdd, Nat.reduceSub]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := by omega
  rw [h1]
  split <;> rename_i h <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢ <;>
    first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega)

/-- A 32-bit result sign-extended, without a case split: the sign bit
`a % 2^32 / 2^31` (`0` or `1`) times the extension. -/
theorem nf_sextw2 (a : Nat) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0) =
      BitVec.ofNat 64 (a % 2 ^ 32 + a % 2 ^ 32 / 2 ^ 31 * 18446744069414584320) := by
  rw [nf_sextw']
  congr 1
  split <;> omega

/-- The high word `i0` of an operand, sign-extended, as a `Nat` (kept whole:
the literal arithmetic never splits it; `hiw_def` at a leaf). -/
def hiw (s e f : Nat) : Nat := s * 18446744071562067968 + e * 2 ^ 20 + f / 2 ^ 32

theorem hiw_def (s e f : Nat) : hiw s e f = s * 18446744071562067968 + e * 2 ^ 20 + f / 2 ^ 32 := rfl

/-- `srai x, 32`: the high word `i0`, sign-extended. -/
theorem fl_hi {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    shift_bits_right_arith (P s e f) (Sail.BitVec.extractLsb (0x20#6) 5 0) = BitVec.ofNat 64 (hiw s e f) := by
  unfold shift_bits_right_arith hiw
  rw [show BitVec.toNatInt (Sail.BitVec.extractLsb (0x20#6) 5 0) = 32 by decide]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sshiftRight, BitVec.msb_eq_decide, P_toNat hs he hf, BitVec.toNat_ofNat]
  simp only [Nat.shiftRight_eq_div_pow, show (64 - 1 : Nat) = 63 from rfl, show Int.toNat 32 = 32 from rfl]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl
  · rw [decide_eq_false (by omega)]; simp only [Bool.false_eq_true, ite_false]; omega
  · rw [decide_eq_true (by omega)]; simp only [ite_true]; omega

/-- `slli 33; srli 53` of the sign-extended high word: the exponent field. -/
theorem fl_e {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    BitVec.ofNat 64 (hiw s e f * 8589934592) >>> 53 = BitVec.ofNat 64 e := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, hiw]
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> omega

/-- `sext.w` of an operand: the low word `i1`, sign-extended. -/
theorem fl_lo {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (P s e f) 31 0) =
      BitVec.ofNat 64 (f % 2 ^ 32 + f % 2 ^ 32 / 2 ^ 31 * 18446744069414584320) := by
  have := nf_sextw2 (s * 2 ^ 63 + e * 2 ^ 52 + f)
  rw [show (s * 2 ^ 63 + e * 2 ^ 52 + f) % 2 ^ 32 = f % 2 ^ 32 by omega] at this
  exact this

/-- A 32-bit result sign-extended (`sext.w`, `addiw`, `addw`, …), on a word in
the `ofNat` normal form. -/
theorem nf_sextw (a : Nat) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0) =
      BitVec.ofNat 64 (a % 2 ^ 32 + if a % 2 ^ 32 < 2 ^ 31 then 0 else 2 ^ 64 - 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.shiftRight_zero, Nat.reduceAdd, Nat.reduceSub]
  have h1 : a % 2 ^ 64 % 2 ^ 32 = a % 2 ^ 32 := by omega
  rw [h1]
  split <;> rename_i h <;> simp only [decide_eq_true_eq, decide_eq_false_iff_not] at h ⊢ <;>
    first | (rw [if_neg (by omega)]; omega) | (rw [if_pos (by omega)]; omega)

/-- The low word of a word in the `ofNat` normal form. -/
theorem lo_toNat (a : Nat) : (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0).toNat = a % 2 ^ 32 := by
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

/-- A shift amount's low five bits. -/
theorem sh5_nat (b : Nat) :
    (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) 4 0).toNat = b % 32 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat]

theorem sh5_toNat (b : Nat) :
    (BitVec.toNatInt (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) 4 0)).toNat =
      b % 32 := by
  simp only [BitVec.toNatInt, sh5_nat]; rfl

/-- `sraw` of a non-negative 32-bit word by a word's low five bits. -/
theorem nf_sraw (a b : Nat) (ha : a % 2 ^ 32 < 2 ^ 31) :
    BitVec.signExtend 64 (shift_bits_right_arith (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) 4 0)) =
      BitVec.ofNat 64 (a % 2 ^ 32 / 2 ^ (b % 32)) := by
  unfold shift_bits_right_arith
  have hX := lo_toNat a
  have hm : (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0).msb = false := by
    rw [BitVec.msb_eq_decide, hX]; simp; omega
  rw [BitVec.sshiftRight_eq_of_msb_false hm, sh5_toNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, hX, Nat.shiftRight_eq_div_pow,
    BitVec.toNat_ofNat]
  have h3 : a % 2 ^ 32 / 2 ^ (b % 32) ≤ a % 2 ^ 32 := Nat.div_le_self _ _
  rw [decide_eq_false (by omega)]
  simp only [Bool.false_eq_true, ite_false, Nat.add_zero]

/-- `srlw` by a word's low five bits. -/
theorem nf_srlw (a b : Nat) :
    BitVec.signExtend 64 (shift_bits_right (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) 4 0)) =
      BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 (a % 2 ^ 32 / 2 ^ (b % 32))) 31 0) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [shift_bits_right, BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, lo_toNat, Nat.shiftRight_eq_div_pow]
  rw [sh5_nat]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide)))).symm

/-- `sllw` by a word's low five bits. -/
theorem nf_sllw (a b : Nat) :
    BitVec.signExtend 64 (shift_bits_left (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0)
      (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) 4 0)) =
      BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 (a % 2 ^ 32 * 2 ^ (b % 32))) 31 0) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [lo_toNat]
  simp only [shift_bits_left, BitVec.shiftLeft_eq', BitVec.toNat_shiftLeft, lo_toNat, Nat.shiftLeft_eq]
  rw [sh5_nat]

/-- `addw`. -/
theorem nf_addw (a b : Nat) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0 + Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) =
      BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 (a % 2 ^ 32 + b % 2 ^ 32)) 31 0) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, lo_toNat]

/-- `subw`. -/
theorem nf_subw (a b : Nat) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0 - Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) =
      BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 (a % 2 ^ 32 + (2 ^ 32 - b % 2 ^ 32))) 31 0) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, lo_toNat]
  omega

/-- `not` (`xori -1`). -/
theorem nf_not (a : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ 18446744073709551615#64 = BitVec.ofNat 64 (2 ^ 64 - 1 - a) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes,
    BitVec.toNat_not]
  simp only [BitVec.toNat_ofNat]
  omega

/-- A mask of low bits (`c + 1` a power of two). -/
theorem nf_andlo (a c : Nat) (hc : (c + 1) &&& c = 0) (hc2 : c < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 c = BitVec.ofNat 64 (a % 2 ^ 64 % (c + 1)) := by
  have hp : (c + 1).isPowerOfTwo := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).1 (by simpa using hc)
  obtain ⟨n, hn⟩ := hp
  have hc' : c = 2 ^ n - 1 := by omega
  have hn64 : n ≤ 64 := by
    rcases Nat.lt_or_ge 64 n with h | h
    · have := Nat.pow_lt_pow_right (a := 2) (by decide) h; omega
    · exact h
  subst hc'
  rw [nf_and_mask a n hn64, show 2 ^ n - 1 + 1 = 2 ^ n by have := Nat.two_pow_pos n; omega]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  have : a % 2 ^ 64 % 2 ^ n < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
    (Nat.pow_le_pow_right (by decide) hn64)
  rw [Nat.mod_eq_of_lt this, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn64)]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n))
    (Nat.pow_le_pow_right (by decide) hn64))

/-- A mask of high bits (`~c`, `c + 1` a power of two): the low bits cleared. -/
theorem nf_andhi (a c : Nat) (hc : (c + 1) &&& c = 0) (hc2 : c < 2 ^ 64) :
    BitVec.ofNat 64 (2 ^ 64 - 1 - c) &&& BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 64 / (c + 1) * (c + 1)) := by
  have hp : (c + 1).isPowerOfTwo := (Nat.and_sub_one_eq_zero_iff_isPowerOfTwo (by omega)).1 (by simpa using hc)
  obtain ⟨n, hn⟩ := hp
  have hn64 : n ≤ 64 := by
    rcases Nat.lt_or_ge 64 n with h | h
    · have := Nat.pow_lt_pow_right (a := 2) (by decide) h; omega
    · exact h
  have e1 : 2 ^ 64 - 1 - c = 2 ^ n * (2 ^ (64 - n) - 1) := by
    rw [Nat.mul_sub, Nat.mul_one, ← Nat.pow_add, show n + (64 - n) = 64 by omega]; omega
  rw [e1, hn]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  have hlt : 2 ^ n * (2 ^ (64 - n) - 1) < 2 ^ 64 := by omega
  have hlt2 : a % 2 ^ 64 / 2 ^ n * 2 ^ n < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (Nat.mod_lt _ (by decide))
  rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    Nat.testBit_div_two_pow]
  simp only [Nat.testBit_mod_two_pow]
  by_cases h1 : n ≤ i
  · rw [show i - n + n = i by omega]
    by_cases h2 : i < 64
    · simp [h1, h2, show i - n < 64 - n by omega]
    · simp [h1, h2, show ¬ i - n < 64 - n by omega]
  · simp [h1, show ¬ i ≥ n by omega]

/-- `nf_andhi` on an evaluated mask. -/
theorem nf_andhiL (a L : Nat) (hL : L < 2 ^ 64) (hp : (2 ^ 64 - L) &&& (2 ^ 64 - L - 1) = 0) (hL0 : 0 < L) :
    BitVec.ofNat 64 L &&& BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 64 / (2 ^ 64 - L) * (2 ^ 64 - L)) := by
  have h := nf_andhi a (2 ^ 64 - 1 - L) (by rw [show 2 ^ 64 - 1 - L + 1 = 2 ^ 64 - L by omega,
    show 2 ^ 64 - 1 - L = 2 ^ 64 - L - 1 by omega]; exact hp) (by omega)
  rw [show 2 ^ 64 - 1 - (2 ^ 64 - 1 - L) = L by omega, show 2 ^ 64 - 1 - L + 1 = 2 ^ 64 - L by omega] at h
  exact h

/-- `slli 32; srli 32`: the low word, zero-extended. -/
theorem fl_zext32 (b : Nat) : BitVec.ofNat 64 (b * 4294967296) >>> 32 = BitVec.ofNat 64 (b % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

theorem p_or_zero (x : BitVec 64) : x ||| 0#64 = x := by simp
theorem p_zero_and (x : BitVec 64) : 0#64 &&& x = 0#64 := by simp
theorem p_and_zero (x : BitVec 64) : x &&& 0#64 = 0#64 := by simp

/-- `(i0 & i) | i1` against zero, as `sext.w` tests it. -/
theorem nf_or_eq0 (a b : Nat) :
    (BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b) 31 0) == 0#64) =
      decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  have e : BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a % 2 ^ 64 ||| b % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (Nat.or_lt_two_pow (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)))).symm
  rw [e, nf_sextw, beq_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  rw [Nat.or_mod_two_pow, Nat.mod_mod_of_dvd _ (by decide), Nat.mod_mod_of_dvd _ (by decide)]
  have h1 := Nat.or_lt_two_pow (Nat.mod_lt a (Nat.two_pow_pos 32)) (Nat.mod_lt b (Nat.two_pow_pos 32))
  apply decide_eq_decide.2
  rw [← Nat.or_eq_zero_iff]
  split <;> omega

/-- The comparisons of the machine's words, on their `toNat`s (a literal's
by evaluation, an `ofNat`'s by `toNat_ofNat`): signed by the offset order. -/
theorem slt_toNat (x y : BitVec 64) :
    zopz0zI_s x y = decide ((x.toNat + 2 ^ 63) % 2 ^ 64 < (y.toNat + 2 ^ 63) % 2 ^ 64) := by
  rw [slt_int', BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have := x.isLt; have := y.isLt
  apply decide_eq_decide.2
  split <;> split <;> omega
theorem sge_toNat (x y : BitVec 64) :
    zopz0zKzJ_s x y = decide ((y.toNat + 2 ^ 63) % 2 ^ 64 ≤ (x.toNat + 2 ^ 63) % 2 ^ 64) := by
  rw [sge_int, BitVec.toInt_eq_toNat_cond, BitVec.toInt_eq_toNat_cond]
  have := x.isLt; have := y.isLt
  apply decide_eq_decide.2
  split <;> split <;> omega
theorem uge_toNat (x y : BitVec 64) : zopz0zKzJ_u x y = decide (y.toNat ≤ x.toNat) := by
  rw [Lua.Vm.Fn.SfCmpLens.uge_nat]

/-- `(x | y) == 0` on full words (`beqz` of an `or`). -/
theorem nf_or_eq0_64 (a b : Nat) :
    (BitVec.ofNat 64 a ||| BitVec.ofNat 64 b == 0#64) = decide (a % 2 ^ 64 = 0 ∧ b % 2 ^ 64 = 0) := by
  rw [beq_toNat]
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.zero_mod]
  apply decide_eq_decide.2
  exact Nat.or_eq_zero_iff

/-- An `or` the path's facts make zero (`beqz` taken on it). -/
theorem nf_or_zero_of (a b : Nat) (h : a % 2 ^ 64 = 0 ∧ b % 2 ^ 64 = 0) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = 0#64 := by
  have := nf_or_eq0_64 a b
  rw [decide_eq_true h] at this
  exact (beq_iff_eq.1 this)

/-- `INSERT_WORDS(x, i0, i1)`: `(i0 << 32) | (i1 << 32 >> 32)`. -/
theorem fl_pack (a b : Nat) :
    shift_bits_left (BitVec.ofNat 64 a) (Sail.BitVec.extractLsb (0x20#6) 5 0) |||
      shift_bits_right (shift_bits_left (BitVec.ofNat 64 b) (Sail.BitVec.extractLsb (0x20#6) 5 0))
        (Sail.BitVec.extractLsb (0x20#6) 5 0) =
      BitVec.ofNat 64 (a % 2 ^ 32 * 2 ^ 32 + b % 2 ^ 32) := by
  rw [sll_lit, sll_lit, srl_lit]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, show (0x20#6 : BitVec 6).toNat = 32 by decide,
    show (Sail.BitVec.extractLsb (0x20#6) 5 0) = 0x20#6 by decide]
  have e1 : a % 2 ^ 64 * 2 ^ 32 % 2 ^ 64 = a % 2 ^ 32 * 2 ^ 32 := by omega
  have e2 : b % 2 ^ 64 * 2 ^ 32 % 2 ^ 64 / 2 ^ 32 = b % 2 ^ 32 := by omega
  rw [e1, e2, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by decide))]
  omega

/-! ## The call nodes -/

open Lua.Num

/-- fdlibm's `huge = 1.0e300` (`.rodata` at `0x8005c4b0`). -/
abbrev hugeW : BitVec 64 := 0x7e37e43c8800759c#64

theorem huge_bytes : ∀ j, j < 8 → Image.rodataByte (0x8005c4b0 - Image.rodataBase + j) =
    BitVec.ofNat 8 (0x7e37e43c8800759c / 2 ^ (8 * j) % 256) := by
  decide +kernel

/-- `ld a1, huge`. -/
theorem huge_ld {m : Mem} (hro : RodataRead m) : bytesT8 m 2147861680 = hugeW := by
  have hb : ∀ j, j < 8 → bytesT1 m (0x8005c4b0 + j) = BitVec.ofNat 8 (0x7e37e43c8800759c / 2 ^ (8 * j) % 256) := by
    intro j hj
    have := hro (0x8005c4b0 - Image.rodataBase + j) (by simp only [Image.rodataBase, Image.rodataSize]; omega)
    rw [show Image.rodataBase + (0x8005c4b0 - Image.rodataBase + j) = 0x8005c4b0 + j by
      simp only [Image.rodataBase]; omega] at this
    rw [this]; exact huge_bytes j hj
  have h0 := hb 0 (by omega)
  simp only [bytesT1, Nat.add_zero] at h0 hb
  simp only [bytesT8, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega),
    hb 5 (by omega), hb 6 (by omega), hb 7 (by omega)]
  decide +kernel

/-- `huge + x > 0` for every `x` with `|x| < 2^52`: the soft-fp sum jams `x`
(`2019 - e ≥ 945` places below `huge`) to one sticky bit, so it is `huge`
or a neighbour (`SfRef.add`, (b2) `SfRef.add_eq`). -/
theorem add_huge (x : F64) (hx : x.bexp < 1075) : F64.compare (F64.add x hugeW) 0#64 = some .gt := by
  rw [← SfRef.add_eq]
  unfold SfRef.add
  rw [show F64.sign hugeW = false by decide, show F64.bexp hugeW = 2019 by decide,
    show F64.frac hugeW = 0x7e43c8800759c by decide]
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hA : SfRef.mant x.bexp x.frac < 2 ^ 56 := by unfold SfRef.mant; split <;> omega
  have hk : 2 ^ 56 ≤ 2 ^ (max 2019 1 - max x.bexp 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : SfRef.rto (SfRef.mant x.bexp x.frac) (max 2019 1 - max x.bexp 1) = 0 ∨
      SfRef.rto (SfRef.mant x.bexp x.frac) (max 2019 1 - max x.bexp 1) = 1 := by
    rcases Nat.eq_zero_or_pos (SfRef.mant x.bexp x.frac) with h0 | h0
    · rw [h0, SfRef.rto_zero_n]; exact .inl rfl
    · exact .inr (SfRef.rto_big h0 (by omega))
  unfold SfRef.addFields
  simp only []
  cases x.sign
  · simp only [ite_true, show ¬ x.bexp = 2019 by omega, show ¬ 2019 < x.bexp by omega, ite_false,
      show ¬ (2019 : Nat) = 2047 by decide]
    unfold SfRef.addAligned
    rcases hr with h | h <;> rw [h] <;> decide +kernel
  · simp only [show ¬ x.bexp = 2019 by omega, show ¬ 2019 < x.bexp by omega,
      ite_false, show ¬ (2019 : Nat) = 2047 by decide]
    unfold SfRef.subMag
    rcases hr with h | h <;> rw [h] <;> simp only [Bool.true_eq_false, ↓reduceIte] <;> decide +kernel

/-- `__gedf2`'s answer on an ordered pair, `>`. -/
theorem gedf2_gt (a b : BitVec 64) (h : F64.compare a b = some .gt) : Lua.Vm.Fn.Gedf2.S a b = 1#64 := by
  unfold Lua.Vm.Fn.Gedf2.S; rw [h]

/-- The machine's `huge + x > 0` (`__adddf3`, then `__gedf2` against `0`):
`1`, on every argument it is asked of. -/
theorem fl_inexact {s e f : Nat} (hs : s < 2) (he : e < 1075) (hf : f < 2 ^ 52) :
    Lua.Vm.Fn.Gedf2.F (F64.add (P s e f) hugeW) 0#64 = 1#64 :=
  (Lua.Vm.Fn.Gedf2.spec_proved _ _).trans (gedf2_gt _ _ (add_huge _ (by
    unfold F64.bexp; rw [P_toNat hs (by omega) hf]; omega)))

/-- The fields of an operand packed from them. -/
theorem fields_P {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    F64.sign (P s e f) = decide (s = 1) ∧ F64.bexp (P s e f) = e ∧ F64.frac (P s e f) = f := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sign_fields, P_toNat hs he hf]; apply decide_eq_decide.2; omega
  · unfold F64.bexp; rw [P_toNat hs he hf]; omega
  · unfold F64.frac; rw [P_toNat hs he hf]; omega

/-- The machine's `x + x` on `±∞` and NaN. -/
theorem fl_twice {s f : Nat} (hs : s < 2) (hf : f < 2 ^ 52) :
    F64.add (P s 2047 f) (P s 2047 f) = SfRef.floorFields (decide (s = 1)) 2047 f := by
  rw [← SfRef.add_eq]
  unfold SfRef.add
  obtain ⟨h1, h2, h3⟩ := fields_P (e := 2047) hs (by omega) hf
  rw [h1, h2, h3]
  unfold SfRef.addFields SfRef.floorFields
  simp only [ite_true, and_self]

/-! ## Exploring a chamber

Every rewrite here is propositional: a definitional step (an `rfl` simp
lemma such as `Nat.add_zero`) that changes a head symbol inside the lifted
DAG leaves the kernel a definitional check that unfolds the other side. -/

theorem p_add_zero (n : Nat) : n + 0 = n := by omega
theorem p_zero_add (n : Nat) : 0 + n = n := by omega
theorem p_zero_mul (n : Nat) : 0 * n = 0 := by omega
theorem p_mul_zero (n : Nat) : n * 0 = 0 := by omega
theorem p_zero_mod (n : Nat) : 0 % n = 0 := Nat.zero_mod n
theorem p_zero_div (n : Nat) : 0 / n = 0 := Nat.zero_div n
/-- A literal multiple of the modulus drops out. -/
theorem nf_addmod (C x M : Nat) (h : C % M = 0) : (C + x) % M = x % M := by
  rw [Nat.add_mod, h, Nat.zero_add, Nat.mod_mod]
theorem nf_addmod' (x C M : Nat) (h : C % M = 0) : (x + C) % M = x % M := by
  rw [Nat.add_comm]; exact nf_addmod C x M h
/-- … and divides out. -/
theorem nf_adddiv (C x M : Nat) (h : C % M = 0) (hM : 0 < M) : (C + x) / M = C / M + x / M := by
  obtain ⟨q, rfl⟩ : ∃ q, C = M * q := ⟨C / M, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)).symm⟩
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hM, Nat.mul_div_cancel_left _ hM, Nat.add_comm]
/-- Nested moduli, the inner a multiple of the outer. -/
theorem nf_modmod (x a b : Nat) (h : a % b = 0) : x % a % b = x % b :=
  Nat.mod_mod_of_dvd x (Nat.dvd_of_mod_eq_zero h)

/-- A sign-extended low word is zero exactly when the word is (stated once:
`omega` on the ite-free extension is a kernel cost at every leaf). -/
theorem nf_sext_eq0 (x : Nat) :
    ((x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616 = 0)
      ↔ x % 4294967296 = 0 := by
  have h := Nat.mod_lt x (show 4294967296 > 0 by decide)
  generalize x % 4294967296 = y at *
  by_cases hy : y < 2147483648
  · rw [Nat.div_eq_of_lt hy, Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · have h1 : y / 2147483648 = 1 := by omega
    rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The ite-free sign extension of a low word, by its sign. -/
theorem sext_val (x : Nat) :
    (x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616
      = if x % 4294967296 < 2147483648 then x % 4294967296
        else x % 4294967296 + 18446744069414584320 := by
  have h := Nat.mod_lt x (show 4294967296 > 0 by decide)
  generalize x % 4294967296 = y at *
  split
  · rw [Nat.div_eq_of_lt (by assumption), Nat.zero_mul, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
  · have h1 : y / 2147483648 = 1 := by omega
    rw [h1, Nat.one_mul, Nat.mod_eq_of_lt (by omega)]

/-- Sign extension is monotone in the unsigned order (`bltu`/`bgeu` on two
`sext.w` words compares the words). -/
theorem nf_sext_le (x y : Nat) :
    (x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616 ≤
      (y % 4294967296 + y % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616
      ↔ x % 4294967296 ≤ y % 4294967296 := by
  rw [sext_val, sext_val]
  split <;> split <;> omega

theorem nf_sext_lt (x y : Nat) :
    (x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616 <
      (y % 4294967296 + y % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616
      ↔ x % 4294967296 < y % 4294967296 := by
  rw [sext_val, sext_val]
  split <;> split <;> omega

/-- The low word of a sign extension. -/
theorem nf_sext_mod32 (x : Nat) :
    (x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 18446744073709551616
      % 4294967296 = x % 4294967296 := by
  rw [sext_val]
  split <;> omega

theorem nf_sext_mod32' (x : Nat) :
    (x % 4294967296 + x % 4294967296 / 2147483648 * 18446744069414584320) % 4294967296
      = x % 4294967296 := by
  have h := nf_sext_mod32 x
  rwa [Nat.mod_mod_of_dvd _ (by decide : 4294967296 ∣ 18446744073709551616)] at h

/-- A mask of low zero bits (`d` a power of two below `2^32`) commutes with
taking the low word. -/
theorem nf_mask_mod32 (a d : Nat) (hd : 4294967296 % d = 0) :
    a / d * d % 4294967296 = a % 4294967296 / d * d := by
  have h1 : a % d = a % 4294967296 % d :=
    (Nat.mod_mod_of_dvd a (Nat.dvd_of_mod_eq_zero hd)).symm
  have e1 := Nat.div_add_mod' a d
  have e2 := Nat.div_add_mod' (a % 4294967296) d
  have e3 := Nat.div_add_mod a 4294967296
  have hl : a % 4294967296 < 4294967296 := Nat.mod_lt _ (by decide)
  generalize a / d * d = X at *
  generalize a % 4294967296 / d * d = Y at *
  omega

theorem p_bv_add_zero (x : BitVec 64) : x + 0#64 = x := by simp
theorem p_bv_zero_add (x : BitVec 64) : 0#64 + x = x := by simp

open Lean Elab Tactic Meta in
/-- Fail at once on a goal with no free variable left (literal arithmetic
already decided it; it is false); `False` is kept (a contradiction among
the hypotheses). -/
elab "fl_open" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  if !t.isConstOf ``False && !t.hasFVar then throwError "fl_open: a closed goal"

/-- Literal arithmetic first (`omega` recurses past `maxRecDepth` on some
unevaluated literal products), then `omega`. -/
macro "fl_omega" : tactic => `(tactic| (
  (all_goals simp (config := { failIfUnchanged := false }) only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceDiv,
    Nat.reduceAnd, Nat.reduceLT, Nat.reduceGT, Nat.reduceLeDiff, Nat.reduceEqDiff, Lua.Vm.Fn.FloorLens.p_add_zero,
    Lua.Vm.Fn.FloorLens.p_zero_add])
  first | done | (fl_open; omega)))

set_option hygiene false in
/-- The calls, `.rodata` and the frame's reloads (on the node's raw forms;
the chamber's `hrod`, `hsp` by name). -/
macro "fl_pre" : tactic => `(tactic| (
  all_goals simp (config := { failIfUnchanged := false }) only [Lua.Vm.Fn.SfLens.sext_eq, BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceAdd,
    BitVec.reduceToNat]
  all_goals simp (config := { failIfUnchanged := false }) (disch := kit_disch) only [Lua.Vm.Sim.bytesT8_memPatch_out, Lua.Vm.Sim.bytesT8_wm8_far,
    Lua.Vm.Sim.bytesT8_wm8_same, Lua.Vm.Fn.FloorLens.huge_ld hrod]
  all_goals simp (config := { failIfUnchanged := false }) only [Lua.Vm.Sim.sdData_id, Lua.Vm.Fn.SfLens.sext64_self, BitVec.signExtend_eq,
    Lua.Vm.Fn.Adddf3.spec_proved _ _ _ _ _ hsp,
    Lua.Vm.Fn.Adddf3.S, Lua.Vm.Fn.FloorLens.fl_pack]
  all_goals simp (config := { failIfUnchanged := false }) only [Lua.Vm.Fn.SfLens.sext_eq, BitVec.reduceSignExtend, BitVec.reduceAdd,
    Lua.Vm.Fn.FloorLens.p_bv_add_zero, Lua.Vm.Fn.FloorLens.p_bv_zero_add]
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [Lua.Vm.Fn.FloorLens.fl_inexact, Lua.Vm.Fn.FloorLens.fl_twice]))

/-- **The normal form**, one `simp` to its fixpoint: the literal steps, the
operand's halves (`fl_hi`, `fl_lo`, `fl_e`), the 32-bit lens, the `ofNat`
arithmetic, the literal multiples dropped from moduli, and the guards decided
where the path's facts decide them (side conditions by `fl_omega`). -/
syntax "fl_all" (Lean.Parser.Tactic.location)? : tactic
macro_rules | `(tactic| fl_all $[$loc]?) => `(tactic| (
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit, BitVec.reduceToNat, Nat.reducePow,
    Lua.Vm.Fn.FloorLens.fl_hi, Lua.Vm.Fn.SfLens.nf_shl, Lua.Vm.Fn.FloorLens.fl_e] $[$loc]?
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit, Lua.Vm.Fn.SfLens.sext_eq,
    BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceAdd, BitVec.reduceToNat, BitVec.reduceHShiftLeft,
    BitVec.reduceHShiftRight, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.ofNat_eq_ofNat, Lua.Vm.Fn.SfLens.nf_zext_bool,
    Lua.Vm.Fn.FloorLens.p_bv_add_zero, Lua.Vm.Fn.FloorLens.p_bv_zero_add,
    Lua.Vm.Fn.FloorLens.fl_hi, Lua.Vm.Fn.FloorLens.fl_e, Lua.Vm.Fn.FloorLens.fl_lo,
    Lua.Vm.Fn.FloorLens.nf_sraw, Lua.Vm.Fn.FloorLens.nf_srlw, Lua.Vm.Fn.FloorLens.nf_sllw,
    Lua.Vm.Fn.FloorLens.nf_addw, Lua.Vm.Fn.FloorLens.nf_subw, Lua.Vm.Fn.FloorLens.nf_not,
    Lua.Vm.Fn.FloorLens.nf_andlo, Lua.Vm.Fn.FloorLens.nf_andhi, Lua.Vm.Fn.FloorLens.nf_andhiL,
    Lua.Vm.Fn.FloorLens.nf_or_eq0, Lua.Vm.Fn.FloorLens.nf_or_eq0_64, Lua.Vm.Fn.FloorLens.nf_or_zero_of,
    Lua.Vm.Fn.FloorLens.p_or_zero, Lua.Vm.Fn.FloorLens.p_zero_and,
    Lua.Vm.Fn.FloorLens.p_and_zero,
    Lua.Vm.Fn.FloorLens.nf_sextw2, Lua.Vm.Fn.SfLens.nf_add, Lua.Vm.Fn.SfLens.nf_shl,
    Lua.Vm.Fn.SfLens.nf_shr, Lua.Vm.Fn.FloorLens.fl_zext32, Lua.Vm.Fn.FloorLens.sge_toNat, Lua.Vm.Fn.FloorLens.slt_toNat,
    Lua.Vm.Fn.FloorLens.uge_toNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceDiv,
    Lua.Vm.Fn.FloorLens.p_add_zero, Lua.Vm.Fn.FloorLens.p_zero_add, Lua.Vm.Fn.FloorLens.p_zero_mul,
    Lua.Vm.Fn.FloorLens.p_mul_zero, Lua.Vm.Fn.FloorLens.p_zero_mod, Lua.Vm.Fn.FloorLens.p_zero_div,
    Lua.Vm.Fn.FloorLens.nf_sext_le, Lua.Vm.Fn.FloorLens.nf_sext_lt, Lua.Vm.Fn.FloorLens.nf_sext_mod32,
    Lua.Vm.Fn.FloorLens.nf_sext_mod32', Lua.Vm.Fn.FloorLens.nf_mask_mod32,
    Lua.Vm.Fn.FloorLens.nf_addmod, Lua.Vm.Fn.FloorLens.nf_addmod', Lua.Vm.Fn.FloorLens.nf_adddiv, Nat.add_assoc, Lua.Vm.Fn.FloorLens.nf_modmod,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true,
    Bool.not_true, Bool.not_false, Bool.not_not, decide_true, decide_false,
    Bool.false_eq_true, Bool.true_eq_false, Bool.and_eq_true, Bool.or_eq_true, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT,
    Nat.reduceGT, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true,
    if_pos, if_neg] $[$loc]?
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.beq_toNat, Lua.Vm.Fn.SfLens.bne_toNat, BitVec.toNat_ofNat, Nat.reducePow,
    Lua.Vm.Fn.FloorLens.nf_sext_eq0,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true, Bool.not_not,
    decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false,
    if_pos, if_neg] $[$loc]?))

/-- `fl_all` without deciding `if`s by `omega` (a leaf cases them first:
an `omega` proof of a reference branch's condition is a kernel cost). -/
syntax "fl_alln" (Lean.Parser.Tactic.location)? : tactic
macro_rules | `(tactic| fl_alln $[$loc]?) => `(tactic| (
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit, BitVec.reduceToNat, Nat.reducePow,
    Lua.Vm.Fn.FloorLens.fl_hi, Lua.Vm.Fn.SfLens.nf_shl, Lua.Vm.Fn.FloorLens.fl_e] $[$loc]?
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit, Lua.Vm.Fn.SfLens.sext_eq,
    BitVec.reduceSignExtend, BitVec.reduceAppend, BitVec.reduceAdd, BitVec.reduceToNat, BitVec.reduceHShiftLeft,
    BitVec.reduceHShiftRight, BitVec.reduceAnd, BitVec.reduceOr, BitVec.reduceXOr, BitVec.reduceNot,
    BitVec.ofNat_eq_ofNat, Lua.Vm.Fn.SfLens.nf_zext_bool,
    Lua.Vm.Fn.FloorLens.p_bv_add_zero, Lua.Vm.Fn.FloorLens.p_bv_zero_add,
    Lua.Vm.Fn.FloorLens.fl_hi, Lua.Vm.Fn.FloorLens.fl_e, Lua.Vm.Fn.FloorLens.fl_lo,
    Lua.Vm.Fn.FloorLens.nf_sraw, Lua.Vm.Fn.FloorLens.nf_srlw, Lua.Vm.Fn.FloorLens.nf_sllw,
    Lua.Vm.Fn.FloorLens.nf_addw, Lua.Vm.Fn.FloorLens.nf_subw, Lua.Vm.Fn.FloorLens.nf_not,
    Lua.Vm.Fn.FloorLens.nf_andlo, Lua.Vm.Fn.FloorLens.nf_andhi, Lua.Vm.Fn.FloorLens.nf_andhiL,
    Lua.Vm.Fn.FloorLens.nf_or_eq0, Lua.Vm.Fn.FloorLens.nf_or_eq0_64, Lua.Vm.Fn.FloorLens.nf_or_zero_of,
    Lua.Vm.Fn.FloorLens.p_or_zero, Lua.Vm.Fn.FloorLens.p_zero_and,
    Lua.Vm.Fn.FloorLens.p_and_zero,
    Lua.Vm.Fn.FloorLens.nf_sextw2, Lua.Vm.Fn.SfLens.nf_add, Lua.Vm.Fn.SfLens.nf_shl,
    Lua.Vm.Fn.SfLens.nf_shr, Lua.Vm.Fn.FloorLens.fl_zext32, Lua.Vm.Fn.FloorLens.sge_toNat, Lua.Vm.Fn.FloorLens.slt_toNat,
    Lua.Vm.Fn.FloorLens.uge_toNat, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceDiv,
    Lua.Vm.Fn.FloorLens.p_add_zero, Lua.Vm.Fn.FloorLens.p_zero_add, Lua.Vm.Fn.FloorLens.p_zero_mul,
    Lua.Vm.Fn.FloorLens.p_mul_zero, Lua.Vm.Fn.FloorLens.p_zero_mod, Lua.Vm.Fn.FloorLens.p_zero_div,
    Lua.Vm.Fn.FloorLens.nf_sext_le, Lua.Vm.Fn.FloorLens.nf_sext_lt, Lua.Vm.Fn.FloorLens.nf_sext_mod32,
    Lua.Vm.Fn.FloorLens.nf_sext_mod32', Lua.Vm.Fn.FloorLens.nf_mask_mod32,
    Lua.Vm.Fn.FloorLens.nf_addmod, Lua.Vm.Fn.FloorLens.nf_addmod', Lua.Vm.Fn.FloorLens.nf_adddiv, Nat.add_assoc, Lua.Vm.Fn.FloorLens.nf_modmod,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true,
    Bool.not_true, Bool.not_false, Bool.not_not, decide_true, decide_false,
    Bool.false_eq_true, Bool.true_eq_false, Bool.and_eq_true, Bool.or_eq_true, Nat.reduceEqDiff, Nat.reduceLeDiff, Nat.reduceLT,
    Nat.reduceGT, ↓reduceIte, ite_true, ite_false, not_true_eq_false, not_false_eq_true] $[$loc]?
  all_goals simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.SfLens.beq_toNat, Lua.Vm.Fn.SfLens.bne_toNat, BitVec.toNat_ofNat, Nat.reducePow,
    Lua.Vm.Fn.FloorLens.nf_sext_eq0,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true, Bool.not_not,
    decide_true, decide_false, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceEqDiff, ↓reduceIte, ite_true, ite_false] $[$loc]?))

macro "fl_nf" : tactic => `(tactic| (fl_pre; fl_all))

/-- The reference's words as `ofNat`, propositionally (a definitional step
here leaves the kernel the reference's unfolding to check). -/
theorem p_bits (neg : Bool) (be f : Nat) :
    Lua.Num.F64.bits neg be f = BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + be * 2 ^ 52 + f) := by
  rw [Lua.Num.F64.bits]
theorem p_qnan : Lua.Num.F64.qnan = BitVec.ofNat 64 9221120237041090560 := by
  rw [Lua.Num.F64.qnan]
theorem p_infty (neg : Bool) :
    Lua.Num.F64.infty neg = BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + 2047 * 2 ^ 52 + 0) := by
  rw [Lua.Num.F64.infty, p_bits]

/-! The reference's branch, chosen by the chamber's facts (never its whole
`if` tree, which the kernel would then check branch by branch). -/

theorem ff_special (s : Bool) (f : Nat) :
    Lua.Num.SfRef.floorFields s 2047 f = if f = 0 then Lua.Num.F64.infty s else Lua.Num.F64.qnan := by
  unfold Lua.Num.SfRef.floorFields; rw [if_pos rfl]
theorem ff_big (s : Bool) (e f : Nat) (h1 : 1075 ≤ e) (h2 : e < 2047) :
    Lua.Num.SfRef.floorFields s e f = Lua.Num.F64.bits s e f := by
  unfold Lua.Num.SfRef.floorFields; rw [if_neg (by omega), if_pos h1]
theorem ff_small (s : Bool) (e f : Nat) (h : e < 1023) :
    Lua.Num.SfRef.floorFields s e f =
      if s then (if e = 0 ∧ f = 0 then Lua.Num.F64.bits true 0 0 else Lua.Num.F64.bits true 1023 0)
      else Lua.Num.F64.bits false 0 0 := by
  unfold Lua.Num.SfRef.floorFields; rw [if_neg (by omega), if_neg (by omega), if_pos h]
theorem ff_mid (s : Bool) (e f : Nat) (h1 : 1023 ≤ e) (h2 : e < 1075) :
    Lua.Num.SfRef.floorFields s e f =
      if f % 2 ^ (1075 - e) = 0 then Lua.Num.F64.bits s e f
      else if s then Lua.Num.F64.bits true 0 ((e * 2 ^ 52 + f) / 2 ^ (1075 - e) * 2 ^ (1075 - e) + 2 ^ (1075 - e))
      else Lua.Num.F64.bits false 0 ((e * 2 ^ 52 + f) / 2 ^ (1075 - e) * 2 ^ (1075 - e)) := by
  unfold Lua.Num.SfRef.floorFields; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

open Lean Elab Tactic Meta in
/-- `unfold_lhs` through the goal's metadata. -/
elab "fl_unfold_lhs" : tactic => do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, lhs, _) := g.eq? | throwError "fl_unfold_lhs: not an equation"
  let .const n _ := lhs.getAppFn | throwError "fl_unfold_lhs: the left side's head is not a constant"
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))

open Lean Elab Tactic Meta in
/-- Split the guard at the head of the goal's left side (a node's fork), not
an `if` inside a datum (a sign-extension's, decided at the leaves). -/
elab "fl_split" : tactic => withMainContext do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, lhs, _) := g.eq? | throwError "fl_split: not an equation"
  unless lhs.isAppOfArity ``ite 5 do throwError "fl_split: the left side is not a fork"
  let cE := lhs.getArg! 1
  if let some t := cE.find? (fun e => e.isAppOfArity ``ite 5) then
    -- a datum's `if` inside the fork's condition: case on it first
    let c ← Term.exprToSyntax (t.getArg! 1)
    let h := mkIdent `hdat
    evalTactic (← `(tactic| (by_cases $h:ident : $c <;>
      first | (simp only [if_pos $h:ident]) | (simp only [if_neg $h:ident]))))
    return
  let c ← Term.exprToSyntax cE
  let h := mkIdent `hfork
  evalTactic (← `(tactic| (by_cases $h:ident : $c <;>
    first | (rw [if_pos $h:ident]) | (rw [if_neg $h:ident]))))
  -- the fork's fact in its literal normal form (no discharger: the fact
  -- never rewrites itself)
  evalTactic (← `(tactic| all_goals (try simp only [Nat.reduceMod, Nat.reducePow,
    Nat.reduceEqDiff, Lua.Vm.Fn.FloorLens.nf_sext_eq0, Lua.Vm.Fn.FloorLens.nf_sext_le,
    Lua.Vm.Fn.FloorLens.nf_sext_lt] at $h:ident)))

/-- Explore a chamber: unfold the node at the head, or split its fork and
drop a side the chamber's facts refute. -/
macro "fl_go" : tactic => `(tactic| (
  repeat' (first
    | (unfold_node []; fl_nf)
    | (fl_split <;> (try (exfalso; fl_omega))))))

open Lean Elab Tactic Meta in
/-- Case on the first `if` left in the goal or its hypotheses (a datum's
sign-extension, a reference branch), its two sides simplified everywhere. -/
elab "fl_case1" : tactic => withMainContext do
  let isIte (t : Expr) : Bool := t.isAppOfArity ``ite 5
  let mut cond? : Option Expr := none
  let g ← instantiateMVars (← getMainTarget)
  if let some t := g.find? isIte then cond? := some (t.getArg! 1)
  if cond?.isNone then
    for d in ← getLCtx do
      if cond?.isNone && !d.isImplementationDetail then
        if let some t := (← instantiateMVars d.type).find? isIte then cond? := some (t.getArg! 1)
  let some c := cond? | throwError "fl_case1: no if"
  let cs ← Term.exprToSyntax c
  evalTactic (← `(tactic| (by_cases hc : $cs <;>
    ((try simp only [if_pos hc] at *); (try simp only [if_neg hc] at *)))))

/-- Close a leaf: the routine's return value against the reference's
branch, both as `ofNat`, compared in `Nat`. -/
macro "fl_leaf" : tactic => `(tactic| (
  fl_unfold_lhs
  fl_nf
  all_goals (simp (config := { failIfUnchanged := false }) (disch := fl_omega) only [
    Lua.Vm.Fn.FloorLens.ff_special, Lua.Vm.Fn.FloorLens.ff_big, Lua.Vm.Fn.FloorLens.ff_small,
    Lua.Vm.Fn.FloorLens.ff_mid])
  all_goals (simp (config := { failIfUnchanged := false }) only [Lua.Vm.Fn.FloorLens.p_bits,
    Lua.Vm.Fn.FloorLens.p_qnan, Lua.Vm.Fn.FloorLens.p_infty])
  all_goals fl_alln
  all_goals (repeat' fl_case1)
  all_goals fl_alln
  all_goals (first | (exfalso; fl_omega) |
    (apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; fl_omega))))

set_option hygiene false in
/-- One chamber of a one-operand routine with a 112-byte run (`floor`): the
frame facts, the high word's value (`hiw`), the DAG explored (`fl_go`), each
leaf closed (`fl_leaf`). The chamber's names (`hs`, `hrod`, `f`, `F`) are the
caller's. -/
macro "fl_chamber " sx:term:max e:term:max : tactic => `(tactic| (
  have := hs.lo; have := hs.hi; have := hs.al; have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hsp : FnSp (s - 64) 48 := fn_sp_in hs (by decide) (by decide)
  have hhiw := Lua.Vm.Fn.FloorLens.hiw_def $sx $e f
  unfold F
  fl_nf
  fl_go
  all_goals fl_leaf))

open Lean in
set_option hygiene false in
/-- **The one-operand chamber generator**, per exponent: for each
`e ∈ [lo, hi)` and sign, the chamber `ch_<e>_<s> : F m s r (P s e f) =
floorFields s e f` (the machine's shifts by `e` literal). -/
macro "fl_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for e in List.range' lo.getNat (hi.getNat - lo.getNat) do
    for sx in [0, 1] do
      let el := Syntax.mkNumLit (toString e)
      let sl := Syntax.mkNumLit (toString sx)
      cmds := cmds.push (← `(command|
        theorem $(mkIdent (Name.mkSimple s!"ch_{e}_{sx}")) (m : Mem) (s : Nat) (r : BitVec 64) (f : Nat)
            (hs : FnSp s 112) (hrod : RodataRead m) (hf : f < 2 ^ 52) :
            F m s r (Lua.Vm.Fn.SfCmpLens.P $sl $el f) =
              Lua.Num.SfRef.floorFields (decide ($sl = 1)) $el f := by
          fl_chamber $sl $el))
  return ⟨mkNullNode cmds⟩

open Lean in
set_option hygiene false in
/-- **The cover** of the chambers: the ranges the machine treats uniformly
(`e < lo`: below one; `hi ≤ e < 2047`: integral; `e = 2047`: `±∞`/NaN),
each one chamber per sign; the per-exponent chambers `ch_<e>_<s>` of
`fl_chambers lo hi` joined by the exponent (`G_mid`); `G_eq` over every
field triple and `F_eq_ref : F m s r x = SfRef.floor x`. -/
macro "fl_cover " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  let st (sl : TSyntax `term) (e : TSyntax `term) : MacroM (TSyntax `term) :=
    `(F m s r (Lua.Vm.Fn.SfCmpLens.P $sl $e f) = Lua.Num.SfRef.floorFields (decide ($sl = 1)) $e f)
  for sx in [0, 1] do
    let sl := Syntax.mkNumLit (toString sx)
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"ch_lo_{sx}")) (m : Mem) (s : Nat) (r : BitVec 64) (e f : Nat)
          (hs : FnSp s 112) (hrod : RodataRead m) (hf : f < 2 ^ 52) (he2 : e < $lo) : $(← st sl (← `(e))) := by
        fl_chamber $sl e))
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"ch_hi_{sx}")) (m : Mem) (s : Nat) (r : BitVec 64) (e f : Nat)
          (hs : FnSp s 112) (hrod : RodataRead m) (hf : f < 2 ^ 52) (he1 : $hi ≤ e) (he2 : e < 2047) :
          $(← st sl (← `(e))) := by
        fl_chamber $sl e))
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"ch_sp_{sx}")) (m : Mem) (s : Nat) (r : BitVec 64) (f : Nat)
          (hs : FnSp s 112) (hrod : RodataRead m) (hf : f < 2 ^ 52) : $(← st sl (← `(2047))) := by
        fl_chamber $sl 2047))
    -- the per-exponent chambers, by the exponent (a balanced split: a
    -- chain of `hi - lo` nested cases is past `maxRecDepth`)
    let rec tree (a b : Nat) (fuel : Nat) : MacroM (TSyntax `tactic) := do
      match fuel with
      | 0 => `(tactic| omega)
      | fuel + 1 =>
        if b ≤ a + 1 then
          let el := Syntax.mkNumLit (toString a)
          let ch := mkIdent (Name.mkSimple s!"ch_{a}_{sx}")
          `(tactic| (have hE : e = $el := by omega
                     subst hE; exact $ch m s r f hs hrod hf))
        else
          let c := (a + b) / 2
          let cl := Syntax.mkNumLit (toString c)
          let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a c fuel):tactic)
          let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree c b fuel):tactic)
          `(tactic| if hS : e < $cl then $t1 else $t2)
    let tac ← tree lo.getNat hi.getNat 64
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"G_mid_{sx}")) (m : Mem) (s : Nat) (r : BitVec 64) (e f : Nat)
          (hs : FnSp s 112) (hrod : RodataRead m) (hf : f < 2 ^ 52) (he1 : $lo ≤ e) (he2 : e < $hi) :
          $(← st sl (← `(e))) := by
        $tac:tactic))
  cmds := cmds.push (← `(command|
    theorem G_eq (m : Mem) (s : Nat) (r : BitVec 64) (sg e f : Nat) (hs : FnSp s 112) (hrod : RodataRead m)
        (hsg : sg < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
        F m s r (Lua.Vm.Fn.SfCmpLens.P sg e f) = Lua.Num.SfRef.floorFields (decide (sg = 1)) e f := by
      rcases (by omega : sg = 0 ∨ sg = 1) with rfl | rfl
      · if h1 : e = 2047 then (subst h1; exact ch_sp_0 m s r f hs hrod hf)
        else if h2 : $hi ≤ e then exact ch_hi_0 m s r e f hs hrod hf h2 (by omega)
        else if h3 : e < $lo then exact ch_lo_0 m s r e f hs hrod hf h3
        else exact G_mid_0 m s r e f hs hrod hf (by omega) (by omega)
      · if h1 : e = 2047 then (subst h1; exact ch_sp_1 m s r f hs hrod hf)
        else if h2 : $hi ≤ e then exact ch_hi_1 m s r e f hs hrod hf h2 (by omega)
        else if h3 : e < $lo then exact ch_lo_1 m s r e f hs hrod hf h3
        else exact G_mid_1 m s r e f hs hrod hf (by omega) (by omega)))
  cmds := cmds.push (← `(command|
    theorem F_eq_ref (m : Mem) (s : Nat) (r : BitVec 64) (x : BitVec 64) (hs : FnSp s 112)
        (hrod : RodataRead m) : F m s r x = Lua.Num.SfRef.floor x := by
      have hx := x.isLt
      conv => lhs; rw [Lua.Vm.Fn.SfCmpLens.P_fields x]
      rw [G_eq m s r _ _ _ hs hrod (by omega) (by omega) (by omega)]
      unfold Lua.Num.SfRef.floor
      rw [Lua.Vm.Fn.SfCmpLens.sign_fields]
      rfl))
  return ⟨mkNullNode cmds⟩

end Lua.Vm.Fn.FloorLens

import Lua.Vm.Fn.Ieee754Pow
import Lua.Vm.Fn.FmodLens
import Lua.Vm.Fn.SqrtSpec
import Lua.Vm.Sim.Kit.FltVal
import Lua.Num.Pow
import Lua.Vm.Fn.PowAttr
import Lua.Vm.Fn.PowStage
import Lua.Vm.Fn.PowRod
import Lua.Vm.Sim.Kit.FnTail

/-!
# The lenses of `__ieee754_pow`'s level (b) (lane float-sf7)

`e_pow.c` on the machine and in `Lua.Num.Pow.ieee754Pow` is the same C: the
machine's soft-float calls are `F64` operations (`CALLEES_FOR`), the model's
are `Float.Model`'s, and both read and build words of the doubles. The proof
walks the machine's fork tree (L5-fork) with the model beside it, every value
in one normal form (`pw_nf`):

* **the Int lens** (`FmodLens`, extended here): a register is
  `BitVec.ofInt 64 i` of an `Int` expression, a guard a `decide` over `Int`;
* **the float lens**: a soft-float result is `BitVec.ofInt 64 (W d)` of the
  model datum `d` it computes (`W d`: `d`'s bits as a signed integer), by the
  bridges `F64.add_eq_model`, …; an operand `ofInt 64 (W d)` reads back as
  `d` (`model_W`), a constant as its model literal;
* **the model's words**: `hiW d`, `loW d` are `W d / 2^32`, `W d % 2^32`, and
  `Int32`/`UInt32` arithmetic is `Int` arithmetic on `toInt`/`toNat`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.PowLens

open Lua.Num Lua.Vm.Fn.FmodLens

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The float lens -/

/-- A model datum's bits as a signed 64-bit integer: the Int lens's atom. -/
def W (d : Float.Model) : Int := d.toBits.toBitVec.toInt

theorem W_lo (d : Float.Model) : -2 ^ 63 ≤ W d := by
  unfold W; have := BitVec.le_toInt d.toBits.toBitVec; simpa using this

theorem W_hi (d : Float.Model) : W d < 2 ^ 63 := by
  unfold W; have := @BitVec.toInt_lt 64 d.toBits.toBitVec; simpa using this

theorem bits_W (d : Float.Model) : d.toBits.toBitVec = BitVec.ofInt 64 (W d) :=
  (BitVec.ofInt_toInt).symm

/-- An operand that is a model datum's bits reads back as the datum. -/
theorem model_W (d : Float.Model) : F64.toModel (BitVec.ofInt 64 (W d)) = d := by
  rw [← bits_W]; exact Lua.Vm.Sim.At.toModel_toBits d

theorem add_l (a b : BitVec 64) :
    F64.add a b = BitVec.ofInt 64 (W (Float.Model.add (F64.toModel a) (F64.toModel b))) := by
  rw [F64.add_eq_model, bits_W]
theorem sub_l (a b : BitVec 64) :
    F64.sub a b = BitVec.ofInt 64 (W (Float.Model.sub (F64.toModel a) (F64.toModel b))) := by
  rw [F64.sub_eq_model, bits_W]
theorem mul_l (a b : BitVec 64) :
    F64.mul a b = BitVec.ofInt 64 (W (Float.Model.mul (F64.toModel a) (F64.toModel b))) := by
  rw [F64.mul_eq_model, bits_W]
theorem div_l (a b : BitVec 64) :
    F64.div a b = BitVec.ofInt 64 (W (Float.Model.div (F64.toModel a) (F64.toModel b))) := by
  rw [F64.div_eq_model, bits_W]
theorem sqrt_l (a : BitVec 64) :
    F64.sqrt a = BitVec.ofInt 64 (W (Float.Model.sqrt (F64.toModel a))) := by
  rw [F64.sqrt_eq_model, bits_W]

/-- A non-NaN pattern's model keeps its bits. -/
theorem toBits_toModel (x : F64) (h : x.cls ≠ .nan) : (F64.toModel x).toBits.toBitVec = x := by
  show Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
    (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 (UInt64.ofBitVec x).toBitVec) = x
  rw [UInt64.toBitVec_ofBitVec, F64.unpack_eq, F64.pack_cls x h]

/-- An operand's words: a non-NaN input is its own datum's bits. -/
theorem W_in (X : Int) (h1 : -2 ^ 63 ≤ X) (h2 : X < 2 ^ 63)
    (hn : ¬ (X / 2 ^ 52 % 2048 = 2047 ∧ X % 2 ^ 52 ≠ 0)) : W (F64.toModel (BitVec.ofInt 64 X)) = X := by
  unfold W
  rw [toBits_toModel, ofInt_toInt X h1 h2]
  have h3 := ofInt_toNat X
  unfold F64.cls F64.bexp F64.frac
  intro hc
  by_cases h1 : (BitVec.ofInt 64 X).toNat / 2 ^ 52 % 2 ^ 11 = 2047
  · by_cases h2 : (BitVec.ofInt 64 X).toNat % 2 ^ 52 = 0
    · rw [ite_eq_left h1, ite_eq_left h2] at hc; cases hc
    · exact hn ⟨by omega, by omega⟩
  · rw [ite_eq_right h1] at hc
    by_cases h3 : (BitVec.ofInt 64 X).toNat / 2 ^ 52 % 2 ^ 11 = 0
    · rw [ite_eq_left h3] at hc; split at hc <;> cases hc
    · rw [ite_eq_right h3] at hc; cases hc

/-- A non-NaN pattern's model keeps its bits (any `Int` image). -/
theorem W_ofInt (e : Int) (hn : ¬ (e / 2 ^ 52 % 2048 = 2047 ∧ e % 2 ^ 52 ≠ 0)) :
    W (F64.toModel (BitVec.ofInt 64 e)) = e.bmod (2 ^ 64) := by
  unfold W
  rw [toBits_toModel, BitVec.toInt_ofInt]
  have h3 := ofInt_toNat e
  unfold F64.cls F64.bexp F64.frac
  intro hc
  by_cases h1 : (BitVec.ofInt 64 e).toNat / 2 ^ 52 % 2 ^ 11 = 2047
  · by_cases h2 : (BitVec.ofInt 64 e).toNat % 2 ^ 52 = 0
    · rw [ite_eq_left h1, ite_eq_left h2] at hc; cases hc
    · exact hn ⟨by omega, by omega⟩
  · rw [ite_eq_right h1] at hc
    by_cases h3 : (BitVec.ofInt 64 e).toNat / 2 ^ 52 % 2 ^ 11 = 0
    · rw [ite_eq_left h3] at hc; split at hc <;> cases hc
    · rw [ite_eq_right h3] at hc; cases hc

/-- `+` and `*` of the model commute (`F64`'s, through the round trip; the
arm kit's `At.model_mul_comm` is the same fact over its imports). -/
theorem madd_comm (a b : Float.Model) : Float.Model.add a b = Float.Model.add b a := by
  have h := F64.add_comm a.toBits.toBitVec b.toBits.toBitVec
  rw [F64.add_eq_model, F64.add_eq_model, Lua.Vm.Sim.At.toModel_toBits, Lua.Vm.Sim.At.toModel_toBits] at h
  have := congrArg F64.toModel h
  rwa [Lua.Vm.Sim.At.toModel_toBits, Lua.Vm.Sim.At.toModel_toBits] at this
theorem mmul_comm (a b : Float.Model) : Float.Model.mul a b = Float.Model.mul b a := by
  have h := F64.mul_comm a.toBits.toBitVec b.toBits.toBitVec
  rw [F64.mul_eq_model, F64.mul_eq_model, Lua.Vm.Sim.At.toModel_toBits, Lua.Vm.Sim.At.toModel_toBits] at h
  have := congrArg F64.toModel h
  rwa [Lua.Vm.Sim.At.toModel_toBits, Lua.Vm.Sim.At.toModel_toBits] at this

theorem bv64_ext (a b : Int) (h : a % 2 ^ 64 = b % 2 ^ 64) : BitVec.ofInt 64 a = BitVec.ofInt 64 b := by
  apply BitVec.eq_of_toNat_eq
  have := ofInt_toNat a; have := ofInt_toNat b
  omega

/-- `F64.neg` is the sign bit flipped. -/
theorem f64neg_ofInt (e : Int) : F64.neg (BitVec.ofInt 64 e) = BitVec.ofInt 64 (e + 9223372036854775808) := by
  apply BitVec.eq_of_toNat_eq
  have hb : F64.bexp (BitVec.ofInt 64 e) < 2048 := Nat.mod_lt _ (by decide)
  have hf : F64.frac (BitVec.ofInt 64 e) < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold F64.neg
  rw [F64.toNat_bits _ _ _ hb hf]
  have hs := F64.toNat_split (BitVec.ofInt 64 e)
  have h1 := ofInt_toNat e
  have h2 := ofInt_toNat (e + 9223372036854775808)
  generalize (BitVec.ofInt 64 (e + 9223372036854775808)).toNat = v at h2 ⊢
  unfold F64.sign at hs ⊢
  generalize F64.bexp (BitVec.ofInt 64 e) = be at hs hb ⊢
  generalize F64.frac (BitVec.ofInt 64 e) = f at hs hf ⊢
  generalize (BitVec.ofInt 64 e).toNat = u at hs h1 ⊢
  by_cases h : 2 ^ 63 ≤ u <;> simp [h] at hs ⊢ <;> omega

/-- The model's negation of a non-NaN pattern: the sign bit flipped. -/
theorem mneg_l (e : Int) (hn : ¬ (e / 2 ^ 52 % 2048 = 2047 ∧ e % 2 ^ 52 ≠ 0)) :
    Float.Model.neg (F64.toModel (BitVec.ofInt 64 e)) = F64.toModel (BitVec.ofInt 64 (e + 9223372036854775808)) := by
  have hc : F64.cls (BitVec.ofInt 64 e) ≠ .nan := by
    have h3 := ofInt_toNat e
    unfold F64.cls F64.bexp F64.frac
    intro hc
    by_cases h1 : (BitVec.ofInt 64 e).toNat / 2 ^ 52 % 2 ^ 11 = 2047
    · by_cases h2 : (BitVec.ofInt 64 e).toNat % 2 ^ 52 = 0
      · rw [ite_eq_left h1, ite_eq_left h2] at hc; cases hc
      · exact hn ⟨by omega, by omega⟩
    · rw [ite_eq_right h1] at hc
      by_cases h3 : (BitVec.ofInt 64 e).toNat / 2 ^ 52 % 2 ^ 11 = 0
      · rw [ite_eq_left h3] at hc; split at hc <;> cases hc
      · rw [ite_eq_right h3] at hc; cases hc
  rw [← f64neg_ofInt, F64.neg_eq_model _ hc, Lua.Vm.Sim.At.toModel_toBits]

/-- `__subdf3` is `__adddf3` of the negation (soft-fp's `_FP_SUB` flips the sign). -/
theorem f64_sub_eq_add_neg (x y : F64) : F64.sub x y = F64.add x (F64.neg y) := by
  unfold F64.sub F64.add
  rw [F64.cls_neg]
  rcases hx : x.cls with _ | a | a | ⟨a, m, e⟩ <;> rcases hy : y.cls with _ | b | b | ⟨b, n, f⟩ <;>
    simp only [F64.Cls.negate] <;> (try cases a) <;> (try cases b) <;>
    simp [F64.sgnApply, Int.sub_eq_add_neg]

/-- gcc's `x + c` for a negative literal `c` (`P2`, `P4`, `e_pow.c:311`):
`x - (-c)`, the same datum. -/
theorem madd_neglit (a : Float.Model) (c : Int) (h1 : -9223372036854775808 ≤ c) (h2 : c < 0) :
    Float.Model.add a (F64.toModel (BitVec.ofInt 64 c)) =
      Float.Model.sub a (F64.toModel (BitVec.ofInt 64 (c + 9223372036854775808))) := by
  have h : F64.sub a.toBits.toBitVec (BitVec.ofInt 64 (c + 9223372036854775808)) =
      F64.add a.toBits.toBitVec (BitVec.ofInt 64 c) := by
    rw [f64_sub_eq_add_neg, f64neg_ofInt]
    congr 1
    apply bv64_ext
    omega
  have := congrArg F64.toModel h
  rw [F64.sub_eq_model, F64.add_eq_model, Lua.Vm.Sim.At.toModel_toBits, Lua.Vm.Sim.At.toModel_toBits,
    Lua.Vm.Sim.At.toModel_toBits] at this
  exact this.symm
theorem madd_neglit' (a : Float.Model) (c : Int) (h1 : -9223372036854775808 ≤ c) (h2 : c < 0) :
    Float.Model.add (F64.toModel (BitVec.ofInt 64 c)) a =
      Float.Model.sub a (F64.toModel (BitVec.ofInt 64 (c + 9223372036854775808))) := by
  rw [madd_comm]; exact madd_neglit a c h1 h2

/-- A register's word read back (`ld` of a spilled `sd`): `ofInt` keeps the
residue only. -/
theorem ofInt_bmod64 (x : Int) : BitVec.ofInt 64 (x.bmod 18446744073709551616) = BitVec.ofInt 64 x :=
  (FmodLens.ofInt_bmod x).symm

/-- Equal bit patterns modulo `2^64`: equal operands. -/
theorem toModel_congr (a b : Int) (h : a % 2 ^ 64 = b % 2 ^ 64) :
    F64.toModel (BitVec.ofInt 64 a) = F64.toModel (BitVec.ofInt 64 b) := by
  congr 1
  apply BitVec.eq_of_toNat_eq
  have := ofInt_toNat a; have := ofInt_toNat b
  omega

/-! ## The Int lens, beyond `FmodLens` -/

/-- `and` with a low mask, of any sign: the value modulo the mask's power. -/
theorem and_low (a : Int) (k : Nat) (hk : k ≤ 64) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 ((2 ^ k - 1 : Nat) : Int) =
      BitVec.ofInt 64 (a % ((2 ^ k : Nat) : Int)) := by
  have hP : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hP64 : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have hd : (2 ^ k : Nat) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 hk
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, ofInt_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  have h1 := ofInt_toNat a
  have h2 := ofInt_toNat (a % ((2 ^ k : Nat) : Int))
  generalize 2 ^ k = P at hP hP64 hd h2 ⊢
  have hdi : ((P : Nat) : Int) ∣ 2 ^ 64 := by exact_mod_cast hd
  have e : (a % 2 ^ 64) % (P : Int) = a % P := Int.emod_emod_of_dvd _ hdi
  have h3 : 0 ≤ a % (P : Int) := Int.emod_nonneg _ (by omega)
  have h4 : a % (P : Int) < P := Int.emod_lt_of_pos _ (by omega)
  have h5 : (a % (P : Int)) % 2 ^ 64 = a % P := Int.emod_eq_of_lt h3 (by omega)
  rw [h5] at h2
  have h6 : (((BitVec.ofInt 64 a).toNat % P : Nat) : Int) = ((BitVec.ofInt 64 a).toNat : Int) % (P : Int) :=
    Int.natCast_emod _ _
  rw [h1, e] at h6
  omega

theorem and_7fffffff' (a : Int) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2147483647 = BitVec.ofInt 64 (a % 2147483648) :=
  and_low a 31 (by decide)
theorem and_fffff' (a : Int) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 1048575 = BitVec.ofInt 64 (a % 1048576) :=
  and_low a 20 (by decide)
theorem and_2047' (a : Int) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2047 = BitVec.ofInt 64 (a % 2048) :=
  and_low a 11 (by decide)
theorem and_1' (a : Int) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 1 = BitVec.ofInt 64 (a % 2) :=
  and_low a 1 (by decide)

/-- `or` of a low word and a high part (`(x << 32 >> 32) | (h << 32)`). -/
theorem or_k32' (a b : Int) (ha : a % 4294967296 = 0) (hb0 : 0 ≤ b) (hb : b < 4294967296) :
    BitVec.ofInt 64 b ||| BitVec.ofInt 64 a = BitVec.ofInt 64 (a + b) := by
  rw [BitVec.or_comm]; exact or_low a b 32 (by decide) ha hb0 hb

/-- A bit above a small word (`ori 0x20000000`-style, `lui` then `or`). -/
theorem or_k29' (b : Int) (hb0 : 0 ≤ b) (hb : b < 536870912) :
    BitVec.ofInt 64 b ||| BitVec.ofInt 64 536870912 = BitVec.ofInt 64 (536870912 + b) := by
  rw [BitVec.or_comm]; exact or_low 536870912 b 29 (by decide) (by decide) hb0 hb

theorem nat_and_hi (u j : Nat) (hj : j ≤ 64) (hu : u < 2 ^ 64) :
    u &&& (2 ^ 64 - 2 ^ j) = u - u % 2 ^ j := by
  have e1 : 2 ^ 64 - 2 ^ j = (2 ^ (64 - j) - 1) * 2 ^ j := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel hj]
  rw [e1, land_field]
  have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have h64 : 2 ^ 64 = 2 ^ (64 - j) * 2 ^ j := by rw [← Nat.pow_add, Nat.sub_add_cancel hj]
  have hlt : u / 2 ^ j < 2 ^ (64 - j) := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← h64]; exact hu
  rw [Nat.mod_eq_of_lt hlt]
  have := Nat.mod_add_div u (2 ^ j)
  rw [Nat.mul_comm] at this
  generalize u / 2 ^ j * 2 ^ j = q at this ⊢
  omega

/-- `and` with a high mask `-2^j` (`sraw` of `0xfff00000` by a literal): the
value with its low `j` bits cleared. -/
theorem and_negpow_j (a : Int) (j : Nat) (hj : j ≤ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-(2 ^ j : Int)) = BitVec.ofInt 64 (a - a % 2 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hle : 2 ^ j < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hd : ((2 ^ j : Nat) : Int) ∣ 2 ^ 64 := by
    have : (2 ^ j : Nat) ∣ 2 ^ 64 := Nat.pow_dvd_pow 2 (by omega)
    exact_mod_cast this
  have hPn : ((2 : Int) ^ j) = ((2 ^ j : Nat) : Int) := by simp
  rw [hPn]
  have h1 := ofInt_toNat a
  have h2 := ofInt_toNat (-((2 ^ j : Nat) : Int))
  have h3 := ofInt_toNat (a - a % ((2 ^ j : Nat) : Int))
  generalize (BitVec.ofInt 64 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 64 (-((2 ^ j : Nat) : Int))).toNat = mk at h2 ⊢
  generalize (BitVec.ofInt 64 (a - a % ((2 ^ j : Nat) : Int))).toNat = w at h3 ⊢
  have hmk : mk = 2 ^ 64 - 2 ^ j := by
    generalize 2 ^ j = P at hpos hle h2 ⊢
    omega
  subst hmk
  have hu : u < 2 ^ 64 := by have := Int.emod_lt_of_pos a (by decide : (0:Int) < 2 ^ 64); omega
  rw [nat_and_hi u j (by omega) hu]
  have e : a % ((2 ^ j : Nat) : Int) = (u : Int) % ((2 ^ j : Nat) : Int) := by
    rw [h1, Int.emod_emod_of_dvd _ hd]
  have hmodu : ((u % 2 ^ j : Nat) : Int) = (u : Int) % ((2 ^ j : Nat) : Int) := Int.natCast_emod _ _
  have hle2 : u % 2 ^ j ≤ u := Nat.mod_le _ _
  generalize u % 2 ^ j = r at hmodu hle2 ⊢
  rw [← hmodu] at e
  generalize ((2 ^ j : Nat) : Int) = P at e h3
  omega

/-! The high masks `-2^j` (`sraw` of `0xfff00000` by a literal), one instance per
`j`: `and_negpow_j` at the literal (the exponent is not in the mask's syntax). -/

theorem and_np1 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2) = BitVec.ofInt 64 (a - a % 2) := by
  simpa only [Int.reducePow] using and_negpow_j a 1 (by decide)
theorem and_np2 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-4) = BitVec.ofInt 64 (a - a % 4) := by
  simpa only [Int.reducePow] using and_negpow_j a 2 (by decide)
theorem and_np3 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-8) = BitVec.ofInt 64 (a - a % 8) := by
  simpa only [Int.reducePow] using and_negpow_j a 3 (by decide)
theorem and_np4 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-16) = BitVec.ofInt 64 (a - a % 16) := by
  simpa only [Int.reducePow] using and_negpow_j a 4 (by decide)
theorem and_np5 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-32) = BitVec.ofInt 64 (a - a % 32) := by
  simpa only [Int.reducePow] using and_negpow_j a 5 (by decide)
theorem and_np6 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-64) = BitVec.ofInt 64 (a - a % 64) := by
  simpa only [Int.reducePow] using and_negpow_j a 6 (by decide)
theorem and_np7 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-128) = BitVec.ofInt 64 (a - a % 128) := by
  simpa only [Int.reducePow] using and_negpow_j a 7 (by decide)
theorem and_np8 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-256) = BitVec.ofInt 64 (a - a % 256) := by
  simpa only [Int.reducePow] using and_negpow_j a 8 (by decide)
theorem and_np9 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-512) = BitVec.ofInt 64 (a - a % 512) := by
  simpa only [Int.reducePow] using and_negpow_j a 9 (by decide)
theorem and_np10 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-1024) = BitVec.ofInt 64 (a - a % 1024) := by
  simpa only [Int.reducePow] using and_negpow_j a 10 (by decide)
theorem and_np11 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2048) = BitVec.ofInt 64 (a - a % 2048) := by
  simpa only [Int.reducePow] using and_negpow_j a 11 (by decide)
theorem and_np12 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-4096) = BitVec.ofInt 64 (a - a % 4096) := by
  simpa only [Int.reducePow] using and_negpow_j a 12 (by decide)
theorem and_np13 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-8192) = BitVec.ofInt 64 (a - a % 8192) := by
  simpa only [Int.reducePow] using and_negpow_j a 13 (by decide)
theorem and_np14 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-16384) = BitVec.ofInt 64 (a - a % 16384) := by
  simpa only [Int.reducePow] using and_negpow_j a 14 (by decide)
theorem and_np15 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-32768) = BitVec.ofInt 64 (a - a % 32768) := by
  simpa only [Int.reducePow] using and_negpow_j a 15 (by decide)
theorem and_np16 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-65536) = BitVec.ofInt 64 (a - a % 65536) := by
  simpa only [Int.reducePow] using and_negpow_j a 16 (by decide)
theorem and_np17 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-131072) = BitVec.ofInt 64 (a - a % 131072) := by
  simpa only [Int.reducePow] using and_negpow_j a 17 (by decide)
theorem and_np18 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-262144) = BitVec.ofInt 64 (a - a % 262144) := by
  simpa only [Int.reducePow] using and_negpow_j a 18 (by decide)
theorem and_np19 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-524288) = BitVec.ofInt 64 (a - a % 524288) := by
  simpa only [Int.reducePow] using and_negpow_j a 19 (by decide)
theorem and_np20 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-1048576) = BitVec.ofInt 64 (a - a % 1048576) := by
  simpa only [Int.reducePow] using and_negpow_j a 20 (by decide)
theorem and_np21 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2097152) = BitVec.ofInt 64 (a - a % 2097152) := by
  simpa only [Int.reducePow] using and_negpow_j a 21 (by decide)
theorem and_np22 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-4194304) = BitVec.ofInt 64 (a - a % 4194304) := by
  simpa only [Int.reducePow] using and_negpow_j a 22 (by decide)
theorem and_np23 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-8388608) = BitVec.ofInt 64 (a - a % 8388608) := by
  simpa only [Int.reducePow] using and_negpow_j a 23 (by decide)
theorem and_np24 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-16777216) = BitVec.ofInt 64 (a - a % 16777216) := by
  simpa only [Int.reducePow] using and_negpow_j a 24 (by decide)
theorem and_np25 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-33554432) = BitVec.ofInt 64 (a - a % 33554432) := by
  simpa only [Int.reducePow] using and_negpow_j a 25 (by decide)
theorem and_np26 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-67108864) = BitVec.ofInt 64 (a - a % 67108864) := by
  simpa only [Int.reducePow] using and_negpow_j a 26 (by decide)
theorem and_np27 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-134217728) = BitVec.ofInt 64 (a - a % 134217728) := by
  simpa only [Int.reducePow] using and_negpow_j a 27 (by decide)
theorem and_np28 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-268435456) = BitVec.ofInt 64 (a - a % 268435456) := by
  simpa only [Int.reducePow] using and_negpow_j a 28 (by decide)
theorem and_np29 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-536870912) = BitVec.ofInt 64 (a - a % 536870912) := by
  simpa only [Int.reducePow] using and_negpow_j a 29 (by decide)
theorem and_np30 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-1073741824) = BitVec.ofInt 64 (a - a % 1073741824) := by
  simpa only [Int.reducePow] using and_negpow_j a 30 (by decide)
theorem and_np31 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2147483648) = BitVec.ofInt 64 (a - a % 2147483648) := by
  simpa only [Int.reducePow] using and_negpow_j a 31 (by decide)
theorem and_np32 (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-4294967296) = BitVec.ofInt 64 (a - a % 4294967296) := by
  simpa only [Int.reducePow] using and_negpow_j a 32 (by decide)
/-- The mask first (`and` with `li -1; slli 32`). -/
theorem and_np32' (a : Int) : BitVec.ofInt 64 (-4294967296) &&& BitVec.ofInt 64 a = BitVec.ofInt 64 (a - a % 4294967296) := by
  rw [BitVec.and_comm, and_np32]

/-- `not` (`xori -1`). -/
theorem xor_m1 (a : Int) : BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 (-1) = BitVec.ofInt 64 (-1 - a) := by
  rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have h0 : 0 ≤ a % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h1 : a % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  have h2 : 0 ≤ (-1 - a) % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  omega

/-- `or` with the high mask `-2^30` (`lui 0xc0000`): the low 30 bits kept,
the rest set. -/
theorem or_np30 (a : Int) : BitVec.ofInt 64 a ||| BitVec.ofInt 64 (-1073741824) =
    BitVec.ofInt 64 (a % 1073741824 - 1073741824) := by
  have hn : ∀ c : Int, ~~~(BitVec.ofInt 64 c) = BitVec.ofInt 64 (-1 - c) := by
    intro c
    rw [← BitVec.xor_allOnes, show BitVec.allOnes 64 = BitVec.ofInt 64 (-1) by decide]
    exact xor_m1 c
  have e1 : BitVec.ofInt 64 (-1073741824) = ~~~(BitVec.ofInt 64 (((2 ^ 30 - 1 : Nat) : Int))) := by
    rw [hn]; rfl
  rw [e1, ← BitVec.not_not (b := BitVec.ofInt 64 a), ← BitVec.not_and, hn a, and_low _ 30 (by decide), hn]
  congr 1
  simp only [Nat.reducePow, Nat.reduceSub, Int.reduceNatCast]
  omega

theorem nat_xor_top (u : Nat) (hu : u < 2 ^ 64) : u ^^^ 2 ^ 63 = (u + 2 ^ 63) % 2 ^ 64 := by
  have hb : ∀ v : Nat, v < 2 ^ 63 → ∀ i, (2 ^ 63 + v).testBit i = (decide (63 = i) ^^ v.testBit i) := by
    intro v hv i
    rcases Nat.lt_trichotomy i 63 with h | h | h
    · rw [Nat.testBit_two_pow_add_gt h, decide_eq_false (by omega), Bool.false_xor]
    · subst h; rw [Nat.testBit_two_pow_add_eq]; simp
    · rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by omega : 2 ^ 63 + v < 2 ^ 64)
          (Nat.pow_le_pow_right (by decide) h)),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hv (Nat.pow_le_pow_right (by decide) (by omega)))]
      simp; omega
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : u < 2 ^ 63
  · rw [show (u + 2 ^ 63) % 2 ^ 64 = 2 ^ 63 + u by omega, hb u h i, Bool.xor_comm]
  · obtain ⟨v, rfl⟩ : ∃ v, u = 2 ^ 63 + v := ⟨u - 2 ^ 63, by omega⟩
    rw [show (2 ^ 63 + v + 2 ^ 63) % 2 ^ 64 = v by omega, hb v (by omega) i]
    cases decide (63 = i) <;> cases v.testBit i <;> rfl

/-- The sign bit flipped (`xor` with `-1 << 63`). -/
theorem xor_top (a : Int) :
    BitVec.ofInt 64 (-9223372036854775808) ^^^ BitVec.ofInt 64 a = BitVec.ofInt 64 (a + 2 ^ 63) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_xor, BitVec.toNat_ofInt, BitVec.toNat_ofInt, BitVec.toNat_ofInt]
  have h0 : 0 ≤ a % 2 ^ 64 := Int.emod_nonneg _ (by decide)
  have h1 : a % 2 ^ 64 < 2 ^ 64 := Int.emod_lt_of_pos _ (by decide)
  obtain ⟨u, hu⟩ := nat_of (a % 2 ^ 64) h0
  have e : (a + 2 ^ 63) % 2 ^ 64 = ((u + 2 ^ 63) % 2 ^ 64 : Nat) := by omega
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at hu e ⊢
  have hc : ((-9223372036854775808 : Int) % 2 ^ 64).toNat = 2 ^ 63 := by decide
  rw [hu, e, Int.toNat_natCast, Int.toNat_natCast, hc, Nat.xor_comm,
    nat_xor_top u (by omega)]

/-! ## The model's words: `Int32`/`UInt32` as `ofInt` of an `Int` -/

theorem ofInt_toNat32 (i : Int) : ((BitVec.ofInt 32 i).toNat : Int) = i % 2 ^ 32 := by
  rw [BitVec.toNat_ofInt]; have : 0 ≤ i % 2 ^ 32 := Int.emod_nonneg _ (by decide); omega

theorem bv32_eq (a b : Int) : BitVec.ofInt 32 a = BitVec.ofInt 32 b ↔ a % 2 ^ 32 = b % 2 ^ 32 := by
  rw [← BitVec.toNat_inj]
  have := ofInt_toNat32 a; have := ofInt_toNat32 b
  omega

theorem u32_bv (a : Int) : (UInt32.ofInt a).toBitVec = BitVec.ofInt 32 a := by
  apply BitVec.eq_of_toNat_eq
  have h0 : 0 ≤ a % 2 ^ 32 := Int.emod_nonneg _ (by decide)
  have h1 : a % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  simp only [UInt32.ofInt, UInt32.toNat_toBitVec, UInt32.toNat_ofNat', BitVec.toNat_ofInt]
  omega

theorem i32_lit (n : Nat) : (no_index (OfNat.ofNat n) : Int32) = Int32.ofInt (n : Int) := by
  rw [Int32.ofInt_eq_ofNat]; rfl
theorem u32_lit (n : Nat) : (no_index (OfNat.ofNat n) : UInt32) = UInt32.ofInt (n : Int) := by
  apply UInt32.toBitVec_inj.1
  rw [u32_bv]; simp
theorem i32_add (a b : Int) : Int32.ofInt a + Int32.ofInt b = Int32.ofInt (a + b) := by
  apply Int32.toBitVec_inj.1; simp
theorem i32_sub (a b : Int) : Int32.ofInt a - Int32.ofInt b = Int32.ofInt (a - b) := by
  apply Int32.toBitVec_inj.1; simp [Int.sub_eq_add_neg, BitVec.sub_eq_add_neg]
theorem i32_neg (a : Int) : -Int32.ofInt a = Int32.ofInt (-a) := by
  apply Int32.toBitVec_inj.1; simp
theorem u32_sub (a b : Int) : UInt32.ofInt a - UInt32.ofInt b = UInt32.ofInt (a - b) := by
  apply UInt32.toBitVec_inj.1; simp only [UInt32.toBitVec_sub, u32_bv]
  simp [Int.sub_eq_add_neg, BitVec.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg]
theorem i32_toU (a : Int) : (Int32.ofInt a).toUInt32 = UInt32.ofInt a := by
  apply UInt32.toBitVec_inj.1; simp [u32_bv]
theorem u32_toI (a : Int) : (UInt32.ofInt a).toInt32 = Int32.ofInt a := by
  apply Int32.toBitVec_inj.1; simp [u32_bv]

/-- `Int32` order on the lens: the words' signed values. -/
theorem i32_lt (a b : Int) : (Int32.ofInt a < Int32.ofInt b) ↔ a.bmod (2 ^ 32) < b.bmod (2 ^ 32) := by
  rw [Int32.lt_iff_toInt_lt, Int32.toInt_ofInt, Int32.toInt_ofInt]
theorem i32_le (a b : Int) : (Int32.ofInt a ≤ Int32.ofInt b) ↔ a.bmod (2 ^ 32) ≤ b.bmod (2 ^ 32) := by
  rw [Int32.le_iff_toInt_le, Int32.toInt_ofInt, Int32.toInt_ofInt]
theorem i32_beq (a b : Int) : (Int32.ofInt a == Int32.ofInt b) = decide (a % 2 ^ 32 = b % 2 ^ 32) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← bv32_eq, ← Int32.toBitVec_ofInt,
    ← Int32.toBitVec_ofInt, Int32.toBitVec_inj]
theorem u32_beq (a b : Int) : (UInt32.ofInt a == UInt32.ofInt b) = decide (a % 2 ^ 32 = b % 2 ^ 32) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← bv32_eq, ← u32_bv, ← u32_bv, UInt32.toBitVec_inj]
theorem i32_bne (a b : Int) : (Int32.ofInt a != Int32.ofInt b) = !decide (a % 2 ^ 32 = b % 2 ^ 32) := by
  rw [bne, i32_beq]
theorem u32_bne (a b : Int) : (UInt32.ofInt a != UInt32.ofInt b) = !decide (a % 2 ^ 32 = b % 2 ^ 32) := by
  rw [bne, u32_beq]

/-- `and` with a low mask of a word. -/
theorem bv32_and_low (a : Int) (k : Nat) (hk : k ≤ 32) :
    BitVec.ofInt 32 a &&& BitVec.ofInt 32 ((2 ^ k - 1 : Nat) : Int) = BitVec.ofInt 32 (a % ((2 ^ k : Nat) : Int)) := by
  have hP : 0 < 2 ^ k := Nat.pow_pos (by decide)
  have hP32 : 2 ^ k ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hk
  have hd : (2 ^ k : Nat) ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 hk
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hm : (BitVec.ofInt 32 ((2 ^ k - 1 : Nat) : Int)).toNat = 2 ^ k - 1 := by
    have := ofInt_toNat32 ((2 ^ k - 1 : Nat) : Int)
    have e : (((2 ^ k - 1 : Nat) : Int)) % 2 ^ 32 = ((2 ^ k - 1 : Nat) : Int) :=
      Int.emod_eq_of_lt (by omega) (by omega)
    omega
  rw [hm, Nat.and_two_pow_sub_one_eq_mod]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (a % ((2 ^ k : Nat) : Int))
  generalize 2 ^ k = P at hP hP32 hd h2 ⊢
  have hdi : ((P : Nat) : Int) ∣ 2 ^ 32 := by exact_mod_cast hd
  have e : (a % 2 ^ 32) % (P : Int) = a % P := Int.emod_emod_of_dvd _ hdi
  have h3 : 0 ≤ a % (P : Int) := Int.emod_nonneg _ (by omega)
  have h4 : a % (P : Int) < P := Int.emod_lt_of_pos _ (by omega)
  have h5 : (a % (P : Int)) % 2 ^ 32 = a % P := Int.emod_eq_of_lt h3 (by omega)
  rw [h5] at h2
  have h6 : (((BitVec.ofInt 32 a).toNat % P : Nat) : Int) = ((BitVec.ofInt 32 a).toNat : Int) % (P : Int) :=
    Int.natCast_emod _ _
  rw [h1, e] at h6
  omega

theorem i32_and_7fffffff (a : Int) : Int32.ofInt a &&& Int32.ofInt 2147483647 = Int32.ofInt (a % 2147483648) := by
  apply Int32.toBitVec_inj.1; simpa using bv32_and_low a 31 (by decide)
theorem i32_and_fffff (a : Int) : Int32.ofInt a &&& Int32.ofInt 1048575 = Int32.ofInt (a % 1048576) := by
  apply Int32.toBitVec_inj.1; simpa using bv32_and_low a 20 (by decide)
theorem i32_and_1 (a : Int) : Int32.ofInt a &&& Int32.ofInt 1 = Int32.ofInt (a % 2) := by
  apply Int32.toBitVec_inj.1; simpa using bv32_and_low a 1 (by decide)
theorem u32_and_7fffffff (a : Int) : UInt32.ofInt a &&& UInt32.ofInt 2147483647 = UInt32.ofInt (a % 2147483648) := by
  apply UInt32.toBitVec_inj.1; simpa [u32_bv] using bv32_and_low a 31 (by decide)

/-- A word's bits by `toNat` of its `ofInt` (the masks below). -/
theorem u32_ext (a b : Int) (h : a % 2 ^ 32 = b % 2 ^ 32) : UInt32.ofInt a = UInt32.ofInt b := by
  apply UInt32.toBitVec_inj.1; rw [u32_bv, u32_bv, bv32_eq]; exact h
theorem i32_ext (a b : Int) (h : a % 2 ^ 32 = b % 2 ^ 32) : Int32.ofInt a = Int32.ofInt b := by
  apply Int32.toBitVec_inj.1; rw [Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, bv32_eq]; exact h

theorem nat_and_800fffff (u : Nat) : u &&& 2148532223 = u / 2 ^ 31 % 2 * 2 ^ 31 + u % 2 ^ 20 := by
  rw [show (2148532223 : Nat) = (2 ^ 1 - 1) * 2 ^ 31 ||| (2 ^ 20 - 1) * 2 ^ 0 by decide, Nat.and_or_distrib_left,
    FmodLens.land_field, FmodLens.land_field, SfLens.or_add _ _ _ (by omega)]
  omega

theorem u32_and_800fffff (a : Int) :
    UInt32.ofInt a &&& UInt32.ofInt 2148532223 = UInt32.ofInt (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_and, u32_bv, u32_bv, u32_bv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 32 2148532223).toNat = 2148532223 by decide, nat_and_800fffff]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20)).toNat = v at h2 ⊢
  omega

theorem u32_and_80000000 (a : Int) :
    UInt32.ofInt a &&& UInt32.ofInt 2147483648 = UInt32.ofInt (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_and, u32_bv, u32_bv, u32_bv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 32 2147483648).toNat = (2 ^ 1 - 1) * 2 ^ 31 by decide,
    FmodLens.land_field]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (a % 2 ^ 32 / 2 ^ 31 * 2 ^ 31)).toNat = v at h2 ⊢
  omega

theorem i32_and_7ff00000 (a : Int) :
    Int32.ofInt a &&& Int32.ofInt 2146435072 = Int32.ofInt (a % 2 ^ 32 / 2 ^ 20 % 2048 * 2 ^ 20) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_and, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 32 2146435072).toNat = (2 ^ 11 - 1) * 2 ^ 20 by decide,
    FmodLens.land_field]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (a % 2 ^ 32 / 2 ^ 20 % 2048 * 2 ^ 20)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (a % 2 ^ 32 / 2 ^ 20 % 2048 * 2 ^ 20)).toNat = v at h2 ⊢
  omega

/-- The machine's `and` with the sign-extended `0x800fffff` of an unsigned word. -/
theorem and_800fffff64 (a : Int) (h0 : 0 ≤ a) (h1 : a < 2 ^ 32) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 (-2146435073) = BitVec.ofInt 64 (a / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 (-2146435073)).toNat =
    (2 ^ 33 - 1) * 2 ^ 31 ||| (2 ^ 20 - 1) * 2 ^ 0 by decide, Nat.and_or_distrib_left,
    FmodLens.land_field, FmodLens.land_field, SfLens.or_add _ _ _ (by omega)]
  have e1 := ofInt_toNat a
  have e2 := ofInt_toNat (a / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20)
  generalize (BitVec.ofInt 64 a).toNat = u at e1 ⊢
  generalize (BitVec.ofInt 64 (a / 2 ^ 31 * 2 ^ 31 + a % 2 ^ 20)).toNat = v at e2 ⊢
  omega

/-- `or` of the sign-and-low-fraction word with an exponent field (`s_scalbn.c:101`). -/
theorem u32_or_slk (S L K : Int) (hS : 0 ≤ S) (hS1 : S < 2 ^ 32) (hS2 : S % 2 ^ 31 = 0) (hL0 : 0 ≤ L)
    (hL : L < 2 ^ 20) (hK0 : 0 ≤ K) (hK : K < 2 ^ 11) :
    UInt32.ofInt (S + L) ||| UInt32.ofInt (K * 1048576) = UInt32.ofInt (S + K * 1048576 + L) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_or, u32_bv, u32_bv, u32_bv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  have h1 := ofInt_toNat32 (S + L); have h2 := ofInt_toNat32 (K * 1048576)
  have h3 := ofInt_toNat32 (S + K * 1048576 + L)
  generalize (BitVec.ofInt 32 (S + L)).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (K * 1048576)).toNat = v at h2 ⊢
  generalize (BitVec.ofInt 32 (S + K * 1048576 + L)).toNat = w at h3 ⊢
  obtain ⟨σ, hσ⟩ : ∃ σ, u = σ * 2 ^ 31 + (u % 2 ^ 20) := ⟨u / 2 ^ 31, by omega⟩
  obtain ⟨κ, hκ⟩ : ∃ κ, v = κ * 2 ^ 20 := ⟨v / 2 ^ 20, by omega⟩
  generalize hl : u % 2 ^ 20 = l at hσ
  have hl2 : l < 2 ^ 20 := by omega
  have hk : κ < 2 ^ 11 := by omega
  have e1 : u = σ * 2 ^ 31 ||| l := by rw [SfLens.or_add _ _ _ (by omega)]; exact hσ
  have e2 : l ||| κ * 2 ^ 20 = κ * 2 ^ 20 + l := by rw [Nat.or_comm, SfLens.or_add _ _ _ hl2]
  have e3 : σ * 2 ^ 31 ||| (κ * 2 ^ 20 + l) = σ * 2 ^ 31 + (κ * 2 ^ 20 + l) := SfLens.or_add _ _ _ (by omega)
  rw [hκ, e1, Nat.or_assoc, e2, e3]
  omega


/-- `or` of a 31-bit magnitude and a sign word (`copysign`). -/
theorem u32_or_31 (a b : Int) (ha0 : 0 ≤ a) (ha : a < 2 ^ 31) (hb0 : 0 ≤ b) (hb1 : b < 2 ^ 32)
    (hb : b % 2 ^ 31 = 0) : UInt32.ofInt a ||| UInt32.ofInt b = UInt32.ofInt (a + b) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_or, u32_bv, u32_bv, u32_bv]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  have h1 := ofInt_toNat32 a; have h2 := ofInt_toNat32 b; have h3 := ofInt_toNat32 (a + b)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 b).toNat = v at h2 ⊢
  generalize (BitVec.ofInt 32 (a + b)).toNat = w at h3 ⊢
  obtain ⟨σ, hσ⟩ : ∃ σ, v = σ * 2 ^ 31 := ⟨v / 2 ^ 31, by omega⟩
  rw [hσ, Nat.or_comm, SfLens.or_add _ _ _ (by omega)]
  omega

/-- `or` of words with disjoint bits: the sum (the high part a multiple of
`2^20`, the low part below it: `j | 0x3ff00000`, `(n & 0xfffff) | 0x100000`). -/
theorem i32_or_k20 (a b : Int) (ha : a % 1048576 = 0) (hb0 : 0 ≤ b)
    (hb : b < 1048576) : Int32.ofInt a ||| Int32.ofInt b = Int32.ofInt (a + b) := by
  apply Int32.toBitVec_inj.1
  simp only [Int32.toBitVec_or, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  have h1 := ofInt_toNat32 a; have h2 := ofInt_toNat32 b; have h3 := ofInt_toNat32 (a + b)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 b).toNat = v at h2 ⊢
  generalize (BitVec.ofInt 32 (a + b)).toNat = w at h3 ⊢
  obtain ⟨q, rfl⟩ : ∃ q, u = q * 2 ^ 20 := ⟨u / 2 ^ 20, by omega⟩
  rw [SfLens.or_add _ _ _ (by omega)]; omega
theorem i32_or_k20' (a b : Int) (ha : a % 1048576 = 0) (hb0 : 0 ≤ b)
    (hb : b < 1048576) : Int32.ofInt b ||| Int32.ofInt a = Int32.ofInt (a + b) := by
  rw [Int32.or_comm]; exact i32_or_k20 a b ha hb0 hb
theorem i32_or_k29' (a b : Int) (ha : a % 536870912 = 0) (hb0 : 0 ≤ b)
    (hb : b < 536870912) : Int32.ofInt b ||| Int32.ofInt a = Int32.ofInt (a + b) := by
  rw [Int32.or_comm]
  apply Int32.toBitVec_inj.1
  simp only [Int32.toBitVec_or, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or]
  have h1 := ofInt_toNat32 a; have h2 := ofInt_toNat32 b; have h3 := ofInt_toNat32 (a + b)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 b).toNat = v at h2 ⊢
  generalize (BitVec.ofInt 32 (a + b)).toNat = w at h3 ⊢
  obtain ⟨q, rfl⟩ : ∃ q, u = q * 2 ^ 29 := ⟨u / 2 ^ 29, by omega⟩
  rw [SfLens.or_add _ _ _ (by omega)]; omega

/-- `or` with zero tests: both zero. -/
theorem u32_or_beq0 (a b : Int) :
    (UInt32.ofInt a ||| UInt32.ofInt b == UInt32.ofInt 0) = decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← UInt32.toBitVec_inj, UInt32.toBitVec_or, u32_bv, u32_bv,
    u32_bv, ← BitVec.toNat_inj, BitVec.toNat_or, show (BitVec.ofInt 32 0).toNat = 0 by decide,
    Nat.or_eq_zero_iff]
  have := ofInt_toNat32 a; have := ofInt_toNat32 b
  omega
theorem i32_or_beq0 (a b : Int) :
    (Int32.ofInt a ||| Int32.ofInt b == Int32.ofInt 0) = decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← Int32.toBitVec_inj, Int32.toBitVec_or,
    Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt,
    ← BitVec.toNat_inj, BitVec.toNat_or, show (BitVec.ofInt 32 0).toNat = 0 by decide, Nat.or_eq_zero_iff]
  have := ofInt_toNat32 a; have := ofInt_toNat32 b
  omega

/-- A word's value (`n.toInt`). -/
theorem i32_toInt (a : Int) : (Int32.ofInt a).toInt = a.bmod 4294967296 := Int32.toInt_ofInt

theorem u32_or_bne0 (a b : Int) :
    (UInt32.ofInt a ||| UInt32.ofInt b != UInt32.ofInt 0) = !decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  rw [bne, u32_or_beq0]
theorem i32_or_bne0 (a b : Int) :
    (Int32.ofInt a ||| Int32.ofInt b != Int32.ofInt 0) = !decide (a % 2 ^ 32 = 0 ∧ b % 2 ^ 32 = 0) := by
  rw [bne, i32_or_beq0]

theorem bv32_smod (k : Int) (h0 : 0 ≤ k) (h1 : k < 32) : (BitVec.ofInt 32 k).smod 32#32 = BitVec.ofInt 32 k := by
  obtain ⟨n, rfl⟩ := nat_of k h0
  have hn : n < 32 := by omega
  rw [show BitVec.ofInt 32 (n : Int) = BitVec.ofNat 32 n by apply BitVec.eq_of_toNat_eq; simp]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_smod]
  have hm : (BitVec.ofNat 32 n).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [hm, show (32#32 : BitVec 32).msb = false by decide]
  dsimp only
  change ((BitVec.ofNat 32 n) % 32#32).toNat = _
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

theorem div_range32 (b P : Int) (hP : 1 ≤ P) (h1 : -2 ^ 31 ≤ b) (h2 : b < 2 ^ 31) :
    -2 ^ 31 ≤ b / P ∧ b / P < 2 ^ 31 := by
  constructor
  · rw [Int.le_ediv_iff_mul_le (by omega)]
    have := Int.mul_le_mul_of_nonneg_left hP (show (0 : Int) ≤ 2 ^ 31 by decide)
    omega
  · rw [Int.ediv_lt_iff_lt_mul (by omega)]
    have : (2 : Int) ^ 31 ≤ 2 ^ 31 * P := by
      have := Int.mul_le_mul_of_nonneg_left hP (show (0 : Int) ≤ 2 ^ 31 by decide)
      simpa using this
    omega

/-- `~~~` of a word. -/
theorem i32_not (a : Int) : ~~~Int32.ofInt a = Int32.ofInt (-1 - a) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_not, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not]
  have h1 := ofInt_toNat32 a; have h2 := ofInt_toNat32 (-1 - a)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (-1 - a)).toNat = v at h2 ⊢
  have : u < 2 ^ 32 := by have := Int.emod_lt_of_pos a (show (0 : Int) < 2 ^ 32 by decide); omega
  omega

/-- `and` of a word with a high mask `-2^j`. -/
theorem i32_and_negpow_j (a : Int) (j : Nat) (hj : j ≤ 31) :
    Int32.ofInt a &&& Int32.ofInt (-(2 ^ j : Int)) = Int32.ofInt (a - a % 2 ^ j) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_and, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and]
  have hpos : 0 < 2 ^ j := Nat.pow_pos (by decide)
  have hle : 2 ^ j < 2 ^ 32 := Nat.pow_lt_pow_right (by decide) (by omega)
  have hd : ((2 ^ j : Nat) : Int) ∣ 2 ^ 32 := by
    have : (2 ^ j : Nat) ∣ 2 ^ 32 := Nat.pow_dvd_pow 2 (by omega)
    exact_mod_cast this
  have hPn : ((2 : Int) ^ j) = ((2 ^ j : Nat) : Int) := by simp
  rw [hPn]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (-((2 ^ j : Nat) : Int))
  have h3 := ofInt_toNat32 (a - a % ((2 ^ j : Nat) : Int))
  generalize (BitVec.ofInt 32 a).toNat = u at h1 ⊢
  generalize (BitVec.ofInt 32 (-((2 ^ j : Nat) : Int))).toNat = mk at h2 ⊢
  generalize (BitVec.ofInt 32 (a - a % ((2 ^ j : Nat) : Int))).toNat = w at h3 ⊢
  have hmk : mk = 2 ^ 32 - 2 ^ j := by
    generalize 2 ^ j = P at hpos hle h2 ⊢
    omega
  subst hmk
  have hu : u < 2 ^ 32 := by have := Int.emod_lt_of_pos a (by decide : (0:Int) < 2 ^ 32); omega
  have hand : u &&& (2 ^ 32 - 2 ^ j) = u - u % 2 ^ j := by
    have e1 : 2 ^ 32 - 2 ^ j = (2 ^ (32 - j) - 1) * 2 ^ j := by
      rw [Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    rw [e1, FmodLens.land_field]
    have h64 : 2 ^ 32 = 2 ^ (32 - j) * 2 ^ j := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
    have hlt : u / 2 ^ j < 2 ^ (32 - j) := by rw [Nat.div_lt_iff_lt_mul hpos, ← h64]; exact hu
    rw [Nat.mod_eq_of_lt hlt]
    have := Nat.mod_add_div u (2 ^ j)
    rw [Nat.mul_comm] at this
    generalize u / 2 ^ j * 2 ^ j = q at this ⊢
    omega
  rw [hand]
  have e : a % ((2 ^ j : Nat) : Int) = (u : Int) % ((2 ^ j : Nat) : Int) := by
    rw [h1, Int.emod_emod_of_dvd _ hd]
  have hmodu : ((u % 2 ^ j : Nat) : Int) = (u : Int) % ((2 ^ j : Nat) : Int) := Int.natCast_emod _ _
  have hle2 : u % 2 ^ j ≤ u := Nat.mod_le _ _
  generalize u % 2 ^ j = r at hmodu hle2 ⊢
  rw [← hmodu] at e
  generalize ((2 ^ j : Nat) : Int) = P at e h3
  omega

theorem i32_and_np1 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-2) = Int32.ofInt (a - a % 2) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 1 (by decide)
theorem i32_and_np2 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-4) = Int32.ofInt (a - a % 4) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 2 (by decide)
theorem i32_and_np3 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-8) = Int32.ofInt (a - a % 8) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 3 (by decide)
theorem i32_and_np4 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-16) = Int32.ofInt (a - a % 16) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 4 (by decide)
theorem i32_and_np5 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-32) = Int32.ofInt (a - a % 32) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 5 (by decide)
theorem i32_and_np6 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-64) = Int32.ofInt (a - a % 64) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 6 (by decide)
theorem i32_and_np7 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-128) = Int32.ofInt (a - a % 128) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 7 (by decide)
theorem i32_and_np8 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-256) = Int32.ofInt (a - a % 256) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 8 (by decide)
theorem i32_and_np9 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-512) = Int32.ofInt (a - a % 512) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 9 (by decide)
theorem i32_and_np10 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-1024) = Int32.ofInt (a - a % 1024) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 10 (by decide)
theorem i32_and_np11 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-2048) = Int32.ofInt (a - a % 2048) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 11 (by decide)
theorem i32_and_np12 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-4096) = Int32.ofInt (a - a % 4096) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 12 (by decide)
theorem i32_and_np13 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-8192) = Int32.ofInt (a - a % 8192) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 13 (by decide)
theorem i32_and_np14 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-16384) = Int32.ofInt (a - a % 16384) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 14 (by decide)
theorem i32_and_np15 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-32768) = Int32.ofInt (a - a % 32768) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 15 (by decide)
theorem i32_and_np16 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-65536) = Int32.ofInt (a - a % 65536) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 16 (by decide)
theorem i32_and_np17 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-131072) = Int32.ofInt (a - a % 131072) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 17 (by decide)
theorem i32_and_np18 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-262144) = Int32.ofInt (a - a % 262144) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 18 (by decide)
theorem i32_and_np19 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-524288) = Int32.ofInt (a - a % 524288) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 19 (by decide)
theorem i32_and_np20 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-1048576) = Int32.ofInt (a - a % 1048576) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 20 (by decide)
theorem i32_and_np21 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-2097152) = Int32.ofInt (a - a % 2097152) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 21 (by decide)
theorem i32_and_np22 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-4194304) = Int32.ofInt (a - a % 4194304) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 22 (by decide)
theorem i32_and_np23 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-8388608) = Int32.ofInt (a - a % 8388608) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 23 (by decide)
theorem i32_and_np24 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-16777216) = Int32.ofInt (a - a % 16777216) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 24 (by decide)
theorem i32_and_np25 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-33554432) = Int32.ofInt (a - a % 33554432) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 25 (by decide)
theorem i32_and_np26 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-67108864) = Int32.ofInt (a - a % 67108864) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 26 (by decide)
theorem i32_and_np27 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-134217728) = Int32.ofInt (a - a % 134217728) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 27 (by decide)
theorem i32_and_np28 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-268435456) = Int32.ofInt (a - a % 268435456) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 28 (by decide)
theorem i32_and_np29 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-536870912) = Int32.ofInt (a - a % 536870912) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 29 (by decide)
theorem i32_and_np30 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-1073741824) = Int32.ofInt (a - a % 1073741824) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 30 (by decide)
theorem i32_and_np31 (a : Int) : Int32.ofInt a &&& Int32.ofInt (-2147483648) = Int32.ofInt (a - a % 2147483648) := by
  simpa only [Int.reducePow] using i32_and_negpow_j a 31 (by decide)

/-- Shifts by a word in range: `>>>` arithmetic on `Int32`, logical on `UInt32`. -/
theorem i32_sra (a k : Int) (h0 : 0 ≤ k) (h1 : k < 32) :
    Int32.ofInt a >>> Int32.ofInt k = Int32.ofInt (a.bmod (2 ^ 32) / 2 ^ k.toNat) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_shiftRight, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt,
    show (32 : BitVec 32) = 32#32 from rfl, bv32_smod k h0 h1, BitVec.sshiftRight_eq']
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_ofInt, BitVec.toInt_ofInt, Int.shiftRight_eq_div_pow]
  obtain ⟨n, rfl⟩ := nat_of k h0
  have hk : (BitVec.ofInt 32 (n : Int)).toNat = n := by simp; omega
  rw [hk, Int.toNat_natCast]
  have hb1 := Int.le_bmod (x := a) (m := 2 ^ 32) (by decide)
  have hb2 := Int.bmod_lt (x := a) (m := 2 ^ 32) (by decide)
  have hp : (1 : Int) ≤ 2 ^ n := by
    have : (1 : Nat) ≤ 2 ^ n := Nat.one_le_two_pow
    exact_mod_cast this
  have q := div_range32 (a.bmod (2 ^ 32)) (2 ^ n) hp (by simpa using hb1) (by simpa using hb2)
  simp only [Int.natCast_pow, Int.cast_ofNat_Int]
  rw [bmod_small _ q.1 q.2]
theorem bv32_umod (k : Int) (h0 : 0 ≤ k) (h1 : k < 32) : BitVec.ofInt 32 k % 32#32 = BitVec.ofInt 32 k := by
  obtain ⟨n, rfl⟩ := nat_of k h0
  rw [show BitVec.ofInt 32 (n : Int) = BitVec.ofNat 32 n by apply BitVec.eq_of_toNat_eq; simp]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simp only [Nat.reducePow, Nat.reduceMod]
  omega

theorem bv32_toNat_k (k : Int) (h0 : 0 ≤ k) (h1 : k < 32) : (BitVec.ofInt 32 k).toNat = k.toNat := by
  obtain ⟨n, rfl⟩ := nat_of k h0
  simp; omega

theorem bv32_shl (a : Int) (n : Nat) : BitVec.ofInt 32 a <<< n = BitVec.ofInt 32 (a * 2 ^ n) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, FmodLens.twoPow_ofInt, ← BitVec.ofInt_mul]

theorem bv32_srl (a : Int) (n : Nat) : BitVec.ofInt 32 a >>> n = BitVec.ofInt 32 (a % 2 ^ 32 / 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have h1 := ofInt_toNat32 a
  have h2 := ofInt_toNat32 (a % 2 ^ 32 / 2 ^ n)
  generalize (BitVec.ofInt 32 (a % 2 ^ 32 / 2 ^ n)).toNat = R at h2 ⊢
  rw [← h1] at h2
  have hl : a % 2 ^ 32 < 2 ^ 32 := Int.emod_lt_of_pos _ (by decide)
  generalize (BitVec.ofInt 32 a).toNat = u at h1 h2 ⊢
  have hP : ((2 : Int) ^ n) = ((2 ^ n : Nat) : Int) := by simp
  rw [hP, ← Int.natCast_ediv] at h2
  have hq : u / 2 ^ n ≤ u := Nat.div_le_self _ _
  generalize u / 2 ^ n = q at h2 hq ⊢
  omega

theorem i32_shl (a k : Int) (h0 : 0 ≤ k) (h1 : k < 32) :
    Int32.ofInt a <<< Int32.ofInt k = Int32.ofInt (a * 2 ^ k.toNat) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_shiftLeft, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt, Int32.toBitVec_ofInt,
    show (32 : BitVec 32) = 32#32 from rfl, bv32_smod k h0 h1, BitVec.shiftLeft_eq', bv32_toNat_k k h0 h1,
    bv32_shl]
theorem u32_srl (a k : Int) (h0 : 0 ≤ k) (h1 : k < 32) :
    UInt32.ofInt a >>> UInt32.ofInt k = UInt32.ofInt (a % 2 ^ 32 / 2 ^ k.toNat) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_shiftRight, u32_bv, u32_bv, u32_bv, show (32 : BitVec 32) = 32#32 from rfl,
    bv32_umod k h0 h1, BitVec.ushiftRight_eq', bv32_toNat_k k h0 h1, bv32_srl]
theorem u32_shl (a k : Int) (h0 : 0 ≤ k) (h1 : k < 32) :
    UInt32.ofInt a <<< UInt32.ofInt k = UInt32.ofInt (a * 2 ^ k.toNat) := by
  apply UInt32.toBitVec_inj.1
  rw [UInt32.toBitVec_shiftLeft, u32_bv, u32_bv, u32_bv, show (32 : BitVec 32) = 32#32 from rfl,
    bv32_umod k h0 h1, BitVec.shiftLeft_eq', bv32_toNat_k k h0 h1, bv32_shl]

/-! ## The model's words of a datum, and its packing -/

theorem hiW_l (d : Float.Model) : Pow.hiW d = Int32.ofInt (W d / 2 ^ 32) := by
  apply Int32.toBitVec_inj.1
  rw [Int32.toBitVec_ofInt]
  unfold Pow.hiW W
  generalize d.toBits = b
  apply BitVec.eq_of_toNat_eq
  simp only [UInt32.toBitVec_toInt32, UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.ushiftRight_eq',
    BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod]
  have h := ofInt_toNat32 (b.toBitVec.toInt / 2 ^ 32)
  have hb := b.toBitVec.isLt
  generalize (BitVec.ofInt 32 (b.toBitVec.toInt / 2 ^ 32)).toNat = R at h ⊢
  rw [BitVec.toInt_eq_toNat_cond] at h
  split at h <;> omega

theorem loW_l (d : Float.Model) : Pow.loW d = UInt32.ofInt (W d) := by
  apply UInt32.toBitVec_inj.1
  rw [u32_bv]
  unfold Pow.loW W
  generalize d.toBits = b
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toBitVec_toUInt32, BitVec.toNat_setWidth]
  have h := ofInt_toNat32 b.toBitVec.toInt
  have hb := b.toBitVec.isLt
  generalize (BitVec.ofInt 32 b.toBitVec.toInt).toNat = R at h ⊢
  rw [BitVec.toInt_eq_toNat_cond] at h
  split at h <;> omega

theorem insertWords_l0 (h l : Int) :
    Pow.insertWords (UInt32.ofInt h) (UInt32.ofInt l) =
      F64.toModel (BitVec.ofInt 64 (h % 2 ^ 32 * 2 ^ 32 + l % 2 ^ 32)) := by
  unfold Pow.insertWords F64.toModel
  congr 1
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_toNat_eq
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64, u32_bv,
    UInt64.toBitVec_ofNat, BitVec.ofNat_eq_ofNat, BitVec.reduceMod, BitVec.shiftLeft_eq',
    UInt64.toBitVec_ofBitVec, BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.reducePow, Nat.reduceMod, Nat.shiftLeft_eq]
  have h1 := ofInt_toNat32 h; have h2 := ofInt_toNat32 l
  have h3 := ofInt_toNat (h % 2 ^ 32 * 2 ^ 32 + l % 2 ^ 32)
  generalize (BitVec.ofInt 32 h).toNat = H at h1 ⊢
  generalize (BitVec.ofInt 32 l).toNat = L at h2 ⊢
  generalize (BitVec.ofInt 64 (h % 2 ^ 32 * 2 ^ 32 + l % 2 ^ 32)).toNat = R at h3 ⊢
  have hH : H < 4294967296 := by omega
  have hL : L < 4294967296 := by omega
  rw [Nat.mod_eq_of_lt (by omega : H < 18446744073709551616), Nat.mod_eq_of_lt (by omega : L < 18446744073709551616),
    Nat.mod_eq_of_lt (by omega : H * 4294967296 < 18446744073709551616)]
  rw [show (4294967296 : Nat) = 2 ^ 32 by rfl, SfLens.or_add _ _ _ (by omega)]
  omega

/-- A word from its halves: the high half unreduced (the machine's `slli 32`
form; `ofInt 64` drops its multiples of `2^64`). -/
theorem insertWords_l (h l : Int) :
    Pow.insertWords (UInt32.ofInt h) (UInt32.ofInt l) =
      F64.toModel (BitVec.ofInt 64 (h * 2 ^ 32 + l % 2 ^ 32)) := by
  rw [insertWords_l0]
  apply toModel_congr
  omega

/-- The low half of a word moved up and back (`slli 32; srli 32`). -/
theorem mul32_lo (a : Int) : a * 4294967296 % 18446744073709551616 / 4294967296 = a % 4294967296 := by
  omega

theorem ofBits_lit (n : Nat) :
    Float.Model.ofBits (no_index (OfNat.ofNat n)) = F64.toModel (BitVec.ofInt 64 (n : Int)) := by
  unfold F64.toModel
  congr 1

theorem nat_xor_1 (v : Nat) : v ^^^ 1 = v / 2 * 2 + (1 - v % 2) := by
  have a1 : (v ^^^ 1) / 2 = v / 2 := by rw [Nat.xor_div_two]; simp
  have a2 : (v ^^^ 1) % 2 = 1 - v % 2 := by
    have := Nat.xor_mod_two_eq_one (a := v) (b := 1)
    have h2 := Nat.mod_two_eq_zero_or_one (v ^^^ 1)
    have h3 := Nat.mod_two_eq_zero_or_one v
    simp only [Nat.one_mod, iff_true] at this
    omega
  have := Nat.div_add_mod (v ^^^ 1) 2
  rw [a1, a2] at this
  omega

/-- A literal with the sign bit clear. -/
theorem ofBits_lit_pos (n : Nat) (_h : n < 2 ^ 63) :
    Float.Model.ofBits (no_index (OfNat.ofNat n)) = F64.toModel (BitVec.ofInt 64 (n : Int)) := ofBits_lit n

/-- A literal with the sign bit set: the machine's (`lit_neg`) signed form. -/
theorem ofBits_lit_neg (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    Float.Model.ofBits (no_index (OfNat.ofNat n)) = F64.toModel (BitVec.ofInt 64 ((n : Int) - 18446744073709551616)) := by
  rw [ofBits_lit]
  congr 1
  apply bv64_ext
  omega

theorem nat_xor_51 (u : Nat) : u ^^^ 2 ^ 51 = u / 2 ^ 52 * 2 ^ 52 + (1 - u / 2 ^ 51 % 2) * 2 ^ 51 + u % 2 ^ 51 := by
  have e1 : (u ^^^ 2 ^ 51) % 2 ^ 51 = u % 2 ^ 51 := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  have e2 : (u ^^^ 2 ^ 51) / 2 ^ 51 = u / 2 ^ 51 ^^^ 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (by decide)]
  have := Nat.div_add_mod (u ^^^ 2 ^ 51) (2 ^ 51)
  rw [e1, e2, nat_xor_1] at this
  omega

/-- A model datum's bits are canonical: a NaN pattern is `0x7ff8000000000000`. -/
theorem bits_canon (d : Float.Model) (h1 : d.toBits.toNat / 2 ^ 52 % 2048 = 2047)
    (h2 : d.toBits.toNat % 2 ^ 52 ≠ 0) : d.toBits.toNat = 0x7ff8000000000000 := by
  have hn := d.valid.eq_packedNaN ((F64.exp_eq_ones _).2 h1) (fun e => h2 ((F64.man_eq_zero _).1 e))
  have := congrArg BitVec.toNat hn
  have hc : (Float.Model.UnpackedFloat.packedNaN Float.Model.Format.binary64).toNat = 0x7ff8000000000000 := by decide
  rw [hc] at this
  simpa using this

/-- The model has no signalling NaN. -/
theorem issignaling_false (d : Float.Model) : Pow.issignaling d = false := by
  unfold Pow.issignaling
  rw [decide_eq_false_iff_not, gt_iff_lt, UInt64.lt_iff_toNat_lt]
  simp only [UInt64.toNat_mul, UInt64.toNat_xor, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceMul]
  rw [nat_xor_51]
  have hb := d.toBits.toNat_lt
  by_cases hc : d.toBits.toNat / 2 ^ 52 % 2048 = 2047 ∧ d.toBits.toNat % 2 ^ 52 ≠ 0
  · rw [bits_canon d hc.1 hc.2]; decide
  · simp only [Nat.reducePow] at hc hb ⊢
    omega

/-- The machine's `SET_LOW_WORD(d, 0)` (`srli 32; slli 32`) read as an
operand: the model's `setLow d 0`, kept folded on both sides. -/
theorem setLow0_l (d : Float.Model) :
    F64.toModel (BitVec.ofInt 64 (W d % 18446744073709551616 / 4294967296 * 4294967296)) =
      Pow.setLow d (UInt32.ofInt 0) := by
  unfold Pow.setLow
  rw [hiW_l, i32_toU, insertWords_l]
  apply toModel_congr
  have := W_lo d; have := W_hi d
  simp only [Int.reducePow, Int.cast_ofNat_Int, Int.natCast_zero, Int.zero_emod, Int.add_zero]
  omega

attribute [pw_lens] Lua.Vm.Fn.PowLens.mul32_lo
/-- `setLow d 0` as the machine's `and` with the high mask. -/
theorem setLow0_l' (d : Float.Model) :
    F64.toModel (BitVec.ofInt 64 (W d - W d % 4294967296)) = Pow.setLow d (UInt32.ofInt 0) := by
  rw [← setLow0_l]
  apply toModel_congr
  have := W_lo d; have := W_hi d
  omega

attribute [pw_lens] setLow0_l' Lua.Vm.Fn.PowLens.and_np32' setLow0_l Lua.Vm.Fn.PowLens.ofInt_bmod64 Lua.Vm.Fn.PowLens.and_np1 Lua.Vm.Fn.PowLens.and_np2 Lua.Vm.Fn.PowLens.and_np3 Lua.Vm.Fn.PowLens.and_np4 Lua.Vm.Fn.PowLens.and_np5 Lua.Vm.Fn.PowLens.and_np6 Lua.Vm.Fn.PowLens.and_np7 Lua.Vm.Fn.PowLens.and_np8 Lua.Vm.Fn.PowLens.and_np9 Lua.Vm.Fn.PowLens.and_np10 Lua.Vm.Fn.PowLens.and_np11 Lua.Vm.Fn.PowLens.and_np12 Lua.Vm.Fn.PowLens.and_np13 Lua.Vm.Fn.PowLens.and_np14 Lua.Vm.Fn.PowLens.and_np15 Lua.Vm.Fn.PowLens.and_np16 Lua.Vm.Fn.PowLens.and_np17 Lua.Vm.Fn.PowLens.and_np18 Lua.Vm.Fn.PowLens.and_np19 Lua.Vm.Fn.PowLens.and_np20 Lua.Vm.Fn.PowLens.and_np21 Lua.Vm.Fn.PowLens.and_np22 Lua.Vm.Fn.PowLens.and_np23 Lua.Vm.Fn.PowLens.and_np24 Lua.Vm.Fn.PowLens.and_np25 Lua.Vm.Fn.PowLens.and_np26 Lua.Vm.Fn.PowLens.and_np27 Lua.Vm.Fn.PowLens.and_np28 Lua.Vm.Fn.PowLens.and_np29 Lua.Vm.Fn.PowLens.and_np30 Lua.Vm.Fn.PowLens.and_np31 Lua.Vm.Fn.PowLens.and_np32

/-! ## The discharger -/

theorem bmod_facts (z : Int) (m : Nat) (h : 0 < m) :
    z.bmod m % (m : Int) = z % m ∧ -((m : Int) / 2) ≤ z.bmod m ∧ z.bmod m < ((m : Int) + 1) / 2 :=
  ⟨Int.bmod_emod, Int.le_bmod h, Int.bmod_lt h⟩

open Lean Elab Tactic Meta in
/-- The `Int.bmod` and `W` atoms of an expression. -/
partial def lensAtomsGo (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e,
    if (e.isAppOfArity ``Int.bmod 2 || e.isAppOfArity ``Lua.Vm.Fn.PowLens.W 1) && !a.contains e then a.push e
    else a)
  match e with
  | .app f a => lensAtomsGo f; lensAtomsGo a
  | .lam _ t b _ => lensAtomsGo t; lensAtomsGo b
  | .forallE _ t b _ => lensAtomsGo t; lensAtomsGo b
  | .letE _ t v b _ => lensAtomsGo t; lensAtomsGo v; lensAtomsGo b
  | .mdata _ b => lensAtomsGo b
  | _ => pure ()

open Lean Elab Tactic Meta in
/-- The `Int.bmod` and `W` atoms of an expression (each shared subterm once). -/
def lensAtoms (e : Expr) : StateT (Array Expr) MetaM Unit := do
  let acc ← get
  let ((), (_, a)) := (lensAtomsGo e).run ({}, acc)
  set a

open Lean Elab Tactic Meta in
/-- `omega` with the facts of the goal's `bmod` atoms (residue and range) and
`W` atoms (range). -/
elab "pw_omega" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let mut atoms : Array Expr := #[]
  let ((), a0) ← (lensAtoms t).run atoms
  atoms := a0
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if (← isProp d.type) then
      let ((), a1) ← (lensAtoms (← instantiateMVars d.type)).run atoms
      atoms := a1
  for a in atoms do
    let aS ← Term.exprToSyntax a
    if a.isAppOfArity ``Int.bmod 2 then
      let zS ← Term.exprToSyntax (a.getArg! 0)
      let mS ← Term.exprToSyntax (a.getArg! 1)
      evalTactic (← `(tactic| have := Lua.Vm.Fn.PowLens.bmod_facts $zS $mS (by decide)))
    else
      let dS ← Term.exprToSyntax (a.getArg! 0)
      evalTactic (← `(tactic| have := Lua.Vm.Fn.PowLens.W_lo $dS))
      evalTactic (← `(tactic| have := Lua.Vm.Fn.PowLens.W_hi $dS))
    let _ := aS
  evalTactic (← `(tactic| omega))

open Lean Elab Tactic Meta in
/-- `pw_omega` when the goal mentions `Int.bmod` (else fail at once). -/
elab "pw_omega_b" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  unless (t.find? (·.isAppOfArity ``Int.bmod 2)).isSome do throwError "no bmod"
  evalTactic (← `(tactic| pw_omega))

open Lean Elab Tactic Meta in
/-- `pw_omega` when the goal or a hypothesis has a `bmod` (the walk's split
facts keep the machine's `bmod`s). -/
elab "pw_omega_h" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let isB := fun (e : Expr) => (e.find? (·.isAppOfArity ``Int.bmod 2)).isSome
  let mut any := isB t
  if !any then
    for d in ← getLCtx do
      if !d.isImplementationDetail && isB (← instantiateMVars d.type) then any := true
  unless any do throwError "no bmod"
  evalTactic (← `(tactic| pw_omega))

/-- The lenses' discharger: `omega`, then with the atoms' facts, then a
closed `decide`. -/
macro "pw_disch" : tactic => `(tactic| first | omega | pw_omega | (fm_ground; decide))

/-- The machine lens's discharger: a closed side condition by `decide`, else
`omega`. -/
macro "pw_disch_l" : tactic => `(tactic| first | (fm_ground; decide) | omega | pw_omega_b)

/-! ## The normal form -/

-- The machine lens (`fm_nf`'s lemmas with the routine's masks, `not`, the
-- sign flip, `srai`, and the float lens).
attribute [pw_lens] Lua.Vm.Fn.FmodLens.sext64 Lua.Vm.Fn.FmodLens.lo_ofInt Lua.Vm.Fn.FmodLens.lo5_ofInt Lua.Vm.Fn.FmodLens.sub32 Lua.Vm.Fn.FmodLens.add32 Lua.Vm.Fn.FmodLens.sll32 Lua.Vm.Fn.FmodLens.srl32 Lua.Vm.Fn.FmodLens.sra32 Lua.Vm.Fn.FmodLens.add64 Lua.Vm.Fn.FmodLens.sub64 Lua.Vm.Fn.FmodLens.sll64 Lua.Vm.Fn.FmodLens.srl64 Lua.Vm.Fn.FmodLens.toNat_ofInt5 Lua.Vm.Fn.FmodLens.toNat_ofInt32 Lua.Vm.Fn.FmodLens.toInt_ofInt32 Lua.Vm.Fn.FmodLens.ext6_toNat Lua.Vm.Fn.FmodLens.bmod_small Lua.Vm.Fn.FmodLens.bmod_small' BitVec.toInt_ofInt Int.reduceNatCast Int.cast_ofNat_Int Lua.Vm.Fn.FmodLens.lit_pos Lua.Vm.Fn.FmodLens.lit_neg Lua.Vm.Fn.FmodLens.lit_pos' Lua.Vm.Fn.FmodLens.lit_neg' Lua.Vm.Fn.FmodLens.slt_ofInt Lua.Vm.Fn.FmodLens.sge_ofInt Lua.Vm.Fn.FmodLens.ult_ofInt Lua.Vm.Fn.FmodLens.uge_ofInt Lua.Vm.Fn.FmodLens.beq_ofInt Lua.Vm.Fn.FmodLens.bne_ofInt Lua.Vm.Fn.FmodLens.or_beq0 Lua.Vm.Fn.FmodLens.or_bne0 Lua.Vm.Fn.FmodLens.or_zero_ofInt Lua.Vm.Fn.FmodLens.zero_or_ofInt Lua.Vm.Fn.FmodLens.or_k20 Lua.Vm.Fn.FmodLens.or_k31 Lua.Vm.Fn.FmodLens.or_k32 Lua.Vm.Fn.FmodLens.or_sx Lua.Vm.Fn.FmodLens.or_k20' Lua.Vm.Fn.FmodLens.and_2047 Lua.Vm.Fn.FmodLens.and_fffff Lua.Vm.Fn.FmodLens.and_7fffffff Lua.Vm.Fn.FmodLens.and_7ff00000 Lua.Vm.Fn.FmodLens.and_hi31 Lua.Vm.Fn.FmodLens.or_shr' Lua.Vm.Fn.FmodLens.or_shr0 Lua.Vm.Fn.FmodLens.or_lo_beq0 Lua.Vm.Fn.FmodLens.or_lo_toInt0 Lua.Vm.Fn.FmodLens.add_ofInt0 ite_eq_left ite_eq_right Int.shiftRight_eq_div_pow BitVec.reduceToInt BitVec.reduceToNat BitVec.reduceAppend BitVec.reduceSignExtend BitVec.reduceAdd BitVec.reduceXOr BitVec.reduceAnd BitVec.reduceOr BitVec.reduceNot BitVec.reduceExtractLsb Int.reducePow Int.reduceMul Int.reduceAdd Int.reduceSub Int.reduceNeg Int.reduceMod Int.reduceDiv Int.reduceToNat Nat.reducePow Nat.reduceMod Nat.reduceAdd Nat.reduceSub Nat.reduceMul Int.add_zero Int.zero_add Int.mul_one Int.sub_zero decide_eq_true_eq decide_eq_false_iff_not Bool.not_eq_true' Bool.not_eq_true Bool.not_true Bool.not_false Bool.not_not decide_true decide_false Bool.false_eq_true Bool.true_eq_false ite_true ite_false Lua.Vm.Fn.PowLens.and_7fffffff' Lua.Vm.Fn.PowLens.and_fffff' Lua.Vm.Fn.PowLens.and_2047' Lua.Vm.Fn.PowLens.and_1' Lua.Vm.Fn.PowLens.xor_m1 Lua.Vm.Fn.PowLens.xor_top Lua.Vm.Fn.PowLens.and_800fffff64 Lua.Vm.Fn.Ieee754Sqrt.sra64 Lua.Vm.Fn.PowLens.add_l Lua.Vm.Fn.PowLens.sub_l Lua.Vm.Fn.PowLens.mul_l Lua.Vm.Fn.PowLens.div_l Lua.Vm.Fn.PowLens.sqrt_l Lua.Vm.Fn.PowLens.model_W Lua.Vm.Fn.PowLens.or_k32' Lua.Vm.Fn.PowLens.or_k29' Lua.Vm.Fn.PowLens.or_np30 Int.add_neg_eq_sub Int.reduceBmod Lua.Vm.Sim.sdData_id Lua.Vm.Sim.bytesT8_writeMap8

-- The model lens.
attribute [pw_mlens] Lua.Vm.Fn.PowLens.hiW_l Lua.Vm.Fn.PowLens.loW_l Lua.Num.Pow.setHigh Lua.Vm.Fn.PowLens.insertWords_l Lua.Vm.Fn.PowLens.issignaling_false Lua.Num.Pow.K Lua.Vm.Fn.PowLens.ofBits_lit_neg Lua.Vm.Fn.PowLens.ofBits_lit_pos Lua.Num.Pow.one Lua.Num.Pow.zero Lua.Num.Pow.two Lua.Vm.Fn.PowLens.i32_lit Lua.Vm.Fn.PowLens.u32_lit Lua.Vm.Fn.PowLens.i32_add Lua.Vm.Fn.PowLens.i32_sub Lua.Vm.Fn.PowLens.i32_neg Lua.Vm.Fn.PowLens.u32_sub Lua.Vm.Fn.PowLens.i32_toU Lua.Vm.Fn.PowLens.u32_toI Lua.Vm.Fn.PowLens.i32_lt Lua.Vm.Fn.PowLens.i32_le Lua.Vm.Fn.PowLens.i32_beq Lua.Vm.Fn.PowLens.u32_beq Lua.Vm.Fn.PowLens.i32_bne Lua.Vm.Fn.PowLens.u32_bne Lua.Vm.Fn.PowLens.i32_and_7fffffff Lua.Vm.Fn.PowLens.i32_and_fffff Lua.Vm.Fn.PowLens.i32_and_1 Lua.Vm.Fn.PowLens.u32_and_7fffffff Lua.Vm.Fn.PowLens.u32_or_beq0 Lua.Vm.Fn.PowLens.i32_or_beq0 Lua.Vm.Fn.PowLens.i32_or_k20 Lua.Vm.Fn.PowLens.i32_or_k20' Lua.Vm.Fn.PowLens.i32_or_k29' Lua.Vm.Fn.PowLens.i32_sra Lua.Vm.Fn.PowLens.i32_shl Lua.Vm.Fn.PowLens.u32_srl Lua.Vm.Fn.PowLens.u32_shl Lua.Vm.Fn.PowLens.u32_and_800fffff Lua.Vm.Fn.PowLens.u32_and_80000000 Lua.Vm.Fn.PowLens.i32_and_7ff00000 Lua.Vm.Fn.PowLens.u32_or_slk Lua.Vm.Fn.PowLens.u32_or_31 Lua.Num.Pow.u Lua.Num.Pow.copysign Lua.Vm.Fn.PowLens.W_ofInt Lua.Vm.Fn.FmodLens.bmod_small' gt_iff_lt ge_iff_le  ite_true ite_false Int.reduceMod Int.reducePow Int.reduceDiv Int.reduceNeg Int.reduceAdd Int.reduceSub Int.reduceMul Int.reduceToNat Int.reduceBmod Nat.reducePow Bool.and_eq_true Bool.or_eq_true decide_eq_true_eq Bool.not_eq_true' Bool.not_eq_eq_eq_not Bool.not_true Bool.not_false Int.cast_ofNat_Int Bool.and_true Bool.true_and Bool.or_false Bool.false_or decide_eq_false_iff_not Bool.false_eq_true Bool.true_eq_false decide_true decide_false Lua.Vm.Fn.PowLens.model_W Lua.Vm.Fn.PowLens.mneg_l Lua.Num.Pow.L1 Lua.Num.Pow.L2 Lua.Num.Pow.L3 Lua.Num.Pow.L4 Lua.Num.Pow.L5 Lua.Num.Pow.L6 Lua.Num.Pow.P1 Lua.Num.Pow.P2 Lua.Num.Pow.P3 Lua.Num.Pow.P4 Lua.Num.Pow.P5 Lua.Num.Pow.lg2 Lua.Num.Pow.lg2_h Lua.Num.Pow.lg2_l Lua.Num.Pow.ovt Lua.Num.Pow.cp Lua.Num.Pow.cp_h Lua.Num.Pow.cp_l Lua.Num.Pow.ivln2 Lua.Num.Pow.ivln2_h Lua.Num.Pow.ivln2_l Lua.Num.Pow.bp Lua.Num.Pow.dp_h Lua.Num.Pow.dp_l Lua.Num.Pow.half Lua.Num.Pow.third Lua.Num.Pow.quarter Lua.Num.Pow.three Lua.Num.Pow.two53 Lua.Vm.Fn.PowLens.madd_neglit Lua.Vm.Fn.PowLens.madd_neglit' Lua.Vm.Fn.PowLens.i32_not Lua.Vm.Fn.PowLens.i32_and_np1 Lua.Vm.Fn.PowLens.i32_and_np2 Lua.Vm.Fn.PowLens.i32_and_np3 Lua.Vm.Fn.PowLens.i32_and_np4 Lua.Vm.Fn.PowLens.i32_and_np5 Lua.Vm.Fn.PowLens.i32_and_np6 Lua.Vm.Fn.PowLens.i32_and_np7 Lua.Vm.Fn.PowLens.i32_and_np8 Lua.Vm.Fn.PowLens.i32_and_np9 Lua.Vm.Fn.PowLens.i32_and_np10 Lua.Vm.Fn.PowLens.i32_and_np11 Lua.Vm.Fn.PowLens.i32_and_np12 Lua.Vm.Fn.PowLens.i32_and_np13 Lua.Vm.Fn.PowLens.i32_and_np14 Lua.Vm.Fn.PowLens.i32_and_np15 Lua.Vm.Fn.PowLens.i32_and_np16 Lua.Vm.Fn.PowLens.i32_and_np17 Lua.Vm.Fn.PowLens.i32_and_np18 Lua.Vm.Fn.PowLens.i32_and_np19 Lua.Vm.Fn.PowLens.i32_and_np20 Lua.Vm.Fn.PowLens.i32_and_np21 Lua.Vm.Fn.PowLens.i32_and_np22 Lua.Vm.Fn.PowLens.i32_and_np23 Lua.Vm.Fn.PowLens.i32_and_np24 Lua.Vm.Fn.PowLens.i32_and_np25 Lua.Vm.Fn.PowLens.i32_and_np26 Lua.Vm.Fn.PowLens.i32_and_np27 Lua.Vm.Fn.PowLens.i32_and_np28 Lua.Vm.Fn.PowLens.i32_and_np29 Lua.Vm.Fn.PowLens.i32_and_np30 Lua.Vm.Fn.PowLens.i32_and_np31 Lua.Vm.Fn.PowLens.u32_or_bne0 Lua.Vm.Fn.PowLens.i32_or_bne0 Lua.Vm.Fn.PowLens.i32_toInt Int.add_zero Int.zero_add Int.sub_zero

/-- **`pw_nf`**: the machine's normal form. -/
syntax "pw_nf" (Lean.Parser.Tactic.location)? : tactic
macro_rules | `(tactic| pw_nf $[$loc]?) => `(tactic| (
  simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_lens, ↓reduceIte] $[$loc]?))

/-- **`pw_model`**: the model's words as `ofInt` of `Int` expressions, its
guards decided over `Int` where the context's facts decide them (`omega`). -/
syntax "pw_model" (" [" Lean.Parser.Tactic.simpArg,* "]")? (Lean.Parser.Tactic.location)? : tactic
macro_rules | `(tactic| pw_model $[[$extra,*]]? $[$loc]?) => do
  let extra := extra.map (·.getElems) |>.getD #[]
  `(tactic| (
  simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_mlens, ↓ite_eq_left, ↓ite_eq_right, ↓reduceIte, $extra,*] $[$loc]?))

/-- `pw_nf` on the left side, `pw_model` on the right (the walk's halves). -/
macro "pw_nf_l" : tactic => `(tactic| (
  conv => lhs; simp (config := { failIfUnchanged := false }) (disch := pw_disch_l) only [pw_lens, ↓reduceIte]))
/-- The model lens on the right side, deciding no `if` (the walk's root). -/
macro "pw_lens_r" : tactic => `(tactic| (
  conv => rhs; simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_mlens, ↓reduceIte]))
macro "pw_model_r" : tactic => `(tactic| (
  conv => rhs; simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_mlens, ↓ite_eq_left, ↓ite_eq_right, ↓reduceIte]))

/-! ## The memory: `.rodata` only

A value function reads the memory only at `.rodata` (`FORWARD` forwards the
frame's reloads), so a node's memory argument is generalised to a variable
with its `RodataRead` fact (`pw_mem`), and a `.rodata` load is its literal
(`pw_rod`: the word computed by evaluation, checked by `decide +kernel`). -/

open Lean Elab Tactic Meta in
/-- The first memory argument of a lifted function (`Lua.Vm.Fn.*.N_…`, `*.F`)
that is not a variable. -/
partial def nodeMem? (e : Expr) : MetaM (Option Expr) := do
  let rec go (e : Expr) : MetaM (Option Expr) := do
    match e with
    | .app .. =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if let .const n _ := f then
        let last := n.getString!
        if (n.getPrefix.toString.startsWith "Lua.Vm.Fn.") && (last.startsWith "N_" || last == "F") &&
            args.size > 0 then
          let a := args[0]!
          if !a.isFVar then
            if (← whnfR (← inferType a)).isAppOf ``Std.ExtHashMap then return some a
      for a in args do
        if let some r ← go a then return some r
      go f
    | .lam _ t b _ => do
      if let some r ← go t then return some r
      go b
    | .letE _ t v b _ => do
      if let some r ← go v then return some r
      go b
    | .mdata _ b => go b
    | _ => return none
  go e

open Lean Elab Tactic Meta in
/-- **`pw_mem`**: every node's memory argument a variable with its
`RodataRead` fact (`fn_rod_patch`: the stores and patches lie above the HTIF
mailbox, `kit_disch` over the stack facts in context). -/
elab "pw_mem" : tactic => do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let some M ← withMainContext do nodeMem? (← instantiateMVars (← getMainTarget)) | return
    withMainContext do
      let Ms ← Term.exprToSyntax M
      evalTactic (← `(tactic| have hro_m : Lua.Vm.Sim.RodataRead $Ms := by fn_rod_patch))
      evalTactic (← `(tactic| generalize $Ms = m_ at hro_m ⊢))

/-- `.rodata`'s 64-bit word at `a` as a literal (`pw_rod`). -/
theorem rod_lit {m : Mem} (hro : RodataRead m) {a : Nat} (v : BitVec 64) (hlo : Image.rodataBase ≤ a)
    (hhi : a + 8 ≤ Image.rodataBase + Image.rodataSize) (hv : Ieee754Sqrt.rodQ a = v) : bytesT8 m a = v := by
  rw [Ieee754Sqrt.rodQ_eq hro hlo hhi, hv]

open Lean Elab Tactic Meta in
/-- **`pw_rod`**: each `.rodata` load `bytesT8 m a` (a literal address, `m`
with its `RodataRead` fact in context) is the word there, computed by
evaluation and checked by `decide +kernel`. -/
elab "pw_rod" : tactic => do
  let mut fuel := 64
  while fuel > 0 do
    fuel := fuel - 1
    let r ← withMainContext do
      let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
      let t := match t.eq? with | some (_, l, _) => l | none => t
      let found := t.find? fun e => e.isAppOfArity ``Vsa.Sim.bytesT8 2 &&
        !(e.getArg! 1).hasFVar && !(e.getArg! 1).hasMVar && (e.getArg! 0).isFVar
      pure found
    let some e := r | return
    withMainContext do
      let aE := e.getArg! 1
      let a ← unsafe evalExpr Nat (mkConst ``Nat) aE
      let mS ← Term.exprToSyntax (e.getArg! 0)
      let aS ← Term.exprToSyntax aE
      let lem := mkIdent (Name.mkStr `Lua.Vm.Fn.PowRod s!"rod_{(Nat.toDigits 16 a).asString}")
      evalTactic (← `(tactic| rw [Lua.Vm.Fn.PowLens.rod_lit (m := $mS) (a := $aS) (by fn_assumption)
        _ (by decide) (by decide) $lem:ident]))

/-! ## The walk: the machine's fork tree, the model beside it (L5-fork) -/

open Lean Elab Tactic Meta in
/-- The left-hand side of an equation goal. -/
def goalLhs? (t : Expr) : Option Expr := (t.eq?).map (·.2.1.cleanupAnnotations)

open Lean Elab Tactic Meta in
/-- The condition of the outermost `if` of an expression (not under binders). -/
partial def firstIte? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``ite 5 then some e
  else match e with
    | .app f a => (firstIte? f).orElse fun _ => firstIte? a
    | .mdata _ b => firstIte? b
    | _ => none

/-- A datum the walk passes to a cut is not a NaN (the cut's premise); its
rules are `Lua/Vm/Fn/PowLeaves.lean`'s. -/
syntax "pw_notnan" : tactic
macro_rules | `(tactic| pw_notnan) => `(tactic| fail "pw_notnan")

open Lean Elab Tactic Meta in
/-- Case-split every `if` of the goal (outermost first, `let`s inlined, the
`match`es on constructors reduced), each case by `simp only` with its
condition; the cases closed by `rfl`. For stage equations between
`Lua/Num/Pow.lean`'s functions and their restatements. -/
partial def iteCases (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then throwError "pw_ite_cases: out of fuel"
  for g in ← getGoals do
    setGoals [g]
    evalTactic (← `(tactic| try simp (config := { zeta := true, failIfUnchanged := false }) only []))
    if (← getGoals).isEmpty then continue
    let t ← instantiateMVars (← getMainTarget)
    match firstIte? t with
    | none => evalTactic (← `(tactic| first | rfl | (exfalso; omega)))
    | some it =>
      if (← getOptions).getBool `pw.debug false then
        IO.println s!"ite_cases {← ppExpr (it.getArg! 1)}"
      -- the first atom of a Boolean condition (`a && b`, `a || b`, `!a`): a
      -- compound condition is decided by its atoms' cases
      let rec atom (c : Expr) (k : Nat) : MetaM Expr := do
        match k, c.eq? with
        | k + 1, some (_, l, r) =>
          if r.isConstOf ``Bool.true then
            if l.isAppOfArity ``Bool.and 2 || l.isAppOfArity ``Bool.or 2 then
              atom (← mkEq (l.getArg! 0) r) k
            else if l.isAppOfArity ``Bool.not 1 then atom (← mkEq (l.getArg! 0) r) k
            else pure c
          else pure c
        | _, _ => pure c
      let c ← atom (it.getArg! 1) 16
      let (gp, gn) ← (← getMainGoal).byCases c `hi_
      for sg in [gp, gn] do
        setGoals [sg.mvarId]
        let h := mkIdent (← sg.mvarId.withContext do return (← sg.fvarId.getDecl).userName)
        evalTactic (← `(tactic| simp (config := { failIfUnchanged := false }) only [$h:ident, ↓reduceIte, Bool.false_eq_true, Bool.true_eq_false, ite_true, ite_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.true_or, Bool.false_or, Bool.or_true, Bool.or_false, Bool.not_true, Bool.not_false]))
        iteCases (fuel - 1)
  setGoals []

open Lean Elab Tactic in
elab "pw_ite_cases" : tactic => iteCases 64

open Lean Elab Tactic Meta in
/-- The lifted function at the head of an expression (`Lua.Vm.Fn.*.N_…`). -/
def headNode? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ =>
    if n.getPrefix.toString.startsWith "Lua.Vm.Fn." && (n.getString!.startsWith "N_" || n.getString! == "F")
    then some n else none
  | _ => none

open Lean Elab Tactic Meta in
/-- The model's frontier: the conditions of the `if`s not under another
`if`'s branches nor a binder (the next decisions of `e_pow.c`). -/
partial def frontierGo (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, a)
  if e.isAppOfArity ``ite 5 then modify fun (v, a) => (v, a.push e)
  else match e with
    | .app f a => frontierGo f; frontierGo a
    | .mdata _ b => frontierGo b
    | _ => pure ()

open Lean Elab Tactic Meta in
def frontier (e : Expr) : Array Expr := ((frontierGo e).run ({}, #[])).2.2

open Lean Elab Tactic Meta in
/-- Prove `p` by a tactic on a fresh goal; `none` if it fails. -/
def proveBy? (p : Expr) (tac : TSyntax `tactic) : TacticM (Option Expr) := do
  let g ← mkFreshExprMVar p
  let saved ← saveState
  try
    let rest ← Tactic.run g.mvarId! (evalTactic tac)
    if rest.isEmpty then return some (← instantiateMVars g)
    saved.restore; return none
  catch _ => saved.restore; return none

open Lean Elab Tactic Meta in
/-- Rewrite the main goal by an equation proof. -/
def rwBy (eq : Expr) : TacticM Unit := do
  let g ← getMainGoal
  let r ← g.rewrite (← g.getType) eq
  let g' ← g.replaceTargetEq r.eNew r.eqProof
  replaceMainGoal (g' :: r.mvarIds)

open Lean Elab Tactic Meta in
/-- `ite_eq_left`/`ite_eq_right` at an `ite` of the goal, from a proof of its condition
or of its negation. -/
def iteEq (ite h : Expr) (pos : Bool) : MetaM Expr := do
  let α := ite.getArg! 0
  let u ← getLevel α
  return mkAppN (mkConst (if pos then ``ite_eq_left else ``ite_eq_right) [u])
    #[ite.getArg! 1, ite.getArg! 2, h, α, ite.getArg! 3, ite.getArg! 4]

open Lean Elab Tactic Meta in
/-- Subterms of `e` satisfying `p` (not under binders), outermost first. -/
partial def collectGo (p : Expr → Bool) (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (v, a) => (v.insert e, if p e then a.push e else a)
  match e with
  | .app f a => collectGo p f; collectGo p a
  | .mdata _ b => collectGo p b
  | _ => pure ()

open Lean Elab Tactic Meta in
def collectP (p : Expr → Bool) (e : Expr) : Array Expr := ((collectGo p e).run ({}, #[])).2.2

/-! ## Variable shifts: one case per amount -/

open Lean Elab Tactic Meta in
/-- The open exponents `e` of `2 ^ e.toNat` in an expression (a shift by a
register: `sraw`, `srlw`, a model `>>>`/`<<<` by a word). -/
def powAmounts (x : Expr) : Array Expr :=
  (collectP (fun t => t.isAppOfArity ``HPow.hPow 6 && (t.getArg! 5).isAppOfArity ``Int.toNat 1 &&
      ((t.getArg! 5).getArg! 0).hasFVar) x).map fun t => (t.getArg! 5).getArg! 0

open Lean Elab Tactic Meta in
/-- An integer bound of `e` from the context (`pw_disch`), by bisection over
`[-128, 128]`: the greatest `c` with `c ≤ e` (`lower`) or the least with
`e ≤ c`. -/
partial def intBound (e : Expr) (lower : Bool) : TacticM (Option Int) := do
  let go (tac : TSyntax `tactic) : TacticM (Option Int) := do
    let test (c : Int) : TacticM Bool := do
      let p ← if lower then mkAppM ``LE.le #[toExpr c, e] else mkAppM ``LE.le #[e, toExpr c]
      return (← withMainContext (proveBy? p tac)).isSome
    if lower then
      if !(← test (-128)) then return none
      let mut lo : Int := -128
      let mut hi : Int := 129
      while hi - lo > 1 do
        let mid := (lo + hi) / 2
        if ← test mid then lo := mid else hi := mid
      return some lo
    else
      if !(← test 128) then return none
      let mut lo : Int := -129
      let mut hi : Int := 128
      while hi - lo > 1 do
        let mid := (lo + hi) / 2
        if ← test mid then hi := mid else lo := mid
      return some hi
  -- `omega` alone when it bounds the amount (its failures are cheap), else `pw_disch`
  match ← go (← `(tactic| omega)) with
  | some b => return some b
  | none => go (← `(tactic| pw_disch))

open Lean Elab Tactic Meta in
/-- Rewrite every open shift amount the context pins to one value. -/
def pwShiftFix : TacticM Unit := do
  let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  for e in (powAmounts t).toList.eraseDups do
    let some lo ← intBound e true | continue
    let some hi ← intBound e false | continue
    if lo != hi then continue
    let h? ← withMainContext do proveBy? (← mkEq e (toExpr lo)) (← `(tactic| pw_disch))
    if let some h := h? then
      try withMainContext (rwBy h) catch _ => pure ()
  evalTactic (← `(tactic| try simp only [Int.reduceToNat, Int.reducePow, Nat.reducePow, Int.reduceDiv,
    Int.reduceMod, Int.reduceMul, Int.reduceAdd, Int.reduceSub, Int.reduceNeg]))

open Lean Elab Tactic in
elab "pw_shift_fix" : tactic => pwShiftFix

open Lean Elab Tactic Meta in
/-- **`pw_front`**: decide the model's frontier `if`s the context decides
(`omega`, then `pw_disch`), each by one rewrite, and reduce the `match`es that
become constructor applications (`simp only`'s iota); the model's undecided
`if`s are never entered. -/
partial def pwFront (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let some (_, _, rhs) := t.eq? | return
  let some it := (frontier rhs.cleanupAnnotations)[0]? | return
  let c := it.getArg! 1
  let shifts := (powAmounts c).size > 0
  let tac ← if shifts then
      `(tactic| first | assumption | (simp only [Bool.not_eq_true, Bool.not_eq_false] at *; assumption) | omega | (simp (config := { failIfUnchanged := true }) (disch := pw_disch) only [pw_mlens, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; pw_disch) | pw_omega_h | (pw_shift_fix; simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_mlens, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; pw_disch))
    else
      `(tactic| first | assumption | (simp only [Bool.not_eq_true, Bool.not_eq_false] at *; assumption) | omega | (simp (config := { failIfUnchanged := true }) (disch := pw_disch) only [pw_mlens, decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]; pw_disch) | pw_omega_h)
  let r ← withMainContext do
    if let some h ← proveBy? c tac then
      rwBy (← iteEq it h true); pure true
    else if let some h ← proveBy? (mkNot c) tac then
      rwBy (← iteEq it h false); pure true
    else pure false
  if r then
    evalTactic (← `(tactic| try conv => rhs; simp (config := { failIfUnchanged := false }) only []))
    if !(← getGoals).isEmpty then pwFront (fuel - 1)

open Lean Elab Tactic in
elab "pw_front" : tactic => pwFront 64

open Lean Elab Tactic Meta in
/-- A debugging line of the walk (`set_option pw.debug true`). -/
def pwDbg (msg : String) : TacticM Unit := do
  if (← getOptions).getBool `pw.debug false then
    IO.println s!"[pw {← IO.monoMsNow}] {msg}"


open Lean Elab Tactic Meta in
/-- A model datum the machine computed (`W d` with `d` not a variable). -/
def isWApp (e : Expr) : Bool :=
  e.isAppOfArity ``Lua.Vm.Fn.PowLens.W 1 && !(e.getArg! 0).isFVar

open Lean Elab Tactic Meta in
/-- A raw word construction read as a model operand: `toModel (ofInt 64 e)`
with `e` not a literal. -/
def isRawOperand (e : Expr) : Bool :=
  e.isAppOfArity ``Lua.Num.F64.toModel 1 &&
    (let b := e.getArg! 0
     b.isAppOfArity ``BitVec.ofInt 2 && (b.getArg! 1).hasFVar)

open Lean Elab Tactic Meta in
/-- **`pw_gen`**: the machine's new values to variables, the model's equal
expressions with them (one name per value, so both sides stay small and in
step, C's `let`s): first the model's operands aligned with the machine's
(a commuted `+`/`*`, `mmul_comm`/`madd_comm`; a raw word construction equal
modulo `2^64`, `toModel_congr` by `omega`). -/
def genCheck (d : Expr) : TacticM Bool := withMainContext do
  let g ← getMainGoal
  let (fvs, g') ← g.generalize #[{ expr := d, xName? := `d_, hName? := some `hd_ }]
  let dv := mkFVar fvs[0]!
  let t := (← instantiateMVars (← g'.getType)).cleanupAnnotations
  let some (_, _, rhs) := t.eq? | return false
  if (collectP (fun e => e == dv) rhs).size == 0 then
    return false
  let (_, g'') ← g'.withContext do g'.assertHypotheses #[
    { userName := `hWlo, type := ← inferType (← mkAppM ``Lua.Vm.Fn.PowLens.W_lo #[dv]),
      value := ← mkAppM ``Lua.Vm.Fn.PowLens.W_lo #[dv] },
    { userName := `hWhi, type := ← inferType (← mkAppM ``Lua.Vm.Fn.PowLens.W_hi #[dv]),
      value := ← mkAppM ``Lua.Vm.Fn.PowLens.W_hi #[dv] }]
  replaceMainGoal [g'']
  return true

open Lean Elab Tactic Meta in
def pwGen : TacticM Unit := withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let some (_, lhs, _) := t.eq? | return
  let ws := (collectP isWApp lhs).toList.eraseDups
  for w in ws do
    let d := w.getArg! 0
    let saved ← saveState
    let r ← (try genCheck d catch e => do pwDbg s!"genCheck threw {(← e.toMessageData.toString).take 300}"; pure false)
    pwDbg s!"gen {r} {← ppExpr d}"
    if r then continue
    saved.restore
    -- a commuted `*`/`+` of the model's
    if d.isAppOfArity ``Float.Model.mul 2 || d.isAppOfArity ``Float.Model.add 2 then
      let lem := if d.isAppOfArity ``Float.Model.mul 2 then ``Lua.Vm.Fn.PowLens.mmul_comm
        else ``Lua.Vm.Fn.PowLens.madd_comm
      let ok ← (do
          rwBy (mkAppN (mkConst lem) #[d.getArg! 1, d.getArg! 0])
          let r ← genCheck d
          pwDbg s!"gen comm {r}"
          pure r) <|> (do pwDbg "gen comm rw failed"; pure false)
      if ok then continue
      saved.restore
    -- a value the model does not compute in this form stays (the leaf compares it)

open Lean Elab Tactic Meta in
/-- One congruence step, never closing a new goal by unfolding (a model
datum's defeq check would evaluate the model's arithmetic); identical sides
are closed by `Eq.refl`. -/
def congr1 : TacticM Unit := do
  let g ← getMainGoal
  let gs ← g.congrN 1 (closePre := false) (closePost := false)
  let mut rest := []
  for g' in gs do
    let t := (← instantiateMVars (← g'.getType)).cleanupAnnotations
    match t.eq? with
    | some (_, a, b) =>
      if a.cleanupAnnotations == b.cleanupAnnotations then g'.refl else rest := rest ++ [g']
    | none =>
      match t.heq? with
      | some (_, a, _, b) =>
        if a.cleanupAnnotations == b.cleanupAnnotations then g'.hrefl else rest := rest ++ [g']
      | none => rest := rest ++ [g']
  setGoals rest

open Lean Elab Tactic Meta in
/-- **`pw_close`**: a leaf's two sides equal by congruence down to their
words, each pair of `ofInt` images equal modulo the word size (`omega`). -/
partial def pwClose (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then throwError "pw_close: out of fuel"
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let some (_, a, b) := t.eq? | throwError "pw_close: not an equation"
  let a := a.cleanupAnnotations
  let b := b.cleanupAnnotations
  if a == b then evalTactic (← `(tactic| rfl)); return
  -- two data's words: the data
  let isW (e : Expr) := e.isAppOfArity ``BitVec.ofInt 2 && (e.getArg! 1).isAppOfArity ``Lua.Vm.Fn.PowLens.W 1
  if isW a && isW b then
    congr1
    let mut acc := []
    for g' in ← getGoals do
      setGoals [g']
      congr1
      acc := acc ++ (← getGoals)
    setGoals acc
    for g' in ← getGoals do
      setGoals [g']
      pwClose (fuel - 1)
    return
  if a.isAppOfArity ``BitVec.ofInt 2 && b.isAppOfArity ``BitVec.ofInt 2 then
    evalTactic (← `(tactic| (apply Lua.Vm.Fn.PowLens.bv64_ext; pw_disch)))
    return
  if a.isAppOfArity ``Int32.ofInt 1 && b.isAppOfArity ``Int32.ofInt 1 then
    evalTactic (← `(tactic| (apply Lua.Vm.Fn.PowLens.i32_ext; pw_disch)))
    return
  if a.isAppOfArity ``UInt32.ofInt 1 && b.isAppOfArity ``UInt32.ofInt 1 then
    evalTactic (← `(tactic| (apply Lua.Vm.Fn.PowLens.u32_ext; pw_disch)))
    return
  if a.isAppOfArity ``Lua.Num.F64.toModel 1 && b.isAppOfArity ``Lua.Num.F64.toModel 1 &&
      (a.getArg! 0).isAppOfArity ``BitVec.ofInt 2 && (b.getArg! 0).isAppOfArity ``BitVec.ofInt 2 then
    evalTactic (← `(tactic| (apply Lua.Vm.Fn.PowLens.toModel_congr; pw_disch)))
    return
  -- a commuted `*`/`+`
  if (a.isAppOfArity ``Float.Model.mul 2 && b.isAppOfArity ``Float.Model.mul 2) ||
      (a.isAppOfArity ``Float.Model.add 2 && b.isAppOfArity ``Float.Model.add 2) then
    let saved ← saveState
    try
      congr1
      for g' in ← getGoals do
        setGoals [g']
        pwClose (fuel - 1)
      return
    catch _ =>
      saved.restore
      let lem := if a.isAppOfArity ``Float.Model.mul 2 then ``Lua.Vm.Fn.PowLens.mmul_comm
        else ``Lua.Vm.Fn.PowLens.madd_comm
      rwBy (mkAppN (mkConst lem) #[a.getArg! 0, a.getArg! 1])
      congr1
      for g' in ← getGoals do
        setGoals [g']
        pwClose (fuel - 1)
      return
  if a.getAppFn == b.getAppFn && a.getAppNumArgs == b.getAppNumArgs && a.getAppNumArgs > 0 then
    congr1
    for g' in ← getGoals do
      setGoals [g']
      let t' := (← instantiateMVars (← g'.getType)).cleanupAnnotations
      if t' == t then throwError "pw_close: no progress"
      pwClose (fuel - 1)
    return
  throwError "pw_close: the sides differ: {a} vs {b}"

open Lean Elab Tactic in
elab "pw_close" : tactic => pwClose 24

/-- A smaller frame below the same `sp`. -/
theorem fnsp_le {s W F : Nat} (h : Lua.Vm.Sim.FnSp s W) (hF : F ≤ W) : Lua.Vm.Sim.FnSp s F :=
  ⟨by have := h.lo; omega, h.hi, h.al⟩

open Lean Elab Tactic Meta in
/-- Rewrite the main goal by the first cut lemma that applies anywhere in it
(a node's lemma, a callee's value), its side conditions by `fn_assumption`,
the frame's stack facts (`fn_sp_in`) or `pw_disch`. -/
def tryCuts (cuts : Array Name) : TacticM Bool := do
  let tgt0 ← instantiateMVars (← getMainTarget)
  let tgt := (goalLhs? tgt0.cleanupAnnotations).getD tgt0
  for c in cuts do
    -- only a lemma whose left side's head occurs in the goal
    let info ← getConstInfo c
    let concl := info.type.getForallBody
    let some (_, l, _) := concl.eq? | continue
    let some hd := l.getAppFn.constName? | continue
    if (collectP (fun e => e.isConstOf hd) tgt).size == 0 then continue
    let saved ← saveState
    pwDbg s!"try {c}"
    let ok ← (withMainContext do
        let main ← getMainGoal
        let lemE ← mkConstWithFreshMVarLevels c
        let (args, _, _) ← forallMetaTelescope (← inferType lemE)
        let r ← main.rewrite (← main.getType) (mkAppN lemE args)
        let main' ← main.replaceTargetEq r.eNew r.eqProof
        for a in args do
          if (← a.mvarId!.isAssigned) then continue
          if !(← isProp (← inferType a)) then continue
          setGoals [a.mvarId!]
          let hsI := mkIdent `hs
          try
            evalTactic (← `(tactic| first | with_reducible rfl | fn_assumption | exact Eq.symm (by assumption) | exact Lua.Vm.Sim.fn_sp_in $hsI (by decide) (by decide) | exact Lua.Vm.Fn.PowLens.fnsp_le $hsI (by decide) | pw_disch | pw_notnan))
          catch e =>
            pwDbg s!"sidefail {← ppExpr (← instantiateMVars (← a.mvarId!.getType))}"
            throw e
        setGoals [main']
        pure true) <|> (do
          saved.restore
          if (← getOptions).getBool `pw.debug false then
            for e in collectP (fun e => e.isAppOf hd) tgt do
              pwDbg s!"nomatch {← ppExpr e}"
          pure false)
    if ok then
      pwDbg s!"cut {c}"
      return true
  return false

open Lean Elab Tactic Meta in
/-- A leaf of the walk (or a node a cut closed): the model's remaining
decisions (`pw_front`), shift amounts the context pins (`pw_shift_fix`), the
model lens, then `rfl` or `pw_close`; a stage the walk reached without its cut
is unfolded and the same applied. -/
def pwLeafCore : TacticM Unit := do
  -- a cut's right side in the machine's lens
  evalTactic (← `(tactic| try pw_nf_l))
  if (← getGoals).isEmpty then return
  -- a path the context refutes
  evalTactic (← `(tactic| try (exfalso; omega)))
  if (← getGoals).isEmpty then return
  pwDbg "leaf front"
  pwFront 64
  pwDbg "leaf fix"
  if !(← getGoals).isEmpty then evalTactic (← `(tactic| try with_reducible rfl))
  for _ in [0:3] do
    if (← getGoals).isEmpty then break
    let t0 ← instantiateMVars (← getMainTarget)
    evalTactic (← `(tactic| try pw_shift_fix))
    if !(← getGoals).isEmpty then evalTactic (← `(tactic| pw_model_r))
    if (← getGoals).isEmpty then break
    if (← instantiateMVars (← getMainTarget)) == t0 then break
  pwDbg "leaf close"
  if !(← getGoals).isEmpty then evalTactic (← `(tactic| try with_reducible rfl))
  if !(← getGoals).isEmpty then evalTactic (← `(tactic| try pw_close))
  pwDbg "leaf done"
  if (← getOptions).getBool `pw.debug.goal false then
    if !(← getGoals).isEmpty then
      pwDbg s!"open leaf:\n{← ppGoal (← getMainGoal)}"

open Lean Elab Tactic Meta in
/-- `pwLeafCore`, and while a stage the walk reached without its cut remains
on the model's side, its outermost one unfolded and the same again. -/
def pwLeaf : TacticM Unit := do
  pwLeafCore
  for _ in [0:4] do
    if (← getGoals).isEmpty then return
    let some ext ← getSimpExtension? `pw_stage | return
    let stages := (← ext.getTheorems).toUnfold
    let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
    let some (_, lhs, rhs) := t.eq? | return
    let isStage := fun (e : Expr) => match e.getAppFn.constName? with
        | some n => stages.contains n | none => false
    -- a stage not under an `if`'s branch (the branches stay for the context to decide)
    let rec topStage? (e : Expr) (k : Nat) : Option Expr :=
      match k with
      | 0 => none
      | k + 1 =>
        if e.isAppOfArity ``ite 5 then none
        else if isStage e then some e
        else e.getAppArgs.foldl (fun acc a => acc.orElse fun _ => topStage? a.cleanupAnnotations k) none
    let lst? := topStage? lhs.cleanupAnnotations 64
    let rst? := topStage? rhs.cleanupAnnotations 64
    let sameHead := fun (a b : Option Expr) => match a, b with
      | some x, some y => x.getAppFn.constName? == y.getAppFn.constName?
      | _, _ => false
    -- the left's stage coarser than the right's (its body calls the right's), or
    -- the right without one: the sides swapped, the coarser one unfolded
    let calls := fun (a b : Option Expr) => do
      match a, b with
      | some x, some y =>
        let some v := (← getConstInfo x.getAppFn.constName!).value? | return false
        return (v.find? (fun e => e.isConstOf y.getAppFn.constName!)).isSome
      | _, _ => return false
    if lst?.isSome && !sameHead lst? rst? &&
        (collectP (fun e => e.isAppOf lst?.get!.getAppFn.constName!) rhs).size == 0 &&
        (rst?.isNone || (← calls lst? rst?)) then
      pwDbg s!"leaf swap for {lst?.get!.getAppFn.constName!}"
      evalTactic (← `(tactic| symm))
      continue
    -- the right's first stage (not under an `if`'s branch) the left does not have
    let rec topStages (e : Expr) (k : Nat) : Array Expr :=
      match k with
      | 0 => #[]
      | k + 1 =>
        if e.isAppOfArity ``ite 5 then #[]
        else
          let here := if isStage e then #[e] else #[]
          e.getAppArgs.foldl (fun acc a => acc ++ topStages a.cleanupAnnotations k) here
    let cands := (topStages rhs.cleanupAnnotations 64).filter fun e =>
      (collectP (fun f => f.isAppOf e.getAppFn.constName!) lhs).size == 0
    let some st := cands[0]? | return
    let nS := mkIdent st.getAppFn.constName!
    pwDbg s!"leaf unfold {st.getAppFn.constName!}"
    evalTactic (← `(tactic| conv => rhs; unfold $nS:ident))
    pwLeafCore

open Lean Elab Tactic Meta in
/-- **`pw_walk`**: normalise both sides (`pw_mem`, `pw_nf`, `pw_model` with the
extra lemmas), then split the machine's guard (`by_cases`, both sides
rewritten by it) or unfold its next node, to the leaves; a leaf is left for
the caller's closer. -/
partial def pwWalk (cuts : Array Name) (fuel : Nat) : TacticM Unit := do
  if fuel = 0 then return
  if (← getGoals).isEmpty then return
  pwDbg "step"
  evalTactic (← `(tactic| pw_mem))
  evalTactic (← `(tactic| pw_rod))
  evalTactic (← `(tactic| pw_nf_l))
  if (← getGoals).isEmpty then return
  pwDbg "gen"
  pwGen
  if (← getGoals).isEmpty then return
  if (← getOptions).getBool `pw.debug.goal false then
    pwDbg s!"goal after gen:\n{← ppExpr (← instantiateMVars (← getMainTarget))}"
  -- a shift by a register: one case per amount the context allows
  let lhsAm := match goalLhs? (← instantiateMVars (← getMainTarget)).cleanupAnnotations with
    | some l => (powAmounts l).toList.eraseDups
    | none => []
  if let some e := lhsAm.head? then
    let lo? ← intBound e true
    let hi? ← intBound e false
    if let (some lo, some hi) := (lo?, hi?) then
      if hi - lo ≤ 64 then
        pwDbg s!"shift cases {lo}..{hi}"
        let mut res : List MVarId := []
        let mut c := lo
        while c ≤ hi do
          let g ← getMainGoal
          let eqc ← g.withContext (mkEq e (toExpr c))
          if c == hi then
            -- the last value: from the others' exclusions
            let h? ← withMainContext do proveBy? eqc (← `(tactic| pw_disch))
            match h? with
            | some h =>
              withMainContext (rwBy h)
              evalTactic (← `(tactic| pw_nf_l))
              pwWalk cuts (fuel - 1)
              res := res ++ (← getGoals)
            | none => res := res ++ [g]
          else
            let (gp, gn) ← g.byCases eqc `hsh_
            setGoals [gp.mvarId]
            withMainContext (rwBy (mkFVar gp.fvarId))
            evalTactic (← `(tactic| pw_nf_l))
            pwWalk cuts (fuel - 1)
            res := res ++ (← getGoals)
            setGoals [gn.mvarId]
          c := c + 1
        setGoals res
        return
  -- a callee's value inside the node's arguments
  let mut inner := 8
  while inner > 0 do
    inner := inner - 1
    let t := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
    let some lhs := goalLhs? t | break
    if (headNode? lhs).isSome || (firstIte? lhs).isSome then
      -- only arguments: the head is the walk's
      -- an `if`'s branches are the walk's too: only its condition
      let args := if lhs.isAppOfArity ``ite 5 then #[lhs.getArg! 1] else lhs.getAppArgs
      if !(args.any fun a => (collectP (fun e => (headNode? e).isSome) a).size > 0) then break
    pwDbg "inner"
    if !(← tryCuts cuts) then break
    pwDbg "inner cut"
    evalTactic (← `(tactic| pw_nf_l))
    if (← getGoals).isEmpty then return
    pwGen
  let gs ← getGoals
  let mut out : List MVarId := []
  for g in gs do
    setGoals [g]
    let t := (← instantiateMVars (← g.getType)).cleanupAnnotations
    match goalLhs? t with
    | none => out := out ++ [g]
    | some lhs =>
      -- a node's arguments' `if`s are values: the node first (its cut or its unfolding)
      let splitAt? := if lhs.isAppOfArity ``ite 5 then firstIte? lhs
        else if (headNode? lhs).isSome then none else firstIte? lhs
      if false then pure ()
      else if let some it := splitAt? then
        let c := it.getArg! 1
        pwDbg s!"split"
        let (gp, gn) ← g.byCases c `hc_
        let mut res : List MVarId := []
        for (sg, pos) in [(gp, true), (gn, false)] do
          setGoals [sg.mvarId]
          withMainContext do
            rwBy (← iteEq it (mkFVar sg.fvarId) pos)
          pwDbg "front"
          if !(← getGoals).isEmpty then pwFront 64
          pwWalk cuts (fuel - 1)
          res := res ++ (← getGoals)
        out := out ++ res
      else if let some n := headNode? lhs then
        -- a cut lemma for this node, else its unfolding
        let cut ← tryCuts cuts
        if cut then
          pwLeaf
          out := out ++ (← getGoals)
        if !cut then
          let nS := mkIdent n
          pwDbg s!"unfold {n}"
          evalTactic (← `(tactic| conv => lhs; unfold $nS:ident))
          pwWalk cuts (fuel - 1)
          out := out ++ (← getGoals)
      else
        -- a leaf: the model's remaining decisions, its lens, the comparison
        pwDbg "leaf"
        let mut k := 8
        while k > 0 do
          k := k - 1
          if !(← tryCuts cuts) then break
          evalTactic (← `(tactic| pw_nf_l))
          if (← getGoals).isEmpty then break
        if (← getGoals).isEmpty then continue
        pwLeaf
        out := out ++ (← getGoals)
  setGoals out

open Lean Elab Tactic in
syntax "pw_walk" ("using" "[" ident,* "]")? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| pw_walk $[using [$ids,*]]?) => do
  let cs : Array Name := (ids.map (·.getElems) |>.getD #[]).map (·.getId.eraseMacroScopes)
  let cs : Array Name ← cs.mapM fun c => do
    try realizeGlobalConstNoOverloadWithInfo (mkIdent c) catch _ => pure c
  -- the range of every datum's word in the goal (the operands, not the model's terms)
  withMainContext do
    let t ← instantiateMVars (← getMainTarget)
    let ((), atoms) ← (lensAtoms t).run #[]
    for a in atoms do
      if a.isAppOfArity ``Lua.Vm.Fn.PowLens.W 1 && (a.getArg! 0).isFVar then
        let dS ← Term.exprToSyntax (a.getArg! 0)
        evalTactic (← `(tactic| have := Lua.Vm.Fn.PowLens.W_lo $dS; have := Lua.Vm.Fn.PowLens.W_hi $dS))
  pwWalk cs 400

open Lean Elab Tactic in
/-- `pw_walk` to a depth (debugging). -/
elab "pw_walk_n " n:num : tactic => pwWalk #[] n.getNat

/-! ## Chambers by an integer key -/

open Lean Elab Command in
/-- **`pw_chambers nm [lo, hi] (k) binders : stmt := by tac`**: the chamber
generator of the walk. A statement whose machine shifts by an amount `k` (a
term over the binders) is proved once per value: `nm_<c>` (`nm_m<c>` for a
negative `c`) with the premise `hK : k = c`, each by `tac` in a declaration of
its own (the heartbeat budget is per declaration), and the cover `nm` with
`hK1 : lo ≤ k`, `hK2 : k ≤ hi`, by a balanced split on `k`; never a hand
chamber list. -/
syntax (name := pwChambers) "pw_chambers " ident " [" "-"? num ", " num "] " "(" term ") "
  bracketedBinder* " : " term " := " "by " tacticSeq : command

open Lean Elab Command in
@[command_elab pwChambers] def elabPwChambers : CommandElab := fun stx => do
  let nm := stx[1].getId
  let lo : Int := (if stx[3].isNone then 1 else -1) * stx[4].isNatLit?.getD 0
  let hi : Int := stx[6].isNatLit?.getD 0
  let k : TSyntax `term := ⟨stx[9]⟩
  let bs : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := stx[11].getArgs.map (⟨·⟩)
  let st : TSyntax `term := ⟨stx[13]⟩
  let tac : TSyntax ``Lean.Parser.Tactic.tacticSeq := ⟨stx[16]⟩
  let lit (c : Int) : TSyntax `term :=
    if c < 0 then ⟨mkNode ``Lean.Parser.Term.app #[mkIdent ``Neg.neg, mkNullNode #[Syntax.mkNumLit (toString c.natAbs)]]⟩
    else Syntax.mkNumLit (toString c)
  let chName (c : Int) : Ident :=
    mkIdent (nm ++ Name.mkSimple (if c < 0 then s!"m{c.natAbs}" else s!"{c}"))
  let mut c := lo
  while c ≤ hi do
    let cl := lit c
    elabCommand (← `(command| theorem $(chName c) $bs* (hK : $k = ($cl : Int)) : $st := by $tac))
    c := c + 1
  -- the cover: a balanced split on `k`
  let rec tree (a b : Int) (fuel : Nat) : CommandElabM (TSyntax `tactic) := do
    match fuel with
    | 0 => `(tactic| omega)
    | fuel + 1 =>
      if b ≤ a then
        `(tactic| (apply $(chName a) <;> first | assumption | omega))
      else
        let m := (a + b) / 2
        let t1 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree a m fuel):tactic)
        let t2 ← `(Lean.Parser.Tactic.tacticSeq| $(← tree (m + 1) b fuel):tactic)
        `(tactic| if _ : $k ≤ ($(lit m) : Int) then $t1 else $t2)
  let t ← tree lo hi 64
  elabCommand (← `(command|
    theorem $(mkIdent nm) $bs* (hK1 : ($(lit lo) : Int) ≤ $k) (hK2 : $k ≤ ($(lit hi) : Int)) : $st := by
      $t:tactic))

end Lua.Vm.Fn.PowLens

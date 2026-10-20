import Lua.Vm.Fn.PowLens
import Lua.Vm.Fn.ScalbnSpec
import Lua.Vm.Fn.PowR
import Lua.Vm.Fn.SfRefInt

/-!
# `__ieee754_pow`'s callees on the lenses (lane float-sf7)

The facts the walk of `__ieee754_pow` applies where the machine calls a
routine whose result is not a soft-float operation:

* the comparisons `__ledf2`/`__gedf2` as tested (`slti`, `bgtz`, `bltz`):
  `F64`'s order, hence the model's (`ledf2_lt0`, `gedf2_gt0`, `gedf2_lt0`);
* the error exits `__math_oflow`/`__math_uflow` (tail calls): the model's
  `mathOflow`/`mathUflow` of the sign the machine computed (`oflow_v`, `uflow_v`);
* `__floatsidf` of a word in range: the model's `ofInt` (`floatsidf_l`);
* the signalling tests of `e_pow.c:121,128` (`sig_ge`, `sig_lt`): false on
  quiet operands.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Num

namespace Lua.Vm.Fn.PowLens

theorem ledf2_lt0 (x y : BitVec 64) :
    zopz0zI_s (Ledf2.S x y) (BitVec.ofInt 64 0) = F64.lt x y := by
  rw [SfLens.slt_int', show (BitVec.ofInt 64 0).toInt = 0 by decide]
  unfold Ledf2.S F64.lt
  rcases F64.compare x y with _ | (_ | _ | _) <;> decide

theorem gedf2_gt0 (x y : BitVec 64) :
    zopz0zI_s (BitVec.ofInt 64 0) (Gedf2.S x y) = F64.lt y x := by
  rw [SfLens.slt_int', show (BitVec.ofInt 64 0).toInt = 0 by decide, F64.lt, F64.compare_swap]
  unfold Gedf2.S
  rcases F64.compare x y with _ | (_ | _ | _) <;> decide

theorem gedf2_lt0 (x y : BitVec 64) :
    zopz0zI_s (Gedf2.S x y) (BitVec.ofInt 64 0) = !F64.le y x := by
  rw [SfLens.slt_int', show (BitVec.ofInt 64 0).toInt = 0 by decide, F64.le, F64.compare_swap]
  unfold Gedf2.S
  rcases F64.compare x y with _ | (_ | _ | _) <;> decide

theorem zext_bool_l (b : Bool) :
    zero_extend (m := 64) (bool_to_bit b) = BitVec.ofInt 64 (if b then 1 else 0) := by
  cases b <;> decide

attribute [pw_lens] ledf2_lt0 gedf2_gt0 gedf2_lt0 zext_bool_l F64.lt_eq_model F64.le_eq_model

/-- `__math_oflow(sign)` (`math_err.c:70-73`, a tail call). -/
theorem oflow_v (m : Mem) (s : Nat) (r : BitVec 64) (b : Bool) (hro : RodataRead m) (hs : FnSp s 112) :
    MathOflow.F m s r (BitVec.ofInt 64 (if b then 1 else 0)) = BitVec.ofInt 64 (W (Pow.mathOflow b)) := by
  fn_sp_factsW
  unfold Pow.mathOflow Pow.xflow
  cases b <;> (pw_lens_r; pw_walk)

/-- `__math_uflow(sign)` (`math_err.c:54-57`, a tail call). -/
theorem uflow_v (m : Mem) (s : Nat) (r : BitVec 64) (b : Bool) (hro : RodataRead m) (hs : FnSp s 112) :
    MathUflow.F m s r (BitVec.ofInt 64 (if b then 1 else 0)) = BitVec.ofInt 64 (W (Pow.mathUflow b)) := by
  fn_sp_factsW
  unfold Pow.mathUflow Pow.xflow
  cases b <;> (pw_lens_r; pw_walk)

/-- `__math_oflow(0)` (the sign known: `e_pow.c:201-204`). -/
theorem oflow_0 (m : Mem) (s : Nat) (r : BitVec 64) (hro : RodataRead m) (hs : FnSp s 112) :
    MathOflow.F m s r (BitVec.ofInt 64 0) = BitVec.ofInt 64 (W (Pow.mathOflow false)) :=
  oflow_v m s r false hro hs

/-- `__math_uflow(0)` (the sign known: `e_pow.c:201-204`). -/
theorem uflow_0 (m : Mem) (s : Nat) (r : BitVec 64) (hro : RodataRead m) (hs : FnSp s 112) :
    MathUflow.F m s r (BitVec.ofInt 64 0) = BitVec.ofInt 64 (W (Pow.mathUflow false)) :=
  uflow_v m s r false hro hs

/-- `__floatsidf(n)` (`e_pow.c:263`) of a word: the model's `ofInt`. -/
theorem floatsidf_l (m : Mem) (s : Nat) (r : BitVec 64) (n : Int) (hs : FnSp s 32)
    (h1 : -2 ^ 31 ≤ n) (h2 : n < 2 ^ 31) :
    Floatsidf.F m s r (BitVec.ofInt 64 n) = BitVec.ofInt 64 (W (Float.Model.ofInt n)) := by
  have h64 : (BitVec.ofInt 64 n).toInt = n := by
    rw [BitVec.toInt_ofInt]; simp only [Int.bmod, Nat.reducePow, Int.reducePow]; split <;> omega
  have hx : ((BitVec.ofInt 64 n).setWidth 32).signExtend 64 = BitVec.ofInt 64 n := by
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_setWidth, h64]
    have := Int.emod_nonneg n (show ((2 : Int) ^ 64) ≠ 0 by decide)
    simp only [BitVec.toNat_ofInt, Int.toNat_of_nonneg this, Int.bmod, Nat.reducePow, Int.reducePow,
      Int.natCast_pow]
    split <;> omega
  rw [Floatsidf.spec_proved m s r _ hs hx, Floatsidf.S, hx, F64.ofInt_eq_model, h64, bits_W]

/-- `ieee754Pow`'s last step (`e_pow.c:198-318`) is the stage `log2Exp`. -/
theorem log2Exp_eq (x : Float.Model) (ix hy iy : Int32) (y sign : Float.Model) :
    (match Pow.log2Split x ix hy iy sign with
      | .inl r => r
      | .inr (t1, t2) => Pow.exp2Tail y t1 t2 sign) = Pow.log2Exp x ix hy iy y sign := by
  unfold Pow.log2Split Pow.log2Exp Pow.logGen Pow.logGenK Pow.logNear Pow.logExp
  pw_ite_cases

/-- `ieee754Pow` is its stage form `powTop` (`Lua/Vm/Fn/PowStage.lean`). -/
theorem ieee754Pow_stage (x y : Float.Model) : Pow.ieee754Pow x y = Pow.powTop x y := by
  unfold Pow.ieee754Pow Pow.powTop Pow.powYi Pow.powAx Pow.powAx0 Pow.powXZ Pow.powXZn Pow.powNY Pow.powSign
  unfold Pow.log2Split Pow.log2Exp Pow.logGen Pow.logGenK Pow.logNear Pow.logExp
  pw_ite_cases

/-- The machine's sign flip (`xor` of bit 63) of a datum that is not a NaN is
the model's `neg` (`e_pow.c:183`). -/
theorem negW_l (z : Float.Model) (hn : ¬ (W z / 2 ^ 52 % 2048 = 2047 ∧ W z % 2 ^ 52 ≠ 0)) :
    BitVec.ofInt 64 (W z + 9223372036854775808) = BitVec.ofInt 64 (W z.neg) := by
  have h1 := mneg_l (W z) hn
  rw [model_W] at h1
  rw [h1, W_ofInt _ (by omega)]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_ofInt]
  simp only [Int.bmod, Nat.reducePow, Int.reducePow]
  have := W_lo z; have := W_hi z
  split <;> split <;> omega

attribute [pw_lens] negW_l

/-- `1/|x|` of `|x| ∈ {0, ∞, 1}` (`e_pow.c:177`) is not a NaN. -/
theorem notNaN_div_one (a : Float.Model)
    (h : W a = 0 ∨ W a = 9218868437227405312 ∨ W a = 4607182418800017408) :
    ¬ (W ((F64.toModel (BitVec.ofInt 64 4607182418800017408)).div a) / 2 ^ 52 % 2048 = 2047 ∧
      W ((F64.toModel (BitVec.ofInt 64 4607182418800017408)).div a) % 2 ^ 52 ≠ 0) := by
  have e : ∀ c : BitVec 64, W ((F64.toModel (BitVec.ofInt 64 4607182418800017408)).div (F64.toModel c)) =
      (F64.div (BitVec.ofInt 64 4607182418800017408) c).toInt := by
    intro c; rw [div_l, BitVec.toInt_ofInt]
    have := W_lo ((F64.toModel (BitVec.ofInt 64 4607182418800017408)).div (F64.toModel c))
    have := W_hi ((F64.toModel (BitVec.ofInt 64 4607182418800017408)).div (F64.toModel c))
    simp only [Int.bmod, Nat.reducePow, Int.reducePow]; split <;> omega
  rw [← model_W a]
  rcases h with h | h | h <;> rw [h, e] <;> decide

/-- `powAx` at `yisint = 0` for a negative `x` is `powAxN`. -/
theorem powAx_neg0 (x y : Float.Model) (hx : Int) (lx : UInt32) (ix hy iy : Int32)
    (h1 : -2 ^ 31 ≤ hx) (h2 : hx < 0) :
    Pow.powAx x y (Int32.ofInt hx) lx ix hy iy (Int32.ofInt 0) = Pow.powAxN x (Int32.ofInt hx) lx ix hy := by
  unfold Pow.powAx Pow.powAx0 Pow.powNY Pow.powAxN
  have hn : ((Pow.u (Int32.ofInt hx) >>> 31 - 1).toInt32 ||| Int32.ofInt 0 == 0) = true := by
    simp (disch := pw_disch) only [pw_mlens]; omega
  simp only [hn, ↓reduceIte]
  rfl

attribute [pw_mlens] powAx_neg0

/-- A model datum with a NaN's bits is the canonical NaN (`Float.Model`'s only one). -/
theorem W_nan (y : Float.Model) (h : W y / 2 ^ 52 % 2048 = 2047 ∧ W y % 2 ^ 52 ≠ 0) :
    W y = 9221120237041090560 := by
  have hl := W_lo y; have hh := W_hi y
  unfold W at *
  obtain ⟨b, hv⟩ := y
  dsimp only at h hl hh ⊢
  have ht : (b.toBitVec.toInt : Int) % 2 ^ 64 = (b.toBitVec.toNat : Int) := by
    rw [BitVec.toInt_eq_toNat_bmod]; have := b.toBitVec.isLt
    simp only [Int.bmod]; split <;> omega
  have hc : F64.cls b.toBitVec = .nan := by
    unfold F64.cls F64.bexp F64.frac
    simp only [Nat.reducePow, Int.reducePow] at h ht ⊢
    have h1 : b.toBitVec.toNat / 4503599627370496 % 2048 = 2047 := by omega
    have h2 : ¬ b.toBitVec.toNat % 4503599627370496 = 0 := by omega
    rw [ite_eq_left h1, ite_eq_right h2]
  have e : b.toBitVec = 0x7ff8000000000000#64 := by
    have hpn := hv.eq_packedNaN
    simp only [F64.cls] at hc
    split at hc
    · split at hc
      · cases hc
      · rename_i h1 h2
        rw [hpn ((F64.exp_eq_ones _).2 h1) (fun e => h2 ((F64.man_eq_zero _).1 e))]
        rfl
    · split at hc
      · split at hc <;> cases hc
      · cases hc
  show b.toBitVec.toInt = _
  rw [e]; decide

/-- `fabs` (`e_pow.c:172`, the bits with the sign cleared) is the model's
`fabs`, NaN included (the model's NaN is the positive `0x7ff8000000000000`). -/
theorem fabs_l (x : Float.Model) : Lua.Vm.Fn.Fabs.F (BitVec.ofInt 64 (W x)) = BitVec.ofInt 64 (W (Pow.fabs x)) := by
  have hl := W_lo x; have hh := W_hi x
  unfold Lua.Vm.Fn.Fabs.F
  simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [pw_lens]
  simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [Pow.fabs, pw_mlens]
  by_cases hn : (W x / 4294967296 % 2147483648 * 4294967296 + W x % 4294967296) / 2 ^ 52 % 2048 = 2047 ∧
      (W x / 4294967296 % 2147483648 * 4294967296 + W x % 4294967296) % 2 ^ 52 ≠ 0
  · have hx := W_nan x ⟨by omega, by omega⟩
    have e : W x / 4294967296 % 2147483648 * 4294967296 + W x % 4294967296 = W x := by omega
    rw [e, model_W, hx]; decide
  · rw [W_ofInt _ hn]
    apply BitVec.eq_of_toInt_eq
    simp only [BitVec.toInt_ofInt, Int.bmod, Nat.reducePow, Int.reducePow]
    split <;> split <;> omega

attribute [pw_lens] fabs_l

/-- `pw_notnan`: `|x|` or `1/|x|` of an `x` the context pins to `±0`, `±∞`, `±1`. -/
macro_rules | `(tactic| pw_notnan) => `(tactic| (subst_vars; first
  | (with_reducible apply Lua.Vm.Fn.PowLens.notNaN_div_one
     simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [Lua.Num.Pow.fabs, pw_mlens]
     first | omega | pw_omega)
  | (simp (config := { failIfUnchanged := false }) (disch := pw_disch) only [Lua.Num.Pow.fabs, pw_mlens]
     first | omega | pw_omega)))

end Lua.Vm.Fn.PowLens

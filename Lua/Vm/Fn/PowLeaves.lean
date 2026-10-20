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

end Lua.Vm.Fn.PowLens

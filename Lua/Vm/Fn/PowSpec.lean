import Lua.Vm.Fn.PowYi

/-!
# `__ieee754_pow` at level (b) (lane float-sf7)

**`Ieee754PowSpec_Statement`, proved** (`spec_proved`): on quiet operands the
lifted `Ieee754Pow.F` is the canonical datum of `e_pow.c`'s transcription
`Lua.Num.Pow.ieee754Pow`.

The machine's fork tree, walked beside the model (`pw_walk`,
`Lua/Vm/Fn/PowLens.lean`) and cut at its joins, one lemma per join over the
stages of `Lua/Vm/Fn/PowStage.lean` (`ieee754Pow_stage : ieee754Pow = powTop`):
the NaN operands (`e_c31c`: `powNaN`), `y ≠ ±0` (`e_c308`), and the whole
function on model data (`F_model`, over `e_c374` of `Lua/Vm/Fn/PowYi.lean`);
a NaN operand of any quiet payload by its words (`F_nan_nn`, `F_nan_nx`,
`F_nan_ny`: the model's datum is the canonical NaN, `W_ofInt_nan`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Ieee754Pow

/-- `e_pow.c:126-130` at `0x8002c31c`: `powNaN`. -/
theorem e_c31c (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx hx : Int) (hro : RodataRead m) (hs : FnSp s 288) (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) :
    N_8002c31c m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 hx) =
      BitVec.ofInt 64 (W (Pow.powNaN x y (Int32.ofInt hx) (UInt32.ofInt lx))) := by
  fn_sp_factsW
  unfold Pow.powNaN
  pw_model_r
  pw_front
  pw_walk

/-- `e_pow.c:126-318` at `0x8002c308`: `y ≠ ±0`. -/
theorem e_c308 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (ly iy hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hiy : iy = hy % 2147483648)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hy0 : ¬ (iy = 0 ∧ ly % 4294967296 = 0)) :
    N_8002c308 m s r g (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 2147483647) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powTop x y)) := by
  fn_sp_factsW
  unfold Pow.powTop
  pw_model_r
  pw_front
  pw_walk using [e_c374, e_c31c]

/-- **`__ieee754_pow` on model data** (`e_pow.c:103-318`): `powTop`. -/
theorem F_model (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (hro : RodataRead m) (hs : FnSp s 288) :
    F m s r g (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y)) = BitVec.ofInt 64 (W (Pow.powTop x y)) := by
  fn_sp_factsW
  unfold F Pow.powTop
  pw_model_r
  pw_walk using [e_c308]

/-- The walk of `__ieee754_pow` on operand words whose NaN-ness is known: the
model's words rewritten once (`W_ofInt`, `W_ofInt_nan`), then
`pw_walk`. -/
macro "pw_nan_case" : tactic => `(tactic| (
  fn_sp_factsW
  unfold F Lua.Num.Pow.powTop Lua.Num.Pow.powNaN
  simp (config := { failIfUnchanged := false }) (disch := omega) only
    [Lua.Vm.Fn.PowLens.W_ofInt_nan, Lua.Vm.Fn.PowLens.W_ofInt]
  pw_model_r
  pw_walk))

/-- `__ieee754_pow(NaN, NaN)`, quiet. -/
theorem F_nan_nn (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (X Y : Int)
    (hro : RodataRead m) (hs : FnSp s 288)
    (hX1 : -2 ^ 63 ≤ X) (hX2 : X < 2 ^ 63) (hY1 : -2 ^ 63 ≤ Y) (hY2 : Y < 2 ^ 63)
    (hXe : X / 2 ^ 52 % 2048 = 2047) (hXf : X % 2 ^ 52 ≠ 0) (hXq : X / 2 ^ 51 % 2 = 1)
    (hYe : Y / 2 ^ 52 % 2048 = 2047) (hYf : Y % 2 ^ 52 ≠ 0) (hYq : Y / 2 ^ 51 % 2 = 1) :
    F m s r g (BitVec.ofInt 64 X) (BitVec.ofInt 64 Y) =
      BitVec.ofInt 64 (W (Pow.powTop (F64.toModel (BitVec.ofInt 64 X)) (F64.toModel (BitVec.ofInt 64 Y)))) := by
  pw_nan_case

/-- `__ieee754_pow(NaN, y)`, quiet, `y` not a NaN. -/
theorem F_nan_nx (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (X Y : Int)
    (hro : RodataRead m) (hs : FnSp s 288)
    (hX1 : -2 ^ 63 ≤ X) (hX2 : X < 2 ^ 63) (hY1 : -2 ^ 63 ≤ Y) (hY2 : Y < 2 ^ 63)
    (hXe : X / 2 ^ 52 % 2048 = 2047) (hXf : X % 2 ^ 52 ≠ 0) (hXq : X / 2 ^ 51 % 2 = 1)
    (hYr : ¬ (Y / 2 ^ 52 % 2048 = 2047 ∧ Y % 2 ^ 52 ≠ 0)) :
    F m s r g (BitVec.ofInt 64 X) (BitVec.ofInt 64 Y) =
      BitVec.ofInt 64 (W (Pow.powTop (F64.toModel (BitVec.ofInt 64 X)) (F64.toModel (BitVec.ofInt 64 Y)))) := by
  pw_nan_case

/-- `__ieee754_pow(x, NaN)`, quiet, `x` not a NaN. -/
theorem F_nan_ny (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (X Y : Int)
    (hro : RodataRead m) (hs : FnSp s 288)
    (hX1 : -2 ^ 63 ≤ X) (hX2 : X < 2 ^ 63) (hY1 : -2 ^ 63 ≤ Y) (hY2 : Y < 2 ^ 63)
    (hXr : ¬ (X / 2 ^ 52 % 2048 = 2047 ∧ X % 2 ^ 52 ≠ 0))
    (hYe : Y / 2 ^ 52 % 2048 = 2047) (hYf : Y % 2 ^ 52 ≠ 0) (hYq : Y / 2 ^ 51 % 2 = 1) :
    F m s r g (BitVec.ofInt 64 X) (BitVec.ofInt 64 Y) =
      BitVec.ofInt 64 (W (Pow.powTop (F64.toModel (BitVec.ofInt 64 X)) (F64.toModel (BitVec.ofInt 64 Y)))) := by
  pw_nan_case

/-- A word's fields over its `Int`. -/
theorem nan_int (X : Int) :
    (F64.isNaN (BitVec.ofInt 64 X) = true ↔ X / 2 ^ 52 % 2048 = 2047 ∧ X % 2 ^ 52 ≠ 0) ∧
      (BitVec.ofInt 64 X).toNat / 2 ^ 51 % 2 = (X / 2 ^ 51 % 2).toNat := by
  rw [Lua.Vm.Fn.Unorddf2.isNaN_fields]
  have h := Lua.Vm.Fn.FmodLens.ofInt_toNat X
  constructor
  · simp only [decide_eq_true_eq]; omega
  · omega

/-- **`Ieee754PowSpec_Statement`, proved.** -/
theorem spec_proved : PowR.Ieee754PowSpec_Statement := by
  intro m s r g x y hro hs hqx hqy
  have ex : x = BitVec.ofInt 64 x.toInt := BitVec.ofInt_toInt.symm
  have ey : y = BitVec.ofInt 64 y.toInt := BitVec.ofInt_toInt.symm
  have hX1 := BitVec.le_toInt x; have hX2 := BitVec.toInt_lt (x := x)
  have hY1 := BitVec.le_toInt y; have hY2 := BitVec.toInt_lt (x := y)
  simp only [Nat.reduceSub, Int.reducePow, Nat.reducePow, Int.reduceNeg] at hX1 hX2 hY1 hY2
  unfold PowR.NotSNaN at hqx hqy
  generalize x.toInt = X at ex hX1 hX2
  generalize y.toInt = Y at ey hY1 hY2
  subst ex ey
  obtain ⟨nX, qX⟩ := nan_int X
  obtain ⟨nY, qY⟩ := nan_int Y
  rw [nX, qX] at hqx; rw [nY, qY] at hqy
  rw [PowLens.bits_W, ieee754Pow_stage]
  by_cases hxn : X / 2 ^ 52 % 2048 = 2047 ∧ X % 2 ^ 52 ≠ 0 <;>
    by_cases hyn : Y / 2 ^ 52 % 2048 = 2047 ∧ Y % 2 ^ 52 ≠ 0
  · exact F_nan_nn m s r g X Y hro hs (by omega) (by omega) (by omega) (by omega)
      hxn.1 hxn.2 (by have := hqx hxn; omega) hyn.1 hyn.2 (by have := hqy hyn; omega)
  · exact F_nan_nx m s r g X Y hro hs (by omega) (by omega) (by omega) (by omega)
      hxn.1 hxn.2 (by have := hqx hxn; omega) hyn
  · exact F_nan_ny m s r g X Y hro hs (by omega) (by omega) (by omega) (by omega)
      hxn hyn.1 hyn.2 (by have := hqy hyn; omega)
  · have wx := W_in X (by omega) (by omega) hxn
    have wy := W_in Y (by omega) (by omega) hyn
    have := F_model m s r g (F64.toModel (BitVec.ofInt 64 X)) (F64.toModel (BitVec.ofInt 64 Y)) hro hs
    rwa [wx, wy] at this

end Lua.Vm.Fn.Ieee754Pow

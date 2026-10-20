import Lua.Vm.Fn.PowLeaves

/-!
# `__ieee754_pow`'s `exp2` tail at level (b) (lane float-sf7)

`e_pow.c:292-318`: the final scaling `exp2Fin` (`0x8002ccd0`, over `scalbn`'s
level-(b) `Scalbn.F_model`), the polynomial `exp2Poly` (`0x8002cb60`), and the
integer part `n` (`0x8002cf98`), one chamber per exponent `k` of the
generator `pw_chambers` (the machine shifts by `k`), joined by its cover
`n_cf98`; `exp2N` below and at the boundary (`e_cf88`, `e_caf4`), the
underflow and overflow tests (`e_cd38`, `e_caa4` over the stages `exp2Lo`,
`exp2Hi`), and `exp2Tail` (`exp2_ca2c`). Each is `pw_walk`
(`Lua/Vm/Fn/PowLens.lean`) over its cuts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Ieee754Pow

/-- `e_pow.c:314-318` at `0x8002ccd0`: `exp2Fin`. -/
theorem fin_ccd0 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v8 v9 v18 v19 : BitVec 64)
    (z sign : Float.Model) (n n20 : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31) (h20 : n20 = (n * 1048576).bmod 4294967296) :
    N_8002ccd0 m s r g v8 v9 (BitVec.ofInt 64 (W z)) v18 v19 (BitVec.ofInt 64 n) (BitVec.ofInt 64 n20)
        (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2Fin z (Int32.ofInt n) sign)) := by
  fn_sp_factsW
  subst h20
  unfold Pow.exp2Fin
  pw_lens_r
  pw_front
  pw_walk using [Scalbn.F_model]

/-- `e_pow.c:304-318` at `0x8002cb60`: `exp2Poly`. -/
theorem poly_cb60 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v8 v9 : BitVec 64)
    (p_l p_h z sign : Float.Model) (n n20 : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31) (h20 : n20 = (n * 1048576).bmod 4294967296)
    (hz : z = Float.Model.add p_l p_h) :
    N_8002cb60 m s r g v8 v9 (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 (W p_h))
        (BitVec.ofInt 64 (W p_l)) (BitVec.ofInt 64 n) (BitVec.ofInt 64 n20) (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2Poly p_l p_h (Int32.ofInt n) sign)) := by
  fn_sp_factsW
  subst h20 hz
  unfold Pow.exp2Poly
  pw_lens_r
  pw_walk using [fin_ccd0]

-- `e_pow.c:295-302` at `0x8002cf98`: `n` and `p_h - t`, one chamber per `k`.
pw_chambers n_cf98 [-1, 10] (iw / 1048576 - 1023)
    (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v8 v9 v20 v21 : BitVec 64)
    (p_l p_h sign : Float.Model) (j iw : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hj1 : -2 ^ 31 ≤ j) (hj2 : j < 2 ^ 31) (hiw : iw = j % 2147483648)
    (hi1 : 1071644672 < iw) (hi2 : iw ≤ 1083231232) :
    N_8002cf98 m s r g v8 v9 (BitVec.ofInt 64 j) (BitVec.ofInt 64 iw) (BitVec.ofInt 64 (W p_h))
        (BitVec.ofInt 64 (W p_l)) v20 v21 (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2N (Int32.ofInt j) p_l p_h sign)) := by
  fn_sp_factsW
  subst hiw
  unfold Pow.exp2N
  pw_lens_r
  pw_front
  pw_walk using [poly_cb60]

/-- `e_pow.c:292-318` at `0x8002cf88`: `exp2N` below the boundary. -/
theorem e_cf88 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v8 v9 v20 v21 : BitVec 64)
    (p_l p_h z sign : Float.Model) (j iw : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hj1 : -2 ^ 31 ≤ j) (hj2 : j < 2 ^ 31) (hiw : iw = j % 2147483648)
    (hi2 : iw < 1083231232) (hz : z = Float.Model.add p_l p_h) :
    N_8002cf88 m s r g v8 v9 (BitVec.ofInt 64 j) (BitVec.ofInt 64 iw) (BitVec.ofInt 64 (W z))
        (BitVec.ofInt 64 (W p_h)) (BitVec.ofInt 64 (W p_l)) v20 v21 (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2N (Int32.ofInt j) p_l p_h sign)) := by
  fn_sp_factsW
  subst hiw
  pw_walk using [n_cf98, poly_cb60]

/-- `e_pow.c:292-318` at `0x8002caf4`: `exp2N` at the boundary (`k = 10`). -/
theorem e_caf4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v8 v9 v20 v21 : BitVec 64)
    (p_l p_h sign : Float.Model) (j : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hj1 : -2 ^ 31 ≤ j) (hj2 : j < 2 ^ 31) (hk : j % 2147483648 / 1048576 - 1023 = 10) :
    N_8002caf4 m s r g v8 v9 (BitVec.ofInt 64 j) (BitVec.ofInt 64 (W p_h)) (BitVec.ofInt 64 (W p_l))
        v20 v21 (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2N (Int32.ofInt j) p_l p_h sign)) := by
  fn_sp_factsW
  unfold Pow.exp2N
  pw_lens_r
  pw_front
  pw_walk using [poly_cb60]

/-- `e_pow.c:282-318` at `0x8002cd38`: `exp2Lo`. -/
theorem e_cd38 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v9 v20 v21 : BitVec 64)
    (p_l p_h z sign : Float.Model) (j : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hz : z = Float.Model.add p_l p_h) (hj : j = W z / 4294967296) (hlt : j < 1083179008) :
    N_8002cd38 m s r g (BitVec.ofInt 64 (W p_l)) v9 (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 j)
        (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 (W p_h)) (BitVec.ofInt 64 (W p_l)) v20 v21
        (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2Lo p_l p_h sign)) := by
  fn_sp_factsW
  subst hj
  unfold Pow.exp2Lo
  simp only [← hz]
  pw_lens_r
  pw_front
  pw_walk using [e_cf88, e_caf4, uflow_v]

/-- `e_pow.c:276-318` at `0x8002caa4`: `exp2Hi`. -/
theorem e_caa4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v9 v20 v21 : BitVec 64)
    (p_l p_h z sign : Float.Model) (j : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hz : z = Float.Model.add p_l p_h) (hj : j = W z / 4294967296) (hge : 1083179008 ≤ j) :
    N_8002caa4 m s r g (BitVec.ofInt 64 (W p_l)) v9 (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 j)
        (BitVec.ofInt 64 (W p_h)) (BitVec.ofInt 64 (W p_l)) v20 v21 (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2Hi p_l p_h sign)) := by
  fn_sp_factsW
  subst hj
  unfold Pow.exp2Hi
  simp only [← hz]
  pw_lens_r
  pw_front
  pw_walk using [e_caf4, oflow_v]

/-- `e_pow.c:269-318` at `0x8002ca2c`: `exp2Tail`. -/
theorem exp2_ca2c (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (v9 v19 v20 v21 : BitVec 64)
    (y t1 t2 sign : Float.Model) (hro : RodataRead m) (hs : FnSp s 288) :
    N_8002ca2c m s r g (BitVec.ofInt 64 (W t1)) v9 (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 (W t2))
        v19 v20 v21 (BitVec.ofInt 64 (W sign)) =
      BitVec.ofInt 64 (W (Pow.exp2Tail y t1 t2 sign)) := by
  fn_sp_factsW
  rw [Pow.exp2Tail_split]
  pw_lens_r
  pw_front
  pw_walk using [e_cd38, e_caa4]

end Lua.Vm.Fn.Ieee754Pow

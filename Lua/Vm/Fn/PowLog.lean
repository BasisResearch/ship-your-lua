import Lua.Vm.Fn.PowExp

/-!
# `__ieee754_pow`'s `log2` part at level (b) (lane float-sf7)

`e_pow.c:220-318`, general case: from each of the three intervals of `|x|`'s
mantissa (`k`, `e_pow.c:229-231`) the series of `:232-266` into `exp2Tail`
(`e_ce14`, `e_cfc4`, `e_c708`: the stage `logExp`, one tactic `pw_logexp`),
the interval selection (`e_c6d4`: `logGenK`), the subnormal scaling
(`e_c69c`: `logGen`); `|y|` large and `x` near one (`e_ce40`: `logNear`);
`log2Split` and `exp2Tail` as one stage (`e_c458`: `log2Exp`). Each is
`pw_walk` over its cuts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Ieee754Pow

/-- The walk of `logExp` from one of the three interval paths into `0x8002c728`. -/
macro "pw_logexp" : tactic => `(tactic| (
  fn_sp_factsW
  unfold Lua.Num.Pow.logExp
  pw_lens_r
  pw_front
  pw_walk using [Lua.Vm.Fn.Ieee754Pow.exp2_ca2c, Lua.Vm.Fn.PowLens.floatsidf_l]))

/-- `e_pow.c:229,232-318` at `0x8002ce14` (`k = 0`). -/
theorem e_ce14 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg : Int) (n ix : Int)
    (hro : RodataRead m) (hs : FnSp s 288) (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31)
    (hi1 : 0x3ff00000 ≤ ix) (hi2 : ix < 0x40000000) :
    N_8002ce14 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 n) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 sg) =
      BitVec.ofInt 64 (W (Pow.logExp ax (Int32.ofInt 0) (Int32.ofInt n) (Int32.ofInt ix) y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  pw_logexp

/-- `e_pow.c:230,232-318` at `0x8002cfc4` (`k = 1`). -/
theorem e_cfc4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg : Int) (n ix : Int)
    (hro : RodataRead m) (hs : FnSp s 288) (hn1 : -2 ^ 31 ≤ n) (hn2 : n < 2 ^ 31)
    (hi1 : 0x3ff00000 ≤ ix) (hi2 : ix < 0x40000000) :
    N_8002cfc4 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 n) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 sg) =
      BitVec.ofInt 64 (W (Pow.logExp ax (Int32.ofInt 1) (Int32.ofInt n) (Int32.ofInt ix) y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  pw_logexp

/-- `e_pow.c:231-318` at `0x8002c708` (`k = 0`, the next binade). -/
theorem e_c708 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg : Int) (n ix : Int)
    (hro : RodataRead m) (hs : FnSp s 288) (hn1 : -2 ^ 31 ≤ n) (hn2 : n + 1 < 2 ^ 31)
    (hi1 : 0x3ff00000 ≤ ix) (hi2 : ix < 0x40000000) :
    N_8002c708 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 n) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 sg) =
      BitVec.ofInt 64 (W (Pow.logExp ax (Int32.ofInt 0) (Int32.ofInt (n + 1)) (Int32.ofInt (ix - 0x00100000)) y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  pw_logexp

/-- `e_pow.c:225-318` at `0x8002c6d4`: `n`, the interval `k`, `logExp`. -/
theorem e_c6d4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg : Int) (n0 ix : Int)
    (hro : RodataRead m) (hs : FnSp s 288) (hn1 : -53 ≤ n0) (hn2 : n0 ≤ 0)
    (hi1 : 0 ≤ ix) (hi2 : ix < 4294967296) :
    N_8002c6d4 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 n0)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 sg) =
      BitVec.ofInt 64 (W (Pow.logGenK ax (Int32.ofInt n0) (Int32.ofInt ix) y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  fn_sp_factsW
  unfold Pow.logGenK
  pw_lens_r
  pw_front
  pw_walk using [e_ce14, e_cfc4, e_c708]

/-- `e_pow.c:220-318` at `0x8002c69c`: subnormal `x` scaled (`:223-224`), `logGenK`. -/
theorem e_c69c (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg ix hx : Int)
    (hro : RodataRead m) (hs : FnSp s 288) (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31)
    (hix : ix = hx % 2147483648) :
    N_8002c69c m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 sg) (BitVec.ofInt 64 hx) =
      BitVec.ofInt 64 (W (Pow.logGen ax (Int32.ofInt ix) y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  fn_sp_factsW
  subst hix
  unfold Pow.logGen
  pw_lens_r
  pw_front
  pw_walk using [e_c6d4]

/-- `e_pow.c:212-318` at `0x8002ce40`: `|y|` large, `x` near one: `logNear`. -/
theorem e_ce40 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (ax y : Float.Model) (sg : Int)
    (hro : RodataRead m) (hs : FnSp s 288) :
    N_8002ce40 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 sg) =
      BitVec.ofInt 64 (W (Pow.logNear ax y (F64.toModel (BitVec.ofInt 64 sg)))) := by
  fn_sp_factsW
  unfold Pow.logNear
  pw_lens_r
  pw_walk using [exp2_ca2c]

/-- `e_pow.c:198-318` at `0x8002c458`: `log2Exp`. -/
theorem e_c458 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x ax y : Float.Model)
    (sg ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hax : ax = Pow.fabs x) :
    N_8002c458 m s r g (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 sg) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.log2Exp x (Int32.ofInt ix) (Int32.ofInt hy) (Int32.ofInt iy) y
        (F64.toModel (BitVec.ofInt 64 sg)))) := by
  fn_sp_factsW
  subst hix hiy
  unfold Pow.log2Exp
  simp only [← hax]
  pw_lens_r
  pw_front
  pw_walk using [e_ce40, e_c69c, oflow_v, uflow_v, oflow_0, uflow_0]

end Lua.Vm.Fn.Ieee754Pow

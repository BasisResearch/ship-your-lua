import Lua.Vm.Fn.PowSpecial

/-!
# `__ieee754_pow`'s `yisint` at level (b) (lane float-sf7)

`e_pow.c:137-150` with the special `y` the machine tests on the way
(`:153-170`): for a negative `x` and `1 ≤ |y| < 2^53` the machine shifts `y`'s
words by its exponent `k`, so the walk is one chamber per `k` of the
generator `pw_chambers` (`e_c580.«k»`), joined by the cover `e_c580`;
`|y| ≥ 2^53` (`e_c3b4`), `|y| < 2^53` (`e_c578`), a negative `x`
(`e_c3ac`), a positive one (`e_c37c`), and both (`e_c374`): `powYi` at
`yisint`, the stage `yisint` unfolded where the walk reaches its value.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Ieee754Pow

-- `e_pow.c:137-318` at `0x8002c580`: `x < 0`, `1 ≤ |y| < 2^53`: `yisint` by the
-- exponent `k` of `y` (the machine shifts by `k`), one chamber per `k`.
pw_chambers e_c580 [0, 52] (iy / 1048576 - 1023)
    (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 0) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296) :
    N_8002c580 m s r g (BitVec.ofInt 64 1072693248) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x))
        (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  unfold Pow.yisint
  pw_model_r
  pw_shift_fix
  pw_model_r
  pw_front
  pw_walk using [e_c5a4, e_cd9c, e_c3c4, e_c4fc]

/-- `e_pow.c:137-318` at `0x8002c3b4`: `x < 0`, `|y| ≥ 2^53` (`yisint = 2`). -/
theorem e_c3b4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hnx : ix ≤ 2146435072) (hny : iy ≤ 2146435072) (hneg : hx < 0) (hbig : 1128267776 ≤ iy) :
    N_8002c3b4 m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  pw_model_r
  pw_front
  pw_walk using [e_c3c4, e_c4fc]

/-- `e_pow.c:137-318` at `0x8002c578`: `x < 0`, `|y| < 2^53`. -/
theorem e_c578 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hnx : ix ≤ 2146435072) (hny : iy ≤ 2146435072) (hneg : hx < 0) (hsmall : iy < 1128267776) :
    N_8002c578 m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  pw_model_r
  pw_front
  pw_walk using [e_c580, e_c5a4, e_cd9c, e_c3c4, e_c4fc]

/-- `e_pow.c:137-318` at `0x8002c3ac`: `x < 0`. -/
theorem e_c3ac (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hnx : ix ≤ 2146435072) (hny : iy ≤ 2146435072) (hneg : hx < 0) :
    N_8002c3ac m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  pw_model_r
  pw_front
  pw_walk using [e_c3b4, e_c578]

/-- `e_pow.c:137-318` at `0x8002c37c`: `x ≥ 0` (`yisint = 0`). -/
theorem e_c37c (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hnx : ix ≤ 2146435072) (hny : iy ≤ 2146435072) (hpos : 0 ≤ hx) :
    N_8002c37c m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  pw_model_r
  pw_front
  pw_walk using [e_c3c4, e_c4fc]

/-- `e_pow.c:137-318` at `0x8002c374`: past the NaN tests, `powYi` at `yisint`. -/
theorem e_c374 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296)
    (hWy : W y / 4294967296 = hy) (hLy : W y % 4294967296 = ly % 4294967296)
    (hnx : ix ≤ 2146435072) (hny : iy ≤ 2146435072) :
    N_8002c374 m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy)
        (Pow.yisint (Int32.ofInt hx) (Int32.ofInt iy) (UInt32.ofInt ly)))) := by
  fn_sp_factsW
  pw_model_r
  pw_front
  pw_walk using [e_c3ac, e_c37c]

end Lua.Vm.Fn.Ieee754Pow

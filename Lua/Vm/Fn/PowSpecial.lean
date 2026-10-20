import Lua.Vm.Fn.PowLog

/-!
# `__ieee754_pow` past the special `y` at level (b) (lane float-sf7)

`e_pow.c:172-318` over the stages of `Lua/Vm/Fn/PowStage.lean`: the sign
(`e_c444`: `powSign`), the negative `x` with a non-integer `y` (`e_c418`:
`powNY`), `x = ±0, ±∞, ±1` (`e_c61c`: `powXZ`, `e_c618`; the sign flip of a
datum that is not a NaN, `negW_l`, its premise by `pw_notnan`), and their
join for `lx = 0` (`e_c600`: `powAx0`), and `powAx` (`e_c3c4`; `e_c4fc` where
`(n | yi) ≠ 0` and the machine skips the test `:191`); a negative `x` with
`|y| < 1` (`e_cd9c`: `powAxN`, `e_c5a4`: `powYi` at `yisint = 0`). Each is `pw_walk` over its cuts.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim Lua.Vm.Fn.FmodLens Lua.Vm.Fn.PowLens Lua.Num

namespace Lua.Vm.Fn.Ieee754Pow

/-- `e_pow.c:193-318` at `0x8002c444`: `powSign`. -/
theorem e_c444 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x ax y : Float.Model)
    (yi n ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hax : ax = Pow.fabs x)
    (hn1 : -1 ≤ n) (hn2 : n ≤ 0) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2) :
    N_8002c444 m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 n) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powSign x y (Int32.ofInt ix) (Int32.ofInt hy) (Int32.ofInt iy)
        (Int32.ofInt n) (Int32.ofInt yi))) := by
  fn_sp_factsW
  unfold Pow.powSign
  pw_lens_r
  pw_front
  pw_walk using [e_c458]

/-- `e_pow.c:190-318` at `0x8002c418`: `powNY`. -/
theorem e_c418 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x ax y : Float.Model)
    (yi ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hax : ax = Pow.fabs x)
    (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2) :
    N_8002c418 m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W x))
        (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powNY x y (Int32.ofInt hx) (Int32.ofInt ix) (Int32.ofInt hy)
        (Int32.ofInt iy) (Int32.ofInt yi))) := by
  fn_sp_factsW
  unfold Pow.powNY
  pw_lens_r
  pw_front
  pw_walk using [e_c444]

/-- `e_pow.c:179-183` at `0x8002c620`: `powXZn`. -/
theorem e_c620 (s : Nat) (r : BitVec 64) (z : Float.Model) (yi ix : Int)
    (hi1 : 0 ≤ ix) (hi2 : ix < 2147483648) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hz : ¬ (W z / 2 ^ 52 % 2048 = 2047 ∧ W z % 2 ^ 52 ≠ 0)) :
    N_8002c620 s r (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 ix) =
      BitVec.ofInt 64 (W (Pow.powXZn z (Int32.ofInt ix) (Int32.ofInt yi))) := by
  unfold Pow.powXZn
  pw_lens_r
  pw_front
  pw_walk

/-- `e_pow.c:178-185` at `0x8002c61c`: `powXZ`. -/
theorem e_c61c (s : Nat) (r : BitVec 64) (z : Float.Model) (yi ix hx : Int)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hix : ix = hx % 2147483648) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hz : ¬ (W z / 2 ^ 52 % 2048 = 2047 ∧ W z % 2 ^ 52 ≠ 0)) :
    N_8002c61c s r (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W z)) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) =
      BitVec.ofInt 64 (W (Pow.powXZ z (Int32.ofInt hx) (Int32.ofInt ix) (Int32.ofInt yi))) := by
  subst hix
  unfold Pow.powXZ
  pw_lens_r
  pw_front
  pw_walk using [e_c620]

/-- `e_pow.c:177-185` at `0x8002c618`: `x` is `±0`, `±∞` or `±1`. -/
theorem e_c618 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x ax : Float.Model)
    (yi ix hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hax : ax = Pow.fabs x) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = 0)
    (hcls : ix = 2146435072 ∨ ix = 1072693248 ∨ ix = 0) :
    N_8002c618 m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) =
      BitVec.ofInt 64 (W (Pow.powXZ (if hy < 0 then (F64.toModel (BitVec.ofInt 64 4607182418800017408)).div ax else ax)
        (Int32.ofInt hx) (Int32.ofInt ix) (Int32.ofInt yi))) := by
  fn_sp_factsW
  pw_lens_r
  pw_front
  pw_walk using [e_c61c]

/-- `e_pow.c:172-318` at `0x8002c600` (`lx = 0`): `powAx0`. -/
theorem e_c600 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x ax y : Float.Model)
    (yi ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hax : ax = Pow.fabs x)
    (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = 0) :
    N_8002c600 m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 (W ax)) (BitVec.ofInt 64 (W x))
        (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powAx0 x y (Int32.ofInt hx) (Int32.ofInt ix)
        (Int32.ofInt hy) (Int32.ofInt iy) (Int32.ofInt yi))) := by
  fn_sp_factsW
  unfold Pow.powAx0
  simp only [← hax]
  pw_lens_r
  pw_front
  pw_walk using [e_c618, e_c418]

/-- `e_pow.c:172-318` at `0x8002c3c4`: `powAx`. -/
theorem e_c3c4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (yi lx ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296) :
    N_8002c3c4 m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x))
        (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powAx x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (Int32.ofInt iy) (Int32.ofInt yi))) := by
  fn_sp_factsW
  unfold Pow.powAx
  pw_lens_r
  pw_front
  pw_walk using [e_c600, e_c418]

/-- `e_pow.c:172-318` at `0x8002c4fc`: `powAx` where `(n | yi) ≠ 0`. -/
theorem e_c4fc (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (yi lx ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 2 ^ 31) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hyi1 : 0 ≤ yi) (hyi2 : yi ≤ 2)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296) (hny : 0 ≤ hx ∨ yi ≠ 0) :
    N_8002c4fc m s r g (BitVec.ofInt 64 yi) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x))
        (BitVec.ofInt 64 (W y)) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powAx x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (Int32.ofInt iy) (Int32.ofInt yi))) := by
  fn_sp_factsW
  unfold Pow.powAx
  pw_lens_r
  pw_front
  pw_walk using [e_c600, e_c444]

/-- `e_pow.c:172-191` at `0x8002cd9c`: `powAxN` (`x < 0`, `yisint = 0`). -/
theorem e_cd9c (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x : Float.Model)
    (lx ix hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 0) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hix : ix = hx % 2147483648)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296) :
    N_8002cd9c m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) =
      BitVec.ofInt 64 (W (Pow.powAxN x (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix) (Int32.ofInt hy))) := by
  fn_sp_factsW
  unfold Pow.powAxN Pow.powXZ
  pw_lens_r
  pw_front
  pw_walk using [e_c620]

/-- `e_pow.c:137-318` at `0x8002c5a4`: `powYi` for `x < 0`, `|y| < 1` (`yisint = 0`). -/
theorem e_c5a4 (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : Float.Model)
    (lx ly ix iy hx hy : Int) (hro : RodataRead m) (hs : FnSp s 288)
    (hx1 : -2 ^ 31 ≤ hx) (hx2 : hx < 0) (hy1 : -2 ^ 31 ≤ hy) (hy2 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hix : ix = hx % 2147483648) (hiy : iy = hy % 2147483648) (hiy1 : iy < 1072693248)
    (hW : W x / 4294967296 = hx) (hL : W x % 4294967296 = lx % 4294967296) :
    N_8002c5a4 m s r g (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (W x)) (BitVec.ofInt 64 (W y))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 iy) =
      BitVec.ofInt 64 (W (Pow.powYi x y (Int32.ofInt hx) (UInt32.ofInt lx) (Int32.ofInt ix)
        (Int32.ofInt hy) (UInt32.ofInt ly) (Int32.ofInt iy) (Int32.ofInt 0))) := by
  fn_sp_factsW
  unfold Pow.powYi
  simp only [Lua.Vm.Fn.PowLens.powAx_neg0 x y hx _ _ _ _ hx1 hx2]
  unfold Pow.powAxN
  pw_model_r
  pw_front
  pw_walk using [e_cd9c, e_c618, e_c418]

end Lua.Vm.Fn.Ieee754Pow

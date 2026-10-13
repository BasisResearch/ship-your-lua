import Lua.Vm.Fn.FmodLoop

/-!
# `__ieee754_fmod`'s loop entries (lane float-sf5, (b1))

`e_fmod.c:102-112` once both operands are set up (`hx:lx`, `hy:ly`
normalised to `[2^52, 2^53)`, `n = ix - iy`): the counter set up at
`0x8002bf28` (`N = n`, from `0x8002bf24`, `0x8002bea4`), the loop
(`loop_bf60`), or for `n = 0` the last subtraction directly (`0x8002bfd0`).
Each gives the remainder `X · 2^n mod Y` packed (`outv`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

section entry
variable {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hy ly : Int)
  (h5 : sx = 0 ∨ sx = 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 21) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
  (hY1 : 2 ^ 52 ≤ hy * 2 ^ 32 + ly % 2 ^ 32) (hiy : iy ≤ 1023)

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- The counter's set-up (`0x8002bf28`: `N = n`) and the loop, `n ≥ 1`. -/
theorem entry_bf28 (n hx lx : Int) (hn1 : 1 ≤ n) (hn2 : n < 2 ^ 31) (hx0 : 0 ≤ hx)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31)
    (hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32))
    (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat)) :
    N_8002bf28 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (n - 1)) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bf28 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (n - 1)) = true := by
  unfold N_8002bf28 T_8002bf28
  fm_nf
  obtain ⟨j, hj⟩ : ∃ j : Nat, n.toNat = j + 1 := ⟨n.toNat - 1, by omega⟩
  have hn : (n - 1 + 1) * 4294967296 % 18446744073709551616 / 4294967296 = 0 + ((j + 1 : Nat) : Int) := by
    omega
  rw [hn, hj]
  exact loop_bf60 hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy j Lua.Vm.Sim.fnFuel 0 _ hx lx
    (by unfold Lua.Vm.Sim.fnFuel; omega) rfl (by omega) (by omega) hx0 hl1 hl2 hX (by rw [← hj]; exact hlow)

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- `0x8002bf24`: the loop for `n = ix - iy ≥ 1`. -/
theorem entry_bf24 (n hx lx : Int) (hn1 : 1 ≤ n) (hn2 : n < 2 ^ 31) (hx0 : 0 ≤ hx)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31)
    (hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32))
    (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat)) :
    N_8002bf24 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 n)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bf24 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 n)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
  unfold N_8002bf24 T_8002bf24
  fm_nf
  rw [show n + -1 = n - 1 by omega]
  exact entry_bf28 hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy n hx lx hn1 hn2 hx0 hl1 hl2 hX hlow

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- `0x8002bfd0`: the loop for `n = ix - iy ≥ 1`, the last subtraction for
`n = 0`. -/
theorem entry_bfd0 (ix hx lx : Int) (hn1 : iy ≤ ix) (hn2 : ix - iy < 2 ^ 31) (hx0 : 0 ≤ hx)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hix : -2 ^ 31 ≤ ix) (hix2 : ix < 2 ^ 31)
    (hiy2 : -2 ^ 31 ≤ iy)
    (hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32))
    (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
      (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat)) :
    N_8002bfd0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bfd0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) = true := by
  unfold N_8002bfd0 T_8002bfd0
  fm_nf
  by_cases h0 : ix = iy
  · subst h0
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one] at hlow ⊢
    have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
    have h0 : 0 ≤ (hx * 2 ^ 32 + lx % 2 ^ 32) % (hy * 2 ^ 32 + ly % 2 ^ 32) := Int.emod_nonneg _ (by omega)
    apply fin_bfd8 hro s r ix sx hx lx hy ly _ h5 hx0 hy0 hy1 hl1 hl2 hm1 hm2 hY1 hX _ hiy hlow
    rw [Int.toNat_of_nonneg h0, mod2 _ _ (by omega) hX]
  · rw [if_pos (by omega), if_pos (by omega)]
    exact entry_bf24 hro s r iy sx hy ly h5 hy0 hy1 hm1 hm2 hY1 hiy (ix - iy) hx lx (by omega) hn2 hx0 hl1 hl2
      hX hlow

include hro h5 hy0 hy1 hm1 hm2 hY1 hiy in
/-- `0x8002bea4`: the loop with `ly = 0` (`y` set up from its low word alone). -/
theorem entry_bea4 (n hx lx : Int) (hn1 : 1 ≤ n) (hn2 : n < 2 ^ 31) (hx0 : 0 ≤ hx)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hly : ly = 0)
    (hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32))
    (hlow : LowOk iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat)) :
    N_8002bea4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 n) =
      outv sx iy ((((hx * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ n.toNat) % (hy * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bea4 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 n) = true := by
  unfold N_8002bea4 T_8002bea4
  fm_nf
  subst hly
  rw [show n + -1 = n - 1 by omega]
  exact entry_bf28 hro s r iy sx hy 0 h5 hy0 hy1 hm1 hm2 hY1 hiy n hx lx hn1 hn2 hx0 hl1 hl2 hX hlow

end entry

end Lua.Vm.Fn.Ieee754Fmod

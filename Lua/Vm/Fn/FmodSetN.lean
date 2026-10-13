import Lua.Vm.Fn.FmodSetX

/-!
# `__ieee754_fmod`'s set-ups of a normal `x` (lane float-sf5, (b1))
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- **A normal `x`, a subnormal `y`** (`e_fmod.c:80-81`, then `y`'s set-up;
`0x8002c098`): the hidden bit or-ed into `x`'s high word. -/
theorem x_c098 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (iy sx ix hxr lx hy ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hxr0 : 0 ≤ hxr) (hxr1 : hxr < 2 ^ 32)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hix1 : -1022 ≤ ix) (hix2 : ix ≤ 1023) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1023)
    (hY1 : 2 ^ 52 ≤ (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)
    (hY2 : (hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
    (hlow : LowOk iy ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
      ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat)) :
    N_8002c098 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) =
      outv sx iy ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ix - iy).toNat) %
        ((hy * 2 ^ 32 + ly % 2 ^ 32) * 2 ^ (-1022 - iy).toNat)).toNat) ∧
    T_8002c098 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) = true := by
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hh := Int.emod_nonneg hxr (show (2 : Int) ^ 20 ≠ 0 by decide)
  have hh2 := Int.emod_lt_of_pos hxr (show (0 : Int) < 2 ^ 20 by decide)
  unfold N_8002c098 T_8002c098
  fm_nf
  have hyx := y_sub hro s r iy sx ix (1048576 + hxr % 1048576) lx hy ly h5 (by omega) hl1 hl2 hy0 hy1 hm1 hm2
    (by omega) hiy1 hiy2 hY1 hY2 (by omega) (by omega) hix2
    (by simp only [Int.reducePow] at hlow ⊢; rw [show 1048576 + hxr % 1048576 = 1048576 + hxr % 1048576 from rfl];
        exact hlow)
  by_cases hb : iy < -1053
  · rw [if_pos hb, if_pos hb]
    rw [if_neg (by omega), if_neg (by omega)] at hyx
    simp only [Int.reducePow] at hyx ⊢; exact hyx
  · rw [if_neg hb, if_neg hb]
    rw [if_pos (by omega), if_pos (by omega)] at hyx
    simp only [Int.reducePow] at hyx ⊢; exact hyx

/-- **Both normal** (`e_fmod.c:72, 80-81, 89-90`, `0x8002bfa8`): `iy` from
`y`'s exponent field, the hidden bits or-ed in, then the loop entry. -/
theorem x_bfa8 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (sx ix hxr lx hya hyr ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hxr0 : 0 ≤ hxr) (hxr1 : hxr < 2 ^ 32)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hya0 : 2 ^ 20 ≤ hya) (hya1 : hya < 2047 * 2 ^ 20)
    (hyr0 : 0 ≤ hyr) (hyr1 : hyr < 2 ^ 32) (hyr2 : hyr % 2 ^ 20 = hya % 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hix1 : hya / 2 ^ 20 - 1023 ≤ ix) (hix2 : ix ≤ 1023)
    (hlow : LowOk (hya / 2 ^ 20 - 1023) ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) *
      2 ^ (ix - (hya / 2 ^ 20 - 1023)).toNat) % (((2 : Int) ^ 20 + hya % 2 ^ 20) * 2 ^ 32 + ly % 2 ^ 32)).toNat)) :
    N_8002bfa8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hya)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) (BitVec.ofInt 64 hyr) =
      outv sx (hya / 2 ^ 20 - 1023) ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) *
        2 ^ (ix - (hya / 2 ^ 20 - 1023)).toNat) % (((2 : Int) ^ 20 + hya % 2 ^ 20) * 2 ^ 32 + ly % 2 ^ 32)).toNat) ∧
    T_8002bfa8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hya)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) (BitVec.ofInt 64 hyr) = true := by
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hly := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hh := Int.emod_nonneg hxr (show (2 : Int) ^ 20 ≠ 0 by decide)
  have hh2 := Int.emod_lt_of_pos hxr (show (0 : Int) < 2 ^ 20 by decide)
  have hy := Int.emod_nonneg hya (show (2 : Int) ^ 20 ≠ 0 by decide)
  have hy2 := Int.emod_lt_of_pos hya (show (0 : Int) < 2 ^ 20 by decide)
  have step : N_8002bfa8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hya)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) (BitVec.ofInt 64 hyr) =
      N_8002bfd0 m s r (BitVec.ofInt 64 (hya / 2 ^ 20 - 1023)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 (2 ^ 20 + hya % 2 ^ 20)) (BitVec.ofInt 64 (2 ^ 20 + hxr % 2 ^ 20))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) ∧
      T_8002bfa8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hya)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 hxr) (BitVec.ofInt 64 hyr) =
      T_8002bfd0 m s r (BitVec.ofInt 64 (hya / 2 ^ 20 - 1023)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 (2 ^ 20 + hya % 2 ^ 20)) (BitVec.ofInt 64 (2 ^ 20 + hxr % 2 ^ 20))
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) := by
    unfold N_8002bfa8 T_8002bfa8
    fm_nf
    rw [show hyr % 1048576 = hya % 1048576 by simpa using hyr2, show hya / 1048576 + -1023 = hya / 1048576 - 1023 by omega]
    exact ⟨rfl, rfl⟩
  rw [step.1, step.2]
  exact entry_bfd0 hro s r (hya / 2 ^ 20 - 1023) sx (2 ^ 20 + hya % 2 ^ 20) ly h5 (by omega) (by omega) hm1 hm2
    (by omega) (by omega) ix (2 ^ 20 + hxr % 2 ^ 20) lx
    (by omega) (by omega) (by omega) hl1 hl2 (by omega) (by omega) (by omega) (by omega) hlow

/-- **A normal `x`, a subnormal `y` with `hy = 0` and bit 31 of `ly` set**
(`iy = -1043`; `y` shifted by 21: `0x8002c15c`), then the loop. -/
theorem x_c15c {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (ex sx hxr lx ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hxr0 : 0 ≤ hxr) (hxr1 : hxr < 2 ^ 32)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 0)
    (hex1 : 1 ≤ ex) (hex2 : ex ≤ 2046)
    (hlow : LowOk (-1043) ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ex + 20).toNat) %
      ((ly % 2 ^ 32) * 2 ^ 21)).toNat)) :
    N_8002c15c m s r (BitVec.ofInt 64 ex) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 hxr) =
      outv sx (-1043) ((((((2 : Int) ^ 20 + hxr % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) * 2 ^ (ex + 20).toNat) %
        ((ly % 2 ^ 32) * 2 ^ 21)).toNat) ∧
    T_8002c15c m s r (BitVec.ofInt 64 ex) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 hxr) = true := by
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hh := Int.emod_nonneg hxr (show (2 : Int) ^ 20 ≠ 0 by decide)
  have hh2 := Int.emod_lt_of_pos hxr (show (0 : Int) < 2 ^ 20 by decide)
  obtain ⟨b1, b2, b3⟩ := shl_facts ly (2 ^ 21)
  have step : N_8002c15c m s r (BitVec.ofInt 64 ex) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 hxr) =
      N_8002bf24 m s r (BitVec.ofInt 64 (-1043)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ex + 20))
        (BitVec.ofInt 64 (ly % 4294967296 / 2048)) (BitVec.ofInt 64 (1048576 + hxr % 1048576))
        (BitVec.ofInt 64 ((ly * 2097152).bmod 4294967296)) ∧
      T_8002c15c m s r (BitVec.ofInt 64 ex) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 hxr) =
      T_8002bf24 m s r (BitVec.ofInt 64 (-1043)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ex + 20))
        (BitVec.ofInt 64 (ly % 4294967296 / 2048)) (BitVec.ofInt 64 (1048576 + hxr % 1048576))
        (BitVec.ofInt 64 ((ly * 2097152).bmod 4294967296)) := by
    unfold N_8002c15c T_8002c15c
    fm_nf
    exact ⟨trivial, trivial⟩
  rw [step.1, step.2]
  simp only [Int.reducePow] at b1 b2 b3
  have hYe : (ly % 2 ^ 32) * 2 ^ 21 = (ly % 4294967296 / 2048) * 2 ^ 32 + (ly * 2097152).bmod 4294967296 % 2 ^ 32 := by
    omega
  rw [hYe] at hlow ⊢
  have hn : (ex + 20).toNat = (ex + 20).toNat := rfl
  exact entry_bf24 hro s r (-1043) sx (ly % 4294967296 / 2048) ((ly * 2097152).bmod 4294967296) h5 (by omega)
    (by omega) b2 b3 (by omega) (by omega) (ex + 20) (1048576 + hxr % 1048576) lx (by omega) (by omega) (by omega)
    hl1 hl2 (by omega) hlow

end Lua.Vm.Fn.Ieee754Fmod

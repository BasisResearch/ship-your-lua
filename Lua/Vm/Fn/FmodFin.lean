import Lua.Vm.Fn.FmodNorm
import Lua.Num.SfRefFmod

/-!
# `__ieee754_fmod`'s last subtraction and its zeros (lane float-sf5, (b1))

* `Zero[sx]` (`e_fmod.c:31`, `.rodata` at `0x80054030`: `+0.0`, `-0.0`), read
  at `0x8002bf78` (`Zero[(uint32_t)sx>>31]`, the sign shifted by `srliw 31`)
  and at `0x8002c1fc` (by `srli 28` of the raw sign word): `ld_bf78`,
  `ld_c1fc`;
* the last subtraction (`e_fmod.c:111-112`, from `0x8002bfd8`): `R = X - Y`
  if `X ≥ Y`, else `X`; zero (`Zero[sx]`), or normalised (`norm_c008`) and
  packed (`pack_c020v`): `fin_bfd8`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

theorem zero_bytes : ∀ j, j < 16 → Image.rodataByte (0x80054030 - Image.rodataBase + j) =
    (if j = 15 then 0x80#8 else 0#8) := by
  decide +kernel

/-- `Zero[b]`. -/
theorem zero_ld {m : Mem} (hro : RodataRead m) (b : Nat) (hb : b < 2) :
    bytesT8 m (0x80054030 + 8 * b) = BitVec.ofInt 64 (b * 2 ^ 63) := by
  have hbyte : ∀ j, j < 16 → bytesT1 m (0x80054030 + j) = (if j = 15 then 0x80#8 else 0#8) := by
    intro j hj
    have := hro (0x80054030 - Image.rodataBase + j) (by simp only [Image.rodataBase, Image.rodataSize]; omega)
    rw [show Image.rodataBase + (0x80054030 - Image.rodataBase + j) = 0x80054030 + j by
      simp only [Image.rodataBase]; omega] at this
    rw [this]; exact zero_bytes j hj
  rcases (by omega : b = 0 ∨ b = 1) with rfl | rfl
  · have h0 := hbyte 0 (by omega)
    simp only [bytesT1, Nat.add_zero] at h0 hbyte
    simp only [Nat.mul_zero, Nat.add_zero, bytesT8, h0, hbyte 1 (by omega), hbyte 2 (by omega),
      hbyte 3 (by omega), hbyte 4 (by omega), hbyte 5 (by omega), hbyte 6 (by omega), hbyte 7 (by omega)]
    decide +kernel
  · simp only [bytesT1] at hbyte
    simp only [bytesT8, show 0x80054030 + 8 * 1 = 0x80054030 + 8 by rfl, hbyte 8 (by omega),
      show 0x80054030 + 8 + 1 = 0x80054030 + 9 by rfl, hbyte 9 (by omega),
      show 0x80054030 + 8 + 2 = 0x80054030 + 10 by rfl, hbyte 10 (by omega),
      show 0x80054030 + 8 + 3 = 0x80054030 + 11 by rfl, hbyte 11 (by omega),
      show 0x80054030 + 8 + 4 = 0x80054030 + 12 by rfl, hbyte 12 (by omega),
      show 0x80054030 + 8 + 5 = 0x80054030 + 13 by rfl, hbyte 13 (by omega),
      show 0x80054030 + 8 + 6 = 0x80054030 + 14 by rfl, hbyte 14 (by omega),
      show 0x80054030 + 8 + 7 = 0x80054030 + 15 by rfl, hbyte 15 (by omega)]
    decide +kernel

theorem ld_bf78 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) :
    N_8002bf78 m s r (BitVec.ofInt 64 sx) = BitVec.ofInt 64 (sx * 2 ^ 32) := by
  unfold N_8002bf78
  fm_nf
  rcases h5 with rfl | rfl
  · rw [show (BitVec.ofInt 64 (2147827760 + 0 % 4294967296 / 2147483648 * 8)).toNat = 0x80054030 + 8 * 0 by
      decide, zero_ld hro 0 (by decide), BitVec.ofInt_toInt]
    decide
  · rw [show (BitVec.ofInt 64 (2147827760 + 2 ^ 31 % 4294967296 / 2147483648 * 8)).toNat = 0x80054030 + 8 * 1 by
      decide, zero_ld hro 1 (by decide), BitVec.ofInt_toInt]
    decide

theorem ld_c1fc {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) :
    N_8002c1fc m s r (BitVec.ofInt 64 sx) = BitVec.ofInt 64 (sx * 2 ^ 32) := by
  unfold N_8002c1fc
  fm_nf
  rcases h5 with rfl | rfl
  · rw [show (BitVec.ofInt 64 (2147827760 + 0 % 18446744073709551616 / 268435456)).toNat = 0x80054030 + 8 * 0 by
      decide, zero_ld hro 0 (by decide), BitVec.ofInt_toInt]
    decide
  · rw [show (BitVec.ofInt 64 (2147827760 + 2 ^ 31 % 18446744073709551616 / 268435456)).toNat =
      0x80054030 + 8 * 1 by decide, zero_ld hro 1 (by decide), BitVec.ofInt_toInt]
    decide

/-- The result of a remainder `R` at exponent `iy` (`e_fmod.c:114-138`):
`Zero[sx]`, or `R` normalised to bit 52 and packed. -/
def outv (sx iy : Int) (R : Nat) : BitVec 64 :=
  if R = 0 then BitVec.ofInt 64 (sx * 2 ^ 32)
  else packv sx (iy - ((52 - R.log2 : Nat) : Int)) ((R : Int) * 2 ^ (52 - R.log2))

/-- The zero test and the conversion back of a remainder `R = hz:lz`
(`e_fmod.c:114-138`, from `0x8002bff0`). -/
theorem fin_bff0 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hz lz : Int)
    (R : Nat) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hz0 : 0 ≤ hz) (hz1 : hz < 2 ^ 21)
    (hl1 : -2 ^ 31 ≤ lz) (hl2 : lz < 2 ^ 31) (hR : (R : Int) = hz * 2 ^ 32 + lz % 2 ^ 32)
    (hiy : iy ≤ 1023) (hlow : R ≠ 0 → -1074 ≤ iy - ((52 - R.log2 : Nat) : Int)) :
    N_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz) (BitVec.ofInt 64 lz) =
      outv sx iy R ∧
    T_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hz) (BitVec.ofInt 64 lz) = true := by
  have hR53 : R < 2 ^ 53 := by
    have : (R : Int) < 2 ^ 53 := by
      have := Int.emod_lt_of_pos lz (show (0 : Int) < 2 ^ 32 by decide); omega
    exact_mod_cast this
  unfold N_8002bff0 T_8002bff0
  fm_nf
  by_cases hR0 : R = 0
  · rw [if_pos (by omega), if_pos (by omega), ld_bf78 hro s r sx h5]
    unfold outv; rw [if_pos hR0]; exact ⟨rfl, rfl⟩
  rw [if_neg (by omega), if_neg (by omega)]
  have hpos : 0 < R := Nat.pos_of_ne_zero hR0
  obtain ⟨hn1, hn2⟩ := Lua.Num.SfRef.norm52 hpos hR53
  have hL := Lua.Num.SfRef.log2_lt53 hR53
  have hlo := hlow hR0
  unfold outv; rw [if_neg hR0]
  unfold N_8002bffc T_8002bffc N_8002c004 T_8002c004
  fm_nf
  by_cases hbig : 2 ^ 52 ≤ R
  · have hl52 : R.log2 = 52 := by
      have := Lua.Num.F64.le_log2_of hbig; omega
    rw [if_pos (by omega), if_pos (by omega)]
    refine ⟨?_, rfl⟩
    rw [pack_c020v s r iy sx hz lz _ (by omega) hiy (by omega) hz1 h5 hl1 hl2 rfl]
    simp only [hl52, Nat.sub_self, Int.natCast_zero, Int.sub_zero, Int.pow_zero, Int.mul_one]
    congr 1; omega
  · rw [if_neg (by omega), if_neg (by omega)]
    have hz1' : 1 ≤ 52 - R.log2 := by
      have : R.log2 < 52 := (Nat.log2_lt (by omega)).2 (by omega)
      omega
    have h1 : (2 : Int) ^ 52 ≤ (R : Int) * 2 ^ (52 - R.log2) := by exact_mod_cast hn1
    have h2 : (R : Int) * 2 ^ (52 - R.log2) < 2 ^ 53 := by exact_mod_cast hn2
    rw [hR] at h1 h2
    obtain ⟨hN, hT⟩ := norm_c008 s r sx h5 (52 - R.log2) Lua.Vm.Sim.fnFuel iy hz lz _ hz1'
      (by unfold Lua.Vm.Sim.fnFuel; omega) hz0 hl1 hl2 rfl h1 h2 hlo hiy
    rw [hR]; exact ⟨hN, hT⟩

/-- The last subtraction's words (`e_fmod.c:111-112`): the borrow, then
`hz:lz` kept when `hz ≥ 0`. -/
theorem sub_bfd8 (m : Mem) (s : Nat) (r : BitVec 64) (iy sx hx lx hy ly lz : Int)
    (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 22) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 22)
    (hb2 : -2147483648 ≤ lz) (hb3 : lz < 2147483648)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31) :
    let b : Int := if ly % 4294967296 ≤ lx % 4294967296 then 0 else 1
    N_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 lz) =
      (if 0 ≤ hx - hy - b then
        N_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 (hx - hy - b)) (BitVec.ofInt 64 lz)
      else N_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx)) ∧
    T_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 lz) =
      (if 0 ≤ hx - hy - b then
        T_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 (hx - hy - b)) (BitVec.ofInt 64 lz)
      else T_8002bff0 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 lx)) := by
  intro b
  unfold N_8002bfd8 T_8002bfd8 N_8002bfe0 T_8002bfe0 N_8002bfe4 T_8002bfe4 N_8002bfe8 T_8002bfe8
  fm_nf
  by_cases hc : ly % 4294967296 ≤ lx % 4294967296
  · have hb : b = 0 := if_pos hc
    rw [hb]
    fm_nf
    trivial
  · have hb : b = 1 := if_neg hc
    rw [hb]
    fm_nf
    simp only [show hx - hy + -1 = hx - hy - 1 by omega]
    trivial

/-- **The last subtraction** (`e_fmod.c:111-112`, from `0x8002bfd8`) and the
conversion back: `R = X - Y` if `X ≥ Y`, else `X`. -/
theorem fin_bfd8 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hx lx hy ly : Int)
    (R : Nat) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 21)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hY1 : 2 ^ 52 ≤ hy * 2 ^ 32 + ly % 2 ^ 32)
    (hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 * (hy * 2 ^ 32 + ly % 2 ^ 32))
    (hR : (R : Int) = if hy * 2 ^ 32 + ly % 2 ^ 32 ≤ hx * 2 ^ 32 + lx % 2 ^ 32
      then hx * 2 ^ 32 + lx % 2 ^ 32 - (hy * 2 ^ 32 + ly % 2 ^ 32) else hx * 2 ^ 32 + lx % 2 ^ 32)
    (hiy : iy ≤ 1023) (hlow : R ≠ 0 → -1074 ≤ iy - ((52 - R.log2 : Nat) : Int)) :
    N_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) = outv sx iy R ∧
    T_8002bfd8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 ((lx - ly).bmod (2 ^ 32))) = true := by
  have hb1 := Int.bmod_emod (x := lx - ly) (m := 2 ^ 32)
  have hb2 := Int.le_bmod (x := lx - ly) (m := 2 ^ 32) (by decide)
  have hb3 := Int.bmod_lt (x := lx - ly) (m := 2 ^ 32) (by decide)
  simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3 ⊢
  have hlx := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hlx2 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hly := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hly2 := Int.emod_lt_of_pos ly (show (0 : Int) < 2 ^ 32 by decide)
  have hx1 : hx < 2 ^ 22 := by omega
  generalize hB : (lx - ly).bmod 4294967296 = lz at hb1 hb2 hb3 ⊢
  obtain ⟨hN, hT⟩ := sub_bfd8 m s r iy sx hx lx hy ly lz hx0 hx1 hy0 (by omega) (by omega) (by omega)
    hl1 hl2 hm1 hm2
  rw [hN, hT]
  split at hR
  · rename_i hge
    by_cases hc : ly % 4294967296 ≤ lx % 4294967296
    · simp only [if_pos hc]
      rw [if_pos (show 0 ≤ hx - hy - 0 by omega), if_pos (show 0 ≤ hx - hy - 0 by omega)]
      exact fin_bff0 hro s r iy sx _ _ R h5 (by omega) (by omega) (by omega) (by omega) (by omega) hiy hlow
    · simp only [if_neg hc]
      rw [if_pos (show 0 ≤ hx - hy - 1 by omega), if_pos (show 0 ≤ hx - hy - 1 by omega)]
      exact fin_bff0 hro s r iy sx _ _ R h5 (by omega) (by omega) (by omega) (by omega) (by omega) hiy hlow
  · rename_i hlt
    by_cases hc : ly % 4294967296 ≤ lx % 4294967296
    · simp only [if_pos hc]
      rw [if_neg (show ¬ 0 ≤ hx - hy - 0 by omega), if_neg (show ¬ 0 ≤ hx - hy - 0 by omega)]
      exact fin_bff0 hro s r iy sx _ _ R h5 hx0 (by omega) hl1 hl2 (by omega) hiy hlow
    · simp only [if_neg hc]
      rw [if_neg (show ¬ 0 ≤ hx - hy - 1 by omega), if_neg (show ¬ 0 ≤ hx - hy - 1 by omega)]
      exact fin_bff0 hro s r iy sx _ _ R h5 hx0 (by omega) hl1 hl2 (by omega) hiy hlow

end Lua.Vm.Fn.Ieee754Fmod

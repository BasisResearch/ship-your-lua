import Lua.Vm.Fn.FmodPre

/-!
# `__ieee754_fmod`: the operands' classes (lane float-sf5, (b1))

`e_fmod.c:58-99`: `ilogb` of each operand and its significand normalised to
bit 52 (`ilg`, `sig`, `e_fmod.c:58-99`), the machine's dispatch on the
classes (normal; subnormal with `hx ≠ 0`; with `hx = 0` and the low word's
bit 31 clear or set), each class one cut lemma composed from the stage
lemmas (`x_c098`, `x_bfa8`, `x_c15c`, `x_be78`, `d_c0d8`, the `ilog_*`
cycles). The result is `outv sx iy (frem …)`: the remainder of the
normalised `x · 2^(ix - iy)` by the normalised `y`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- `ilogb` of a finite nonzero operand from its words (`e_fmod.c:58-77`):
`(hx >> 20) - 1023`, or a subnormal's by its leading bit. -/
def ilg (h l : Int) : Int :=
  if 2 ^ 20 ≤ h then h / 2 ^ 20 - 1023 else ((h * 2 ^ 32 + l % 2 ^ 32).toNat.log2 : Int) - 1074

/-- The significand normalised to bit 52 (`e_fmod.c:80-99`): the hidden bit
or-ed in, or a subnormal shifted by `-1022 - ilogb`. -/
def sig (h l : Int) : Int :=
  if 2 ^ 20 ≤ h then (2 ^ 20 + h % 2 ^ 20) * 2 ^ 32 + l % 2 ^ 32
  else (h * 2 ^ 32 + l % 2 ^ 32) * 2 ^ (-1022 - ilg h l).toNat

/-- The remainder the routine converts back (`e_fmod.c:103-112`). -/
def frem (hx lx hy ly : Int) : Nat := ((sig hx lx * 2 ^ (ilg hx lx - ilg hy ly).toNat) % sig hy ly).toNat

theorem ilg_norm (h l : Int) (h0 : 2 ^ 20 ≤ h) : ilg h l = h / 2 ^ 20 - 1023 := by
  unfold ilg; rw [if_pos h0]
theorem sig_norm (h l : Int) (h0 : 2 ^ 20 ≤ h) : sig h l = (2 ^ 20 + h % 2 ^ 20) * 2 ^ 32 + l % 2 ^ 32 := by
  unfold sig; rw [if_pos h0]
theorem sig_sub (h l : Int) (h0 : h < 2 ^ 20) :
    sig h l = (h * 2 ^ 32 + l % 2 ^ 32) * 2 ^ (-1022 - ilg h l).toNat := by
  unfold sig; rw [if_neg (by omega)]

/-- A subnormal's `ilogb` and normalised significand. -/
theorem subn (h l : Int) (h0 : 0 ≤ h) (h1 : h < 2 ^ 20) (hz : h * 2 ^ 32 + l % 2 ^ 32 ≠ 0) :
    -1074 ≤ ilg h l ∧ ilg h l ≤ -1023 ∧
    2 ^ 52 ≤ (h * 2 ^ 32 + l % 2 ^ 32) * 2 ^ (-1022 - ilg h l).toNat ∧
    (h * 2 ^ 32 + l % 2 ^ 32) * 2 ^ (-1022 - ilg h l).toNat < 2 ^ 53 := by
  have hl0 := Int.emod_nonneg l (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hl1 := Int.emod_lt_of_pos l (show (0 : Int) < 2 ^ 32 by decide)
  unfold ilg; rw [if_neg (by omega)]
  generalize hR : (h * 2 ^ 32 + l % 2 ^ 32).toNat = R
  have hRi : (R : Int) = h * 2 ^ 32 + l % 2 ^ 32 := by rw [← hR, Int.toNat_of_nonneg (by omega)]
  rw [← hRi]
  have hR0 : 0 < R := by omega
  have hR52 : R < 2 ^ 52 := by omega
  have hL := Lua.Num.SfRef.log2_lt52 hR52
  obtain ⟨n1, n2⟩ := Lua.Num.SfRef.norm52 hR0 (by omega)
  rw [show (-1022 - ((R.log2 : Int) - 1074)).toNat = 52 - R.log2 by omega]
  have c1 : (2 : Int) ^ 52 ≤ (R : Int) * 2 ^ (52 - R.log2) := by exact_mod_cast n1
  have c2 : (R : Int) * 2 ^ (52 - R.log2) < 2 ^ 53 := by exact_mod_cast n2
  omega

/-- **After `y`'s `ilogb`** (`0x8002be68`, `y` subnormal, `hy < 2^20`): `x`
normal (`x_c098`), deep (`d_c0d8`) or shallow subnormal (`x_be78`). -/
theorem L_be68 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0) (hyz : hy * 2 ^ 32 + ly % 2 ^ 32 ≠ 0)
    (hle : ilg hy ly ≤ ilg hx lx) (hlow : LowOk (ilg hy ly) (frem hx lx hy ly)) :
    N_8002be68 m s r (BitVec.ofInt 64 (ilg hy ly)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (sx + hx)) = outv sx (ilg hy ly) (frem hx lx hy ly) ∧
    T_8002be68 m s r (BitVec.ofInt 64 (ilg hy ly)) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (sx + hx)) = true := by
  obtain ⟨y1, y2, y3, y4⟩ := subn hy ly hy0 hy1 hyz
  unfold frem at hlow ⊢
  rw [sig_sub hy ly hy1] at hlow ⊢
  generalize ilg hy ly = iy at *
  by_cases hn : 2 ^ 20 ≤ hx
  · -- `x` normal
    rw [ilg_norm hx lx hn, sig_norm hx lx hn] at *
    have e : N_8002be68 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 (hx / 2 ^ 20 - 1023)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (sx + hx)) = N_8002c098 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (hx / 2 ^ 20 - 1023)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 (sx + hx)) ∧
      T_8002be68 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx)
        (BitVec.ofInt 64 (hx / 2 ^ 20 - 1023)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (sx + hx)) = T_8002c098 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx)
          (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (hx / 2 ^ 20 - 1023)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 ly)
          (BitVec.ofInt 64 (sx + hx)) := by
      unfold N_8002be68 T_8002be68
      fm_nf
      exact ⟨trivial, trivial⟩
    rw [e.1, e.2, show hx % 2 ^ 20 = (sx + hx) % 2 ^ 20 by omega]
    rw [show hx % 2 ^ 20 = (sx + hx) % 2 ^ 20 by omega] at hlow
    exact x_c098 hro s r iy sx (hx / 2 ^ 20 - 1023) (sx + hx) lx hy ly h5 (by omega) (by omega) hl1 hl2 hy0 hy1
      hm1 hm2 (by omega) (by omega) y1 y2 y3 y4 hlow
  · obtain ⟨x1, x2, x3, x4⟩ := subn hx lx hx0 (by omega) hxz
    rw [sig_sub hx lx (by omega)] at *
    generalize ilg hx lx = ix at *
    by_cases hd : ix < -1053
    · -- `x` deep: `hx = 0`, `lx < 2^21`
      have hp : (2 : Int) ^ 32 ≤ 2 ^ (-1022 - ix).toNat := ipow_mono (by omega)
      have hl0 := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
      have hX : hx * 2 ^ 32 + lx % 2 ^ 32 < 2 ^ 21 := by
        have := Int.mul_le_mul_of_nonneg_left hp (show 0 ≤ hx * 2 ^ 32 + lx % 2 ^ 32 by omega)
        omega
      have hx00 : hx = 0 := by omega
      have hlx : lx % 2 ^ 32 = lx := by omega
      subst hx00
      have hpy : (2 : Int) ^ 32 ≤ 2 ^ (-1022 - iy).toNat := ipow_mono (by omega)
      have hY : hy * 2 ^ 32 + ly % 2 ^ 32 < 2 ^ 21 := by
        have := Int.mul_le_mul_of_nonneg_left hpy (show 0 ≤ hy * 2 ^ 32 + ly % 2 ^ 32 by
          have := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide); omega)
        omega
      have hy00 : hy = 0 := by omega
      subst hy00
      have hly : ly % 2 ^ 32 = ly := by omega
      have hly0 : 0 ≤ ly := by omega
      simp only [Int.zero_mul, Int.zero_add, hlx, hly] at *
      unfold N_8002be68 T_8002be68 N_8002be70 T_8002be70
      fm_nf
      exact d_c0d8 hro s r iy sx ix lx ly _ h5 (by omega) x1 (by omega) x3 x4 hly0 hm2 y1 hle y3 y4 hlow
    · unfold N_8002be68 T_8002be68 N_8002be70 T_8002be70
      fm_nf
      exact x_be78 hro s r iy ix sx hx lx hy ly h5 hx0 (by omega) hl1 hl2 hy0 hy1 hm1 hm2 (by omega) x2 x3 x4
        y1 y2 y3 y4 hle hlow

theorem log2_shift (w k a : Nat) (hw : 0 < w) (ha : a < 2 ^ k) : (w * 2 ^ k + a).log2 = w.log2 + k := by
  apply (Nat.log2_eq_iff (by have := Nat.two_pow_pos k; have : 0 < w * 2 ^ k := Nat.mul_pos hw this; omega)).2
  have h1 : 2 ^ w.log2 ≤ w := Nat.log2_self_le (by omega)
  have h2 : w < 2 ^ (w.log2 + 1) := Nat.lt_log2_self
  have p1 : 2 ^ w.log2 * 2 ^ k ≤ w * 2 ^ k := Nat.mul_le_mul_right _ h1
  have p2 : (w + 1) * 2 ^ k ≤ 2 ^ (w.log2 + 1) * 2 ^ k := Nat.mul_le_mul_right _ h2
  rw [Nat.pow_add, Nat.pow_add, Nat.pow_add] at *
  rw [Nat.add_mul, Nat.one_mul] at p2
  constructor
  · omega
  · rw [Nat.pow_one] at p2 ⊢
    have : 2 ^ w.log2 * 2 ^ k * 2 = 2 ^ w.log2 * 2 * 2 ^ k := by
      rw [Nat.mul_assoc, Nat.mul_comm (2 ^ k), ← Nat.mul_assoc]
    omega

/-- `ilogb` of a subnormal with `hy ≠ 0` (`e_fmod.c:62-63`): from `hy << 11`. -/
theorem ilg_hi (h l : Int) (h0 : 0 < h) (h1 : h < 2 ^ 20) :
    ilg h l = -1022 - ((31 - (h * 2048).toNat.log2 : Nat) : Int) := by
  unfold ilg; rw [if_neg (by omega)]
  have hl0 := Int.emod_nonneg l (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hl1 := Int.emod_lt_of_pos l (show (0 : Int) < 2 ^ 32 by decide)
  rw [show Int.toNat (h * 2 ^ 32 + l % 2 ^ 32) = h.toNat * 2 ^ 32 + (l % 2 ^ 32).toNat by omega,
    show Int.toNat (h * 2048) = h.toNat * 2 ^ 11 by omega, log2_shift _ _ _ (by omega) (by omega),
    show Nat.log2 (h.toNat * 2 ^ 11) = h.toNat.log2 + 11 by
      have := log2_shift h.toNat 11 0 (by omega) (by omega); simpa only [Nat.add_zero] using this]
  have : h.toNat.log2 ≤ 19 := by
    have := (Nat.log2_lt (n := h.toNat) (by omega)).2 (show h.toNat < 2 ^ 20 by omega); omega
  omega

/-- `ilogb` of a subnormal with `hy = 0` (`e_fmod.c:60-61`): from `ly`. -/
theorem ilg_lo (l : Int) (h0 : 0 < l) (h1 : l < 2 ^ 31) :
    ilg 0 l = -1043 - ((31 - l.toNat.log2 : Nat) : Int) := by
  unfold ilg; rw [if_neg (by omega)]
  rw [show Int.toNat ((0 : Int) * 2 ^ 32 + l % 2 ^ 32) = l.toNat by omega]
  have : l.toNat.log2 ≤ 30 := by
    have := (Nat.log2_lt (n := l.toNat) (by omega)).2 (show l.toNat < 2 ^ 31 by omega); omega
  omega

/-- **`y` subnormal with `hy ≠ 0`** (`0x8002c080`): its `ilogb` cycle, then `L_be68`. -/
theorem L_c080 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 < hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0)
    (hle : ilg hy ly ≤ ilg hx lx) (hlow : LowOk (ilg hy ly) (frem hx lx hy ly)) :
    N_8002c080 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) = outv sx (ilg hy ly) (frem hx lx hy ly) ∧
    T_8002c080 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) = true := by
  have hlg := ilg_hi hy ly hy0 hy1
  have hw : (((hy * 2048).toNat : Nat) : Int) = hy * 2048 := by omega
  have hwl : (hy * 2048).toNat.log2 ≤ 30 := by
    have := (Nat.log2_lt (n := (hy * 2048).toNat) (by omega)).2 (show (hy * 2048).toNat < 2 ^ 31 by omega); omega
  have e : N_8002c080 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) =
      N_8002c088 fnFuel m s r (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 (((hy * 2048).toNat : Nat) : Int))
        (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) ∧
    T_8002c080 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) =
      T_8002c088 fnFuel m s r (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 (((hy * 2048).toNat : Nat) : Int))
        (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) := by
    rw [hw]
    unfold N_8002c080 T_8002c080
    fm_nf
    exact ⟨trivial, trivial⟩
  rw [e.1, e.2]
  obtain ⟨n1, t1⟩ := ilog_c088 m s r _ _ _ _ _ _ _ (31 - (hy * 2048).toNat.log2) fnFuel (hy * 2048).toNat (-1022)
    (by omega) rfl (by omega) (by omega) (by unfold fnFuel; omega) (by omega) (by omega)
  rw [n1, t1]
  unfold N_8002c094 T_8002c094
  rw [← hlg]
  exact L_be68 hro s r sx lx hx hy ly h5 hx0 hx1 hl1 hl2 (by omega) hy1 hm1 hm2 hxz (by omega) hle hlow

/-- **`y` subnormal with `hy = 0`, `ly`'s bit 31 clear** (`0x8002be58`): its
`ilogb` cycle, then `L_be68`. -/
theorem L_be58 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : 0 < ly) (hm2 : ly < 2 ^ 31)
    (hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0)
    (hle : ilg 0 ly ≤ ilg hx lx) (hlow : LowOk (ilg 0 ly) (frem hx lx 0 ly)) :
    N_8002be58 m s r (BitVec.ofInt 64 ly) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) =
      outv sx (ilg 0 ly) (frem hx lx 0 ly) ∧
    T_8002be58 m s r (BitVec.ofInt 64 ly) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
        (BitVec.ofInt 64 0) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) = true := by
  have hlg := ilg_lo ly hm1 hm2
  have hwl : ly.toNat.log2 ≤ 30 := by
    have := (Nat.log2_lt (n := ly.toNat) (by omega)).2 (show ly.toNat < 2 ^ 31 by omega); omega
  have hw : ((ly.toNat : Nat) : Int) = ly := by omega
  unfold N_8002be58 T_8002be58
  obtain ⟨n1, t1⟩ := ilog_be5c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx))
    (BitVec.ofInt 64 0) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx))
    (31 - ly.toNat.log2) fnFuel ly.toNat (-1043)
    (by omega) rfl (by omega) (by omega) (by unfold fnFuel; omega) (by omega) (by omega)
  rw [hw] at n1 t1
  simp only [show ((0#64) + sign_extend (m := 64) (0xbed#12)) = BitVec.ofInt 64 (-1043) by decide]
  rw [n1, t1, ← hlg]
  exact L_be68 hro s r sx lx hx 0 ly h5 hx0 hx1 hl1 hl2 (by omega) (by omega) (by omega) hm2 hxz (by omega) hle hlow

/-- `ilogb` of a subnormal with `hy = 0` and `ly`'s bit 31 set (`e_fmod.c:60`: no shift). -/
theorem ilg_s3 (l : Int) (h0 : -2 ^ 31 ≤ l) (h1 : l < 0) : ilg 0 l = -1043 := by
  unfold ilg; rw [if_neg (by omega)]
  have : (Int.toNat ((0 : Int) * 2 ^ 32 + l % 2 ^ 32)).log2 = 31 := by
    apply (Nat.log2_eq_iff (by omega)).2; omega
  omega

/-- **`y` subnormal with `hy = 0`, `ly`'s bit 31 set** (`0x8002c1bc`, `iy = -1043`):
`x`'s shift as at `0x8002be78`, then `y`'s set-up `0x8002c0b4`. -/
theorem L_c1bc {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 0)
    (hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0)
    (hle : ilg 0 ly ≤ ilg hx lx) (hlow : LowOk (ilg 0 ly) (frem hx lx 0 ly)) :
    N_8002c1bc m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = outv sx (ilg 0 ly) (frem hx lx 0 ly) ∧
    T_8002c1bc m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
  obtain ⟨x1, x2, x3, x4⟩ := subn hx lx hx0 hx1 hxz
  unfold frem at hlow ⊢
  rw [sig_sub hx lx hx1, sig_sub 0 ly (by omega)] at hlow ⊢
  rw [ilg_s3 ly hm1 hm2] at hle hlow ⊢
  generalize ilg hx lx = ix at *
  have e : N_8002c1bc m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      N_8002be78 m s r (BitVec.ofInt 64 (-1043)) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 0) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (-1053)) ∧
    T_8002c1bc m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      T_8002be78 m s r (BitVec.ofInt 64 (-1043)) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix) (BitVec.ofInt 64 0) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly)
        (BitVec.ofInt 64 (-1053)) := by
    unfold N_8002c1bc T_8002c1bc N_8002be78 T_8002be78
    fm_nf
    exact ⟨trivial, trivial⟩
  rw [e.1, e.2]
  have hly := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
  exact x_be78 hro s r (-1043) ix sx hx lx 0 ly h5 hx0 hx1 hl1 hl2 (by omega) (by omega) hm1 (by omega) (by omega)
    x2 x3 x4 (by omega) (by omega) (by simp only [Int.reducePow, Int.reduceToNat, Int.reduceSub]; omega)
    (by simp only [Int.reducePow, Int.reduceToNat, Int.reduceSub]; omega) hle hlow

/-- **`x` subnormal after its `ilogb`** (`0x8002be40`), `y` subnormal: `y`'s
class (`e_fmod.c:68-77`) to `L_c080`, `L_be58` or `L_c1bc`. -/
theorem L_be40 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0) (hyz : hy * 2 ^ 32 + ly % 2 ^ 32 ≠ 0)
    (hle : ilg hy ly ≤ ilg hx lx) (hlow : LowOk (ilg hy ly) (frem hx lx hy ly)) :
    N_8002be40 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) =
      outv sx (ilg hy ly) (frem hx lx hy ly) ∧
    T_8002be40 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (ilg hx lx)) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) = true := by
  have hix := (subn hx lx hx0 hx1 hxz).2.1
  unfold N_8002be40 T_8002be40 N_8002be4c T_8002be4c
  fm_nf
  by_cases hh : hy = 0
  · subst hh
    unfold N_8002be50 T_8002be50
    fm_nf
    by_cases hn : ly < 0
    · unfold N_8002c1b4 T_8002c1b4
      have := ilg_s3 ly hm1 hn
      fm_nf
      exact L_c1bc hro s r sx lx hx ly h5 hx0 hx1 hl1 hl2 hm1 hn hxz hle hlow
    · have hp : 0 < ly := by omega
      fm_nf
      exact L_be58 hro s r sx lx hx ly h5 hx0 (by omega) hl1 hl2 hp hm2 hxz hle hlow
  · fm_nf
    exact L_c080 hro s r sx lx hx hy ly h5 hx0 (by omega) hl1 hl2 (by omega) hy1 hm1 hm2 hxz hle hlow

/-- **`x` subnormal with `hx = 0`, `lx`'s bit 31 set** (`0x8002c22c`, `ix =
-1043` without a cycle), `y` subnormal: `y`'s class to `L_c080`, `L_be58` or
`L_c1bc`. -/
theorem L_c22c {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 0) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hyz : hy * 2 ^ 32 + ly % 2 ^ 32 ≠ 0)
    (hle : ilg hy ly ≤ ilg 0 lx) (hlow : LowOk (ilg hy ly) (frem 0 lx hy ly)) :
    N_8002c22c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + 0)) (BitVec.ofInt 64 (sy + hy)) =
      outv sx (ilg hy ly) (frem 0 lx hy ly) ∧
    T_8002c22c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + 0)) (BitVec.ofInt 64 (sy + hy)) = true := by
  have hix := ilg_s3 lx hl1 hl2
  have hxz : (0 : Int) * 2 ^ 32 + lx % 2 ^ 32 ≠ 0 := by omega
  unfold N_8002c22c T_8002c22c N_8002c250 T_8002c250
  fm_nf
  by_cases hh : hy = 0
  · subst hh
    unfold N_8002c254 T_8002c254
    fm_nf
    by_cases hn : ly < 0
    · unfold N_8002c260 T_8002c260
      fm_nf
      have h := L_c1bc hro s r sx lx 0 ly h5 (by omega) (by omega) hl1 (by omega) hm1 hn hxz hle hlow
      rw [hix] at h
      exact h
    · have hp : 0 < ly := by omega
      fm_nf
      have h := L_be58 hro s r sx lx 0 ly h5 (by omega) (by omega) hl1 (by omega) hp hm2 hxz hle hlow
      simp only [hix, Int.add_zero] at h ⊢
      exact h
  · unfold N_8002c288 T_8002c288
    fm_nf
    have h := L_c080 hro s r sx lx 0 hy ly h5 (by omega) (by omega) hl1 (by omega) (by omega) hy1 hm1 hm2 hxz hle hlow
    simp only [hix, Int.add_zero] at h ⊢
    exact h

/-- **`x` normal** (`0x8002bf94`, `ix = (hx >> 20) - 1023`): `y` normal
(`x_bfa8`), or subnormal by class (`L_c080`, `L_be58`, `x_c15c`). -/
theorem L_bf94 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31) (hx0 : 2 ^ 20 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2047 * 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hyz : hy * 2 ^ 32 + ly % 2 ^ 32 ≠ 0)
    (hle : ilg hy ly ≤ ilg hx lx) (hlow : LowOk (ilg hy ly) (frem hx lx hy ly)) :
    N_8002bf94 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) =
      outv sx (ilg hy ly) (frem hx lx hy ly) ∧
    T_8002bf94 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) = true := by
  have hix := ilg_norm hx lx hx0
  unfold N_8002bf94 T_8002bf94
  fm_nf
  rw [show hx / 1048576 + -1023 = ilg hx lx by omega]
  by_cases hn : 2 ^ 20 ≤ hy
  · -- `y` normal
    rw [if_neg (by omega), if_neg (by omega)]
    have hlow' := hlow
    unfold frem at hlow'
    rw [sig_norm hx lx hx0, sig_norm hy ly hn, ilg_norm hy ly hn,
      show hx % 2 ^ 20 = (sx + hx) % 2 ^ 20 by omega] at hlow'
    have h := x_bfa8 hro s r sx (ilg hx lx) (sx + hx) lx hy (sy + hy) ly h5 (by omega) (by omega) hl1 hl2 hn hy1
      (by omega) (by omega) (by omega) hm1 hm2 (by rw [← ilg_norm hy ly hn]; exact hle) (by omega) hlow'
    unfold frem
    rw [sig_norm hx lx hx0, sig_norm hy ly hn, ilg_norm hy ly hn,
      show hx % 2 ^ 20 = (sx + hx) % 2 ^ 20 by omega]
    exact h
  · rw [if_pos (by omega), if_pos (by omega)]
    unfold N_8002c07c T_8002c07c
    fm_nf
    by_cases hh : hy = 0
    · subst hh
      unfold N_8002c154 T_8002c154
      fm_nf
      by_cases hneg : ly < 0
      · fm_nf
        have h3 := ilg_s3 ly hm1 hneg
        have hf : frem hx lx 0 ly = ((((2 : Int) ^ 20 + (sx + hx) % 2 ^ 20) * 2 ^ 32 + lx % 2 ^ 32) *
            2 ^ (hx / 1048576 + 20).toNat % ((ly % 2 ^ 32) * 2 ^ 21)).toNat := by
          unfold frem
          rw [sig_norm hx lx hx0, sig_sub 0 ly (by omega), h3, hix,
            show (sx + hx) % 2 ^ 20 = hx % 2 ^ 20 by omega, show (-1022 - -1043 : Int).toNat = 21 by decide,
            show hx / 2 ^ 20 - 1023 - -1043 = hx / 1048576 + 20 by omega, Int.zero_mul, Int.zero_add]
        rw [hf, h3]
        rw [hf, h3] at hlow
        exact x_c15c hro s r (hx / 1048576) sx (sx + hx) lx ly h5 (by omega) (by omega) hl1 hl2 hm1 hneg
          (by omega) (by omega) hlow
      · have hp : 0 < ly := by omega
        fm_nf
        exact L_be58 hro s r sx lx hx ly h5 (by omega) hx1 hl1 hl2 hp hm2 (by omega) hle hlow
    · fm_nf
      exact L_c080 hro s r sx lx hx hy ly h5 (by omega) hx1 hl1 hl2 (by omega) (by omega) hm1 hm2 (by omega) hle hlow

/-- **The operands' classes** (`0x8002be1c`, `|x| > |y|`, both finite, `y ≠ 0`):
`x` normal (`L_bf94`), or `x`'s `ilogb` (`e_fmod.c:58-65`: the cycle from
`hx << 11`, from `lx`, or none for `lx`'s bit 31) and `y`'s class
(`L_be40`, `L_c22c`). -/
theorem L_be1c {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx lx hx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31) (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2047 * 2 ^ 20) (hm1 : -2 ^ 31 ≤ ly)
    (hm2 : ly < 2 ^ 31) (hyz : hy * 2 ^ 32 + ly % 2 ^ 32 ≠ 0)
    (hgt : hy * 2 ^ 32 + ly % 2 ^ 32 < hx * 2 ^ 32 + lx % 2 ^ 32)
    (hle : ilg hy ly ≤ ilg hx lx) (hlow : LowOk (ilg hy ly) (frem hx lx hy ly)) :
    N_8002be1c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) (BitVec.ofInt 64 2146435072) =
      outv sx (ilg hy ly) (frem hx lx hy ly) ∧
    T_8002be1c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) (BitVec.ofInt 64 2146435072) =
      true := by
  have hl0 := Int.emod_nonneg lx (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hl3 := Int.emod_lt_of_pos lx (show (0 : Int) < 2 ^ 32 by decide)
  have hm0 := Int.emod_nonneg ly (show (2 : Int) ^ 32 ≠ 0 by decide)
  have hm3 := Int.emod_lt_of_pos ly (show (0 : Int) < 2 ^ 32 by decide)
  unfold N_8002be1c T_8002be1c
  fm_nf
  by_cases hn : 2 ^ 20 ≤ hx
  · fm_nf
    exact L_bf94 hro s r sx lx hx sy hy ly h5 h6 hn hx1 hl1 hl2 hy0 hy1 hm1 hm2 hyz hle hlow
  · have hys : hy < 2 ^ 20 := by omega
    have hxz : hx * 2 ^ 32 + lx % 2 ^ 32 ≠ 0 := by omega
    fm_nf
    unfold N_8002be24 T_8002be24
    fm_nf
    by_cases hh : hx = 0
    · subst hh
      unfold N_8002be28 T_8002be28
      fm_nf
      by_cases hneg : lx < 0
      · fm_nf
        have h := L_c22c hro s r sx lx sy hy ly h5 h6 hl1 hneg hy0 hys hm1 hm2 hyz hle hlow
        simp only [Int.add_zero] at h
        exact h
      · have hp : 0 < lx := by omega
        fm_nf
        have hlg := ilg_lo lx hp hl2
        have hwl : lx.toNat.log2 ≤ 30 := by
          have := (Nat.log2_lt (n := lx.toNat) (by omega)).2 (show lx.toNat < 2 ^ 31 by omega); omega
        have hw : ((lx.toNat : Nat) : Int) = lx := by omega
        unfold N_8002be30 T_8002be30
        obtain ⟨n1, t1⟩ := ilog_be34 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
          (BitVec.ofInt 64 0) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + 0)) (BitVec.ofInt 64 (sy + hy))
          (31 - lx.toNat.log2) fnFuel lx.toNat (-1043)
          (by omega) rfl (by omega) (by omega) (by unfold fnFuel; omega) (by omega) (by omega)
        rw [hw] at n1 t1
        simp only [show ((0#64) + sign_extend (m := 64) (0xbed#12)) = BitVec.ofInt 64 (-1043) by decide]
        simp only [Int.add_zero] at n1 t1
        rw [n1, t1, ← hlg]
        have h := L_be40 hro s r sx lx 0 sy hy ly h5 h6 (by omega) (by omega) hl1 hl2 hy0 hys hm1 hm2 hxz hyz hle hlow
        simp only [Int.add_zero] at h
        exact h
    · have hlg := ilg_hi hx lx (by omega) (by omega)
      have hwl : (hx * 2048).toNat.log2 ≤ 30 := by
        have := (Nat.log2_lt (n := (hx * 2048).toNat) (by omega)).2 (show (hx * 2048).toNat < 2 ^ 31 by omega); omega
      have hw : (((hx * 2048).toNat : Nat) : Int) = hx * 2048 := by omega
      fm_nf
      have e : N_8002bed8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
            (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) =
          N_8002bee0 fnFuel m s r (BitVec.ofInt 64 (((hx * 2048).toNat : Nat) : Int)) (BitVec.ofInt 64 sx)
            (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
            (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) ∧
        T_8002bed8 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
            (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) =
          T_8002bee0 fnFuel m s r (BitVec.ofInt 64 (((hx * 2048).toNat : Nat) : Int)) (BitVec.ofInt 64 sx)
            (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (-1022)) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
            (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) := by
        rw [hw]
        unfold N_8002bed8 T_8002bed8
        fm_nf
        exact ⟨trivial, trivial⟩
      rw [e.1, e.2]
      obtain ⟨n1, t1⟩ := ilog_bee0 m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy)
        (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy))
        (31 - (hx * 2048).toNat.log2) fnFuel (hx * 2048).toNat (-1022)
        (by omega) rfl (by omega) (by omega) (by unfold fnFuel; omega) (by omega) (by omega)
      rw [n1, t1]
      unfold N_8002beec T_8002beec
      rw [← hlg]
      exact L_be40 hro s r sx lx hx sy hy ly h5 h6 hx0 (by omega) hl1 hl2 hy0 hys hm1 hm2 hxz hyz hle hlow

end Lua.Vm.Fn.Ieee754Fmod

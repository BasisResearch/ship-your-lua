import Lua.Vm.Fn.FmodSetN

/-!
# `__ieee754_fmod` on two deep subnormals (lane float-sf5, (b1))

Both operands below `2^-1043` (`n ≥ 32` for each: `hx = lx << (n - 32)`,
`lx = 0`, and as much for `y`): `0x8002c0d8` (`x`'s shift), `0x8002c0e8`
(`y`'s shift; the loop for `ix ≠ iy`), `0x8002c100` (`ix = iy`: one
subtraction of the high words, then zero, the normalisation or the
subnormal pack).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- **`ix = iy`, both deep** (`0x8002c100`): `R = hx - hy` (high words, the low
words zero) or `hx`, then the conversion back. -/
theorem deep_c100 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (iy sx hx hy : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 2 ^ 20 ≤ hx) (hx1 : hx < 2 ^ 21) (hy0 : 2 ^ 20 ≤ hy) (hy1 : hy < 2 ^ 21)
    (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1054)
    (hlow : LowOk iy (((hx * 2 ^ 32) % (hy * 2 ^ 32)).toNat)) :
    N_8002c100 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) =
      outv sx iy (((hx * 2 ^ 32) % (hy * 2 ^ 32)).toNat) ∧
    T_8002c100 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 hx) = true := by
  have hm : (hx * 2 ^ 32) % (hy * 2 ^ 32) = (if hy ≤ hx then hx - hy else hx) * 2 ^ 32 := by
    rw [mod2 _ _ (by omega) (by omega)]; split <;> omega
  generalize hRd : ((hx * 2 ^ 32) % (hy * 2 ^ 32)).toNat = R at hlow ⊢
  have hRv : (R : Int) = (if hy ≤ hx then hx - hy else hx) * 2 ^ 32 := by
    rw [← hRd, hm, Int.toNat_of_nonneg (by split <;> omega)]
  unfold N_8002c100 T_8002c100 N_8002c290 T_8002c290 N_8002c294 T_8002c294 N_8002c2a4
  unfold N_8002c108 T_8002c108 N_8002c10c T_8002c10c N_8002c004 T_8002c004
  fm_nf
  unfold outv
  by_cases hge : hy ≤ hx
  · rw [if_pos hge] at hRv
    by_cases h0 : hx = hy
    · subst h0
      fm_nf
      rw [ld_bf78 hro s r sx h5]
      exact ⟨by simp only [Int.reducePow], trivial⟩
    · -- `0 < hz < 2^20`: normalised
      fm_nf
      have hR0 : R ≠ 0 := by omega
      have hR53 : R < 2 ^ 52 := by omega
      obtain ⟨hn1, hn2⟩ := Lua.Num.SfRef.norm52 (Nat.pos_of_ne_zero hR0) (by omega)
      have hlo := hlow hR0
      have hz1' : 1 ≤ 52 - R.log2 := by
        have : R.log2 < 52 := (Nat.log2_lt hR0).2 hR53
        omega
      have h1 : (2 : Int) ^ 52 ≤ (R : Int) * 2 ^ (52 - R.log2) := by exact_mod_cast hn1
      have h2 : (R : Int) * 2 ^ (52 - R.log2) < 2 ^ 53 := by exact_mod_cast hn2
      rw [hRv] at h1 h2
      obtain ⟨hN, hT⟩ := norm_c008 s r sx h5 (52 - R.log2) Lua.Vm.Sim.fnFuel iy (hx - hy)
        0 _ hz1' (by unfold Lua.Vm.Sim.fnFuel; omega) (by omega) (by omega) (by omega)
        (by simp) h1 h2 hlo (by omega)
      rw [hRv]
      exact ⟨hN, hT⟩
  · rw [if_neg hge] at hRv
    fm_nf
    refine ⟨?_, trivial⟩
    have hl52 : R.log2 = 52 := by
      have h1 := Lua.Num.F64.le_log2_of (show 2 ^ 52 ≤ R by omega)
      have h2 : R.log2 < 53 := (Nat.log2_lt (by omega)).2 (by omega)
      omega
    try rw [if_neg (show ¬ R = 0 by omega)]
    rw [hl52, pack_c118 s r iy sx hx 0 hiy1 (by omega) hx0 hx1 h5 (by omega) (by omega)]
    simp only [Nat.sub_self, Int.natCast_zero, Int.sub_zero, Int.pow_zero, Int.mul_one, hRv, Int.zero_emod,
      Int.add_zero]
    unfold packv
    rw [if_neg (by omega)]

open Lean in
set_option hygiene false in
/-- **The chamber generator for `0x8002c0e8`** (`y` deep: `hy = ly << (n - 32)`,
`n = -1022 - iy ≥ 32`; then the loop, or `deep_c100` for `ix = iy`). -/
macro "fm_dc0e8_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    let hyw ← if n = 32 then `(ly) else `(ly * 2 ^ ($nl - 32))
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"dc0e8_{n}")) {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
          (sx ix hx ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 2 ^ 20 ≤ hx) (hx1 : hx < 2 ^ 21)
          (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31) (hY1 : 2 ^ 52 ≤ ly * 2 ^ $nl) (hY2 : ly * 2 ^ $nl < 2 ^ 53)
          (hix : -$il ≤ ix) (hix2 : ix ≤ -1054)
          (hlow : LowOk (-$il) ((((hx * 2 ^ 32) * 2 ^ (ix - -$il).toNat) % (ly * 2 ^ $nl)).toNat)) :
          N_8002c0e8 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 (-1054)) (BitVec.ofInt 64 sx)
              (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
            outv sx (-$il) ((((hx * 2 ^ 32) * 2 ^ (ix - -$il).toNat) % (ly * 2 ^ $nl)).toNat) ∧
          T_8002c0e8 m s r (BitVec.ofInt 64 (-$il)) (BitVec.ofInt 64 (-1054)) (BitVec.ofInt 64 sx)
              (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
        have hYe : ly * 2 ^ $nl = ($hyw) * 2 ^ 32 := by (try simp only [Int.reducePow, Nat.reduceSub]) <;> omega
        rw [hYe] at hlow hY1 hY2 ⊢
        by_cases he : ix = -$il
        · subst he
          unfold N_8002c0e8 T_8002c0e8
          fm_nf
          simp only [Int.reducePow, Nat.reduceSub] at hlow hY1 hY2 ⊢
          have h := deep_c100 hro s r (-$il) sx hx ($hyw) h5 hx0 hx1 (by simp only [Int.reducePow, Nat.reduceSub]; omega)
            (by simp only [Int.reducePow, Nat.reduceSub]; omega) (by omega) (by omega)
            (by simp only [Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one, Int.reducePow, Nat.reduceSub] at hlow ⊢
                try exact hlow)
          simp only [Int.sub_self, Int.toNat_zero, Int.pow_zero, Int.mul_one, Int.reducePow, Nat.reduceSub] at h ⊢
          try exact h
        · first | (exfalso; omega) | skip
          all_goals (
            have hne : -$il < ix := by omega
            unfold N_8002c0e8 T_8002c0e8
            fm_nf
            simp only [Int.reducePow, Nat.reduceSub] at hlow hY1 hY2 ⊢
            have h := entry_bea4 hro s r (-$il) sx ($hyw) 0 h5 (by simp only [Int.reducePow, Nat.reduceSub]; omega)
              (by simp only [Int.reducePow, Nat.reduceSub]; omega) (by omega) (by omega)
              (by simp only [Int.reducePow, Nat.reduceSub, Int.zero_emod, Int.add_zero]; omega) (by omega)
              (ix - -$il) hx 0 (by omega) (by omega) (by omega) (by omega) (by omega) rfl
              (by simp only [Int.reducePow, Nat.reduceSub, Int.zero_emod, Int.add_zero]; omega)
              (by simp only [Int.reducePow, Nat.reduceSub, Int.zero_emod, Int.add_zero] at hlow ⊢; exact hlow)
            simp only [Int.zero_emod, Int.add_zero, Int.reducePow, Nat.reduceSub] at h ⊢
            exact h)))
  return ⟨mkNullNode cmds⟩

fm_dc0e8_chambers 32 53

/-- **`y` deep** (`0x8002c0e8`, `e_fmod.c:97-99`: `hy = ly << (n - 32)`), `x`
deep (`hx` its shifted high word, `lx = 0`): the loop, or one subtraction
for `ix = iy`. -/
theorem d_c0e8 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (iy sx ix hx ly : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hx0 : 2 ^ 20 ≤ hx) (hx1 : hx < 2 ^ 21)
    (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -1054)
    (hY1 : 2 ^ 52 ≤ ly * 2 ^ (-1022 - iy).toNat) (hY2 : ly * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
    (hix : iy ≤ ix) (hix2 : ix ≤ -1054)
    (hlow : LowOk iy ((((hx * 2 ^ 32) * 2 ^ (ix - iy).toNat) % (ly * 2 ^ (-1022 - iy).toNat)).toNat)) :
    N_8002c0e8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1054)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) =
      outv sx iy ((((hx * 2 ^ 32) * 2 ^ (ix - iy).toNat) % (ly * 2 ^ (-1022 - iy).toNat)).toNat) ∧
    T_8002c0e8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 (-1054)) (BitVec.ofInt 64 sx)
        (BitVec.ofInt 64 ix) (BitVec.ofInt 64 hx) (BitVec.ofInt 64 ly) = true := by
  fm_cover dc0e8 iy 32 53 at hY1 hY2 hlow using hro s r sx ix hx ly h5 hx0 hx1 hm0 hm2 hY1 hY2 hix hix2 hlow



open Lean in
set_option hygiene false in
/-- **The chamber generator for `0x8002c0d8`** (`e_fmod.c:84-87`, `x` deep:
`hx = lx << (n - 32)`, `n = -1022 - ix ≥ 32`), then `d_c0e8` (`y` is deeper
still, `iy ≤ ix`). -/
macro "fm_dc0d8_chambers " lo:num hi:num : command => do
  let mut cmds : Array (TSyntax `command) := #[]
  for n in List.range' lo.getNat (hi.getNat - lo.getNat) do
    let il := Syntax.mkNumLit (toString (1022 + n))
    let nl := Syntax.mkNumLit (toString n)
    let hxw ← if n = 32 then `(lx) else `(lx * 2 ^ ($nl - 32))
    cmds := cmds.push (← `(command|
      theorem $(mkIdent (Name.mkSimple s!"dc0d8_{n}")) {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
          (iy sx lx ly : Int) (v14 : BitVec 64) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hl0 : 0 ≤ lx)
          (hX1 : 2 ^ 52 ≤ lx * 2 ^ $nl) (hX2 : lx * 2 ^ $nl < 2 ^ 53)
          (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ -$il)
          (hY1 : 2 ^ 52 ≤ ly * 2 ^ (-1022 - iy).toNat) (hY2 : ly * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
          (hlow : LowOk iy (((lx * 2 ^ $nl * 2 ^ (-$il - iy).toNat) % (ly * 2 ^ (-1022 - iy).toNat)).toNat)) :
          N_8002c0d8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (-$il))
              v14 (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (-1053)) =
            outv sx iy (((lx * 2 ^ $nl * 2 ^ (-$il - iy).toNat) % (ly * 2 ^ (-1022 - iy).toNat)).toNat) ∧
          T_8002c0d8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 (-$il))
              v14 (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (-1053)) = true := by
        have hXe : lx * 2 ^ $nl = ($hxw) * 2 ^ 32 := by (try simp only [Int.reducePow, Nat.reduceSub]) <;> omega
        rw [hXe] at hlow hX1 hX2 ⊢
        have h := d_c0e8 hro s r iy sx (-$il) ($hxw) ly h5 (by (try simp only [Int.reducePow, Nat.reduceSub] at hX1 ⊢) <;> omega)
          (by (try simp only [Int.reducePow, Nat.reduceSub] at hX2 ⊢) <;> omega) hm0 hm2 hiy1 (by omega) hY1 hY2
          (by omega) (by omega) hlow
        unfold N_8002c0d8 T_8002c0d8
        fm_nf
        simp only [Int.reducePow, Nat.reduceSub] at h ⊢
        exact h))
  return ⟨mkNullNode cmds⟩

fm_dc0d8_chambers 32 53

/-- **`x` deep** (`0x8002c0d8`, `e_fmod.c:84-87`: `hx = lx << (n - 32)`, then
`y`'s set-up `d_c0e8`). -/
theorem d_c0d8 {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64)
    (iy sx ix lx ly : Int) (v14 : BitVec 64) (h5 : sx = 0 ∨ sx = 2 ^ 31) (hl0 : 0 ≤ lx)
    (hix1 : -1074 ≤ ix) (hix2 : ix ≤ -1054)
    (hX1 : 2 ^ 52 ≤ lx * 2 ^ (-1022 - ix).toNat) (hX2 : lx * 2 ^ (-1022 - ix).toNat < 2 ^ 53)
    (hm0 : 0 ≤ ly) (hm2 : ly < 2 ^ 31) (hiy1 : -1074 ≤ iy) (hiy2 : iy ≤ ix)
    (hY1 : 2 ^ 52 ≤ ly * 2 ^ (-1022 - iy).toNat) (hY2 : ly * 2 ^ (-1022 - iy).toNat < 2 ^ 53)
    (hlow : LowOk iy (((lx * 2 ^ (-1022 - ix).toNat * 2 ^ (ix - iy).toNat) %
      (ly * 2 ^ (-1022 - iy).toNat)).toNat)) :
    N_8002c0d8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        v14 (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (-1053)) =
      outv sx iy (((lx * 2 ^ (-1022 - ix).toNat * 2 ^ (ix - iy).toNat) % (ly * 2 ^ (-1022 - iy).toNat)).toNat) ∧
    T_8002c0d8 m s r (BitVec.ofInt 64 iy) (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 ix)
        v14 (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (-1053)) = true := by
  fm_cover dc0d8 ix 32 53 at hX1 hX2 hlow using
    hro s r iy sx lx ly v14 h5 hl0 hX1 hX2 hm0 hm2 hiy1 hiy2 hY1 hY2 hlow

#print axioms d_c0d8

end Lua.Vm.Fn.Ieee754Fmod

import Lua.Vm.Fn.FmodTop
import Lua.Vm.Fn.SfRefFmodModel

/-!
# `__ieee754_fmod`, proved at level (b) (lane float-sf5)

(b1) `F_eq_ref`: the lifted function of `__ieee754_fmod` (`e_fmod.c`,
`Lua/Vm/Fn/Ieee754Fmod`) is `SfRef.fmod` on every pair of operands: the
operand tests (`Lua/Vm/Fn/FmodPre.lean`), the classes (`L_be1c`,
`Lua/Vm/Fn/FmodTop.lean`), and the bridge of the word lens to the fields
(`ilg_fields`, `sig_fields`, `outv_pack`, `lowOk_of`). (b2) `fmod_model`
(`Lua/Vm/Fn/SfRefFmodModel.lean`): `SfRef.fmod` is `Lua.Num.fmod` on the
model. `spec_proved` is the routine's level-2 equation.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Fmod

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim Lua.Num Lua.Num.SfRef

set_option linter.unusedVariables false

/-! ## The word lens of a datum (`EXTRACT_WORDS`) -/

/-- The sign word `hx & 0x80000000`. -/
def sw (x : F64) : Int := if x.sign then 2 ^ 31 else 0
/-- The high word without the sign. -/
def hw (x : F64) : Int := (x.bexp : Int) * 2 ^ 20 + (x.frac / 2 ^ 32 : Nat)
/-- The low word, sign-extended (`lw`). -/
def lw (x : F64) : Int := ((x.frac % 2 ^ 32 : Nat) : Int).bmod (2 ^ 32)

/-- The word lens's ranges (`EXTRACT_WORDS`). -/
structure LensOk (x : F64) : Prop where
  sgn : sw x = 0 ∨ sw x = 2 ^ 31
  h0 : 0 ≤ hw x
  h1 : hw x < 2 ^ 31
  l1 : -2 ^ 31 ≤ lw x
  l2 : lw x < 2 ^ 31
  lmod : lw x % 2 ^ 32 = ((x.frac % 2 ^ 32 : Nat) : Int)

theorem lens_bounds (x : F64) : LensOk x := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have h1 := Int.le_bmod (x := ((x.frac % 2 ^ 32 : Nat) : Int)) (m := 2 ^ 32) (by decide)
  have h2 := Int.bmod_lt (x := ((x.frac % 2 ^ 32 : Nat) : Int)) (m := 2 ^ 32) (by decide)
  have h3 : (((x.frac % 2 ^ 32 : Nat) : Int)).bmod (2 ^ 32) % 2 ^ 32 = ((x.frac % 2 ^ 32 : Nat) : Int) % 2 ^ 32 :=
    Int.bmod_emod
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (try unfold sw) <;> (try unfold hw) <;> (try unfold lw)
  · split <;> simp
  · omega
  · omega
  · omega
  · omega
  · rw [h3]; omega

/-- **A datum in the word lens.** -/
theorem lens_eq (x : F64) : x = BitVec.ofInt 64 ((sw x + hw x) * 2 ^ 32 + lw x % 2 ^ 32) := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hl := (lens_bounds x).lmod
  conv => lhs; rw [← bits_self x]
  rw [hl]
  unfold F64.bits sw hw
  rw [show ((if x.sign then (2 : Int) ^ 31 else 0) + ((x.bexp : Int) * 2 ^ 20 + ((x.frac / 2 ^ 32 : Nat) : Int))) *
      2 ^ 32 + ((x.frac % 2 ^ 32 : Nat) : Int) =
      (((if x.sign then 2 ^ 63 else 0) + x.bexp * 2 ^ 52 + x.frac : Nat) : Int) by split <;> omega]
  exact (ofInt_ofNat _).symm

/-! ## The lens's `ilogb`, significand and result are the reference's -/

theorem ilg_fields (x : F64) (h0 : x.bexp ≠ 0 ∨ x.frac ≠ 0) :
    ilg (hw x) (lw x) = normExp x.bexp x.frac := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hl := (lens_bounds x).lmod
  unfold ilg normExp
  by_cases he : x.bexp = 0
  · rw [if_neg (by unfold hw; rw [he]; omega), if_pos he]
    rw [hl, show Int.toNat (hw x * 2 ^ 32 + ((x.frac % 2 ^ 32 : Nat) : Int)) = x.frac by unfold hw; rw [he]; omega]
  · rw [if_pos (by unfold hw; omega), if_neg he]
    unfold hw; omega

theorem sig_fields (x : F64) (h0 : x.bexp ≠ 0 ∨ x.frac ≠ 0) :
    sig (hw x) (lw x) = (normSig x.bexp x.frac : Int) := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hl := (lens_bounds x).lmod
  have hi := ilg_fields x h0
  unfold sig normSig
  by_cases he : x.bexp = 0
  · rw [if_neg (by unfold hw; rw [he]; omega), if_pos he, hi]
    unfold normExp
    rw [if_pos he, hl, show (-1022 - ((x.frac.log2 : Int) - 1074)).toNat = 52 - x.frac.log2 by omega]
    rw [show hw x * 2 ^ 32 + ((x.frac % 2 ^ 32 : Nat) : Int) = (x.frac : Int) by unfold hw; rw [he]; omega]
    simp only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
  · rw [if_pos (by unfold hw; omega), if_neg he, hl]
    unfold hw; omega

/-- **The result** (`e_fmod.c:114-138`): `outv` is the reference's `fmodPack`. -/
theorem outv_pack (b : Bool) (iy : Int) (R : Nat) (hR : R < 2 ^ 53) :
    outv (if b then 2 ^ 31 else 0) iy R = fmodPack b iy R := by
  unfold outv fmodPack
  by_cases h0 : R = 0
  · rw [if_pos h0, if_pos h0]; cases b <;> decide
  rw [if_neg h0, if_neg h0]
  obtain ⟨n1, n2⟩ := norm52 (Nat.pos_of_ne_zero h0) hR
  generalize 52 - R.log2 = z at *
  simp only []
  have hc : (R : Int) * 2 ^ z = ((R * 2 ^ z : Nat) : Int) := by simp only [Int.natCast_mul, Int.natCast_pow, Int.cast_ofNat_Int]
  rw [hc]
  generalize R * 2 ^ z = M at *
  unfold packv F64.bits
  split
  · rename_i he
    rw [← ofInt_ofNat]
    congr 1
    split <;> omega
  · rename_i he
    rw [← ofInt_ofNat]
    have hk : ((M / 2 ^ (-1022 - (iy - (z : Int))).toNat : Nat) : Int) =
        (M : Int) / 2 ^ (-1022 - (iy - (z : Int))).toNat := by
      simp only [Int.natCast_ediv, Int.natCast_pow, Int.cast_ofNat_Int]
    congr 1
    rw [Int.natCast_add, hk]
    split <;> simp <;> omega

/-! ## The reference's main case, and the result's range -/

/-- `fmodFields` for `|x| > |y|`, both finite, `y ≠ 0`: the loop is the
remainder (`fmodLoop_rem`). -/
theorem fmodFields_gt (sx sy : Bool) (ex fx ey fy : Nat) (hex : ex ≤ 2046) (hey : ey ≤ 2046)
    (hfx : fx < 2 ^ 52) (hfy : fy < 2 ^ 52) (hx0 : ex ≠ 0 ∨ fx ≠ 0) (hy0 : ey ≠ 0 ∨ fy ≠ 0)
    (hgt : ey * 2 ^ 52 + fy < ex * 2 ^ 52 + fx) :
    fmodFields sx ex fx sy ey fy = fmodPack sx (normExp ey fy)
      (normSig ex fx * 2 ^ (normExp ex fx - normExp ey fy).toNat % normSig ey fy) := by
  have ⟨hmy1, hmy2⟩ := normSig_bounds ey fy hfy hy0
  have ⟨hmx1, hmx2⟩ := normSig_bounds ex fx hfx hx0
  unfold fmodFields
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  dsimp only
  rw [fmodLoop_pack, fmodLoop_rem _ _ _ (by omega) (by omega)]

/-- The remainder is a multiple of `2^(-1022 - iy)` when `y` is subnormal:
both operands are, at `y`'s scale. -/
theorem fmod_dvd (ex fx ey fy : Nat) (hfx : fx < 2 ^ 52) (hfy : fy < 2 ^ 52)
    (hle : normExp ey fy ≤ normExp ex fx) :
    normExp ey fy < -1022 → 2 ^ (-1022 - normExp ey fy).toNat ∣
      normSig ex fx * 2 ^ (normExp ex fx - normExp ey fy).toNat % normSig ey fy := by
  intro hlt
  have gx := ce_ge ex
  have gy := ce_ge ey
  have hnx := normExp_eq ex fx hfx
  have hny := normExp_eq ey fy hfy
  have sx := nsh_le ex fx hfx
  have sy := nsh_le ey fy hfy
  have dY : 2 ^ (-1022 - normExp ey fy).toNat ∣ normSig ey fy := by
    rw [normSig_eq]
    exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show (-1022 - normExp ey fy).toNat ≤ nsh ey fy by omega))
      (Nat.dvd_mul_left _ _)
  rw [Nat.dvd_mod_iff dY, normSig_eq, Nat.mul_assoc, ← Nat.pow_add]
  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 (show (-1022 - normExp ey fy).toNat ≤
    nsh ex fx + (normExp ex fx - normExp ey fy).toNat by omega)) (Nat.dvd_mul_left _ _)

/-- **The result's exponent is in range** (`LowOk`): `R · 2^(iy - 52)` is a
multiple of `2^-1074`. -/
theorem lowOk_of (iy : Int) (R : Nat) (hR : R < 2 ^ 53) (hiy : -1074 ≤ iy)
    (hd : iy < -1022 → 2 ^ (-1022 - iy).toNat ∣ R) : LowOk iy R := by
  intro h0
  have hL := log2_lt53 hR
  by_cases hlt : iy < -1022
  · have hk := Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (hd hlt)
    have := (Nat.le_log2 h0).2 hk
    omega
  · omega

theorem frem_fields (x y : F64) (hx0 : x.bexp ≠ 0 ∨ x.frac ≠ 0) (hy0 : y.bexp ≠ 0 ∨ y.frac ≠ 0) :
    frem (hw x) (lw x) (hw y) (lw y) =
      normSig x.bexp x.frac * 2 ^ (normExp x.bexp x.frac - normExp y.bexp y.frac).toNat %
        normSig y.bexp y.frac := by
  unfold frem
  rw [sig_fields x hx0, sig_fields y hy0, ilg_fields x hx0, ilg_fields y hy0]
  rw [show (2 : Int) ^ (normExp x.bexp x.frac - normExp y.bexp y.frac).toNat =
      ((2 ^ (normExp x.bexp x.frac - normExp y.bexp y.frac).toNat : Nat) : Int) by
    simp only [Int.natCast_pow, Int.cast_ofNat_Int], ← Int.natCast_mul, ← Int.natCast_emod, Int.toNat_natCast]

/-! ## The lens's arithmetic (one small `omega` each) -/

theorem lens_val (x : F64) : hw x * 2 ^ 32 + lw x % 2 ^ 32 = (x.bexp : Int) * 2 ^ 52 + x.frac := by
  have hl := (lens_bounds x).lmod
  rw [hl]; unfold hw; omega

theorem lens_sp (x y : F64) (h : (y.bexp = 0 ∧ y.frac = 0) ∨ x.bexp = 2047 ∨ (y.bexp = 2047 ∧ y.frac ≠ 0)) :
    (hw y = 0 ∧ lw y % 2 ^ 32 = 0) ∨ 2047 * 2 ^ 20 ≤ hw x ∨ 2047 * 2 ^ 20 < hw y ∨
      (hw y = 2047 * 2 ^ 20 ∧ lw y % 2 ^ 32 ≠ 0) := by
  have hfy : y.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hl := (lens_bounds y).lmod
  rw [hl]; unfold hw; omega

theorem hw_lt (x : F64) (h : x.bexp ≤ 2046) : hw x < 2047 * 2 ^ 20 := by
  have hfx : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold hw; omega

/-- A finite `y`'s high word, and an infinity's low word. -/
theorem hw_fin (y : F64) (h : y.bexp = 2047 → y.frac = 0) :
    hw y ≤ 2047 * 2 ^ 20 ∧ (hw y = 2047 * 2 ^ 20 → lw y = 0) := by
  have hby : y.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfy : y.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold hw lw
  refine ⟨by omega, fun h2 => ?_⟩
  rw [show y.frac % 2 ^ 32 = 0 by omega]; rfl

theorem lens_lt (x y : F64) (h : x.bexp * 2 ^ 52 + x.frac < y.bexp * 2 ^ 52 + y.frac) :
    hw x * 2 ^ 32 + lw x % 2 ^ 32 < hw y * 2 ^ 32 + lw y % 2 ^ 32 := by
  rw [lens_val, lens_val]; omega

theorem lens_ne0 (y : F64) (h : y.bexp ≠ 0 ∨ y.frac ≠ 0) : hw y * 2 ^ 32 + lw y % 2 ^ 32 ≠ 0 := by
  rw [lens_val]; omega

theorem lens_same (x y : F64) (h : x.bexp * 2 ^ 52 + x.frac = y.bexp * 2 ^ 52 + y.frac) :
    hw y = hw x ∧ lw x % 2 ^ 32 = lw y % 2 ^ 32 := by
  have hfx : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hfy : y.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hl := (lens_bounds x).lmod
  have hm := (lens_bounds y).lmod
  rw [hl, hm]; unfold hw; omega

theorem lens_ne0' (x y : F64) (h : x.bexp * 2 ^ 52 + x.frac = y.bexp * 2 ^ 52 + y.frac)
    (hy : y.bexp ≠ 0 ∨ y.frac ≠ 0) : hw x ≠ 0 ∨ lw y ≠ 0 := by
  have h1 := lens_ne0 y hy
  have ⟨e1, e2⟩ := lens_same x y h
  have hm := (lens_bounds y).lmod
  rw [e1] at h1
  by_cases h0 : hw x = 0
  · right; intro h3; rw [h3] at h1; omega
  · left; exact h0

/-! ## (b1) -/

/-- **(b1) for `__ieee754_fmod`**: its lifted function is `SfRef.fmod`, and
its termination function holds, on every pair of operands. -/
theorem F_eq_ref (m : Mem) (s : Nat) (r : BitVec 64) (x y : F64) (hs : FnSp s 128) (hro : RodataRead m) :
    F m s r x y = SfRef.fmod x y ∧ T m s r x y = true := by
  have hbx : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfx : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hby : y.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfy : y.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have LX := lens_bounds x
  have LY := lens_bounds y
  have eX := lens_eq x
  have eY := lens_eq y
  unfold SfRef.fmod
  by_cases hsp : (y.bexp = 0 ∧ y.frac = 0) ∨ x.bexp = 2047 ∨ (y.bexp = 2047 ∧ y.frac ≠ 0)
  · have h := pre_nan (m := m) s r (sw x) (hw x) (lw x) (sw y) (hw y) (lw y) LX.sgn LY.sgn LX.h0 LX.h1
      LY.h0 LY.h1 LX.l1 LX.l2 LY.l1 LY.l2 (lens_sp x y hsp)
    rw [← eX, ← eY, nan_beb0 s r x y hs, divmul_nan x y hsp] at h
    unfold fmodFields; rw [if_pos hsp]; exact h
  have hex : x.bexp ≤ 2046 := by clear LX LY eX eY; omega
  have hy0 : y.bexp ≠ 0 ∨ y.frac ≠ 0 := by clear LX LY eX eY; omega
  have hinf : y.bexp = 2047 → y.frac = 0 := by clear LX LY eX eY; omega
  have hxf := hw_lt x hex
  have hyf := hw_fin y hinf
  by_cases hlt : x.bexp * 2 ^ 52 + x.frac < y.bexp * 2 ^ 52 + y.frac
  · unfold fmodFields
    rw [if_neg hsp, if_pos hlt]
    have h := pre_lt (m := m) s r (sw x) (hw x) (lw x) (sw y) (hw y) (lw y) LX.sgn LY.sgn LX.h0 hxf LY.h0 hyf.1
      LX.l1 LX.l2 LY.l1 LY.l2 hyf.2 (lens_lt x y hlt)
    rw [← eX, ← eY] at h
    rw [bits_self x]; exact h
  by_cases heq : x.bexp * 2 ^ 52 + x.frac = y.bexp * 2 ^ 52 + y.frac
  · unfold fmodFields
    rw [if_neg hsp, if_neg hlt, if_pos heq]
    have ⟨hh, hl⟩ := lens_same x y heq
    rw [hh] at eY
    have h := pre_eq (m := m) hro s r (sw x) (hw x) (lw x) (sw y) (lw y) LX.sgn LY.sgn LX.h0 hxf
      LX.l1 LX.l2 LY.l1 LY.l2 (lens_ne0' x y heq hy0) hl
    rw [← eX, ← eY] at h
    rw [h.1, h.2]
    refine ⟨?_, rfl⟩
    unfold sw; cases x.sign <;> decide
  have hx0 : x.bexp ≠ 0 ∨ x.frac ≠ 0 := by clear LX LY eX eY; omega
  have hgt : y.bexp * 2 ^ 52 + y.frac < x.bexp * 2 ^ 52 + x.frac := by clear LX LY eX eY; omega
  have hey : y.bexp ≤ 2046 := by
    rcases Nat.lt_or_ge y.bexp 2047 with h | h
    · omega
    · have : 2047 * 2 ^ 52 ≤ y.bexp * 2 ^ 52 := Nat.mul_le_mul_right _ h
      clear LX LY eX eY; omega
  have hmono := normExp_mono hfx hfy hy0 hgt
  have hbd := normExp_bounds y.bexp y.frac hey hfy
  have ⟨hmy1, hmy2⟩ := normSig_bounds y.bexp y.frac hfy hy0
  have hR : normSig x.bexp x.frac * 2 ^ (normExp x.bexp x.frac - normExp y.bexp y.frac).toNat %
      normSig y.bexp y.frac < 2 ^ 53 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by omega)) (by omega)
  have hyf' := hw_lt y hey
  have h1 := pre_be1c (m := m) s r (sw x) (hw x) (lw x) (sw y) (hw y) (lw y) LX.sgn LY.sgn LX.h0 hxf LY.h0 hyf'
    LX.l1 LX.l2 LY.l1 LY.l2 (lens_ne0' y y rfl hy0) (lens_lt y x hgt)
  have h2 := L_be1c hro s r (sw x) (lw x) (hw x) (sw y) (hw y) (lw y) LX.sgn LY.sgn LX.h0 hxf LX.l1
    LX.l2 LY.h0 hyf' LY.l1 LY.l2 (lens_ne0 y hy0) (lens_lt y x hgt)
    (by rw [ilg_fields x hx0, ilg_fields y hy0]; exact hmono)
    (by rw [ilg_fields y hy0, frem_fields x y hx0 hy0]
        exact lowOk_of _ _ hR hbd.1 (fmod_dvd _ _ _ _ hfx hfy hmono))
  rw [← h1.1, ← h1.2, ← eX, ← eY, ilg_fields y hy0, frem_fields x y hx0 hy0] at h2
  rw [h2.1, h2.2, fmodFields_gt x.sign y.sign _ _ _ _ hex hey hfx hfy hx0 hy0 hgt]
  refine ⟨?_, rfl⟩
  exact outv_pack x.sign _ _ hR

/-! ## The level-2 equation and the summary -/

/-- The routine's value: `SfRef.fmod` (`e_fmod.c`), `Lua.Num.fmod` on the
model by `SfRef.fmod_model`. -/
abbrev S (a b : BitVec 64) : BitVec 64 := Lua.Num.SfRef.fmod a b

/-- **`__ieee754_fmod`'s level-2 equation** (`F = S`; the `Zero[]` table
read needs the image's `.rodata`). -/
theorem spec_proved (m : Mem) (s : Nat) (r a b : BitVec 64) (hsp : FnSp s 128) (hrod : RodataRead m) :
    F m s r a b = S a b :=
  (F_eq_ref m s r a b hsp hrod).1

/-- The termination function holds on every pair of operands. -/
theorem T_true (m : Mem) (s : Nat) (r a b : BitVec 64) (hsp : FnSp s 128) (hrod : RodataRead m) :
    T m s r a b = true :=
  (F_eq_ref m s r a b hsp hrod).2

open ConcurrencyInterfaceV1 Vsa.Logic in
/-- **`__ieee754_fmod`'s summary with the reference as its result** (`sum`
with `T_true` and `spec_proved`). It takes no premise: the NaN path's
`__divdf3` call is a call node of the proved `Divdf3.sum_div`
(`Lua/Vm/Fn/DivSum.lean`), whose frame stores the caller's `g`, so the memory
`Fm` takes `g`. -/
theorem sum_ref (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 128) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002bdb4#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, S v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm (m) s r g v10 v11) (s - 128) 128) o)) := by
  have h := sum m o s r g v10 v11 hs hr hrod (T_true m s r v10 v11 hs hrod)
  rwa [spec_proved m s r v10 v11 hs hrod] at h

end Lua.Vm.Fn.Ieee754Fmod

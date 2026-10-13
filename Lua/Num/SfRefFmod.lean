import Lua.Num.SfRefSpec

/-!
# `SfRef.fmod`: newlib's fdlibm `__ieee754_fmod` over the fields (lane float-sf5, (b2))

libm's `__ieee754_fmod` (newlib 4.5.0 `libm/math/e_fmod.c`, entry
`0x8002bdb4` in the ELF) works on the 32-bit halves `hx:lx`, `hy:ly` of its
operands. Over the fields `(s, e, f)` it is:

* `y = ±0`, `x` not finite or `y` a NaN: `(x*y)/(x*y)`, the canonical NaN
  (`e_fmod.c:47`);
* `|x| < |y|`: `x` (`e_fmod.c:52`); `|x| = |y|`: `Zero[sx]`, the zero of
  `x`'s sign (`e_fmod.c:54`);
* otherwise `ix = ilogb(x)`, `iy = ilogb(y)` (`e_fmod.c:58-77`, the
  subnormal ones by counting shifts: `normExp`) and the significands
  normalised to `[2^52, 2^53)` (`e_fmod.c:79-100`: `normSig`); the fix-point
  loop (`e_fmod.c:103-110`: `fmodLoop`, `n = ix - iy` doublings of `X =
  hx:lx` reduced by `Y = hy:ly`, `none` its early `return Zero[sx]`); the
  last subtraction (`e_fmod.c:111-112`); then the conversion back
  (`e_fmod.c:114-138`: `fmodPack`, normalise `R` to bit 52 with `iy`
  decremented, a normal or a subnormal result).

The shift-subtract loop is exact: (b2) is `fmod_model`, `SfRef.fmod` is
`Lua.Num.fmod` (`Lua/Num/Arith.lean`) on the model.
-/

namespace Lua.Num.SfRef

set_option linter.deprecated false

open F64

/-- The significand of a nonzero finite field pair, normalised to
`[2^52, 2^53)` (`e_fmod.c:79-100`, "set up {hx,lx}"): `|x| = normSig · 2^(normExp - 52)`. -/
def normSig (e f : Nat) : Nat := if e = 0 then f * 2 ^ (52 - f.log2) else 2 ^ 52 + f

/-- `ilogb` of a nonzero finite field pair (`e_fmod.c:58-77`): a subnormal's by its
leading bit. -/
def normExp (e f : Nat) : Int := if e = 0 then (f.log2 : Int) - 1074 else (e : Int) - 1023

/-- The fix-point loop (`e_fmod.c:103-110`): `n` doublings of `X = hx:lx`,
reduced by `Y = hy:ly` when `X ≥ Y`; `none` is the early `return Zero[sx]`
(`hz|lz == 0`). -/
def fmodLoop (Y : Nat) : Nat → Nat → Option Nat
  | 0, X => some X
  | n + 1, X =>
    if X < Y then fmodLoop Y n (2 * X)
    else if X = Y then none
    else fmodLoop Y n (2 * (X - Y))

/-- The conversion back (`e_fmod.c:114-138`): zero, or `R` normalised to bit 52
(`iy` decremented once per doubling) and packed normal (`iy ≥ -1022`) or
subnormal (shifted right by `-1022 - iy`). -/
def fmodPack (s : Bool) (iy : Int) (R : Nat) : F64 :=
  if R = 0 then zero s
  else
    let z := 52 - R.log2
    let e := iy - z
    if -1022 ≤ e then bits s (e + 1023).toNat (R * 2 ^ z - 2 ^ 52)
    else bits s 0 (R * 2 ^ z / 2 ^ (-1022 - e).toNat)

/-- `__ieee754_fmod` (`e_fmod.c`) over the operands' fields. -/
def fmodFields (sx : Bool) (ex fx : Nat) (_sy : Bool) (ey fy : Nat) : F64 :=
  if (ey = 0 ∧ fy = 0) ∨ ex = 2047 ∨ (ey = 2047 ∧ fy ≠ 0) then qnan
  else if ex * 2 ^ 52 + fx < ey * 2 ^ 52 + fy then bits sx ex fx
  else if ex * 2 ^ 52 + fx = ey * 2 ^ 52 + fy then zero sx
  else
    let Y := normSig ey fy
    match fmodLoop Y (normExp ex fx - normExp ey fy).toNat (normSig ex fx) with
    | none => zero sx
    | some X => fmodPack sx (normExp ey fy) (if Y ≤ X then X - Y else X)

/-- `SfRef.fmod`. -/
def fmod (x y : F64) : F64 := fmodFields x.sign x.bexp x.frac y.sign y.bexp y.frac

/-! ## The loop is the remainder -/

/-- **The fix-point loop's invariant** (`X < 2Y`): its early exit is a zero
remainder, and its result reduces to `X · 2^n mod Y`. -/
theorem fmodLoop_spec (Y : Nat) (hY : 0 < Y) : ∀ (n X : Nat), X < 2 * Y →
    (fmodLoop Y n X = none → X * 2 ^ n % Y = 0) ∧
    (∀ X', fmodLoop Y n X = some X' → X' < 2 * Y ∧ X' % Y = X * 2 ^ n % Y)
  | 0, X, hX => by
    refine ⟨fun h => by simp [fmodLoop] at h, fun X' h => ?_⟩
    simp only [fmodLoop, Option.some.injEq] at h
    subst h; simp [hX]
  | n + 1, X, hX => by
    have e2 : X * 2 ^ (n + 1) = 2 * X * 2 ^ n := by
      rw [Nat.pow_succ, Nat.mul_comm (2 ^ n) 2, ← Nat.mul_assoc, Nat.mul_comm X 2]
    by_cases h1 : X < Y
    · have ih := fmodLoop_spec Y hY n (2 * X) (by omega)
      simp only [fmodLoop, if_pos h1]
      rw [e2]; exact ih
    · by_cases h2 : X = Y
      · simp only [fmodLoop, if_neg h1, if_pos h2]
        subst h2
        refine ⟨fun _ => Nat.mul_mod_right _ _, fun X' h => by cases h⟩
      · have ih := fmodLoop_spec Y hY n (2 * (X - Y)) (by omega)
        simp only [fmodLoop, if_neg h1, if_neg h2]
        have e3 : X * 2 ^ (n + 1) % Y = 2 * (X - Y) * 2 ^ n % Y := by
          have : X * 2 ^ (n + 1) = 2 * (X - Y) * 2 ^ n + Y * (2 * 2 ^ n) := by
            rw [Nat.pow_succ]
            have hXY : X = (X - Y) + Y := by omega
            conv => lhs; rw [hXY]
            simp only [Nat.add_mul]
            ac_rfl
          rw [this, Nat.add_mul_mod_self_left]
        rw [e3]; exact ih

/-- The remainder after the last subtraction (`e_fmod.c:111-112`). -/
theorem fmodLoop_rem (Y n X : Nat) (hY : 0 < Y) (hX : X < 2 * Y) :
    (match fmodLoop Y n X with
      | none => (0 : Nat)
      | some X' => if Y ≤ X' then X' - Y else X') = X * 2 ^ n % Y := by
  have h := fmodLoop_spec Y hY n X hX
  split
  · rename_i hn; exact (h.1 hn).symm
  · rename_i X' hs
    obtain ⟨h1, h2⟩ := h.2 X' hs
    rw [← h2]
    split
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    · rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The conversion back is exact -/

theorem log2_lt53 {R : Nat} (h : R < 2 ^ 53) : R.log2 ≤ 52 := by
  rcases Nat.eq_zero_or_pos R with h0 | h0
  · subst h0; simp
  · exact Nat.lt_succ_iff.1 ((Nat.log2_lt (by omega)).2 h)

/-- `R` normalised to bit 52. -/
theorem norm52 {R : Nat} (h0 : 0 < R) (h : R < 2 ^ 53) :
    2 ^ 52 ≤ R * 2 ^ (52 - R.log2) ∧ R * 2 ^ (52 - R.log2) < 2 ^ 53 := by
  have hL := log2_lt53 h
  have h1 : 2 ^ R.log2 ≤ R := Nat.log2_self_le (by omega)
  have h2 : R < 2 ^ (R.log2 + 1) := Nat.lt_log2_self
  constructor
  · calc 2 ^ 52 = 2 ^ R.log2 * 2 ^ (52 - R.log2) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ R * 2 ^ (52 - R.log2) := Nat.mul_le_mul_right _ h1
  · calc R * 2 ^ (52 - R.log2) < 2 ^ (R.log2 + 1) * 2 ^ (52 - R.log2) :=
          Nat.mul_lt_mul_of_pos_right h2 (Nat.two_pow_pos _)
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega

/-- A normal field pair rounds to itself. -/
theorem bits_normal (s : Bool) (be M : Nat) (h1 : 1 ≤ be) (h2 : be ≤ 2046) (hM1 : 2 ^ 52 ≤ M)
    (hM2 : M < 2 ^ 53) : bits s be (M - 2 ^ 52) = roundExact s M ((be : Int) - 1075) := by
  have ⟨e1, e2, e3⟩ := fields_bits s be (M - 2 ^ 52) (by omega) (by omega)
  have hr := round_fields (bits s be (M - 2 ^ 52)) (by omega) (by omega)
  rw [e1, e2, e3] at hr
  unfold cm ce at hr
  rw [if_neg (by omega), if_neg (by omega), show M - 2 ^ 52 + 2 ^ 52 = M by omega] at hr
  exact hr.symm

/-- A subnormal field pair rounds to itself. -/
theorem bits_sub (s : Bool) (q : Nat) (h0 : 0 < q) (h : q < 2 ^ 52) :
    bits s 0 q = roundExact s q (-1074) := by
  have ⟨e1, e2, e3⟩ := fields_bits s 0 q (by omega) h
  have hr := round_fields (bits s 0 q) (by omega) (by omega)
  rw [e1, e2, e3] at hr
  exact hr.symm

/-- **The conversion back** (`e_fmod.c:114-138`) is the exact rounding of
`R · 2^(iy - 52)`, when that value is a multiple of `2^-1074`. -/
theorem fmodPack_eq (s : Bool) (iy : Int) (R : Nat) (hR : R < 2 ^ 53) (hiy : iy ≤ 1023)
    (hd : iy < -1022 → 2 ^ (-1022 - iy).toNat ∣ R) :
    fmodPack s iy R = roundExact s R (iy - 52) := by
  unfold fmodPack
  split
  · rename_i h; subst h; exact (round_zero s _).symm
  rename_i hR0
  have hpos : 0 < R := Nat.pos_of_ne_zero hR0
  have hL := log2_lt53 hR
  obtain ⟨hn1, hn2⟩ := norm52 hpos hR
  generalize hz : 52 - R.log2 = z at hn1 hn2
  have hsc : roundExact s (R * 2 ^ z) (iy - 52 - z) = roundExact s R (iy - 52) :=
    round_scale s R z (iy - 52)
  dsimp only
  split
  · rename_i he
    rw [bits_normal s _ _ (by omega) (by omega) hn1 hn2, ← hsc]
    congr 1; omega
  · rename_i he
    have hk : 0 < (-1022 - (iy - z)).toNat := by omega
    -- the dropped bits are zero
    have hdv : 2 ^ (-1022 - (iy - z)).toNat ∣ R * 2 ^ z := by
      by_cases hiy2 : iy < -1022
      · have h1 := hd hiy2
        have : (-1022 - (iy - z)).toNat = (-1022 - iy).toNat + z := by omega
        rw [this, Nat.pow_add]
        exact Nat.mul_dvd_mul_right h1 _
      · have : (-1022 - (iy - z)).toNat ≤ z := by omega
        exact Nat.dvd_trans (Nat.pow_dvd_pow 2 this) (Nat.dvd_mul_left _ _)
    obtain ⟨q, hq⟩ := hdv
    have hk2 := Nat.two_pow_pos (-1022 - (iy - z)).toNat
    rw [hq, Nat.mul_div_cancel_left _ hk2]
    have hq0 : 0 < q := by
      rcases Nat.eq_zero_or_pos q with h | h
      · rw [h, Nat.mul_zero] at hq; omega
      · exact h
    have hq52 : q < 2 ^ 52 := by
      have : 2 ≤ 2 ^ (-1022 - (iy - z)).toNat := by
        calc 2 = 2 ^ 1 := rfl
          _ ≤ _ := Nat.pow_le_pow_right (by decide) hk
      have : 2 * q ≤ 2 ^ (-1022 - (iy - z)).toNat * q := Nat.mul_le_mul_right _ this
      omega
    rw [bits_sub s q hq0 hq52, ← hsc, hq, Nat.mul_comm]
    have hs2 : roundExact s (q * 2 ^ (-1022 - (iy - z)).toNat) (-1074 - (-1022 - (iy - z)).toNat) =
        roundExact s q (-1074) := round_scale s q (-1022 - (iy - z)).toNat (-1074)
    rw [← hs2]
    congr 1; omega

/-! ## The fields: normalised significands, scaled values -/

/-- The normalising shift of a significand (`0` for a normal one). -/
def nsh (e f : Nat) : Nat := if e = 0 then 52 - f.log2 else 0

theorem normSig_eq (e f : Nat) : normSig e f = cm e f * 2 ^ nsh e f := by
  unfold normSig cm nsh; split <;> simp; omega

theorem log2_lt52 {f : Nat} (hf : f < 2 ^ 52) : f.log2 ≤ 51 := by
  rcases Nat.eq_zero_or_pos f with h0 | h0
  · subst h0; simp
  · exact Nat.lt_succ_iff.1 ((Nat.log2_lt (by omega)).2 hf)

theorem normExp_eq (e f : Nat) (hf : f < 2 ^ 52) : normExp e f = ce e - nsh e f + 52 := by
  have := log2_lt52 hf
  unfold normExp ce nsh; split <;> omega

theorem normExp_bounds (e f : Nat) (he : e ≤ 2046) (hf : f < 2 ^ 52) :
    -1074 ≤ normExp e f ∧ normExp e f ≤ 1023 := by
  have := log2_lt52 hf
  unfold normExp; split <;> omega

theorem nsh_le (e f : Nat) (hf : f < 2 ^ 52) : nsh e f ≤ 52 := by unfold nsh; split <;> omega

theorem normSig_bounds (e f : Nat) (hf : f < 2 ^ 52) (h0 : e ≠ 0 ∨ f ≠ 0) :
    2 ^ 52 ≤ normSig e f ∧ normSig e f < 2 ^ 53 := by
  unfold normSig
  split
  · rename_i he
    have hpos : 0 < f := by omega
    exact norm52 hpos (by omega)
  · omega

/-- The value of fields `(e, f)` in units of `2^-1074`. -/
def vu (e f : Nat) : Nat := cm e f * 2 ^ (ce e + 1074).toNat

/-- The value is monotone in the bit pattern. -/
theorem vu_lt {e1 f1 e2 f2 : Nat} (hf1 : f1 < 2 ^ 52) (hf2 : f2 < 2 ^ 52)
    (h : e1 * 2 ^ 52 + f1 < e2 * 2 ^ 52 + f2) : vu e1 f1 < vu e2 f2 := by
  unfold vu cm ce
  by_cases he : e1 = e2
  · subst he
    have hf : f1 < f2 := by omega
    split
    · simp; omega
    · exact Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
  have he2 : e1 < e2 := by
    rcases Nat.lt_or_ge e1 e2 with h' | h'
    · exact h'
    · have : e2 * 2 ^ 52 + 2 ^ 52 ≤ e1 * 2 ^ 52 := by
        have := Nat.mul_le_mul_right (2 ^ 52) (show e2 + 1 ≤ e1 by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; exact this
      omega
  rw [if_neg (show ¬ e2 = 0 by omega), if_neg (show ¬ e2 = 0 by omega)]
  have hb : 2 ^ 52 ≤ (f2 + 2 ^ 52) * 2 ^ (((e2 : Int) - 1075 + 1074).toNat) :=
    Nat.le_trans (by omega) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  split
  · rename_i h0
    simp only [show ((-1074 : Int) + 1074).toNat = 0 from rfl, Nat.pow_zero, Nat.mul_one]
    omega
  · rename_i h0
    have hk : ((e1 : Int) - 1075 + 1074).toNat + 1 ≤ ((e2 : Int) - 1075 + 1074).toNat := by omega
    calc (f1 + 2 ^ 52) * 2 ^ (((e1 : Int) - 1075 + 1074).toNat)
        < 2 ^ 53 * 2 ^ (((e1 : Int) - 1075 + 1074).toNat) :=
          Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)
      _ = 2 ^ 52 * 2 ^ (((e1 : Int) - 1075 + 1074).toNat + 1) := by
          rw [show (2 : Nat) ^ 53 = 2 ^ 52 * 2 by decide,
            Nat.pow_succ 2 (((e1 : Int) - 1075 + 1074).toNat)]; ac_rfl
      _ ≤ 2 ^ 52 * 2 ^ (((e2 : Int) - 1075 + 1074).toNat) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hk)
      _ ≤ (f2 + 2 ^ 52) * 2 ^ (((e2 : Int) - 1075 + 1074).toNat) :=
          Nat.mul_le_mul_right _ (by omega)

/-- A value at a common exponent `t ≤ ce e` is the value in units of
`2^-1074`, scaled. -/
theorem vu_scale (e f : Nat) (t : Int) (ht : t ≤ ce e) (ht2 : -1074 ≤ t) :
    cm e f * 2 ^ (ce e - t).toNat * 2 ^ (t + 1074).toNat = vu e f := by
  unfold vu
  rw [Nat.mul_assoc, ← Nat.pow_add]
  congr 2
  have := ce_ge e
  omega

theorem log2_mono {a b : Nat} (h : a ≤ b) : a.log2 ≤ b.log2 := by
  rcases Nat.eq_zero_or_pos a with h0 | h0
  · subst h0; simp
  · exact (Nat.le_log2 (by omega)).2 (Nat.le_trans (Nat.log2_self_le (by omega)) h)

/-- `ilogb` is monotone in the bit pattern. -/
theorem normExp_mono {ex fx ey fy : Nat} (hfx : fx < 2 ^ 52) (hfy : fy < 2 ^ 52)
    (hy0 : ey ≠ 0 ∨ fy ≠ 0) (h : ey * 2 ^ 52 + fy < ex * 2 ^ 52 + fx) :
    normExp ey fy ≤ normExp ex fx := by
  have h1 := log2_lt52 hfx
  have h2 := log2_lt52 hfy
  unfold normExp
  by_cases hx : ex = 0
  · have hy : ey = 0 := by
      rcases Nat.eq_zero_or_pos ey with h' | h'
      · exact h'
      · have : 2 ^ 52 ≤ ey * 2 ^ 52 := Nat.le_mul_of_pos_left _ h'
        omega
    rw [if_pos hx, if_pos hy]
    have : fy.log2 ≤ fx.log2 := log2_mono (by omega)
    omega
  · rw [if_neg hx]
    split
    · omega
    · rename_i hy
      have : ey ≤ ex := by
        rcases Nat.lt_or_ge ex ey with h' | h'
        · have : ex * 2 ^ 52 + 2 ^ 52 ≤ ey * 2 ^ 52 := by
            have := Nat.mul_le_mul_right (2 ^ 52) (show ex + 1 ≤ ey by omega)
            rw [Nat.add_mul, Nat.one_mul] at this; exact this
          omega
        · exact h'
      omega

/-! ## (b2) on finite operands -/

/-- The conversion's argument: `match` over the loop, as a remainder. -/
theorem fmodLoop_pack (s : Bool) (iy : Int) (Y n X : Nat) :
    (match fmodLoop Y n X with
      | none => zero s
      | some X' => fmodPack s iy (if Y ≤ X' then X' - Y else X')) =
    fmodPack s iy (match fmodLoop Y n X with
      | none => (0 : Nat)
      | some X' => if Y ≤ X' then X' - Y else X') := by
  split <;> simp [fmodPack]

/-- **(b2) for two finite operands, `y ≠ 0`**: the model's remainder at the
smaller exponent, exactly rounded (`Lua.Num.fmod`'s finite branch). -/
theorem fmodFields_fin (sx sy : Bool) (ex fx ey fy : Nat) (hex : ex ≤ 2046) (hey : ey ≤ 2046)
    (hfx : fx < 2 ^ 52) (hfy : fy < 2 ^ 52) (hx0 : ex ≠ 0 ∨ fx ≠ 0) (hy0 : ey ≠ 0 ∨ fy ≠ 0) :
    fmodFields sx ex fx sy ey fy =
      let e := min (ce ex) (ce ey)
      let r := (cm ex fx * 2 ^ (ce ex - e).toNat) % (cm ey fy * 2 ^ (ce ey - e).toNat)
      if r = 0 then zero sx else roundExact sx r e := by
  have hcx := cm_bounds ex fx hfx
  have hcy := cm_bounds ey fy hfy
  have hpx := cm_pos hx0
  have hpy := cm_pos hy0
  have gx := ce_ge ex
  have gy := ce_ge ey
  dsimp only
  generalize he : min (ce ex) (ce ey) = e
  have hle1 : e ≤ ce ex := by omega
  have hle2 : e ≤ ce ey := by omega
  have hge : -1074 ≤ e := by omega
  -- the operands at the common exponent `e`, in units of `2^-1074`
  have sx' := vu_scale ex fx e hle1 hge
  have sy' := vu_scale ey fy e hle2 hge
  have hP := Nat.two_pow_pos (e + 1074).toNat
  unfold fmodFields
  rw [if_neg (by omega)]
  by_cases hlt : ex * 2 ^ 52 + fx < ey * 2 ^ 52 + fy
  · -- `|x| < |y|`: `x`
    rw [if_pos hlt]
    have hv := vu_lt hfx hfy hlt
    have hXY : cm ex fx * 2 ^ (ce ex - e).toNat < cm ey fy * 2 ^ (ce ey - e).toNat := by
      rw [← sx', ← sy'] at hv; exact Nat.lt_of_mul_lt_mul_right hv
    rw [Nat.mod_eq_of_lt hXY, if_neg (Nat.ne_of_gt (Nat.mul_pos hpx (Nat.two_pow_pos _)))]
    have hs : roundExact sx (cm ex fx * 2 ^ (ce ex - e).toNat) (ce ex - ((ce ex - e).toNat : Int)) =
        roundExact sx (cm ex fx) (ce ex) := round_scale sx (cm ex fx) (ce ex - e).toNat (ce ex)
    rw [show ce ex - ((ce ex - e).toNat : Int) = e by omega] at hs
    rw [hs]
    have ⟨e1, e2, e3⟩ := fields_bits sx ex fx (by omega) hfx
    have hr := round_fields (bits sx ex fx) (by omega) (by omega)
    rw [e1, e2, e3] at hr
    exact hr.symm
  rw [if_neg hlt]
  by_cases heq : ex * 2 ^ 52 + fx = ey * 2 ^ 52 + fy
  · -- `|x| = |y|`: `Zero[sx]`
    rw [if_pos heq]
    have h1 : ex = ey := by
      rcases Nat.lt_trichotomy ex ey with h' | h' | h'
      · have := Nat.mul_le_mul_right (2 ^ 52) (show ex + 1 ≤ ey by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      · exact h'
      · have := Nat.mul_le_mul_right (2 ^ 52) (show ey + 1 ≤ ex by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
    have h2 : fx = fy := by subst h1; omega
    subst h1 h2
    rw [Nat.mod_self, if_pos rfl]
  rw [if_neg heq]
  have hgt : ey * 2 ^ 52 + fy < ex * 2 ^ 52 + fx := by omega
  -- the main case: the loop is the remainder at `iy - 52`
  have hmono := normExp_mono hfx hfy hy0 hgt
  have hnx := normExp_eq ex fx hfx
  have hny := normExp_eq ey fy hfy
  have hbx := normExp_bounds ex fx hex hfx
  have hby := normExp_bounds ey fy hey hfy
  have hsx := nsh_le ex fx hfx
  have hsy := nsh_le ey fy hfy
  have ⟨hmy1, hmy2⟩ := normSig_bounds ey fy hfy hy0
  have ⟨hmx1, hmx2⟩ := normSig_bounds ex fx hfx hx0
  rw [fmodLoop_pack, fmodLoop_rem _ _ _ (by omega) (by omega)]
  -- `mx · 2^n = cm ex fx · 2^j1`, `my = cm ey fy · 2^j2`, both `2^d` times the model's
  have hd : 0 ≤ e - (normExp ey fy - 52) := by omega
  have hX : normSig ex fx * 2 ^ (normExp ex fx - normExp ey fy).toNat =
      cm ex fx * 2 ^ (ce ex - e).toNat * 2 ^ (e - (normExp ey fy - 52)).toNat := by
    rw [normSig_eq, Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    congr 2; omega
  have hY : normSig ey fy = cm ey fy * 2 ^ (ce ey - e).toNat * 2 ^ (e - (normExp ey fy - 52)).toNat := by
    rw [normSig_eq, Nat.mul_assoc, ← Nat.pow_add]
    congr 2; omega
  rw [hX, hY, Nat.mul_mod_mul_right]
  generalize hr : cm ex fx * 2 ^ (ce ex - e).toNat % (cm ey fy * 2 ^ (ce ey - e).toNat) = r
  have hrlt : r < cm ey fy * 2 ^ (ce ey - e).toNat := by
    rw [← hr]; exact Nat.mod_lt _ (Nat.mul_pos hpy (Nat.two_pow_pos _))
  have hR53 : r * 2 ^ (e - (normExp ey fy - 52)).toNat < 2 ^ 53 := by
    have : r * 2 ^ (e - (normExp ey fy - 52)).toNat <
        cm ey fy * 2 ^ (ce ey - e).toNat * 2 ^ (e - (normExp ey fy - 52)).toNat :=
      Nat.mul_lt_mul_of_pos_right hrlt (Nat.two_pow_pos _)
    rw [← hY] at this; omega
  rw [fmodPack_eq sx (normExp ey fy) _ hR53 (by omega) (fun hlo => by
    apply Nat.dvd_trans (Nat.pow_dvd_pow 2
      (show (-1022 - normExp ey fy).toNat ≤ (e - (normExp ey fy - 52)).toNat by omega))
    exact Nat.dvd_mul_left _ _)]
  by_cases hr0 : r = 0
  · rw [hr0, if_pos rfl, Nat.zero_mul]; exact round_zero sx _
  · rw [if_neg hr0]
    have hs : roundExact sx (r * 2 ^ (e - (normExp ey fy - 52)).toNat)
        (e - ((e - (normExp ey fy - 52)).toNat : Int)) = roundExact sx r e :=
      round_scale sx r (e - (normExp ey fy - 52)).toNat e
    rw [show e - ((e - (normExp ey fy - 52)).toNat : Int) = normExp ey fy - 52 by omega] at hs
    exact hs

/-- **(b2) for `fmod`**, by the operands' classes, in the shape of
`Lua.Num.fmod` (`Lua/Num/Arith.lean`): NaN for a NaN operand, `x = ±∞` or
`y = ±0`; `x` for `x = ±0` or `y = ±∞`; otherwise the exact remainder at
the smaller exponent, rounded exactly (`fmodFields_fin`). -/
theorem fmod_cls (x y : F64) : fmod x y = match x.cls, y.cls with
    | .nan, _ => qnan
    | _, .nan => qnan
    | .inf _, _ => qnan
    | _, .zero _ => qnan
    | .zero _, _ => x
    | .fin .., .inf _ => x
    | .fin s m₁ e₁, .fin _ m₂ e₂ =>
      let e := min e₁ e₂
      let r := (m₁ <<< (e₁ - e).toNat) % (m₂ <<< (e₂ - e).toNat)
      if r = 0 then zero s else roundExact s r e := by
  have hbx : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfx : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hby : y.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfy : y.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hx := bits_self x
  unfold fmod
  -- the special operands
  by_cases xn : x.bexp = 2047 ∧ x.frac ≠ 0
  · have hc : x.cls = .nan := by unfold cls; rw [if_pos xn.1, if_neg xn.2]
    rw [hc]; unfold fmodFields; rw [if_pos (Or.inr (Or.inl xn.1))]
  by_cases yn : y.bexp = 2047 ∧ y.frac ≠ 0
  · have hc : y.cls = .nan := by unfold cls; rw [if_pos yn.1, if_neg yn.2]
    rw [hc]; unfold fmodFields; rw [if_pos (Or.inr (Or.inr yn))]
    split <;> simp_all
  by_cases xi : x.bexp = 2047
  · have hc : x.cls = .inf x.sign := by unfold cls; rw [if_pos xi, if_pos (by omega)]
    rw [hc]; unfold fmodFields; rw [if_pos (Or.inr (Or.inl xi))]
    split <;> simp_all
  by_cases yz : y.bexp = 0 ∧ y.frac = 0
  · have hc : y.cls = .zero y.sign := by unfold cls; rw [if_neg (by omega), if_pos yz.1, if_pos yz.2]
    rw [hc]; unfold fmodFields; rw [if_pos (Or.inl yz)]
    split <;> simp_all
  have hcx : x.cls = if x.bexp = 0 ∧ x.frac = 0 then .zero x.sign else .fin x.sign (cm x.bexp x.frac) (ce x.bexp) := by
    unfold cls cm ce; rw [if_neg xi]; split <;> split <;> simp_all
  by_cases yi : y.bexp = 2047
  · -- `y = ±∞`: `x`
    have hc : y.cls = .inf y.sign := by unfold cls; rw [if_pos yi, if_pos (by omega)]
    unfold fmodFields
    rw [if_neg (by omega), if_pos (by omega), hc, hcx]
    by_cases xz : x.bexp = 0 ∧ x.frac = 0
    · rw [if_pos xz]; exact hx
    · rw [if_neg xz]; exact hx
  have hcy : y.cls = .fin y.sign (cm y.bexp y.frac) (ce y.bexp) := by
    unfold cls cm ce; rw [if_neg yi]; split <;> simp_all
  by_cases xz : x.bexp = 0 ∧ x.frac = 0
  · -- `x = ±0`: `x`
    rw [hcy, hcx, if_pos xz]
    unfold fmodFields
    rw [if_neg (by omega), if_pos (by omega)]
    exact hx
  rw [hcy, hcx, if_neg xz]
  simp only []
  rw [fmodFields_fin _ _ _ _ _ _ (by omega) (by omega) hfx hfy (by omega) (by omega)]
  simp only [align_eq, Nat.shiftLeft_eq]

end Lua.Num.SfRef

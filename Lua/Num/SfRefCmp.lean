import Lua.Num.SfRefSpec

/-!
# `SfRef` comparisons: `__eqdf2`, `__ledf2`, `__gedf2` (lane float-sf2)

The soft-fp-shaped references of the comparison routines, over the operands'
fields (libgcc `soft-fp/op-common.h` `_FP_CMP` and `_FP_CMP_EQ`, through
`soft-fp/double.h` `FP_CMP_D`/`FP_CMP_EQ_D`; `soft-fp/{eqdf2,ledf2,gedf2}.c`
pass `un` = `1`, `2`, `-2`), and (b2): each is the `F64` comparison.

No rounding is involved. The law is round 1's `compare_key`: off NaN, the
IEEE order is the integer order on the sign-magnitude key
`±(e · 2^52 + f)` (`key`), which is also what `F64.compare`'s
lexicographic order on `(exponent, mantissa)` computes (`lex_mag`).
-/

namespace Lua.Num.SfRef

open F64

/-- `_FP_CMP_D (ret, X, Y, un, 2)` (`op-common.h`), over the fields:
unordered (a NaN operand) gives `un`; two zeros are equal whatever their
signs; otherwise the sign, then the exponent, then the fraction decide. -/
def cmpFields (un : Int) (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat) : Int :=
  if (ea = 2047 ∧ fa ≠ 0) ∨ (eb = 2047 ∧ fb ≠ 0) then un
  else if ea = 0 ∧ fa = 0 ∧ eb = 0 ∧ fb = 0 then 0
  else if ea = 0 ∧ fa = 0 then (if sb then 1 else -1)
  else if eb = 0 ∧ fb = 0 then (if sa then -1 else 1)
  else if sa ≠ sb then (if sa then -1 else 1)
  else if eb < ea then (if sa then -1 else 1)
  else if ea < eb then (if sa then 1 else -1)
  else if fb < fa then (if sa then -1 else 1)
  else if fa < fb then (if sa then 1 else -1)
  else 0

/-- `_FP_CMP_EQ_D (ret, X, Y, 2)` (`op-common.h`): `0` iff equal (`-0 = +0`),
`1` otherwise and on a NaN operand. -/
def eqFields (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat) : Int :=
  if (ea = 2047 ∧ fa ≠ 0) ∨ (eb = 2047 ∧ fb ≠ 0) then 1
  else if ea = eb ∧ fa = fb ∧ (sa = sb ∨ (ea = 0 ∧ fa = 0)) then 0 else 1

/-- `__ledf2` (`un = 2`) and `__gedf2` (`un = -2`). -/
def cmp (un : Int) (a b : F64) : Int := cmpFields un a.sign a.bexp a.frac b.sign b.bexp b.frac
/-- `__eqdf2`. -/
def eqv (a b : F64) : Int := eqFields a.sign a.bexp a.frac b.sign b.bexp b.frac

/-- The routines' result for a three-way comparison (`un`: unordered). -/
def ordInt (un : Int) : Option Ordering → Int
  | none => un
  | some .lt => -1
  | some .eq => 0
  | some .gt => 1

/-! ## (b2) -/

theorem ord_int (a b : Int) : Ord.compare a b = if a < b then .lt else if a = b then .eq else .gt := rfl
theorem ord_nat (a b : Nat) : Ord.compare a b = if a < b then .lt else if a = b then .eq else .gt := rfl

/-- `compare_key` on finite operands of one sign: `F64.compare`'s
lexicographic order on `(ce, cm)` is the order of `e · 2^52 + f`. -/
theorem lex_mag (ea fa eb fb : Nat) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) :
    (Ord.compare (ce ea) (ce eb)).then (Ord.compare (cm ea fa) (cm eb fb)) =
      if ea * 2 ^ 52 + fa < eb * 2 ^ 52 + fb then .lt
      else if ea * 2 ^ 52 + fa = eb * 2 ^ 52 + fb then .eq else .gt := by
  rw [ord_int, ord_nat]
  unfold ce cm
  by_cases h1 : ea = 0 <;> by_cases h2 : eb = 0 <;> simp only [h1, h2, ite_true, ite_false] <;>
    (repeat' split) <;> first | rfl | (exfalso; omega)

/-- The sign-magnitude key of the fields (`compare_key`). -/
def key (s : Bool) (e f : Nat) : Int := if s then -((e * 2 ^ 52 + f : Nat) : Int) else ((e * 2 ^ 52 + f : Nat) : Int)

/-- Three-way order of two integers. -/
def ordO (x y : Int) : Ordering := if x < y then .lt else if x = y then .eq else .gt

/-- `_FP_CMP_D` off NaN is the order of the keys. -/
theorem cmpFields_key (un : Int) (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52)
    (han : ¬ (ea = 2047 ∧ fa ≠ 0)) (hbn : ¬ (eb = 2047 ∧ fb ≠ 0)) :
    cmpFields un sa ea fa sb eb fb = ordInt un (some (ordO (key sa ea fa) (key sb eb fb))) := by
  unfold cmpFields key ordO
  rw [if_neg (by omega)]
  cases sa <;> cases sb <;> simp only [ite_true, ite_false, Bool.false_eq_true, ne_eq, not_true_eq_false,
    not_false_eq_true, reduceCtorEq] <;> (repeat' split) <;> first | rfl | (exfalso; omega)

/-- `F64.compare` off NaN is the order of the keys (`compare_key`). -/
theorem compare_key (a b : F64) (han : ¬ (a.bexp = 2047 ∧ a.frac ≠ 0)) (hbn : ¬ (b.bexp = 2047 ∧ b.frac ≠ 0)) :
    F64.compare a b = some (ordO (key a.sign a.bexp a.frac) (key b.sign b.bexp b.frac)) := by
  have hfa : a.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hea : a.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hfb : b.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have heb : b.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hcls : ∀ x : F64, x.bexp < 2048 → x.frac < 2 ^ 52 → ¬ (x.bexp = 2047 ∧ x.frac ≠ 0) →
      (x.bexp = 2047 ∧ x.frac = 0 ∧ x.cls = .inf x.sign) ∨ (x.bexp = 0 ∧ x.frac = 0 ∧ x.cls = .zero x.sign) ∨
      ((x.bexp ≠ 0 ∨ x.frac ≠ 0) ∧ x.bexp ≠ 2047 ∧ x.cls = .fin x.sign (cm x.bexp x.frac) (ce x.bexp)) := by
    intro x h1 h2 h3
    by_cases hi : x.bexp = 2047
    · exact Or.inl ⟨hi, by omega, cls_inf' hi (by omega)⟩
    by_cases hz : x.bexp = 0 ∧ x.frac = 0
    · exact Or.inr (Or.inl ⟨hz.1, hz.2, cls_zero' hz.1 hz.2⟩)
    · exact Or.inr (Or.inr ⟨by omega, hi, cls_fin' (by omega) hi⟩)
  have hl := lex_mag a.bexp a.frac b.bexp b.frac hfa hfb
  unfold F64.compare
  rcases hcls a hea hfa han with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
  rcases hcls b heb hfb hbn with ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ | ⟨g1, g2, g3⟩ <;>
  rw [h3, g3] <;> generalize a.sign = sa at * <;> generalize b.sign = sb at * <;>
  cases sa <;> cases sb <;> dsimp only <;> rw [Option.some.injEq] <;> (try rw [hl]) <;>
  simp only [key, ordO, Bool.false_eq_true, ite_true, ite_false, Bool.not_false, Bool.not_true, ↓reduceIte] <;>
  (repeat' split) <;> first | rfl | (exfalso; omega)

/-- **(b2) for `__ledf2`/`__gedf2`**: `_FP_CMP_D` is `F64.compare`. -/
theorem cmp_eq (un : Int) (a b : F64) : cmp un a b = ordInt un (F64.compare a b) := by
  have hfa : a.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hfb : b.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold cmp
  by_cases han : a.bexp = 2047 ∧ a.frac ≠ 0
  · unfold F64.compare cmpFields; rw [cls_nan' han.1 han.2, if_pos (Or.inl han)]; rfl
  by_cases hbn : b.bexp = 2047 ∧ b.frac ≠ 0
  · unfold F64.compare cmpFields; rw [cls_nan' hbn.1 hbn.2, if_pos (Or.inr hbn)]; cases a.cls <;> rfl
  rw [cmpFields_key un _ _ _ _ _ _ hfa hfb han hbn, compare_key a b han hbn]

/-- `_FP_CMP_EQ_D` off NaN is the equality of the keys. -/
theorem eqFields_key (sa : Bool) (ea fa : Nat) (sb : Bool) (eb fb : Nat)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52)
    (han : ¬ (ea = 2047 ∧ fa ≠ 0)) (hbn : ¬ (eb = 2047 ∧ fb ≠ 0)) :
    eqFields sa ea fa sb eb fb = if key sa ea fa = key sb eb fb then 0 else 1 := by
  unfold eqFields key
  rw [if_neg (by omega)]
  cases sa <;> cases sb <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, false_or, true_or,
    and_true, eq_self_iff_true] <;> (repeat' split) <;> first | rfl | (exfalso; omega)

/-- **(b2) for `__eqdf2`**: `_FP_CMP_EQ_D` is `F64.eq`. -/
theorem eqv_eq (a b : F64) : eqv a b = if F64.eq a b then 0 else 1 := by
  have hfa : a.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hfb : b.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold eqv F64.eq
  by_cases han : a.bexp = 2047 ∧ a.frac ≠ 0
  · unfold F64.compare eqFields; rw [cls_nan' han.1 han.2, if_pos (Or.inl han)]; rfl
  by_cases hbn : b.bexp = 2047 ∧ b.frac ≠ 0
  · unfold F64.compare eqFields; rw [cls_nan' hbn.1 hbn.2, if_pos (Or.inr hbn)]; cases a.cls <;> rfl
  rw [eqFields_key _ _ _ _ _ _ hfa hfb han hbn, compare_key a b han hbn]
  unfold ordO
  (repeat' split) <;> first | rfl | (exfalso; simp_all)

end Lua.Num.SfRef

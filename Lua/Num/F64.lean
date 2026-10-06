/-!
# `F64`: an exact-dyadic binary64 library over `BitVec 64`, proved equal to `Float.Model`

δ's float spec is Lean core's `Float.Model` (`Init/Data/Float/Model/`,
`abstractions/FLOAT-DESIGN.md` §1). This module is the *proof library*
beside it: the same IEEE binary64 operations, round-to-nearest-even, written
over `BitVec 64` with closed-form `Nat`/`Int` arithmetic (one `/`, `%` per
rounding instead of the model's bit-at-a-time `Nat.repeat` shifts), so that

* the machine proofs (libgcc soft-fp, `FLOAT-DESIGN.md` §3 level 2) can target
  arithmetic statements, and
* lemmas proved here transfer to `Float.Model` through the bridge theorems
  `F64.*_eq_model` (`F64.op x y = (Float.Model.op ⟦x⟧ ⟦y⟧).toBits`).

The bridges are *unconditional* equalities of bits: every NaN this library
produces is the canonical quiet NaN `0x7ff8000000000000`, which is both the
model's `packedNaN` and the NaN libgcc's RISC-V soft-fp returns (checked on
the ELF under Sail: `c/tests/float/nan_probe.lua`, every NaN-producing `+ − × ÷ %`
gives `9221120237041090560`, and `-(0/0)` gives `0xfff8000000000000`, the
inline sign flip of `luai_numunm`, `vendor/lua-5.4.7/src/llimits.h:349`).

The routines it specifies (libgcc 15.2.0 soft-fp, linked `identical_mod_reloc`,
`function_match.tsv`; the soft-fp sources are not vendored here, so this is
their IEEE 754 round-to-nearest-even contract, not a line-by-line
transcription): `__adddf3`, `__subdf3`, `__muldf3`, `__divdf3`, `__floatdidf`
(`ofInt`; `__floatsidf` on a sign-extended `int`), `__fixdfdi` (`truncInt?`),
and `__eqdf2`/`__ledf2`/`__gedf2` (`compare`). The canonical NaN
(RISC-V `sfp-machine.h`: no NaN payload or sign propagation) is the one
the ELF returns, checked on Sail (`c/tests/float/`).
-/

namespace Lua.Num

/-- A binary64 datum is its bits. -/
abbrev F64 := BitVec 64

namespace F64

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-! ## Fields and classes -/

/-- The sign bit. -/
def sign (x : F64) : Bool := decide (2 ^ 63 ≤ x.toNat)
/-- The biased exponent field (11 bits). -/
def bexp (x : F64) : Nat := x.toNat / 2 ^ 52 % 2 ^ 11
/-- The fraction field (52 bits). -/
def frac (x : F64) : Nat := x.toNat % 2 ^ 52

/-- What the bits denote. `fin neg m e` is `(-1)^neg · m · 2^e` with `0 < m < 2^53`. -/
inductive Cls where
  | nan
  | inf (neg : Bool)
  | zero (neg : Bool)
  | fin (neg : Bool) (m : Nat) (e : Int)
deriving DecidableEq, Repr

/-- Decode (`_FP_UNPACK_D`, `soft-fp/double.h`; IEEE 754-2019 §3.4). -/
def cls (x : F64) : Cls :=
  if x.bexp = 2047 then (if x.frac = 0 then .inf x.sign else .nan)
  else if x.bexp = 0 then (if x.frac = 0 then .zero x.sign else .fin x.sign x.frac (-1074))
  else .fin x.sign (x.frac + 2 ^ 52) ((x.bexp : Int) - 1075)

/-- Assemble sign, biased exponent and fraction (`_FP_PACK_RAW_D`). -/
def bits (neg : Bool) (be f : Nat) : F64 :=
  BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + be * 2 ^ 52 + f)

/-- The canonical quiet NaN (`_FP_NANFRAC_D`, `_FP_NANSIGN_D = 0`). -/
def qnan : F64 := 0x7ff8000000000000#64
/-- Signed infinity. -/
def infty (neg : Bool) : F64 := bits neg 2047 0
/-- Signed zero. -/
def zero (neg : Bool) : F64 := bits neg 0 0

/-- Is the datum a NaN? -/
def isNaN (x : F64) : Bool := x.cls == .nan

/-- Sign flip of every datum, NaN included (Lua's `luai_numunm`,
`llimits.h:349`, compiled to an inline `xor` of bit 63: `-(0/0)` is
`0xfff8000000000000` on the ELF). The model's `neg` canonicalises NaN
instead, so `neg_eq_model` holds off NaN only. -/
def neg (x : F64) : F64 := bits (!x.sign) x.bexp x.frac

/-! ## Rounding -/

/-- Pack a finite value `(-1)^neg · m · 2^E` whose mantissa is already rounded
(`m < 2^53`, `E ≥ -1074`, and `m ≥ 2^52` unless `E = -1074`); overflow gives ±∞. -/
def packFin (neg : Bool) (m : Nat) (E : Int) : F64 :=
  if m = 0 then zero neg
  else if 2047 ≤ E + 1075 then infty neg
  else if 2 ^ 52 ≤ m then bits neg (E + 1075).toNat (m - 2 ^ 52)
  else bits neg 0 m

/-- The exponent of the last mantissa bit kept when `n · 2^e` is rounded to
binary64 (`Format.targetExponent`): 53 significant bits, at least `2^-1074`. -/
def target (n : Nat) (e : Int) : Int := max ((n.log2 : Int) + 1 + e - 53) (-1074)

/-- Drop the low `s` bits of `n`, carrying the round and sticky bits `rb`, `st`
(`_FP_FRAC_SRS`; the model's `ExtendedMantissa >>> s` in closed form). -/
def shr (n : Nat) (rb st : Bool) (s : Nat) : Nat × Bool × Bool :=
  if s = 0 then (n, rb, st)
  else (n / 2 ^ s, decide (n / 2 ^ (s - 1) % 2 = 1), decide (n % 2 ^ (s - 1) ≠ 0) || rb || st)

/-- Round to nearest, ties to even, on mantissa `q` with round bit `rb` and
sticky bit `st` (`_FP_ROUND_NEAREST`). -/
def rne (q : Nat) (rb st : Bool) : Nat := if rb && (st || q % 2 == 1) then q + 1 else q

/-- Pack a rounded mantissa `m ≤ 2^53` at exponent `T`, renormalising a carry
out of the top bit (`m = 2^53`). -/
def finish (neg : Bool) (m : Nat) (T : Int) : F64 :=
  if m = 2 ^ 53 then packFin neg (2 ^ 52) (T + 1) else packFin neg m T

/-- Round-to-nearest-even of `(-1)^neg · (n + f) · 2^e` to binary64, where the
residual `f ∈ [0, 1)` is described by `rb` (`f ≥ 1/2`) and `st` (`f ∉ {0, 1/2}`),
the round and sticky bits. A result of magnitude zero keeps the sign `neg`
(the sign of an exact zero sum, IEEE 754 §6.3, is the caller's).

When `n` has fewer bits than binary64 keeps (`e > target n e`) the value is
exact and `n` is shifted left; there `rb`/`st` must be `false`. -/
def round (neg : Bool) (n : Nat) (e : Int) (rb st : Bool) : F64 :=
  let T := target n e
  if e ≤ T then
    let (q, rb', st') := shr n rb st (T - e).toNat
    finish neg (rne q rb' st') T
  else packFin neg (n <<< (e - T).toNat) T

/-- Exact rounding of `(-1)^neg · n · 2^e` (no residual). -/
abbrev roundExact (neg : Bool) (n : Nat) (e : Int) : F64 := round neg n e false false

/-- Exact rounding of a signed `s · 2^e`; an exact zero gets the sign `zneg`. -/
def normalize (s : Int) (e : Int) (zneg : Bool) : F64 :=
  if s = 0 then zero zneg else roundExact (s < 0) s.natAbs e

/-- Express `m · 2^e` at the exponent `t ≤ e`: the mantissa `m · 2^(e - t)`. -/
def align (m : Nat) (e t : Int) : Nat := m <<< (e - t).toNat

/-- Signed mantissa. -/
def sgnApply (neg : Bool) (m : Nat) : Int := if neg then -(m : Int) else m

/-! ## Arithmetic (`soft-fp/op-common.h` `_FP_ADD_INTERNAL`, `_FP_MUL`, `_FP_DIV`, `_FP_SQRT`) -/

/-- `__adddf3`. -/
def add (x y : F64) : F64 :=
  match x.cls, y.cls with
  | .nan, _ => qnan
  | _, .nan => qnan
  | .inf a, .inf b => if a = b then infty a else qnan
  | .inf a, _ => infty a
  | _, .inf b => infty b
  | .zero a, .zero b => zero (a && b)
  | .zero _, _ => y
  | _, .zero _ => x
  | .fin a m₁ e₁, .fin b m₂ e₂ =>
    normalize (sgnApply a (align m₁ e₁ (min e₁ e₂)) + sgnApply b (align m₂ e₂ (min e₁ e₂)))
      (min e₁ e₂) false

/-- `__subdf3`. -/
def sub (x y : F64) : F64 :=
  match x.cls, y.cls with
  | .nan, _ => qnan
  | _, .nan => qnan
  | .inf a, .inf b => if a = !b then infty a else qnan
  | .inf a, _ => infty a
  | _, .inf b => infty (!b)
  | .zero a, .zero b => zero (a && !b)
  | .zero _, .fin .. => neg y
  | _, .zero _ => x
  | .fin a m₁ e₁, .fin b m₂ e₂ =>
    normalize (sgnApply a (align m₁ e₁ (min e₁ e₂)) - sgnApply b (align m₂ e₂ (min e₁ e₂)))
      (min e₁ e₂) false

/-- `__muldf3`. -/
def mul (x y : F64) : F64 :=
  match x.cls, y.cls with
  | .nan, _ => qnan
  | _, .nan => qnan
  | .inf a, .inf b => infty (a ^^ b)
  | .inf a, .fin b .. => infty (a ^^ b)
  | .fin a .., .inf b => infty (a ^^ b)
  | .inf _, .zero _ => qnan
  | .zero _, .inf _ => qnan
  | .fin a .., .zero b => zero (a ^^ b)
  | .zero a, .fin b .. => zero (a ^^ b)
  | .zero a, .zero b => zero (a ^^ b)
  | .fin a m₁ e₁, .fin b m₂ e₂ => roundExact (a ^^ b) (m₁ * m₂) (e₁ + e₂)

/-- Mantissa, exponent, round and sticky bits of `m₁·2^e₁ / (m₂·2^e₂)`, with the
dividend shifted so that the quotient has at least the bits binary64 keeps. -/
def divCore (m₁ : Nat) (e₁ : Int) (m₂ : Nat) (e₂ : Int) : Nat × Int × Bool × Bool :=
  let t := min (e₁ - e₂)
    (max (((m₁.log2 : Int) + 1 + e₁) - ((m₂.log2 : Int) + 1 + e₂) - 53) (-1074))
  let a := m₁ <<< (e₁ - e₂ - t).toNat
  let r := a % m₂
  (a / m₂, t, decide (m₂ ≤ 2 * r), decide (r ≠ 0 ∧ 2 * r ≠ m₂))

/-- `__divdf3`. -/
def div (x y : F64) : F64 :=
  match x.cls, y.cls with
  | .nan, _ => qnan
  | _, .nan => qnan
  | .inf _, .inf _ => qnan
  | .inf a, .fin b .. => infty (a ^^ b)
  | .fin a .., .inf b => zero (a ^^ b)
  | .inf a, .zero b => infty (a ^^ b)
  | .zero a, .inf b => zero (a ^^ b)
  | .fin a .., .zero b => infty (a ^^ b)
  | .zero a, .fin b .. => zero (a ^^ b)
  | .zero _, .zero _ => qnan
  | .fin a m₁ e₁, .fin b m₂ e₂ =>
    let (q, t, rb, st) := divCore m₁ e₁ m₂ e₂
    round (a ^^ b) q t rb st

/-- Root, exponent, round and sticky bits of `√(m·2^e)`: the radicand is shifted
to an even exponent `2t` with enough bits for a 53-bit root. -/
def sqrtCore (m : Nat) (e : Int) : Nat × Int × Bool × Bool :=
  let t := min (e.ediv 2) (max (((m.log2 : Int) + 1 + e + 1).ediv 2 - 53) (-1074))
  let a := m <<< (e - 2 * t).toNat
  let r := a.sqrt
  let rem := a - r * r
  -- `√a < r + 1/2 ↔ rem ≤ r`; `√a = r + 1/2` is impossible
  (r, t, decide (rem ≠ 0 ∧ r < rem), decide (rem ≠ 0))

/-- Square root (`__ieee754_sqrt`, newlib `libm/math/e_sqrt.c`: correctly rounded). -/
def sqrt (x : F64) : F64 :=
  match x.cls with
  | .nan => qnan
  | .inf false => infty false
  | .inf true => qnan
  | .fin true .. => qnan
  | .zero a => zero a
  | .fin false m e =>
    let (r, t, rb, st) := sqrtCore m e
    round false r t rb st

/-- `__floatdidf` (and `__floatsidf` on a sign-extended `int`): RNE of the
two's-complement value; `0 ↦ +0`. -/
def ofInt (i : BitVec 64) : F64 := normalize i.toInt 0 false

/-! ## Comparison (`_FP_CMP_D`: NaN unordered, `-0 = +0`) -/

/-- Three-way comparison; `none` iff a NaN is involved. -/
def compare (x y : F64) : Option Ordering :=
  match x.cls, y.cls with
  | .nan, _ => none
  | _, .nan => none
  | .inf a, .inf b => some (Ord.compare (!a) (!b))
  | .inf false, _ => some .gt
  | .inf true, _ => some .lt
  | _, .inf false => some .lt
  | _, .inf true => some .gt
  | .fin false .., .zero _ => some .gt
  | .fin true .., .zero _ => some .lt
  | .zero _, .fin false .. => some .lt
  | .zero _, .fin true .. => some .gt
  | .zero _, .zero _ => some .eq
  | .fin true m₁ e₁, .fin true m₂ e₂ => some ((Ord.compare e₁ e₂).then (Ord.compare m₁ m₂)).swap
  | .fin true .., .fin false .. => some .lt
  | .fin false .., .fin true .. => some .gt
  | .fin false m₁ e₁, .fin false m₂ e₂ => some ((Ord.compare e₁ e₂).then (Ord.compare m₁ m₂))

/-- `x < y` (`__ltdf2 < 0`). -/
def lt (x y : F64) : Bool := x.compare y == some .lt
/-- `x ≤ y` (`__ledf2 ≤ 0`). -/
def le (x y : F64) : Bool := (x.compare y).any (·.isLE)
/-- `x == y` (`__eqdf2 = 0`). -/
def eq (x y : F64) : Bool := x.compare y == some .eq

/-! ## Bridge to `Float.Model`

`toModel x` is the model datum with the bits `x` (NaNs canonicalised). The
bridge theorems say each operation's bits are the model's:

| `F64` | `Float.Model` | theorem |
|---|---|---|
| `ofInt` | `ofInt` | `ofInt_eq_model` |
| `add`, `sub`, `mul`, `div` | `add`, `sub`, `mul`, `div` | `add_eq_model`, `sub_eq_model`, `mul_eq_model`, `div_eq_model` |
| `sqrt` | `sqrt` | `sqrt_eq_model` |
| `neg` (off NaN) | `neg` | `neg_eq_model` |
| `compare`, `lt`, `le`, `eq` | `compare`, `lt`, `le`, `beq` | `compare_eq_model`, `lt_eq_model`, `le_eq_model`, `eq_eq_model` |

The route: `unpack_eq`/`pack_cls` (decode and re-pack are `cls`/`Cls.toU`),
`packFin_eq` (the packing of a rounded finite value), `round_eq_model` (the
closed-form `shr`/`rne`/`finish` against the model's bit-at-a-time
`roundWithAccuracy`, from `shiftRight_succ`), `roundExact_eq_model` and
`normalize_eq_model`; per operation only the class case split remains
(`f64_special`), plus, for `mul`/`div`/`sqrt`, that the exact mantissa has
the bits binary64 keeps (`mul_target`, `div_target`, `sqrt_target`).
-/

open Float.Model.UnpackedFloat

def sgn (neg : Bool) : Sign := if neg then .negative else .positive

def Cls.toU : Cls → UnpackedFloat
  | .nan => .notANumber
  | .inf a => .infinity (sgn a)
  | .zero a => .zero (sgn a)
  | .fin a m e => if h : 0 < m then .finite (sgn a) m e h else .zero (sgn a)

theorem toNat_split (x : F64) :
    x.toNat = (if x.sign then 2 ^ 63 else 0) + x.bexp * 2 ^ 52 + x.frac := by
  have := x.isLt
  simp only [sign, bexp, frac]
  by_cases h : 2 ^ 63 ≤ x.toNat <;> simp [h] <;> omega

theorem packComponents_toNat (s : Sign) (ex : BitVec 11) (mt : BitVec 52) :
    (packComponents Float.Model.Format.binary64 s ex mt).toNat
      = s.toBitVec.toNat * 2 ^ 63 + ex.toNat * 2 ^ 52 + mt.toNat := by
  simp only [packComponents, BitVec.toNat_append]
  have h1 := ex.isLt
  have h2 := mt.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt h1, ← Nat.shiftLeft_add_eq_or_of_lt h2]
  simp only [Nat.shiftLeft_eq]
  omega

theorem exp_eq_ones (x : F64) : (BitVec.extractLsb' 52 11 x = -1#11) ↔ x.bexp = 2047 := by
  rw [BitVec.toNat_eq]; simp [bexp, Nat.shiftRight_eq_div_pow]

theorem exp_eq_zero (x : F64) : (BitVec.extractLsb' 52 11 x = 0#11) ↔ x.bexp = 0 := by
  rw [BitVec.toNat_eq]; simp [bexp, Nat.shiftRight_eq_div_pow]

theorem man_eq_zero (x : F64) : (BitVec.extractLsb' 0 52 x = 0#52) ↔ x.frac = 0 := by
  rw [BitVec.toNat_eq]; simp [frac]

theorem sign_ofBitVec (x : F64) : Sign.ofBitVec (BitVec.extractLsb' (52 + 11) 1 x) = sgn x.sign := by
  have := x.isLt
  simp only [Sign.ofBitVec, sgn, sign, BitVec.toNat_eq, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp [h]; omega
  · simp [h]; omega

theorem eb : Float.Model.Format.binary64.exponentBias = 1023 := rfl

theorem unpack_eq (x : F64) : UnpackedFloat.unpack Float.Model.Format.binary64 x = x.cls.toU := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  unfold UnpackedFloat.unpack
  simp only [unpackSign, sign_ofBitVec]
  split
  · rename_i h1; have h1 := (exp_eq_ones x).mp h1
    split
    · rename_i h2; have h2 := (man_eq_zero x).mp h2
      simp [cls, h1, h2, Cls.toU]
    · rename_i h2; have h2 : ¬ x.frac = 0 := fun h => h2 ((man_eq_zero x).mpr h)
      simp [cls, h1, h2, Cls.toU]
  · rename_i h1; have h1 : ¬ x.bexp = 2047 := fun h => h1 ((exp_eq_ones x).mpr h)
    split
    · rename_i h3; have h3 := (exp_eq_zero x).mp h3
      split
      · rename_i h2; have h2 := (man_eq_zero x).mp h2
        simp [cls, h1, h2, h3, Cls.toU]
      · rename_i h2; have h2' : ¬ x.frac = 0 := fun h => h2 ((man_eq_zero x).mpr h)
        have hp : 0 < x.frac := Nat.pos_of_ne_zero h2'
        have hc : x.cls = .fin x.sign x.frac (-1074) := by simp [cls, h1, h3, h2']
        rw [hc]
        simp only [Cls.toU, hp, dite_true, UnpackedFloat.finite.injEq, true_and]
        simp only [unpackMantissa, unpackExponent, bexp, frac, BitVec.extractLsb'_toNat,
          Nat.shiftRight_eq_div_pow, eb] at *
        refine ⟨by simp, by omega⟩
    · rename_i h3; have h3 : ¬ x.bexp = 0 := fun h => h3 ((exp_eq_zero x).mpr h)
      have hp : 0 < x.frac + 2 ^ 52 := by omega
      have hc : x.cls = .fin x.sign (x.frac + 2 ^ 52) ((x.bexp : Int) - 1075) := by simp [cls, h1, h3]
      rw [hc]
      simp only [Cls.toU, hp, dite_true, UnpackedFloat.finite.injEq, true_and]
      have hm := (BitVec.extractLsb' 0 52 x).isLt
      simp only [unpackMantissa, unpackExponent, BitVec.toNat_append, BitVec.extractLsb'_toNat,
        Nat.shiftRight_zero] at hm ⊢
      rw [← Nat.shiftLeft_add_eq_or_of_lt hm]
      simp only [bexp, frac, Nat.shiftRight_eq_div_pow, eb, Nat.shiftLeft_eq] at *
      refine ⟨by simp; omega, by omega⟩

theorem toNat_bits (neg : Bool) (be f : Nat) (hb : be < 2048) (hf : f < 2 ^ 52) :
    (bits neg be f).toNat = (if neg then 2 ^ 63 else 0) + be * 2 ^ 52 + f := by
  simp only [bits, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  split <;> omega

theorem sgn_toBitVec (neg : Bool) : (sgn neg).toBitVec.toNat = if neg then 1 else 0 := by
  cases neg <;> rfl

theorem bits_eq_pack (neg : Bool) (be f : Nat) (hb : be < 2048) (hf : f < 2 ^ 52) :
    bits neg be f = packComponents Float.Model.Format.binary64 (sgn neg)
      (BitVec.ofNat 11 be) (BitVec.ofNat 52 f) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bits neg be f hb hf, packComponents_toNat, sgn_toBitVec]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show be < 2 ^ 11 by omega), Nat.mod_eq_of_lt hf]
  cases neg <;> simp

theorem qnan_eq_pack : qnan = UnpackedFloat.pack Float.Model.Format.binary64 .notANumber := by
  decide

theorem infty_eq_pack (neg : Bool) :
    infty neg = UnpackedFloat.pack Float.Model.Format.binary64 (.infinity (sgn neg)) := by
  cases neg <;> decide

theorem zero_eq_pack (neg : Bool) :
    zero neg = UnpackedFloat.pack Float.Model.Format.binary64 (.zero (sgn neg)) := by
  cases neg <;> decide

theorem log2_eq_52 {m : Nat} (h0 : 0 < m) (h1 : m < 2 ^ 53) : m.log2 + 1 = 53 ↔ 2 ^ 52 ≤ m := by
  constructor
  · intro h
    have := Nat.log2_self_le (Nat.ne_of_gt h0)
    rw [show m.log2 = 52 by omega] at this; exact this
  · intro h
    have := (Nat.log2_eq_iff (Nat.ne_of_gt h0) (k := 52)).mpr ⟨h, h1⟩
    omega

theorem packFin_eq (neg : Bool) (m : Nat) (E : Int) (hm : 0 < m) (hm2 : m < 2 ^ 53)
    (hE : -1074 ≤ E) :
    packFin neg m E = UnpackedFloat.pack Float.Model.Format.binary64 (.finite (sgn neg) m E hm) := by
  have hm52 := log2_eq_52 hm hm2
  simp only [packFin, UnpackedFloat.pack]
  repeat' split
  all_goals simp only [eb, Float.Model.Format.mantissaBits, Float.Model.Format.exponentBits,
      Float.Model.Format.mantissaBitsWithoutImplicit] at *
  all_goals try omega
  · rw [infty_eq_pack]; rfl
  · apply BitVec.eq_of_toNat_eq
    rw [toNat_bits _ _ _ (by omega) (by omega), packComponents_toNat, sgn_toBitVec]
    simp only [BitVec.toNat_ofNat]
    cases neg <;> simp <;> omega
  · rw [bits_eq_pack _ _ _ (by omega) (by omega)]

/-- The facts a decoded finite value carries: a positive 53-bit mantissa, in
canonical form (normal, or subnormal at the least exponent). -/
structure FinOk (m : Nat) (e : Int) : Prop where
  pos : 0 < m
  lt : m < 2 ^ 53
  emin : -1074 ≤ e
  emax : e ≤ 971
  canon : 2 ^ 52 ≤ m ∨ e = -1074

theorem cls_fin {x : F64} {a m e} (h : x.cls = .fin a m e) : FinOk m e ∧ a = x.sign := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  simp only [cls] at h
  split at h
  · split at h <;> cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, rfl⟩
    · cases h; exact ⟨⟨by omega, by omega, by omega, by omega, by omega⟩, rfl⟩

/-- Re-packing a decoded non-NaN datum gives it back. -/
theorem pack_cls (x : F64) (h : x.cls ≠ .nan) :
    UnpackedFloat.pack Float.Model.Format.binary64 x.cls.toU = x := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hx := toNat_split x
  by_cases h1 : x.bexp = 2047
  · by_cases h2 : x.frac = 0
    · have hc : x.cls = .inf x.sign := by simp [cls, h1, h2]
      rw [hc, Cls.toU, ← infty_eq_pack]
      apply BitVec.eq_of_toNat_eq; rw [infty, toNat_bits _ _ _ (by omega) (by omega)]; omega
    · exact absurd (by simp [cls, h1, h2]) h
  · by_cases h3 : x.bexp = 0
    · by_cases h2 : x.frac = 0
      · have hc : x.cls = .zero x.sign := by simp [cls, h1, h2, h3]
        rw [hc, Cls.toU, ← zero_eq_pack]
        apply BitVec.eq_of_toNat_eq; rw [zero, toNat_bits _ _ _ (by omega) (by omega)]; omega
      · have hc : x.cls = .fin x.sign x.frac (-1074) := by simp [cls, h1, h2, h3]
        have hp : 0 < x.frac := by omega
        rw [hc, Cls.toU, dif_pos hp, ← packFin_eq _ _ _ hp (by omega) (by omega)]
        unfold packFin
        rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        apply BitVec.eq_of_toNat_eq; rw [toNat_bits _ _ _ (by omega) (by omega)]; omega
    · have hc : x.cls = .fin x.sign (x.frac + 2 ^ 52) ((x.bexp : Int) - 1075) := by
        simp [cls, h1, h3]
      have hp : 0 < x.frac + 2 ^ 52 := by omega
      rw [hc, Cls.toU, dif_pos hp, ← packFin_eq _ _ _ hp (by omega) (by omega)]
      unfold packFin
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      apply BitVec.eq_of_toNat_eq; rw [toNat_bits _ _ _ (by omega) (by omega)]; omega

/-- The model's view of an `F64` (NaNs canonicalised). -/
def toModel (x : F64) : Float.Model := Float.Model.ofBits (UInt64.ofBitVec x)

theorem packedNaN_unpack :
    UnpackedFloat.unpack Float.Model.Format.binary64
      (UnpackedFloat.pack Float.Model.Format.binary64 .notANumber) = .notANumber := rfl

theorem toModel_unpack (x : F64) : (toModel x).unpack = x.cls.toU := by
  show UnpackedFloat.unpack Float.Model.Format.binary64 (UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.unpack Float.Model.Format.binary64 x)) = _
  rw [unpack_eq x]
  by_cases hc : x.cls = .nan
  · rw [hc]; exact packedNaN_unpack
  · rw [pack_cls x hc, unpack_eq]

/-! ### Rounding against the model's `roundWithAccuracy` -/


/-- The model's `Accuracy` for round bit `rb` and sticky bit `st`. -/
def acc : Bool → Bool → Accuracy
  | false, false => .exact
  | false, true => .inexact .lt
  | true, false => .inexact .eq
  | true, true => .inexact .gt

theorem ofMantissaAndAccuracy_acc (n : Nat) (rb st : Bool) :
    ExtendedMantissa.ofMantissaAndAccuracy n (acc rb st) = ⟨n, rb, st⟩ := by
  cases rb <;> cases st <;> rfl

theorem target_eq (n : Nat) (e : Int) :
    Float.Model.Format.binary64.targetExponent (Float.Model.totalExponent n e) = target n e := by
  simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent, target,
    Float.Model.Format.mantissaBits, Float.Model.Format.minExponent]
  congr 1 <;> simp <;> omega

theorem shiftRight_succ (em : ExtendedMantissa) (s : Nat) :
    em >>> (s + 1) = ⟨em.mantissa / 2 ^ (s + 1), decide (em.mantissa / 2 ^ s % 2 = 1),
      decide (em.mantissa % 2 ^ s ≠ 0) || em.roundBit || em.stickyBit⟩ := by
  induction s with
  | zero =>
    show ExtendedMantissa.shiftRightOne em = _
    simp only [ExtendedMantissa.shiftRightOne, Nat.pow_zero, Nat.div_one, Nat.mod_one,
      Nat.pow_one, ne_eq, not_true_eq_false, decide_false, Bool.false_or]
    congr 1
    cases h : em.mantissa % 2 == 1 <;> simp_all <;> omega
  | succ s ih =>
    show ExtendedMantissa.shiftRightOne (em >>> (s + 1)) = _
    rw [ih]
    simp only [ExtendedMantissa.shiftRightOne, Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    have hm := @Nat.mod_pow_succ em.mantissa 2 s
    have hp : 0 < 2 ^ s := Nat.two_pow_pos s
    have h2 : em.mantissa / 2 ^ s % 2 < 2 := Nat.mod_lt _ (by decide)
    congr 1
    · cases h : em.mantissa / 2 ^ (s + 1) % 2 == 1 <;> simp_all <;> omega
    · cases em.roundBit <;> cases em.stickyBit <;>
        by_cases h1 : em.mantissa / 2 ^ s % 2 = 1 <;> by_cases h3 : em.mantissa % 2 ^ s = 0 <;>
        simp_all [Nat.mul_eq_zero] <;> omega

theorem shiftRight_eq_shr (n : Nat) (rb st : Bool) (s : Nat) :
    (⟨n, rb, st⟩ : ExtendedMantissa) >>> s =
      ⟨(shr n rb st s).1, (shr n rb st s).2.1, (shr n rb st s).2.2⟩ := by
  cases s with
  | zero => rfl
  | succ s => rw [shiftRight_succ]; simp [shr]

theorem roundedMantissa_eq (q : Nat) (rb st : Bool) :
    (ExtendedMantissa.mk q rb st).roundedMantissa = rne q rb st := by
  cases rb <;> cases st <;>
    simp [ExtendedMantissa.roundedMantissa, ExtendedMantissa.accuracy,
      Accuracy.roundToNearestEven, rne]
  cases h : q % 2 == 1 <;> simp_all <;> omega

theorem lt_two_pow_of_log2 {n k : Nat} (h : n.log2 + 1 ≤ k) : n < 2 ^ k :=
  Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) h)

theorem log2_shiftLeft {n : Nat} (k : Nat) (hn : 0 < n) : (n <<< k).log2 = n.log2 + k := by
  rw [Nat.shiftLeft_eq]
  have h1 := Nat.log2_self_le (Nat.ne_of_gt hn)
  have h2 := @Nat.lt_log2_self n
  have hk := Nat.two_pow_pos k
  apply (Nat.log2_eq_iff (Nat.ne_of_gt (Nat.mul_pos hn hk))).mpr
  rw [Nat.pow_add, show n.log2 + k + 1 = (n.log2 + 1) + k by omega, Nat.pow_add]
  exact ⟨Nat.mul_le_mul_right _ h1, Nat.mul_lt_mul_of_pos_right h2 hk⟩

theorem shr_fst_lt (n : Nat) (rb st : Bool) (e : Int) (hT : e ≤ target n e) :
    (shr n rb st (target n e - e).toNat).1 < 2 ^ 53 := by
  have ht : (n.log2 : Int) + 1 + e - 53 ≤ target n e := by simp only [target]; omega
  unfold shr
  split
  · show n < 2 ^ 53
    exact lt_two_pow_of_log2 (by omega)
  · show n / 2 ^ (target n e - e).toNat < 2 ^ 53
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
    rw [← Nat.pow_add]
    exact lt_two_pow_of_log2 (by omega)

theorem second_stage (m : Nat) (T : Int) (hm : m ≤ 2 ^ 53) (hT : -1074 ≤ T) :
    shiftToTargetExponent Float.Model.Format.binary64 m T .exact =
      if m = 2 ^ 53 then (⟨2 ^ 52, false, false⟩, T + 1) else (⟨m, false, false⟩, T) := by
  unfold shiftToTargetExponent shiftToExponent
  rw [target_eq, show Accuracy.exact = acc false false from rfl, ofMantissaAndAccuracy_acc]
  simp only []
  split
  · subst m
    have : target (2 ^ 53) T = T + 1 := by
      simp only [target, Nat.log2_two_pow]; omega
    rw [this, show (T + 1 - T).toNat = 1 by omega, shiftRight_eq_shr]
    simp [shr]
  · have hl : m.log2 ≤ 52 := by
      by_cases h0 : m = 0
      · subst h0; simp
      · have := (Nat.log2_lt h0 (k := 53)).mpr (by omega); omega
    have : (target m T - T).toNat = 0 := by simp only [target]; omega
    rw [this]; simp only [Int.natCast_zero, Int.add_zero]; rfl

/-- `round` is the model's `roundWithAccuracy` whenever no bits need to be
shifted in (`e ≤ target n e`: the case of every mantissa the operations
produce). -/
theorem first_stage (n : Nat) (e : Int) (rb st : Bool) (hT : e ≤ target n e) :
    shiftToTargetExponent Float.Model.Format.binary64 n e (acc rb st) =
      (⟨(shr n rb st (target n e - e).toNat).1, (shr n rb st (target n e - e).toNat).2.1,
        (shr n rb st (target n e - e).toNat).2.2⟩, target n e) := by
  unfold shiftToTargetExponent shiftToExponent
  rw [target_eq, ofMantissaAndAccuracy_acc]
  simp only []
  rw [shiftRight_eq_shr]
  simp only [Prod.mk.injEq, true_and]
  omega

theorem round_eq_model (neg : Bool) (n : Nat) (e : Int) (rb st : Bool) (hT : e ≤ target n e) :
    round neg n e rb st = UnpackedFloat.pack Float.Model.Format.binary64
      (roundWithAccuracy Float.Model.Format.binary64 (sgn neg) n e (acc rb st)) := by
  have hq := shr_fst_lt n rb st e hT
  have hTmin : -1074 ≤ target n e := by simp only [target]; omega
  unfold roundWithAccuracy
  rw [first_stage n e rb st hT]
  simp only [roundedMantissa_eq]
  unfold round
  simp only [if_pos hT]
  generalize shr n rb st (target n e - e).toNat = qq at hq ⊢
  obtain ⟨q, rb', st'⟩ := qq
  simp only at hq ⊢
  have hm : rne q rb' st' ≤ 2 ^ 53 := by unfold rne; split <;> omega
  unfold finish
  have hs := second_stage _ _ hm hTmin
  by_cases h53 : rne q rb' st' = 2 ^ 53
  · rw [if_pos h53] at hs
    simp only [hs]
    rw [if_pos h53, packFin_eq _ _ _ (by decide) (by decide) (by omega)]
    simp
  · rw [if_neg h53] at hs
    simp only [hs]
    rw [if_neg h53]
    by_cases h0 : rne q rb' st' = 0
    · simp only [h0, dite_true, packFin, ite_true]; exact zero_eq_pack neg
    · simp only [h0, dite_false]
      rw [packFin_eq _ _ _ (Nat.pos_of_ne_zero h0) (by omega) hTmin]

theorem roundExact_eq_model (neg : Bool) (n : Nat) (e : Int) (hn : 0 < n) :
    roundExact neg n e = UnpackedFloat.pack Float.Model.Format.binary64
      (UnpackedFloat.round Float.Model.Format.binary64 (sgn neg) n e) := by
  unfold UnpackedFloat.round decreaseExponent
  rw [target_eq]
  simp only []
  by_cases h : e ≤ target n e
  · rw [show (e - target n e).toNat = 0 by omega]
    simp only [Nat.shiftLeft_zero, Int.natCast_zero, Int.sub_zero]
    exact round_eq_model neg n e false false h
  · have hk : ((e - target n e).toNat : Int) = e - target n e := by omega
    rw [hk, show e - (e - target n e) = target n e by omega]
    have hl := log2_shiftLeft (e - target n e).toNat hn
    have ht : target (n <<< (e - target n e).toNat) (target n e) = target n e := by
      simp only [target] at *; rw [hl]; omega
    rw [show Accuracy.exact = acc false false from rfl,
      ← round_eq_model neg (n <<< (e - target n e).toNat) (target n e) false false
        (by rw [ht]; exact Int.le_refl _)]
    -- the left side is the exact branch of `round`
    have hlt : n <<< (e - target n e).toNat < 2 ^ 53 := by
      have : (n.log2 : Int) + 1 + e - 53 ≤ target n e := by simp only [target]; omega
      exact lt_two_pow_of_log2 (by rw [hl]; omega)
    unfold roundExact round
    rw [if_neg h, ht, if_pos (Int.le_refl _)]
    simp only [Int.sub_self, Int.toNat_zero, shr, ite_true, rne, Bool.false_and, Bool.false_eq_true,
      ite_false, finish]
    rw [if_neg (by omega)]

theorem normalize_eq_model (s e : Int) (z : Bool) :
    normalize s e z = UnpackedFloat.pack Float.Model.Format.binary64
      (UnpackedFloat.normalize Float.Model.Format.binary64 s e (sgn z)) := by
  unfold normalize UnpackedFloat.normalize
  rcases Int.lt_trichotomy s 0 with h | h | h
  · rw [if_neg (by omega), (Int.compare_eq_lt).mpr h]
    simp only
    rw [roundExact_eq_model _ _ _ (by omega), decide_eq_true h]
    simp only [sgn, ite_true]
    congr 2; omega
  · subst h; simp [zero_eq_pack]
  · rw [if_neg (by omega), (Int.compare_eq_gt).mpr h]
    simp only
    rw [roundExact_eq_model _ _ _ (by omega), decide_eq_false (by omega)]
    simp only [sgn]
    congr 2; omega

/-- **Bridge: `ofInt`.** `__floatdidf` is the model's `ofInt` of the two's-complement value. -/
theorem ofInt_eq_model (i : BitVec 64) :
    ofInt i = (Float.Model.ofInt i.toInt).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.normalize Float.Model.Format.binary64 i.toInt 0 .positive)
  exact normalize_eq_model _ _ false

theorem toU_fin {a : Bool} {m : Nat} {e : Int} (h : 0 < m) :
    (Cls.fin a m e).toU = .finite (sgn a) m e h := dif_pos h

theorem sgn_beq (a b : Bool) : (sgn a == sgn b) = (a == b) := by cases a <;> cases b <;> rfl

theorem sgn_apply (a : Bool) (m : Nat) : (sgn a).apply m = sgnApply a m := by cases a <;> rfl

/-- **Bridge: `add`.** -/
theorem add_eq_model (x y : F64) :
    add x y = (Float.Model.add (toModel x) (toModel y)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.add Float.Model.Format.binary64 (toModel x).unpack (toModel y).unpack)
  rw [toModel_unpack, toModel_unpack]
  unfold add
  cases hx : x.cls <;> cases hy : y.cls <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;> (try rw [toU_fin (cls_fin hy).1.pos]) <;>
    simp only [Cls.toU, UnpackedFloat.add]
  all_goals first
    | rw [← qnan_eq_pack]
    | rw [← infty_eq_pack]
    | (rename_i a b; cases a <;> cases b <;> simp only [sgn_beq] <;> simp <;>
        first
          | rw [← qnan_eq_pack]
          | rw [← infty_eq_pack]
          | rw [← zero_eq_pack]
          | rw [show UnpackedFloat.Sign.positive = sgn false from rfl, ← zero_eq_pack])
    | (rw [← toU_fin (cls_fin hy).1.pos, ← hy, pack_cls y (by simp [hy])])
    | (rw [← toU_fin (cls_fin hx).1.pos, ← hx, pack_cls x (by simp [hx])])
    | (rw [normalize_eq_model]
       simp only [decreaseExponent, sgn_apply, align]
       rfl)

theorem sgn_neg (a : Bool) : -(sgn a) = sgn (!a) := by cases a <;> rfl
theorem sgn_mul (a b : Bool) : sgn a * sgn b = sgn (a ^^ b) := by cases a <;> cases b <;> rfl
theorem sgn_div (a b : Bool) : sgn a / sgn b = sgn (a ^^ b) := by cases a <;> cases b <;> rfl

theorem fields_bits (neg : Bool) (be f : Nat) (hb : be < 2048) (hf : f < 2 ^ 52) :
    (bits neg be f).sign = neg ∧ (bits neg be f).bexp = be ∧ (bits neg be f).frac = f := by
  simp only [sign, bexp, frac, toNat_bits neg be f hb hf]
  cases neg <;> simp <;> omega

/-- The class of a sign-flipped datum. -/
def Cls.negate : Cls → Cls
  | .nan => .nan
  | .inf a => .inf (!a)
  | .zero a => .zero (!a)
  | .fin a m e => .fin (!a) m e

theorem cls_neg (x : F64) : (neg x).cls = x.cls.negate := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  obtain ⟨h1, h2, h3⟩ := fields_bits (!x.sign) x.bexp x.frac hb hf
  unfold neg cls
  rw [h1, h2, h3]
  split
  · split <;> rfl
  · split
    · split <;> rfl
    · rfl

/-- **Bridge: `sub`.** -/
theorem sub_eq_model (x y : F64) :
    sub x y = (Float.Model.sub (toModel x) (toModel y)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.sub Float.Model.Format.binary64 (toModel x).unpack (toModel y).unpack)
  rw [toModel_unpack, toModel_unpack]
  unfold sub
  cases hx : x.cls <;> cases hy : y.cls <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;> (try rw [toU_fin (cls_fin hy).1.pos]) <;>
    simp only [Cls.toU, UnpackedFloat.sub, sgn_neg]
  all_goals first
    | rw [← qnan_eq_pack]
    | rw [← infty_eq_pack]
    | (rename_i a b; cases a <;> cases b <;> simp only [sgn_beq, sgn_neg] <;> simp <;>
        first
          | rw [← qnan_eq_pack]
          | rw [← infty_eq_pack]
          | rw [← zero_eq_pack]
          | rw [show UnpackedFloat.Sign.positive = sgn false from rfl, ← zero_eq_pack])
    | (rename_i a' a m e
       have hn : (neg y).cls = .fin (!a) m e := by rw [cls_neg, hy]; rfl
       rw [← toU_fin (cls_fin hn).1.pos, ← hn, pack_cls _ (by simp [hn])])
    | (rw [← toU_fin (cls_fin hx).1.pos, ← hx, pack_cls x (by simp [hx])])
    | (rw [normalize_eq_model]
       simp only [decreaseExponent, sgn_apply, align]
       rfl)

theorem le_log2_of {n k : Nat} (h : 2 ^ k ≤ n) : k ≤ n.log2 :=
  (Nat.le_log2 (by have := Nat.two_pow_pos k; omega)).mpr h

theorem mul_target {m₁ m₂ : Nat} {e₁ e₂ : Int} (h₁ : FinOk m₁ e₁) (h₂ : FinOk m₂ e₂) :
    e₁ + e₂ ≤ target (m₁ * m₂) (e₁ + e₂) := by
  have p1 := h₁.pos; have p2 := h₂.pos
  unfold target
  rcases h₁.canon with c1 | c1
  · have : 2 ^ 52 ≤ m₁ * m₂ := Nat.le_trans c1 (Nat.le_mul_of_pos_right _ p2)
    have := le_log2_of this; omega
  · rcases h₂.canon with c2 | c2
    · have : 2 ^ 52 ≤ m₁ * m₂ := Nat.le_trans c2 (Nat.le_mul_of_pos_left _ p1)
      have := le_log2_of this; omega
    · omega

/-- The closers shared by the binary-operation bridges: the special classes
re-packed, a passed-through operand re-packed (`pack_cls`). -/
macro "f64_special" : tactic => `(tactic| first
    | rw [← qnan_eq_pack]
    | rw [← infty_eq_pack]
    | rw [← zero_eq_pack]
    | (rename_i a b; cases a <;> cases b <;> simp only [sgn_beq, sgn_neg, sgn_mul, sgn_div] <;>
        simp <;>
        first
          | rw [← qnan_eq_pack]
          | rw [← infty_eq_pack]
          | rw [← zero_eq_pack]
          | rw [show UnpackedFloat.Sign.positive = sgn false from rfl, ← zero_eq_pack]))

/-- **Bridge: `mul`.** -/
theorem mul_eq_model (x y : F64) :
    mul x y = (Float.Model.mul (toModel x) (toModel y)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.mul Float.Model.Format.binary64 (toModel x).unpack (toModel y).unpack)
  rw [toModel_unpack, toModel_unpack]
  unfold mul
  cases hx : x.cls <;> cases hy : y.cls <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;> (try rw [toU_fin (cls_fin hy).1.pos]) <;>
    simp only [Cls.toU, UnpackedFloat.mul, sgn_mul]
  all_goals first
    | f64_special
    | (rw [show Accuracy.exact = acc false false from rfl,
          ← round_eq_model _ _ _ _ _ (mul_target (cls_fin hx).1 (cls_fin hy).1)])

/-- **Bridge: `neg`**, off NaN (the model's `neg` canonicalises NaN; Lua's flips its sign). -/
theorem neg_eq_model (x : F64) (h : x.cls ≠ .nan) :
    neg x = (Float.Model.neg (toModel x)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64 (toModel x).unpack.neg
  rw [toModel_unpack, ← pack_cls (neg x) (by rw [cls_neg]; cases hc : x.cls <;> simp_all [Cls.negate])]
  rw [cls_neg]
  cases hc : x.cls with
  | nan => exact absurd hc h
  | inf a => cases a <;> rfl
  | zero a => cases a <;> rfl
  | fin a m e =>
    simp only [Cls.negate, Cls.toU, (cls_fin hc).1.pos, dite_true, UnpackedFloat.neg, sgn_neg]

/-- **Bridge: `compare`** (hence `lt`, `le`, `eq`). -/
theorem compare_eq_model (x y : F64) :
    F64.compare x y = Float.Model.compare (toModel x) (toModel y) := by
  show _ = UnpackedFloat.compare (toModel x).unpack (toModel y).unpack
  rw [toModel_unpack, toModel_unpack]
  unfold F64.compare
  rcases hx : x.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₁, e₁⟩ <;>
  rcases hy : y.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₂, e₂⟩ <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;> (try rw [toU_fin (cls_fin hy).1.pos]) <;>
    rfl

theorem lt_eq_model (x y : F64) : lt x y = Float.Model.lt (toModel x) (toModel y) := by
  simp only [lt, compare_eq_model]; rfl

theorem le_eq_model (x y : F64) : le x y = Float.Model.le (toModel x) (toModel y) := by
  simp only [le, compare_eq_model]; rfl

theorem eq_eq_model (x y : F64) : eq x y = Float.Model.beq (toModel x) (toModel y) := by
  simp only [eq, compare_eq_model]; rfl

theorem log2_of_le {q : Nat} (h : 2 ^ 52 ≤ q) : 52 ≤ q.log2 := le_log2_of h

/-- The quotient `divCore` computes has the bits binary64 keeps. -/
theorem div_target (m₁ m₂ : Nat) (e₁ e₂ : Int) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    (divCore m₁ e₁ m₂ e₂).2.1 ≤ target (divCore m₁ e₁ m₂ e₂).1 (divCore m₁ e₁ m₂ e₂).2.1 := by
  simp only [divCore]
  generalize ht : min (e₁ - e₂) (max ((m₁.log2 : Int) + 1 + e₁ - ((m₂.log2 : Int) + 1 + e₂) - 53)
    (-1074)) = t
  unfold target
  by_cases hm : t ≤ -1074
  · omega
  · have hk : (m₁.log2 : Int) + (e₁ - e₂ - t).toNat ≥ 53 + m₂.log2 := by omega
    have a1 := Nat.log2_self_le (Nat.ne_of_gt h₁)
    have a2 := @Nat.lt_log2_self m₂
    have : 2 ^ 52 ≤ (m₁ <<< (e₁ - e₂ - t).toNat) / m₂ := by
      apply (Nat.le_div_iff_mul_le h₂).mpr
      rw [Nat.shiftLeft_eq]
      calc 2 ^ 52 * m₂ ≤ 2 ^ 52 * 2 ^ (m₂.log2 + 1) := Nat.mul_le_mul_left _ (Nat.le_of_lt a2)
        _ = 2 ^ (53 + m₂.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ (m₁.log2 + (e₁ - e₂ - t).toNat) := Nat.pow_le_pow_right (by decide) (by omega)
        _ = 2 ^ m₁.log2 * 2 ^ (e₁ - e₂ - t).toNat := Nat.pow_add _ _ _
        _ ≤ m₁ * 2 ^ (e₁ - e₂ - t).toNat := Nat.mul_le_mul_right _ a1
    have := log2_of_le this
    omega

theorem accuracyOfFraction_eq (r d : Nat) (hd : 0 < d) :
    accuracyOfFraction r d = acc (decide (d ≤ 2 * r)) (decide (r ≠ 0 ∧ 2 * r ≠ d)) := by
  unfold accuracyOfFraction
  by_cases h0 : r = 0
  · subst h0
    have : ¬ d ≤ 2 * 0 := by omega
    rw [decide_eq_false this]; simp [acc]
  · rw [if_neg h0]
    rcases Nat.lt_trichotomy (2 * r) d with h | h | h
    · rw [(Nat.compare_eq_lt).mpr h]
      simp [acc, h0, show ¬ d ≤ 2 * r by omega, show 2 * r ≠ d by omega]
    · rw [(Nat.compare_eq_eq).mpr h]
      simp [acc, h0, show d ≤ 2 * r by omega, h]
    · rw [(Nat.compare_eq_gt).mpr h]
      simp [acc, h0, show d ≤ 2 * r by omega, show 2 * r ≠ d by omega]

theorem divCore_eq (m₁ m₂ : Nat) (e₁ e₂ : Int) (h₂ : 0 < m₂) :
    UnpackedFloat.divCore Float.Model.Format.binary64 m₁ e₁ m₂ e₂ =
      ((divCore m₁ e₁ m₂ e₂).1, (divCore m₁ e₁ m₂ e₂).2.1,
        acc (divCore m₁ e₁ m₂ e₂).2.2.1 (divCore m₁ e₁ m₂ e₂).2.2.2) := by
  unfold UnpackedFloat.divCore divCore
  simp only [Float.Model.Format.targetExponent, Float.Model.totalExponent,
    Float.Model.Format.mantissaBits, Float.Model.Format.minExponent]
  rw [accuracyOfFraction_eq _ _ h₂]
  simp only [Prod.mk.injEq]
  refine ⟨?_, ?_, ?_⟩ <;> (congr <;> simp <;> omega)

/-- **Bridge: `div`.** -/
theorem div_eq_model (x y : F64) :
    div x y = (Float.Model.div (toModel x) (toModel y)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.div Float.Model.Format.binary64 (toModel x).unpack (toModel y).unpack)
  rw [toModel_unpack, toModel_unpack]
  unfold div
  cases hx : x.cls <;> cases hy : y.cls <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;> (try rw [toU_fin (cls_fin hy).1.pos]) <;>
    simp only [Cls.toU, UnpackedFloat.div, sgn_div]
  all_goals first
    | f64_special
    | (rw [divCore_eq _ _ _ _ (cls_fin hy).1.pos]
       simp only []
       rw [← round_eq_model _ _ _ _ _ (div_target _ _ _ _ (cls_fin hx).1.pos (cls_fin hy).1.pos)])

theorem targetExponent_eq (x : Int) :
    Float.Model.Format.binary64.targetExponent x = max (x - 53) (-1074) := by
  simp only [Float.Model.Format.targetExponent, Float.Model.Format.mantissaBits,
    Float.Model.Format.minExponent]
  congr 1 <;> simp <;> omega

theorem acc_rem (rem r : Nat) :
    (if rem = 0 then Accuracy.exact else Accuracy.inexact (if rem ≤ r then .lt else .gt)) =
      acc (decide (rem ≠ 0 ∧ r < rem)) (decide (rem ≠ 0)) := by
  by_cases h0 : rem = 0
  · simp [h0, acc]
  · by_cases h1 : rem ≤ r
    · simp [h0, h1, acc, show ¬ r < rem by omega]
    · simp [h0, h1, acc, show r < rem by omega]

theorem sqrtCore_eq (m : Nat) (e : Int) :
    UnpackedFloat.sqrtCore Float.Model.Format.binary64 m e =
      ((sqrtCore m e).1, (sqrtCore m e).2.1, acc (sqrtCore m e).2.2.1 (sqrtCore m e).2.2.2) := by
  unfold UnpackedFloat.sqrtCore sqrtCore
  rw [targetExponent_eq]
  simp only [Float.Model.totalExponent, Int.natCast_add, Int.cast_ofNat_Int]
  simp only [Prod.mk.injEq, true_and]
  exact acc_rem _ _

/-- The root `sqrtCore` computes has the bits binary64 keeps. -/
theorem sqrt_target (m : Nat) (e : Int) (h : 0 < m) :
    (sqrtCore m e).2.1 ≤ target (sqrtCore m e).1 (sqrtCore m e).2.1 := by
  simp only [sqrtCore]
  generalize ht : min (e.ediv 2) (max (((m.log2 : Int) + 1 + e + 1).ediv 2 - 53) (-1074)) = t
  unfold target
  by_cases hm : t ≤ -1074
  · omega
  · simp only [show ∀ a : Int, a.ediv 2 = a / 2 from fun _ => rfl] at ht
    have hs : m.log2 + (e - 2 * t).toNat ≥ 104 := by omega
    have a1 := Nat.log2_self_le (Nat.ne_of_gt h)
    have ha : 2 ^ 104 ≤ m <<< (e - 2 * t).toNat := by
      rw [Nat.shiftLeft_eq]
      calc 2 ^ 104 ≤ 2 ^ (m.log2 + (e - 2 * t).toNat) := Nat.pow_le_pow_right (by decide) hs
        _ = 2 ^ m.log2 * 2 ^ (e - 2 * t).toNat := Nat.pow_add _ _ _
        _ ≤ m * 2 ^ (e - 2 * t).toNat := Nat.mul_le_mul_right _ a1
    have hr : 2 ^ 52 ≤ (m <<< (e - 2 * t).toNat).sqrt := by
      generalize m <<< (e - 2 * t).toNat = a at ha
      have := Nat.lt_succ_sqrt a
      refine Nat.le_of_not_lt fun hc => ?_
      have hc : a.sqrt + 1 ≤ 2 ^ 52 := hc
      have := Nat.mul_le_mul hc hc
      simp only [Nat.succ_eq_add_one] at *
      omega
    have := log2_of_le hr
    omega

/-- **Bridge: `sqrt`.** -/
theorem sqrt_eq_model (x : F64) :
    sqrt x = (Float.Model.sqrt (toModel x)).toBits.toBitVec := by
  show _ = UnpackedFloat.pack Float.Model.Format.binary64
    (UnpackedFloat.sqrt Float.Model.Format.binary64 (toModel x).unpack)
  rw [toModel_unpack]
  unfold sqrt
  rcases hx : x.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m, e⟩ <;>
    (try rw [toU_fin (cls_fin hx).1.pos]) <;>
    simp only [Cls.toU, UnpackedFloat.sqrt, sgn, ite_true, ite_false, Bool.false_eq_true]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [sqrtCore_eq]
    simp only []
    rw [show UnpackedFloat.Sign.positive = sgn false from rfl,
      ← round_eq_model _ _ _ _ _ (sqrt_target _ _ (cls_fin hx).1.pos)]
  · rfl

/-! ## Sanity lemmas

The facts the float arms are expected to need first, kept minimal:
`add_comm`, `mul_comm`, `neg_neg`; the comparison's `compare_swap`,
`trichotomy` (off NaN) and `lt_irrefl`; `ofInt_exact` (`__floatdidf` is exact
on `|i| ≤ 2^53`, read back through `__fixdfdi`'s truncation `truncInt?`).
Through the bridges they hold of `Float.Model` too.
-/

theorem add_comm (x y : F64) : add x y = add y x := by
  unfold add
  cases hx : x.cls <;> cases hy : y.cls <;> simp only [Int.add_comm, Int.min_comm, Bool.and_comm]
  all_goals first | rfl | (rename_i a b; cases a <;> cases b <;> rfl)

theorem mul_comm (x y : F64) : mul x y = mul y x := by
  unfold mul
  cases hx : x.cls <;> cases hy : y.cls <;> simp only [Nat.mul_comm, Int.add_comm, Bool.xor_comm]

theorem compare_swap (x y : F64) : F64.compare y x = (F64.compare x y).map Ordering.swap := by
  unfold F64.compare
  rcases hx : x.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₁, e₁⟩ <;>
  rcases hy : y.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₂, e₂⟩ <;>
    simp [Ordering.swap_then, Int.compare_swap, Nat.compare_swap, Ordering.swap_swap] <;> rfl

/-- Trichotomy off NaN. -/
theorem trichotomy (x y : F64) (hx : x.cls ≠ .nan) (hy : y.cls ≠ .nan) :
    lt x y ∨ eq x y ∨ lt y x := by
  have hs := compare_swap x y
  unfold lt eq
  rw [hs]
  have : F64.compare x y ≠ none := by
    unfold F64.compare
    rcases hcx : x.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₁, e₁⟩ <;>
    rcases hcy : y.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m₂, e₂⟩ <;> simp_all
  cases h : F64.compare x y with
  | none => exact absurd h this
  | some o => cases o <;> simp

theorem lt_irrefl (x : F64) : lt x x = false := by
  unfold lt F64.compare
  rcases hx : x.cls with _ | (_ | _) | (_ | _) | ⟨(_ | _), m, e⟩ <;> simp [Ordering.then]

theorem neg_neg (x : F64) : neg (neg x) = x := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  obtain ⟨h1, h2, h3⟩ := fields_bits (!x.sign) x.bexp x.frac hb hf
  unfold neg
  rw [h1, h2, h3, Bool.not_not]
  apply BitVec.eq_of_toNat_eq
  rw [toNat_bits _ _ _ hb hf, toNat_split x]

/-- `__fixdfdi`'s truncation toward zero, as an integer without the range
clamp (`_FP_TO_INT`); `none` on NaN and ±∞. -/
def truncInt? (x : F64) : Option Int :=
  match x.cls with
  | .zero _ => some 0
  | .fin a m e => some (sgnApply a (if 0 ≤ e then m <<< e.toNat else m / 2 ^ (-e).toNat))
  | _ => none

theorem cls_packFin_normal (neg : Bool) (m : Nat) (E : Int) (h1 : 2 ^ 52 ≤ m) (h2 : m < 2 ^ 53)
    (hE : -1074 ≤ E) (hE2 : E + 1075 < 2047) : (packFin neg m E).cls = .fin neg m E := by
  unfold packFin
  rw [if_neg (by omega), if_neg (by omega), if_pos h1]
  obtain ⟨s1, s2, s3⟩ := fields_bits neg (E + 1075).toNat (m - 2 ^ 52) (by omega) (by omega)
  unfold cls
  rw [s1, s2, s3, if_neg (by omega), if_neg (by omega)]
  simp only [Cls.fin.injEq, true_and]
  omega

theorem roundExact_top (neg : Bool) : roundExact neg (2 ^ 53) 0 = packFin neg (2 ^ 52) 1 := by
  cases neg <;> decide +kernel

theorem shiftLeft_top : (2 ^ 52 : Nat) <<< (1 : Int).toNat = 2 ^ 53 := by decide

theorem truncInt_zero : truncInt? (zero false) = some 0 := by decide +kernel

theorem truncInt_top (neg : Bool) : truncInt? (roundExact neg (2 ^ 53) 0) = some (sgnApply neg (2 ^ 53)) := by
  cases neg <;> decide +kernel

theorem truncInt_small (neg : Bool) (n : Nat) (hn : 0 < n) (h52le : n.log2 ≤ 52) :
    truncInt? (roundExact neg n 0) = some (sgnApply neg n) := by
  have hL := Nat.log2_self_le (Nat.ne_of_gt hn)
  have hL2 := @Nat.lt_log2_self n
  have hT : target n 0 = (n.log2 : Int) - 52 := by simp only [target]; omega
  unfold roundExact round
  rw [hT]
  by_cases hl : n.log2 ≤ 51
  · rw [if_neg (by omega)]
    have hs := log2_shiftLeft (((0 : Int) - ((n.log2 : Int) - 52)).toNat) hn
    have hk : ((0 : Int) - ((n.log2 : Int) - 52)).toNat = 52 - n.log2 := by omega
    have hm1 : 2 ^ 52 ≤ n <<< ((0 : Int) - ((n.log2 : Int) - 52)).toNat := by
      rw [Nat.shiftLeft_eq, hk]
      calc 2 ^ 52 = 2 ^ n.log2 * 2 ^ (52 - n.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ n * 2 ^ (52 - n.log2) := Nat.mul_le_mul_right _ hL
    have hm2 : n <<< ((0 : Int) - ((n.log2 : Int) - 52)).toNat < 2 ^ 53 :=
      lt_two_pow_of_log2 (by rw [hs]; omega)
    unfold truncInt?
    rw [cls_packFin_normal _ _ _ hm1 hm2 (by omega) (by omega)]
    simp only [show ¬ (0 : Int) ≤ (n.log2 : Int) - 52 by omega, ite_false]
    rw [Nat.shiftLeft_eq, show (-((n.log2 : Int) - 52)).toNat = ((0 : Int) - ((n.log2 : Int) - 52)).toNat
      by omega, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · have h52 : n.log2 = 52 := by omega
    have h52' : 2 ^ 52 ≤ n := by rw [h52] at hL; exact hL
    have hlt : n < 2 ^ 53 := by rw [h52] at hL2; exact hL2
    rw [if_pos (by omega)]
    rw [show ((n.log2 : Int) - 52 - 0).toNat = 0 by omega]
    simp only [shr, ite_true, rne, Bool.false_and, Bool.false_eq_true, ite_false, finish]
    rw [if_neg (by omega)]
    unfold truncInt?
    rw [cls_packFin_normal _ _ _ h52' (by omega) (by omega) (by omega)]
    simp only [show (0 : Int) ≤ (n.log2 : Int) - 52 by omega, ite_true,
      show ((n.log2 : Int) - 52).toNat = 0 by omega, Nat.shiftLeft_zero]

/-- `ofInt` is exact on integers of magnitude at most `2^53`. -/
theorem ofInt_exact (i : BitVec 64) (h : i.toInt.natAbs ≤ 2 ^ 53) :
    truncInt? (ofInt i) = some i.toInt := by
  unfold ofInt normalize
  by_cases h0 : i.toInt = 0
  · rw [if_pos h0, h0]; exact truncInt_zero
  rw [if_neg h0]
  have hsign : sgnApply (decide (i.toInt < 0)) i.toInt.natAbs = i.toInt := by
    unfold sgnApply; split <;> rename_i hh <;> simp at hh <;> omega
  have hn : 0 < i.toInt.natAbs := by omega
  generalize i.toInt.natAbs = n at h hn hsign
  by_cases hn53 : n = 2 ^ 53
  · subst hn53; have := truncInt_top (decide (i.toInt < 0)); rw [hsign] at this; exact this
  · have : n.log2 ≤ 52 := by
      have := (Nat.log2_lt (Nat.ne_of_gt hn) (k := 53)).mpr (by omega); omega
    have := truncInt_small (decide (i.toInt < 0)) n hn this; rw [hsign] at this; exact this

end F64
end Lua.Num

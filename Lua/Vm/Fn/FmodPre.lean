import Lua.Vm.Fn.FmodDeep
import Lua.Vm.Fn.SfRefMul

/-!
# `__ieee754_fmod`'s operand tests (lane float-sf5, (b1))

`e_fmod.c:41-56`: the words of `x` and `y` (`EXTRACT_WORDS`), the special
operands (`y = 0`, `x` not finite, `y` NaN: `(x*y)/(x*y)`, through
`__muldf3`'s summary and `F64.div`), `|x| < |y|` (`return x`), `|x| = |y|`
(`return Zero[sx]`), and otherwise the cut at `0x8002be1c` (the operands'
classes). The operands are in the word lens `(sx + hx)·2^32 + lx mod 2^32`
(`sx` the sign word, `hx` the high word without it, `lx` the low word
sign-extended).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
namespace Lua.Vm.Fn.Ieee754Fmod
open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim
set_option linter.unusedVariables false

/-- The high word of `(W, l)`. -/
theorem word_hi (W l : Int) (h0 : 0 ≤ W) (h1 : W < 2 ^ 32) :
    (W * 4294967296 + l % 4294967296) % 18446744073709551616 / 4294967296 = W := by omega
/-- The low word of `(W, l)`, sign-extended. -/
theorem word_lo (W l : Int) (h1 : -2 ^ 31 ≤ l) (h2 : l < 2 ^ 31) :
    (W * 4294967296 + l % 4294967296).bmod 4294967296 = l := by
  simp only [Int.bmod]; split <;> omega
theorem xor_k : BitVec.ofInt 64 (-2147483648) ^^^ BitVec.ofInt 64 (-1) = BitVec.ofInt 64 2147483647 := by decide

theorem bit01 (p q : Nat) (hp : p < 2) (hq : q < 2) : p ||| q = if p = 0 ∧ q = 0 then 0 else 1 := by
  rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl <;> rcases (show q = 0 ∨ q = 1 by omega) with rfl | rfl <;> rfl

/-- `(l | -l) >> 31` (`e_fmod.c:47`, `(ly|-ly)>>31`): whether the low word is nonzero. -/
theorem nzbit (l : Int) :
    (shift_bits_right (Sail.BitVec.extractLsb (BitVec.ofInt 64 l ||| BitVec.ofInt 64 ((0 - l).bmod 4294967296)) 31 0)
      (31#5)).toInt = if l % 4294967296 = 0 then 0 else 1 := by
  unfold shift_bits_right
  rw [BitVec.ushiftRight_eq', BitVec.toInt_eq_toNat_bmod]
  simp only [BitVec.toNat_ushiftRight, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
    BitVec.toNat_or, BitVec.toNat_ofInt, Nat.shiftRight_zero, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_zero, Nat.div_one, Nat.or_mod_two_pow, Nat.or_div_two_pow, show (31#5).toNat = 31 from rfl]
  rw [bit01 _ _ (by omega) (by omega)]
  have hb1 := Int.le_bmod (x := 0 - l) (m := 4294967296) (by decide)
  have hb2 := Int.bmod_lt (x := 0 - l) (m := 4294967296) (by decide)
  have hb3 := Int.bmod_emod (x := 0 - l) (m := 4294967296)
  split <;> split <;> simp only [Int.bmod] <;> (try split) <;> omega

theorem sgn_mod (sx hx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h0 : 0 ≤ hx) (h1 : hx < 2 ^ 31) :
    (sx + hx) % 2147483648 = hx := by omega
theorem sgn_div (sx hx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) (h0 : 0 ≤ hx) (h1 : hx < 2 ^ 31) :
    (sx + hx) / 2147483648 * 2147483648 = sx := by omega

theorem nor1 (a : Nat) : a ||| 1 = a / 2 * 2 + 1 := by
  have h1 : (a ||| 1) % 2 = 1 := by
    rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.or_mod_two_pow, bit01 _ _ (by omega) (by omega)]
    simp
  have h2 : (a ||| 1) / 2 = a / 2 := by
    have := Nat.or_div_two_pow (a := a) (b := 1) (n := 1)
    simp only [Nat.pow_one, Nat.reduceDiv, Nat.or_zero] at this
    exact this
  omega

/-- `hy | ((ly|-ly)>>31)` (`e_fmod.c:47`). -/
theorem or_nz (a l : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a ||| BitVec.ofInt 64 (if l % 4294967296 = 0 then 0 else 1) =
      BitVec.ofInt 64 (if l % 4294967296 = 0 then a else a / 2 * 2 + 1) := by
  split
  · exact or_zero_ofInt a
  · obtain ⟨u, rfl⟩ : ∃ u : Nat, a = (u : Int) := ⟨a.toNat, (Int.toNat_of_nonneg ha).symm⟩
    rw [show ((u : Int) / 2 * 2 + 1) = ((u / 2 * 2 + 1 : Nat) : Int) by omega, ofInt_ofNat, ofInt_ofNat,
      show (1 : Int) = ((1 : Nat) : Int) by rfl, ofInt_ofNat]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : u < 2 ^ 64), Nat.mod_eq_of_lt (by omega : u / 2 * 2 + 1 < 2 ^ 64),
      show 1 % 2 ^ 64 = 1 from rfl, nor1]

/-- One normalisation round of the operands' words. -/
macro "fm_tnf" : tactic => `(tactic| (
  fm_nf
  try simp (disch := omega) only [word_hi, word_lo, xor_k, sgn_mod, sgn_div, nzbit, or_nz]
  try fm_nf))

theorem pre_be1c {m : Mem} (s : Nat) (r : BitVec 64) (sx hx lx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31)
    (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20) (hy0 : 0 ≤ hy) (hy1 : hy < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hyz : hy ≠ 0 ∨ ly ≠ 0)
    (hgt : hy * 2 ^ 32 + ly % 2 ^ 32 < hx * 2 ^ 32 + lx % 2 ^ 32) :
    F m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      N_8002be1c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) (BitVec.ofInt 64 2146435072) ∧
    T m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      T_8002be1c m s r (BitVec.ofInt 64 sx) (BitVec.ofInt 64 lx) (BitVec.ofInt 64 hy) (BitVec.ofInt 64 hx)
        (BitVec.ofInt 64 ly) (BitVec.ofInt 64 (sx + hx)) (BitVec.ofInt 64 (sy + hy)) (BitVec.ofInt 64 2146435072) := by
  unfold F T
  fm_tnf
  unfold N_8002bddc T_8002bddc N_8002bdf0 T_8002bdf0
  fm_tnf
  unfold N_8002be04 T_8002be04
  fm_tnf
  by_cases hlt : hy < hx
  · fm_tnf
    unfold N_8002bed0 T_8002bed0 N_8002be1c T_8002be1c N_8002be24 T_8002be24
    fm_tnf
    exact ⟨trivial, trivial⟩
  · fm_tnf
    unfold N_8002be10 T_8002be10 N_8002be14 T_8002be14 N_8002be18 T_8002be18
    fm_tnf
    exact ⟨trivial, trivial⟩

/-- **`|x| < |y|`** (`e_fmod.c:52`: `return x`), `y` finite or infinite. -/
theorem pre_lt {m : Mem} (s : Nat) (r : BitVec 64) (sx hx lx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31)
    (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20) (hy0 : 0 ≤ hy) (hy1 : hy ≤ 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hinf : hy = 2047 * 2 ^ 20 → ly = 0)
    (hlt : hx * 2 ^ 32 + lx % 2 ^ 32 < hy * 2 ^ 32 + ly % 2 ^ 32) :
    F m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32) ∧
    T m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      true := by
  unfold F T
  fm_tnf
  unfold N_8002bddc T_8002bddc N_8002bdf0 T_8002bdf0
  fm_tnf
  unfold N_8002be04 T_8002be04 N_8002be10 T_8002be10 N_8002be14 T_8002be14 N_8002c078
  fm_tnf
  simp only [ite_self, and_self]

/-- The `Zero[sx]` load's side conditions. -/
theorem ld_c1fcT {m : Mem} (s : Nat) (r : BitVec 64) (sx : Int) (h5 : sx = 0 ∨ sx = 2 ^ 31) :
    T_8002c1fc m s r (BitVec.ofInt 64 sx) = true := by
  unfold T_8002c1fc
  rcases h5 with rfl | rfl <;> decide

/-- **`|x| = |y|`** (`e_fmod.c:53`: `return Zero[sx]`). -/
theorem pre_eq {m : Mem} (hro : RodataRead m) (s : Nat) (r : BitVec 64) (sx hx lx sy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31)
    (hx0 : 0 ≤ hx) (hx1 : hx < 2047 * 2 ^ 20)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hyz : hx ≠ 0 ∨ ly ≠ 0) (heq : lx % 2 ^ 32 = ly % 2 ^ 32) :
    F m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hx) * 2 ^ 32 + ly % 2 ^ 32)) =
      BitVec.ofInt 64 (sx * 2 ^ 32) ∧
    T m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hx) * 2 ^ 32 + ly % 2 ^ 32)) =
      true := by
  unfold F T
  fm_tnf
  unfold N_8002bddc T_8002bddc N_8002bdf0 T_8002bdf0
  fm_tnf
  unfold N_8002be04 T_8002be04 N_8002be10 T_8002be10 N_8002be14 T_8002be14 N_8002be18 T_8002be18
  fm_tnf
  exact ⟨ld_c1fc hro s r sx h5, ld_c1fcT s r sx h5⟩

/-! ## The special operands: `(x*y)/(x*y)` (`e_fmod.c:47-49`) -/

open Lua.Num in
theorem cls_infty' (a : Bool) : (F64.infty a).cls = .inf a := by cases a <;> decide
open Lua.Num in
theorem cls_zero'' (a : Bool) : (F64.zero a).cls = .zero a := by cases a <;> decide
open Lua.Num in
theorem cls_qnan : F64.qnan.cls = .nan := by decide

open Lua.Num in
/-- A NaN, an infinity or a zero divided by itself is the canonical NaN. -/
theorem div_self_sp (z : F64) (h : z.cls = .nan ∨ (∃ a, z.cls = .inf a) ∨ ∃ a, z.cls = .zero a) :
    F64.div z z = F64.qnan := by
  unfold F64.div
  rcases h with h | ⟨a, h⟩ | ⟨a, h⟩ <;> rw [h]

open Lua.Num in
/-- **`(x*y)/(x*y)` is the canonical NaN** when `y` is zero or NaN or `x` is
not finite (`e_fmod.c:47-49`). -/
theorem divmul_nan (x y : F64)
    (h : (y.bexp = 0 ∧ y.frac = 0) ∨ x.bexp = 2047 ∨ (y.bexp = 2047 ∧ y.frac ≠ 0)) :
    F64.div (F64.mul x y) (F64.mul x y) = F64.qnan := by
  apply div_self_sp
  have h' : y.cls = .zero y.sign ∨ x.cls = .nan ∨ x.cls = .inf x.sign ∨ y.cls = .nan := by
    rcases h with ⟨h1, h2⟩ | h1 | ⟨h1, h2⟩
    · left; simp [F64.cls, h1, h2]
    · right; unfold F64.cls; rw [if_pos h1]; split <;> simp
    · right; right; right; simp [F64.cls, h1, h2]
  unfold F64.mul
  rcases h' with h1 | h1 | h1 | h1 <;> rw [h1]
  · cases x.cls <;> simp [cls_infty', cls_zero'', cls_qnan]
  · simp [cls_qnan]
  · cases y.cls <;> simp [cls_infty', cls_zero'', cls_qnan]
  · cases x.cls <;> simp [cls_infty', cls_zero'', cls_qnan]

/-- The special operands' path (`e_fmod.c:47-49`): to `0x8002beb0`. -/
theorem pre_nan {m : Mem} (s : Nat) (r : BitVec 64) (sx hx lx sy hy ly : Int)
    (h5 : sx = 0 ∨ sx = 2 ^ 31) (h6 : sy = 0 ∨ sy = 2 ^ 31)
    (hx0 : 0 ≤ hx) (hx1 : hx < 2 ^ 31) (hy0 : 0 ≤ hy) (hy1 : hy < 2 ^ 31)
    (hl1 : -2 ^ 31 ≤ lx) (hl2 : lx < 2 ^ 31) (hm1 : -2 ^ 31 ≤ ly) (hm2 : ly < 2 ^ 31)
    (hsp : (hy = 0 ∧ ly % 2 ^ 32 = 0) ∨ 2047 * 2 ^ 20 ≤ hx ∨ 2047 * 2 ^ 20 < hy ∨
      (hy = 2047 * 2 ^ 20 ∧ ly % 2 ^ 32 ≠ 0)) :
    F m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      N_8002beb0 m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32))
        (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) ∧
    T m s r (BitVec.ofInt 64 ((sx + hx) * 2 ^ 32 + lx % 2 ^ 32)) (BitVec.ofInt 64 ((sy + hy) * 2 ^ 32 + ly % 2 ^ 32)) =
      true := by
  unfold F T
  fm_tnf
  by_cases hz : hy = 0 ∧ ly % 2 ^ 32 = 0
  · fm_tnf
    exact ⟨trivial, trivial⟩
  · fm_tnf
    unfold N_8002bddc T_8002bddc N_8002bdf0 T_8002bdf0
    fm_tnf
    simp only [ite_self, and_self]

/-- `0x8002beb0`: `(x*y)/(x*y)` through `__muldf3`'s summary. -/
theorem nan_beb0 {m : Mem} (s : Nat) (r x y : BitVec 64) (hs : FnSp s 128) :
    N_8002beb0 m s r x y = Lua.Num.F64.div (Lua.Num.F64.mul x y) (Lua.Num.F64.mul x y) := by
  unfold N_8002beb0 N_8002bebc N_8002bec4
  rw [Lua.Vm.Fn.Muldf3.spec_proved _ _ _ _ _ ⟨by have := hs.lo; omega, by have := hs.hi; omega,
    by have := hs.al; omega⟩]
  rw [show sign_extend (m := 64) (0#12) = 0#64 from rfl, BitVec.add_zero]

end Lua.Vm.Fn.Ieee754Fmod

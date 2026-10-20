import Lua.Vm.Fn.Pow
import Lua.Vm.Fn.SqrtSpec
import Lua.Vm.Fn.SfRefCmp
import Lua.Num.Pow

/-!
# libm's `pow` wrapper at level (b) (lane float-sf6)

`pow` (`w_pow.c:59-101`, entry `0x8002b9fc`) is lifted at level (a) by
`scripts/gen_lua_fn.py` (`Lua.Vm.Fn.Pow`: `__ieee754_pow`, `__unorddf2`,
`__eqdf2`, `finite`, `__ledf2`, `__errno` as call nodes; `errno`'s store
outside the frame, `OUTER`). Its value (`n_wrap`, `F_wrap`) is

  `z := __ieee754_pow(x, y)`; `z`, except `x == 0` and `y == 0` (both
  ordered): the `.rodata` constant `1.0` (`0x8005c488`);

every `errno` path returns `z`. `__unorddf2` is proved here (`Unorddf2.spec_proved`,
the comparison family's chamber generator `sfc_chambers`): `F a b ≠ 0` iff a
NaN operand.

**(b2) on the model** (`model`): `pow` is `Lua.Num.pow` (`Lua/Num/Pow.lean`,
`w_pow.c`'s transcription over `Float.Model`) on the model of its operands,
given `__ieee754_pow`'s level (b), the named obligation
`Ieee754PowSpec_Statement` (`e_pow.c`'s transcription `Lua.Num.Pow.ieee754Pow`
against the lifted `Ieee754Pow.F`; open, PHASES.md). Signalling-NaN operands are
outside `Float.Model` (`Lua/Num/Pow.lean`'s header: `pow(sNaN, 0)` is a NaN on
the ELF, `1` on the model), so the obligation and `model` exclude them
(`NotSNaN`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.Unorddf2
/-- The exponent test (`__unorddf2`'s `~(a >> 52) << 53 != 0`): not all ones. -/
theorem guard_e (a : BitVec 64) :
    ((shift_bits_left ((shift_bits_right a (Sail.BitVec.extractLsb (0x34#6) 5 0)) ^^^
      sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x35#6) 5 0)) != (0#64)) =
      decide (a.toNat / 2 ^ 52 % 2048 ≠ 2047) := by
  rw [Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit]
  simp only [Lua.Vm.Fn.SfLens.sext_eq, BitVec.reduceSignExtend]
  rw [show (0xffffffffffffffff#64 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.xor_allOnes]
  have ha := a.isLt
  have e : ((~~~(a >>> (0x34#6 : BitVec 6).toNat)) <<< (0x35#6 : BitVec 6).toNat).toNat =
      (2 ^ 64 - 1 - a.toNat / 2 ^ 52) * 2 ^ 53 % 2 ^ 64 := by
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_not, BitVec.toNat_ushiftRight]
    simp only [show (0x34#6 : BitVec 6).toNat = 52 from rfl, show (0x35#6 : BitVec 6).toNat = 53 from rfl,
      Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, ← BitVec.toNat_inj, e, BitVec.toNat_ofNat, decide_eq_true_eq]
  omega

/-- `e - 2047 <u 1`: the exponent is all ones. -/
theorem ult_e {e : Nat} (he : e < 2048) :
    zopz0zI_u (BitVec.ofNat 64 e + sign_extend (m := 64) (0x801#12)) (sign_extend (m := 64) (0x001#12)) =
      decide (e = 2047) := by
  simp only [Lua.Vm.Fn.SfLens.sext_eq, BitVec.reduceSignExtend, BitVec.ofNat_add_ofNat]
  rw [Lua.Vm.Fn.SfLens.nf_ult_neg (by decide) (by decide) (by omega)]

/-- `0 <u f`: the fraction is nonzero. -/
theorem ult_f {f : Nat} (hf : f < 2 ^ 52) : zopz0zI_u (0#64) (BitVec.ofNat 64 f) = decide (f ≠ 0) := by
  rw [Lua.Vm.Fn.SfLens.ult_nat]
  simp only [BitVec.toNat_ofNat]
  rw [Bool.eq_iff_iff, decide_eq_true_eq, decide_eq_true_eq]
  omega

theorem beq0 {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n == 0#64) = decide (n = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat,
    BitVec.toNat_ofNat]
  omega

/-- The lifted function over the operands' fields. -/
theorem F_fields (a b : BitVec 64) :
    F a b = if (a.toNat / 2 ^ 52 % 2048 = 2047 ∧ a.toNat % 2 ^ 52 ≠ 0) ∨
      (b.toNat / 2 ^ 52 % 2048 = 2047 ∧ b.toNat % 2 ^ 52 ≠ 0) then 1#64 else 0#64 := by
  unfold F N_8002f0d8 N_8002f0e4 N_8002f0e0
  rw [guard_e, Lua.Vm.Fn.SfLens.argE, Lua.Vm.Fn.SfLens.argF, Lua.Vm.Fn.SfLens.argF,
    ult_e (by omega), ult_f (by omega), beq0 (by omega)]
  by_cases h1 : a.toNat / 2 ^ 52 % 2048 = 2047 <;> by_cases h2 : a.toNat % 2 ^ 52 = 0 <;>
    by_cases h3 : b.toNat / 2 ^ 52 % 2048 = 2047 <;> by_cases h4 : b.toNat % 2 ^ 52 = 0 <;>
    simp [h1, h2, h3, h4] <;> decide

theorem isNaN_fields (a : BitVec 64) :
    Lua.Num.F64.isNaN a = decide (a.toNat / 2 ^ 52 % 2048 = 2047 ∧ a.toNat % 2 ^ 52 ≠ 0) := by
  unfold Lua.Num.F64.isNaN Lua.Num.F64.cls Lua.Num.F64.bexp Lua.Num.F64.frac
  by_cases h1 : a.toNat / 2 ^ 52 % 2 ^ 11 = 2047
  · by_cases h2 : a.toNat % 2 ^ 52 = 0
    · simp [h1, h2]
    · simp [h1, h2]
  · have h1' : ¬ a.toNat / 2 ^ 52 % 2048 = 2047 := h1
    simp only [h1, ite_false, false_and, decide_false]
    split <;> (try split) <;> rfl

/-- `__unorddf2`'s specification (`soft-fp/unorddf2.c`): `1` on a NaN operand. -/
def S (a b : BitVec 64) : BitVec 64 := if Lua.Num.F64.isNaN a || Lua.Num.F64.isNaN b then 1#64 else 0#64

/-- **`__unorddf2`, proved**: nonzero exactly on a NaN operand. -/
theorem spec_proved (a b : BitVec 64) : F a b = S a b := by
  rw [F_fields, S, isNaN_fields, isNaN_fields]
  by_cases h : (a.toNat / 2 ^ 52 % 2048 = 2047 ∧ a.toNat % 2 ^ 52 ≠ 0) ∨
      (b.toNat / 2 ^ 52 % 2048 = 2047 ∧ b.toNat % 2 ^ 52 ≠ 0)
  · rw [if_pos h]
    rcases h with h | h <;> simp [h]
  · rw [if_neg h]
    simp only [not_or] at h
    simp [h.1, h.2]

end Lua.Vm.Fn.Unorddf2
namespace Lua.Vm.Fn.PowR

open Lua.Num

/-- Not a signalling NaN (a quiet NaN's bit 51 is set; `Float.Model` has no
signalling NaN). -/
def NotSNaN (x : F64) : Prop := F64.isNaN x = true → x.toNat / 2 ^ 51 % 2 = 1

/-- **`__ieee754_pow` at level (b)** (open; PHASES.md): the lifted function is
`e_pow.c`'s transcription `Lua.Num.Pow.ieee754Pow` on the model of quiet
operands. Evidence: `Lua/Vm/Fn/PowTest.lean` (16,900 operand pairs). -/
def Ieee754PowSpec_Statement : Prop :=
  ∀ (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (x y : F64), RodataRead m → FnSp s 288 →
    NotSNaN x → NotSNaN y →
    F64.toModel (Ieee754Pow.F m s r g x y) = Lua.Num.Pow.ieee754Pow (F64.toModel x) (F64.toModel y)

/-- `w_pow.c`'s `1.0` (`.rodata` at `0x8005c488`). -/
abbrev oneW : BitVec 64 := 0x3ff0000000000000#64

theorem one_ld {m : Mem} (hro : RodataRead m) : bytesT8 m 2147861640 = oneW := by
  rw [Ieee754Sqrt.rodQ_eq hro (by decide) (by decide)]; decide +kernel

/-- `pow`'s value over `z = __ieee754_pow(x, y)` (`w_pow.c:70-81`): `z`
unless both `x` and `y` compare equal to `0` (`__eqdf2`), with `y` not a NaN
(`__unorddf2`). -/
def wrapV (z x y : F64) : F64 :=
  if Unorddf2.F y y != 0#64 then z
  else if Eqdf2.F x 0#64 != 0#64 then z
  else if Eqdf2.F y 0#64 != 0#64 then z
  else oneW

/-- **The wrapper's value** (every `errno` path returns `z`). -/
theorem n_wrap {m : Mem} (s : Nat) (r : BitVec 64) (g : SFrame) (v9 v10 v18 : BitVec 64)
    (hro : RodataRead m) : Pow.N_8002ba1c m s r g v9 v10 v18 = wrapV v10 v18 v9 := by
  have z0 : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  have ha : (((0x8002ba50#64) + sign_extend (m := 64) ((0x00031#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xa38#12)).toNat = 2147861640 := by decide
  have t1 : ∀ v8 v9 v18, Pow.N_8002ba94 s r v8 v9 v18 = v8 := by
    intro v8 v9 v18
    simp only [Pow.N_8002ba58, Pow.N_8002baf8, Pow.N_8002baf4, Pow.N_8002bac8, Pow.N_8002bac4,
      Pow.N_8002babc, Pow.N_8002bab8, Pow.N_8002bab0, Pow.N_8002baac, Pow.N_8002baa0, Pow.N_8002bb08,
      Pow.N_8002bb04, Pow.N_8002baf0, Pow.N_8002bae4, Pow.N_8002bae0, Pow.N_8002bad8, Pow.N_8002bad4,
      Pow.N_8002bacc, Pow.N_8002ba9c, Pow.N_8002ba94, z0, BitVec.add_zero, ite_self]
  have t2 : ∀ v8 v9 v18, Pow.N_8002ba74 s r v8 v9 v18 = v8 := by
    intro v8 v9 v18
    simp only [Pow.N_8002ba58, Pow.N_8002baf8, Pow.N_8002baf4, Pow.N_8002ba90, Pow.N_8002ba8c,
      Pow.N_8002ba80, Pow.N_8002ba7c, Pow.N_8002ba74, z0, BitVec.add_zero, ite_self]
  simp only [Pow.N_8002ba1c, Pow.N_8002ba2c, Pow.N_8002ba30, Pow.N_8002ba3c, Pow.N_8002ba40,
    Pow.N_8002ba4c, Pow.N_8002ba50, Pow.N_8002ba58, t1, t2, z0, BitVec.add_zero, ha]
  rw [one_ld hro]
  simp only [Lua.Vm.Fn.SfLens.sext_eq, BitVec.reduceSignExtend]
  unfold wrapV
  exact rfl

/-- `Float.Model`'s NaN test is `F64`'s. -/
theorem isNaN_model (x : F64) : Float.Model.isNaN (F64.toModel x) = F64.isNaN x := by
  unfold Float.Model.isNaN F64.isNaN
  rw [F64.toModel_unpack]
  rcases x.cls with _ | a | a | ⟨a, m, e⟩
  · rfl
  · rfl
  · rfl
  · by_cases h : 0 < m
    · simp only [F64.Cls.toU, h, dite_true]; rfl
    · simp only [F64.Cls.toU, h, dite_false]; rfl

theorem toModel_zero : F64.toModel 0#64 = Float.Model.ofNat 0 := by decide +kernel

/-- **(b2) of the wrapper**: given `z`'s model, `pow`'s value is `Lua.Num.pow`'s. -/
theorem wrap_model {z x y : F64}
    (hz : F64.toModel z = Lua.Num.Pow.ieee754Pow (F64.toModel x) (F64.toModel y)) :
    F64.toModel (wrapV z x y) = Lua.Num.pow (F64.toModel x) (F64.toModel y) := by
  unfold wrapV Lua.Num.pow
  rw [Unorddf2.spec_proved, Eqdf2.spec_proved, Eqdf2.spec_proved, ← toModel_zero, isNaN_model,
    ← F64.eq_eq_model, ← F64.eq_eq_model, ← hz]
  unfold Eqdf2.S Unorddf2.S
  simp only [Bool.or_self]
  cases hn : F64.isNaN y <;> cases e1 : F64.eq x 0#64 <;> cases e2 : F64.eq y 0#64 <;> rfl

/-- **`pow` on the model** (`w_pow.c`), given `__ieee754_pow`'s level (b). -/
theorem model (hP : Ieee754PowSpec_Statement) (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame)
    (x y : F64) (hro : RodataRead m) (hs : FnSp s 320) (hx : NotSNaN x) (hy : NotSNaN y) :
    F64.toModel (Pow.F m s r g x y) = Lua.Num.pow (F64.toModel x) (F64.toModel y) := by
  have z0 : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  fn_sp_factsW
  fn_imp_facts
  unfold Pow.F
  rw [n_wrap _ _ _ _ _ _ (by fn_rod_patch4)]
  simp only [z0, BitVec.add_zero]
  exact wrap_model (hP _ _ _ _ x y (by fn_rod_patch4) (fn_sp_in hs (by decide) (by decide)) hx hy)

end Lua.Vm.Fn.PowR


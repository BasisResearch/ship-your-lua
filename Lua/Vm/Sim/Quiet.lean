import Lua.Bytecode.Semantics
import Lua.Num.F64

/-!
# Quiet float payloads (lane F1-22)

A float payload the relation admits is not a signalling NaN
(`Lua.Bytecode.isSNaN`, the test `Const.toValue?` already makes of a constant:
`lundump.c`'s `loadNumber` copies raw bytes, so only a binary chunk carries
one). `Float.Model` has no signalling NaN, so the ELF's libm differs from the
model on one (`pow(sNaN, ±0)`, `Lua/Vm/Fn/PowTest.lean`); `ValRepr.flt` keeps
the fact. Its sources: a model datum's bits (`isSNaN_toBits`: the arms' stored
results and conversions), a sign flip (`isSNaN_xor_sign`: `OP_UNM`), a copy of
a represented payload, and a constant (`Const.toValue?`).
-/

namespace Lua.Bytecode

open Lua.Num

/-- `isSNaN` over the fields: the exponent all ones, a nonzero fraction, the
quiet bit (51) clear. -/
theorem isSNaN_fields (x : BitVec 64) :
    isSNaN x = decide (x.toNat / 2 ^ 52 % 2048 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0 ∧
      x.toNat / 2 ^ 51 % 2 = 0) := by
  have e1 : ((x >>> 52) &&& 0x7ff#64).toNat = x.toNat / 2 ^ 52 % 2048 := by
    rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    exact Nat.and_two_pow_sub_one_eq_mod _ 11
  have e2 : (x &&& 0xfffffffffffff#64).toNat = x.toNat % 2 ^ 52 := by
    rw [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 52
  have e3 : x.getLsbD 51 = decide (x.toNat / 2 ^ 51 % 2 = 1) := by
    rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  unfold isSNaN
  rw [e3]
  have b1 : ((x >>> 52) &&& 0x7ff#64 = 0x7ff#64) ↔ x.toNat / 2 ^ 52 % 2048 = 2047 := by
    rw [BitVec.toNat_eq, e1]; rfl
  have b2 : (x &&& 0xfffffffffffff#64 ≠ 0#64) ↔ x.toNat % 2 ^ 52 ≠ 0 := by
    rw [ne_eq, BitVec.toNat_eq, e2]; rfl
  by_cases h1 : x.toNat / 2 ^ 52 % 2048 = 2047 <;>
  by_cases h2 : x.toNat % 2 ^ 52 = 0 <;>
  by_cases h3 : x.toNat / 2 ^ 51 % 2 = 1 <;>
  simp_all <;> omega

/-- **The bridge to `F64`'s class**: not a signalling NaN is "a NaN has its
quiet bit set" (`Lua.Vm.Fn.PowR.NotSNaN`'s form). -/
theorem isSNaN_eq_false_iff (x : BitVec 64) :
    isSNaN x = false ↔ (F64.isNaN x = true → x.toNat / 2 ^ 51 % 2 = 1) := by
  have hn : F64.isNaN x = true ↔ x.toNat / 2 ^ 52 % 2048 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0 := by
    simp only [F64.isNaN, F64.cls, F64.bexp, F64.frac]
    by_cases h1 : x.toNat / 2 ^ 52 % 2 ^ 11 = 2047 <;> by_cases h2 : x.toNat % 2 ^ 52 = 0 <;>
      simp [h1, h2] <;> (try split) <;> simp_all
  rw [isSNaN_fields, hn, decide_eq_false_iff_not]
  constructor
  · intro h ⟨h1, h2⟩; omega
  · intro h ⟨h1, h2, h3⟩; have := h ⟨h1, h2⟩; omega

/-- `isSNaN` reads the low 63 bits only. -/
theorem isSNaN_congr {x y : BitVec 64} (h : x.toNat % 2 ^ 63 = y.toNat % 2 ^ 63) :
    isSNaN x = isSNaN y := by
  rw [isSNaN_fields, isSNaN_fields]
  have k : ∀ z : BitVec 64, z.toNat / 2 ^ 52 % 2048 = z.toNat % 2 ^ 63 / 2 ^ 52 ∧
      z.toNat % 2 ^ 52 = z.toNat % 2 ^ 63 % 2 ^ 52 ∧
      z.toNat / 2 ^ 51 % 2 = z.toNat % 2 ^ 63 / 2 ^ 51 % 2 := fun z => by
    have := z.isLt; omega
  obtain ⟨a1, a2, a3⟩ := k x
  obtain ⟨b1, b2, b3⟩ := k y
  rw [a1, a2, a3, b1, b2, b3, h]

/-- **A sign flip keeps quietness** (`OP_UNM`'s inline `xor`). -/
theorem isSNaN_xor_sign (x : BitVec 64) :
    isSNaN (x ^^^ 0x8000000000000000#64) = isSNaN x := by
  apply isSNaN_congr
  rw [BitVec.toNat_xor, Nat.xor_mod_two_pow]; simp

/-- **A model datum's bits are quiet**: `Float.Model`'s only NaN is the
canonical `0x7ff8000000000000`. -/
theorem isSNaN_toBits (y : Float.Model) : isSNaN y.toBits.toBitVec = false := by
  rw [isSNaN_eq_false_iff]
  intro hn
  obtain ⟨b, hv⟩ := y
  have hc : F64.cls b.toBitVec = .nan := by
    simpa [F64.isNaN] using hn
  have e : b.toBitVec = 0x7ff8000000000000#64 := by
    have hpn := hv.eq_packedNaN
    simp only [F64.cls] at hc
    split at hc
    · split at hc
      · cases hc
      · rename_i h1 h2
        rw [hpn ((F64.exp_eq_ones _).2 h1) (fun e => h2 ((F64.man_eq_zero _).1 e))]
        rfl
    · split at hc
      · split at hc <;> cases hc
      · cases hc
  show b.toBitVec.toNat / 2 ^ 51 % 2 = 1
  rw [e]; decide

end Lua.Bytecode

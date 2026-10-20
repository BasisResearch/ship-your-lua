import Lua.Vm.Sim.Kit.FltVal

/-!
# `luai_numunm` on the ELF: the inline sign flip (lane F2)

`OP_UNM` on a float compiles to `xor` with `1 << 63`, no call. Its payload
is the kernel's `Float.Model.neg` for every datum, NaN included: the model
canonicalises NaN on both sides (`F64.toModel`), so the bridge holds where
`F64.neg_eq_model` (bits) holds only off NaN.
-/

namespace Lua.Num.F64

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat

/-- `F64.neg` is the machine's `xor` of the sign bit. -/
theorem neg_eq_xor (x : F64) : neg x = x ^^^ 0x8000000000000000#64 := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  apply BitVec.eq_of_toNat_eq
  rw [neg, toNat_bits _ _ _ hb hf, BitVec.toNat_xor]
  have hx := x.isLt
  have h1 : (x.toNat ^^^ (0x8000000000000000#64 : BitVec 64).toNat) / 2 ^ 63 = x.toNat / 2 ^ 63 ^^^ 1 := by
    rw [Nat.xor_div_two_pow]; rfl
  have h2 : (x.toNat ^^^ (0x8000000000000000#64 : BitVec 64).toNat) % 2 ^ 63 = x.toNat % 2 ^ 63 := by
    rw [Nat.xor_mod_two_pow]; simp
  have h3 := Nat.div_add_mod (x.toNat ^^^ (0x8000000000000000#64 : BitVec 64).toNat) (2 ^ 63)
  generalize x.toNat ^^^ (0x8000000000000000#64 : BitVec 64).toNat = y at h1 h2 h3
  simp only [sign, bexp, frac]
  rcases (by omega : x.toNat / 2 ^ 63 = 0 ∨ x.toNat / 2 ^ 63 = 1) with h | h <;>
    rw [h] at h1 <;> simp at h1 <;> by_cases hs : 2 ^ 63 ≤ x.toNat <;> simp [hs] <;> omega

/-- **The model of the flipped datum is the model's `neg`**, NaN included. -/
theorem toModel_neg (x : F64) : toModel (neg x) = Float.Model.neg (toModel x) := by
  have e1 : Float.Model.neg (toModel x) = Float.Model.pack x.cls.toU.neg := by
    unfold Float.Model.neg; rw [toModel_unpack]
  have e2 : toModel (neg x) = Float.Model.pack (neg x).cls.toU := by
    unfold toModel Float.Model.ofBits; rw [← unpack_eq]
  rw [e1, e2, cls_neg]
  congr 1
  cases hc : x.cls with
  | nan => rfl
  | inf a => cases a <;> rfl
  | zero a => cases a <;> rfl
  | fin a m e =>
    simp only [Cls.negate, Cls.toU, (cls_fin hc).1.pos, dite_true, UnpackedFloat.neg, sgn_neg]

end Lua.Num.F64

namespace Lua.Vm.Sim

open Lua.Num Lua.Vm.Layout Lua.Bytecode

/-- **`OP_UNM`'s stored float**: the float tag and the payload with its sign
bit flipped represent the kernel's `.flt (neg x) (!n)`. -/
theorem ValRepr.flt_neg {mo : Mem} {ι : Strs} {t : BitVec 8} (ht : t = BitVec.ofNat 8 vNumFlt)
    (b : BitVec 64) (hq : isSNaN b = false) :
    ValRepr mo ι t (b ^^^ 0x8000000000000000#64) (.flt (F64.toModel b).neg !b.msb) := by
  subst ht
  have hm : (F64.neg b).msb = !b.msb := by
    rw [F64.neg_eq_xor, BitVec.msb_xor, show (0x8000000000000000#64 : BitVec 64).msb = true by decide,
      Bool.xor_true]
  have hq' : isSNaN (F64.neg b) = false := by rw [F64.neg_eq_xor, isSNaN_xor_sign, hq]
  rw [← F64.neg_eq_xor, ← F64.toModel_neg, ← hm]
  exact ValRepr.flt hq'

end Lua.Vm.Sim

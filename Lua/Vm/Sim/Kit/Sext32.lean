import Lua.Vm.Sim.Kit.AtFn

/-!
# A small word's `sext.w`

`fmt_sext32_ofNat`: the 64-bit sign extension of a 32-bit literal below
`2 ^ 31` is the literal (a `lw` of a small count). Its own module so a
callee's at-lemmas can use it without `FmtLib`'s `at_eq` hooks
(`Kit/AtNarrow.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

/-- A 32-bit literal's `sext.w` (a `lw` of a small word). -/
theorem fmt_sext32_ofNat {n : Nat} (h : n < 2 ^ 31) :
    sign_extend (m := 64) (BitVec.ofNat 32 n) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  split <;> rename_i hm <;> simp only [decide_eq_true_eq] at hm <;> omega

theorem sext12_ofNat {k : Nat} (hk : k < 2 ^ 11) :
    sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_eq_decide, BitVec.toNat_ofNat]
  split <;> rename_i hm <;> simp only [decide_eq_true_eq] at hm <;> omega

/-- `addiw` of a small immediate to a small 32-bit count. -/
theorem addiw32_ofNat {n k : Nat} (hk : k < 2 ^ 11) (h : n + k < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb
      (sign_extend (m := 64) (BitVec.ofNat 32 n) + sign_extend (m := 64) (BitVec.ofNat 12 k)) 31 0)
      = BitVec.ofNat 64 (n + k) := by
  rw [fmt_sext32_ofNat (by omega), sext12_ofNat hk, BitVec.ofNat_add_ofNat]
  have e : Sail.BitVec.extractLsb (BitVec.ofNat 64 (n + k)) 31 0 = BitVec.ofNat 32 (n + k) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero, BitVec.toNat_ofNat]
    rw [Nat.mod_mod_of_dvd _ (by decide)]
  rw [e, fmt_sext32_ofNat h]

end Lua.Vm.Sim.Kit

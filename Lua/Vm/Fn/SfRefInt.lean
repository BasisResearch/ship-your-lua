import Lua.Vm.Fn.SfRefCmp
import Lua.Num.SfRefInt

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens Lua.Vm.Fn.SfCmpLens

namespace Lua.Vm.Fn.SfIntLens
open Lean Elab Tactic Meta

/-- `unfold_lhs` through the goal's metadata. -/
elab "unfold_lhs'" : tactic => do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, lhs, _) := g.eq? | throwError "unfold_lhs': not an equation"
  let .const n _ := lhs.getAppFn | throwError "unfold_lhs': the left side's head is not a constant"
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))

end Lua.Vm.Fn.SfIntLens

namespace Lua.Vm.Fn.Fixdfdi
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

theorem nf_or52 {f : Nat} (h : f < 2 ^ 52) :
    BitVec.ofNat 64 f ||| 4503599627370496#64 = BitVec.ofNat 64 (2 ^ 52 + f) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : f < 2 ^ 64), show (4503599627370496 : Nat) % 2 ^ 64 = 1 * 2 ^ 52 by decide,
    add_or _ _ _ h]
  omega

theorem ofInt_negNat {X : Nat} (h0 : 0 < X) (h1 : X ≤ 2 ^ 63) :
    BitVec.ofInt 64 (-(X : Int)) = BitVec.ofNat 64 (2 ^ 64 - X) := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofInt_small (by omega) (by omega), BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  split <;> omega

/-- The leaves' normal form (`sf_nf`'s literal and `ofNat` steps; `sf_nf`
itself recurses past `maxRecDepth` on the saturated leaf's `2^63 - 1`). -/
macro "sfi_nf" : tactic => `(tactic| (
  try simp only [Nat.reducePow] at *
  try simp only [Lua.Vm.Fn.SfLens.srl_lit, Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.sext_eq,
    BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceHShiftRight, BitVec.add_zero, BitVec.zero_add]
  try simp only [BitVec.ofNat_eq_ofNat]
  try simp (disch := omega) only [Lua.Vm.Fn.SfLens.nf_add, Lua.Vm.Fn.SfLens.nf_sub_wrap]
  try simp only [Nat.reducePow, Nat.reduceAdd, Nat.zero_add]))

/-- A chamber of `__fixdfdi`: the operand unpacked, the DAG explored, the
leaf's word against the reference's branch (`sgnApply` of the shifted
mantissa, negation as `2^64 - X`). -/
macro "sfi_chamber" : tactic => `(tactic| (
  unfold F
  simp (disch := omega) only [Lua.Vm.Fn.SfCmpLens.argA_P, Lua.Vm.Fn.SfCmpLens.argE_P, Lua.Vm.Fn.SfCmpLens.argF_P]
  sf_nf
  repeat' (first
    | (unfold_node []; sf_nf; try simp (disch := omega) only [Lua.Vm.Fn.Fixdfdi.nf_or52,
        Lua.Vm.Fn.SfLens.nf_shr, Lua.Vm.Fn.SfLens.nf_shl])
    | (split <;> (try (exfalso; omega))))
  all_goals (unfold_lhs'; sfi_nf)
  all_goals (try simp only [Lua.Num.SfRef.toIntFields, Lua.Num.F64.sgnApply, decide_eq_true_eq])
  all_goals (repeat (simp (disch := omega) only [if_pos, if_neg]))
  all_goals (try simp only [Nat.reducePow] at *)
  all_goals (try simp (disch := omega) only [Lua.Vm.Fn.Fixdfdi.ofInt_negNat, Lua.Vm.Fn.SfLens.nf_ofInt_nat])
  all_goals (first | rfl | decide | (congr 1; omega))))

open Lua.Num in
theorem ch_lo (s e f : Nat) (hs : s < 2) (hf : f < 2 ^ 52) (h1 : e < 1023) :
    F (P s e f) = BitVec.ofInt 64 (SfRef.toIntFields (decide (s = 1)) e f) := by
  sfi_chamber

open Lua.Num in
theorem ch_hi (s e f : Nat) (hs : s < 2) (hf : f < 2 ^ 52) (h1 : 1086 ≤ e) (h2 : e < 2048) :
    F (P s e f) = BitVec.ofInt 64 (SfRef.toIntFields (decide (s = 1)) e f) := by
  rcases (by omega : s = 0 ∨ s = 1) with rfl | rfl <;> sfi_chamber

open Lua.Num in
theorem ch_shl (s e f : Nat) (hs : s < 2) (hf : f < 2 ^ 52) (h1 : 1075 ≤ e) (h2 : e < 1086) :
    F (P s e f) = BitVec.ofInt 64 (SfRef.toIntFields (decide (s = 1)) e f) := by
  have hv0 : 0 < (2 ^ 52 + f) * 2 ^ (e - 1075) := Nat.mul_pos (by omega) (Nat.two_pow_pos _)
  have hv1 : (2 ^ 52 + f) * 2 ^ (e - 1075) < 2 ^ 63 := SfRef.mul_pow_lt (by omega) (by omega)
  sfi_chamber

open Lua.Num in
theorem ch_shr (s e f : Nat) (hs : s < 2) (hf : f < 2 ^ 52) (h1 : 1023 ≤ e) (h2 : e < 1075) :
    F (P s e f) = BitVec.ofInt 64 (SfRef.toIntFields (decide (s = 1)) e f) := by
  have hv0 : 0 < (2 ^ 52 + f) / 2 ^ (1075 - e) :=
    Nat.div_pos (Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) (Nat.le_add_right _ _))
      (Nat.two_pow_pos _)
  have hv1 : (2 ^ 52 + f) / 2 ^ (1075 - e) ≤ 2 ^ 52 + f := Nat.div_le_self _ _
  sfi_chamber

open Lua.Num in
/-- The cover of the chambers. -/
theorem G_eq (s e f : Nat) (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    F (P s e f) = BitVec.ofInt 64 (SfRef.toIntFields (decide (s = 1)) e f) := by
  by_cases h1 : e < 1023
  · exact ch_lo s e f hs hf h1
  by_cases h2 : 1086 ≤ e
  · exact ch_hi s e f hs hf h2 he
  by_cases h3 : 1075 ≤ e
  · exact ch_shl s e f hs hf h3 (by omega)
  · exact ch_shr s e f hs hf (by omega) (by omega)

open Lua.Num in
/-- **`SoftFloatSpec.fixdfdi`, proved**: (b1) the chambers, then (b2)
`SfRef.toInt_eq`. -/
theorem spec_proved (x : BitVec 64) : F x = S x := by
  have hx := x.isLt
  conv => lhs; rw [P_fields x]
  rw [G_eq _ _ _ (by omega) (by omega) (by omega)]
  have h : SfRef.toInt x = BitVec.ofInt 64 (SfRef.toIntFields (decide (x.toNat / 2 ^ 63 = 1))
      (x.toNat / 2 ^ 52 % 2048) (x.toNat % 2 ^ 52)) := by
    unfold SfRef.toInt; rw [sign_fields]; rfl
  rw [← h, SfRef.toInt_eq]
  rfl

end Lua.Vm.Fn.Fixdfdi

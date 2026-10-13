import Lua.Vm.Fn.SfRefCmp
import Lua.Num.SfRefInt

/-!
# `__fixdfdi`, `__floatdidf`, `__floatsidf` against `SfRef` (lane float-sf2, (b1))

The conversions' lifted functions (`Lua/Vm/Fn/{Fixdfdi,Floatdidf,Floatsidf}`)
are the soft-fp-shaped references of `Lua/Num/SfRefInt.lean`; with (b2)
(`SfRef.toInt_eq`, `SfRef.ofInt_eq`) each `SoftFloatSpec` field is a theorem
(`<R>.spec_proved`).

* `__fixdfdi`: four chambers by the exponent (below the bias, a right
  shift, a left shift, saturated), one tactic (`sfi_chamber`).
* `__floatdidf`: B-SFREF's stage structure, one lemma per machine site: the
  round and pack (`g_2a8`, `_FP_ROUND`), the sticky shift (`g_308`,
  `_FP_FRAC_SRS` by `nf_sticky`/`nf_srs`), the left shift (`g_2a0`), the exact
  pack (`g_248`, through `exact_pack`); the entry forwards the frame's reloads
  (`frame_addr32`) and the magnitude (`abs_nf`) and `__clzdi2` (`nf_clz`).
* `__floatsidf`: the same entry on a canonical `int` (`canon_range`,
  `sign32_nf`, `mag32_nf`), always the exact pack (`exact_pack`).
-/

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

/-- `srai x, 63`: the sign mask. -/
theorem sra63 (x : BitVec 64) :
    shift_bits_right_arith x (Sail.BitVec.extractLsb (0x3f#6) 5 0) =
      if x.toNat < 2 ^ 63 then 0#64 else BitVec.allOnes 64 := by
  unfold shift_bits_right_arith
  rw [show BitVec.toNatInt (Sail.BitVec.extractLsb (0x3f#6) 5 0) = 63 by decide]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have h1 := x.toInt_lt
  have h2 := x.le_toInt
  have hc := BitVec.toInt_eq_toNat_cond x
  simp only [show Int.toNat 63 = 63 from rfl] at *
  split
  · rw [show (0#64 : BitVec 64).toInt = 0 by decide]
    split at hc <;> omega
  · rw [show (BitVec.allOnes 64).toInt = -1 by decide]
    split at hc <;> omega

/-- `__floatdidf`'s magnitude `(x ^ (x >>s 63)) - (x >>s 63)`. -/
theorem abs_nf (x : BitVec 64) :
    ((shift_bits_right_arith x (Sail.BitVec.extractLsb (0x3f#6) 5 0)) ^^^ x) -
      (shift_bits_right_arith x (Sail.BitVec.extractLsb (0x3f#6) 5 0)) = BitVec.ofNat 64 x.toInt.natAbs := by
  rw [sra63]
  have hc := BitVec.toInt_eq_toNat_cond x
  have hx := x.isLt
  split
  · rw [BitVec.zero_xor, BitVec.sub_zero]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    simp at hc
    split at hc <;> omega
  · rw [BitVec.allOnes_xor]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_not, BitVec.toNat_allOnes, BitVec.toNat_ofNat]
    simp at hc
    split at hc <;> omega

/-- `& 0x7ff` of an exponent. -/
theorem and7ff {E : Nat} (hE : E < 2048) : BitVec.ofNat 64 E &&& sign_extend (m := 64) (0x7ff#12) = BitVec.ofNat 64 E := by
  rw [sext_eq, show BitVec.signExtend 64 (0x7ff#12) = 2047#64 by decide, nf_and2047, Nat.mod_eq_of_lt hE]
/-- `(W << 9) >> 12`: bits 3..54 of the working mantissa (the hidden bit dropped). -/
theorem frac55 (W : Nat) :
    shift_bits_right (shift_bits_left (BitVec.ofNat 64 W) (Sail.BitVec.extractLsb (0x09#6) 5 0))
      (Sail.BitVec.extractLsb (0x0c#6) 5 0) = BitVec.ofNat 64 (W % 2 ^ 55 / 8) := by
  rw [sll_lit, srl_lit]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `_FP_PACK_RAW_D`'s three fields or-ed: exponent `A`, fraction `F`, sign `B`. -/
theorem nf_or3 {A F S : Nat} (hA : A % 2 ^ 52 = 0) (hA2 : A < 2 ^ 63) (hF : F < 2 ^ 52) (hS : S < 2) :
    BitVec.ofNat 64 A ||| BitVec.ofNat 64 F ||| BitVec.ofNat 64 (S * 9223372036854775808) =
      BitVec.ofNat 64 (S * 9223372036854775808 + A + F) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : A < 2 ^ 64), Nat.mod_eq_of_lt (by omega : F < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : S * 9223372036854775808 < 2 ^ 64)]
  have e1 : A = A / 2 ^ 52 * 2 ^ 52 := by omega
  rw [e1, or_add _ _ _ hF, show S * 9223372036854775808 = S * 2 ^ 63 by rfl,
    add_or _ _ _ (by omega)]
  have : (A / 2 ^ 52 * 2 ^ 52 + F) % 2 ^ 64 = A / 2 ^ 52 * 2 ^ 52 + F := Nat.mod_eq_of_lt (by omega)
  omega

open Lua.Num in
theorem exact_pack_lt {z n : Nat} (hz1 : 11 ≤ z) (hz : z ≤ 63) (hn0 : 0 < n) (hL : n.log2 = 63 - z) :
    n * 2 ^ (z - 11) < 2 ^ 53 := by
  have ⟨_, hn2⟩ := SfRef.log2_bounds hn0
  rw [hL] at hn2
  calc n * 2 ^ (z - 11) < 2 ^ (63 - z + 1) * 2 ^ (z - 11) := Nat.mul_lt_mul_of_pos_right hn2 (Nat.two_pow_pos _)
    _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega

open Lua.Num in
/-- `_FP_FROM_INT`'s exact branch (at most 53 significant bits, `z ≥ 11`
leading zeros) is the pack of the shifted magnitude. -/
theorem exact_pack {S z n : Nat} (hS : S < 2) (hz1 : 11 ≤ z) (hz : z ≤ 63) (hn0 : 0 < n) (hL : n.log2 = 63 - z) :
    SfRef.roundPack (decide (S = 1)) (1086 - z) (n * 2 ^ (z - 8)) =
      BitVec.ofNat 64 (S * 2 ^ 63 + (1086 - z) * 2 ^ 52 + n * 2 ^ (z - 11) % 2 ^ 52) := by
  have ⟨hn1, _⟩ := SfRef.log2_bounds hn0
  rw [hL] at hn1
  have hB1 : 2 ^ 52 ≤ n * 2 ^ (z - 11) := by
    calc 2 ^ 52 = 2 ^ (63 - z) * 2 ^ (z - 11) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ n * 2 ^ (z - 11) := Nat.mul_le_mul_right _ hn1
  have hB2 := exact_pack_lt hz1 hz hn0 hL
  have hAB : n * 2 ^ (z - 8) = n * 2 ^ (z - 11) * 8 := by
    rw [Nat.mul_assoc, show (8 : Nat) = 2 ^ 3 by rfl, ← Nat.pow_add]; congr 2; omega
  rw [hAB, SfRef.roundPack_keep (by omega) (by omega)]
  simp only [Lua.Vm.Fn.SfLens.bits_nf, decide_eq_true_eq]
  congr 1; split <;> omega

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

namespace Lua.Vm.Fn.Floatdidf
open Lua.Vm.Fn.SfIntLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- A slot of the 32-byte frame below `sp = s`. -/
theorem frame_addr32 {s : Nat} (o : BitVec 12) (h1 : 32 ≤ s) (h2 : s ≤ 2 ^ 32) (ho : o.toNat < 2048) :
    (BitVec.ofNat 64 s + sign_extend (m := 64) (0xfe0#12) + sign_extend (m := 64) o).toNat = s - 32 + o.toNat := by
  have e1 : (sign_extend (m := 64) (0xfe0#12)).toNat = 2 ^ 64 - 32 := by decide
  have e2 : (sign_extend (m := 64) o).toNat = o.toNat := by
    rw [sext_eq, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
    have : ¬ 2 ^ (12 - 1) ≤ o.toNat := by omega
    simp [this]; omega
  rw [BitVec.toNat_add, BitVec.toNat_add, e1, e2, BitVec.toNat_ofNat]
  omega

/-- The pack (`_FP_PACK_RAW_D` after `_FP_FRAC_SRL (X, 3)`, `0x8002f2e0`). -/
theorem nf_2e0 (m : Mem) (s : Nat) (r : BitVec 64) {S E W : Nat} (hS : S < 2) (hE : E < 2048) (hW : W < 2 ^ 64) :
    N_8002f2e0 m s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 E) (BitVec.ofNat 64 W) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + W % 2 ^ 55 / 8) := by
  unfold N_8002f2e0
  rw [Lua.Vm.Fn.SfIntLens.and7ff hE, Lua.Vm.Fn.SfIntLens.frac55 W]
  rw [pack_eq hE (by omega) hS]

open Lua.Num in
/-- `_FP_ROUND` and the pack (`0x8002f2a8`): the working mantissa `W` (hidden
bit at 55) at biased exponent `E`. -/
theorem g_2a8 (m : Mem) (s : Nat) (r : BitVec 64) {S E W : Nat} (hS : S < 2) (hE1 : 1 ≤ E) (hE : E ≤ 2045)
    (hW1 : 2 ^ 55 ≤ W) (hW : W < 2 ^ 56) :
    N_8002f2a8 m s r (BitVec.ofNat 64 W) (BitVec.ofNat 64 S) (BitVec.ofNat 64 E) (BitVec.ofNat 64 E) =
      SfRef.roundPack (decide (S = 1)) E W := by
  sf_go []
  all_goals sf_close [nf_2e0]

open Lua.Num in
/-- The sticky shift to the working mantissa (`_FP_FRAC_SRS`, `0x8002f308`),
then the round stage. -/
theorem g_308 (m : Mem) (s : Nat) (r : BitVec 64) {S E z n : Nat} (hS : S < 2) (hE1 : 1 ≤ E) (hE : E ≤ 2045)
    (hz : z ≤ 7) (hn0 : 0 < n) (hL : n.log2 = 63 - z) (hn : n < 2 ^ 64) :
    N_8002f308 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 n) (BitVec.ofNat 64 S) (BitVec.ofNat 64 E)
      (BitVec.ofNat 64 E) = SfRef.roundPack (decide (S = 1)) E (SfRef.rto n (8 - z)) := by
  unfold N_8002f308
  sf_nf
  rw [show z + 56 = 64 - (8 - z) by omega, nf_sticky (by omega), BitVec.or_comm]
  simp only [decide_eq_true_eq]
  rw [nf_srs hn]
  have ⟨hn1, _⟩ := SfRef.log2_bounds hn0
  rw [hL] at hn1
  have hk : 2 ^ (8 - z) ≤ n := Nat.le_trans (Nat.pow_le_pow_right (by decide) (by omega)) hn1
  have hl := SfRef.log2_rto hk
  have hr0 : 0 < SfRef.rto n (8 - z) := SfRef.rto_pos hn0
  have ⟨hr1, hr2⟩ := SfRef.log2_bounds hr0
  have hr55 : (SfRef.rto n (8 - z)).log2 = 55 := by omega
  rw [hr55] at hr1 hr2
  exact g_2a8 m s r hS hE1 hE hr1 hr2

open Lua.Num in
/-- The left shift to the working mantissa (`8 ≤ z ≤ 10`, `0x8002f2a0`), then
the round stage. -/
theorem g_2a0 (m : Mem) (s : Nat) (r : BitVec 64) {S E z n : Nat} (hS : S < 2) (hE1 : 1 ≤ E) (hE : E ≤ 2045)
    (hz1 : 8 ≤ z) (hz : z ≤ 10) (hn0 : 0 < n) (hL : n.log2 = 63 - z) :
    N_8002f2a0 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 n) (BitVec.ofNat 64 S) (BitVec.ofNat 64 E)
      (BitVec.ofNat 64 E) = SfRef.roundPack (decide (S = 1)) E (n * 2 ^ (z - 8)) := by
  have ⟨hn1, hn2⟩ := SfRef.log2_bounds hn0
  rw [hL] at hn1 hn2
  have hW1 : 2 ^ 55 ≤ n * 2 ^ (z - 8) := by
    calc 2 ^ 55 = 2 ^ (63 - z) * 2 ^ (z - 8) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ n * 2 ^ (z - 8) := Nat.mul_le_mul_right _ hn1
  have hW2 : n * 2 ^ (z - 8) < 2 ^ 56 := by
    calc n * 2 ^ (z - 8) < 2 ^ (63 - z + 1) * 2 ^ (z - 8) := Nat.mul_lt_mul_of_pos_right hn2 (Nat.two_pow_pos _)
      _ = 2 ^ 56 := by rw [← Nat.pow_add]; congr 1; omega
  unfold N_8002f2a0
  sf_nf
  exact g_2a8 m s r hS hE1 hE hW1 hW2

/-- The exact pack, `z > 11` (`0x8002f328`). -/
theorem nf_328 (m : Mem) (s : Nat) (r : BitVec 64) {S E z n : Nat} (hS : S < 2) (hE : E < 2048) (hz1 : 11 ≤ z)
    (hz : z ≤ 63) (hB : n * 2 ^ (z - 11) < 2 ^ 64) :
    N_8002f328 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 n) (BitVec.ofNat 64 S) (BitVec.ofNat 64 E) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + n * 2 ^ (z - 11) % 2 ^ 52) := by
  unfold N_8002f328
  rw [Lua.Vm.Fn.SfIntLens.and7ff hE]
  sf_nf
  rw [Lua.Vm.Fn.SfIntLens.nf_or3 (by omega) (by omega) (by omega) hS]
/-- The exact pack, `z = 11` (`0x8002f250`). -/
theorem nf_250 (m : Mem) (s : Nat) (r : BitVec 64) {S n : Nat} (hS : S < 2) (hn : n < 2 ^ 64) :
    N_8002f250 m s r (BitVec.ofNat 64 n) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + 1075 * 2 ^ 52 + n % 2 ^ 52) := by
  unfold N_8002f250
  sf_nf
  rw [Lua.Vm.Fn.SfIntLens.nf_or3 (by omega) (by omega) (by omega) hS]

open Lua.Num in
/-- The exact pack (`z ≥ 11`: at most 53 significant bits, `0x8002f248`). -/
theorem g_248 (m : Mem) (s : Nat) (r : BitVec 64) {S z n : Nat} (hS : S < 2)
    (hz1 : 11 ≤ z) (hz : z ≤ 63) (hn0 : 0 < n) (hL : n.log2 = 63 - z) :
    N_8002f248 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 n) (BitVec.ofNat 64 S) (BitVec.ofNat 64 z)
      (BitVec.ofNat 64 (1086 - z)) = SfRef.roundPack (decide (S = 1)) (1086 - z) (n * 2 ^ (z - 8)) := by
  have ⟨hn1, hn2⟩ := SfRef.log2_bounds hn0
  rw [hL] at hn1 hn2
  rw [exact_pack hS hz1 hz hn0 hL]
  unfold N_8002f248
  sf_go []
  · rw [nf_328 m s r hS (by omega) hz1 hz (Nat.lt_trans (exact_pack_lt hz1 hz hn0 hL) (by decide))]
  · rw [nf_250 m s r hS (Nat.lt_of_lt_of_le hn2 (Nat.pow_le_pow_right (by decide) (by omega)))]
    have hz11 : z = 11 := by omega
    subst hz11
    congr 1; simp

open Lua.Num in
/-- **Level (b1) for `__floatdidf`**: the lifted function is `SfRef.ofInt`
(`_FP_FROM_INT`), on any stack pointer the routine's frame fits below. -/
theorem F_eq_sfref (m : Mem) (s : Nat) (r x : BitVec 64) (hsp : Lua.Vm.Sim.FnSp s 32) :
    F m s r x = SfRef.ofInt x := by
  have hs1 : 32 ≤ s := by have := hsp.lo; unfold Vsa.Sim.tohostAddr at this; omega
  have hs2 : s ≤ 2 ^ 32 := hsp.hi
  by_cases hx : x = 0#64
  · subst hx; unfold F N_8002f278; simp only [beq_self_eq_true, ite_true]; decide
  unfold F
  rw [if_neg (by simpa using hx)]
  unfold N_8002f204
  rw [abs_nf, argA]
  unfold N_8002f22c
  simp only [sext64_self, Lua.Vm.Sim.sdData_id]
  simp (disch := first | omega | decide) only [frame_addr32]
  simp only [BitVec.reduceToNat]
  simp (disch := omega) only [Lua.Vm.Sim.bytesT8_wm8_same, Lua.Vm.Sim.bytesT8_wm8_far]
  have hn0 : 0 < x.toInt.natAbs := by
    have : x.toInt ≠ 0 := fun h => hx (by
      apply BitVec.eq_of_toInt_eq; rw [h]; decide)
    omega
  have hn1 : x.toInt.natAbs ≤ 2 ^ 63 := by have := x.toInt_lt; have := x.le_toInt; omega
  have hsg : decide (x.toInt < 0) = decide (x.toNat / 2 ^ 63 = 1) := by
    have hc := BitVec.toInt_eq_toNat_cond x
    have := x.isLt
    split at hc
    · rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    · rw [decide_eq_true (by omega), decide_eq_true (by omega)]
  have hneg : x.toNat / 2 ^ 63 < 2 := by have := x.isLt; omega
  unfold SfRef.ofInt
  rw [hsg]
  generalize x.toInt.natAbs = n at *
  generalize x.toNat / 2 ^ 63 = neg at *
  simp (disch := omega) only [BitVec.add_zero, sext_eq, BitVec.reduceSignExtend, nf_clz]
  have hL : n.log2 < 64 := (Nat.log2_lt (by omega)).2 (by omega)
  unfold SfRef.fromNat
  rw [if_neg (show ¬ n = 0 by omega)]
  have hLn : n.log2 = 63 - (63 - n.log2) := by omega
  have hz63 : 63 - n.log2 ≤ 63 := by omega
  generalize 63 - n.log2 = z at *
  sf_nf
  split
  · unfold N_8002f294
    sf_nf
    split
    · rw [g_308 _ _ r hneg (by omega) (by omega) (by omega) hn0 hLn (by omega), if_neg (by omega)]
    · rw [g_2a0 _ _ r hneg (by omega) (by omega) (by omega) (by omega) hn0 hLn, if_pos (by omega)]
  · rw [g_248 _ _ r hneg (by omega) (by omega) hn0 hLn, if_pos (by omega)]

open Lua.Num in
/-- **`SoftFloatSpec.floatdidf`, proved**: (b1) `F_eq_sfref`, (b2) `SfRef.ofInt_eq`. -/
theorem spec_proved (m : Mem) (s : Nat) (r x : BitVec 64) (hsp : Lua.Vm.Sim.FnSp s 32) :
    F m s r x = S x := by
  rw [F_eq_sfref m s r x hsp, SfRef.ofInt_eq]

end Lua.Vm.Fn.Floatdidf

namespace Lua.Vm.Fn.Floatsidf
open Lua.Vm.Fn.SfIntLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

theorem ext32_toNat (x : BitVec 64) : (Sail.BitVec.extractLsb x 31 0).toNat = x.toNat % 2 ^ 32 := by
  simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

/-- A canonical `int` argument (the upper word the low word's sign). -/
theorem canon_range {x : BitVec 64} (hx : (x.setWidth 32).signExtend 64 = x) :
    x.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ x.toNat := by
  have h := congrArg BitVec.toNat hx
  rw [BitVec.toNat_signExtend, BitVec.msb_eq_decide] at h
  simp only [BitVec.toNat_setWidth] at h
  have := x.isLt
  split at h <;> rename_i hm <;> simp at hm <;> omega

/-- `srai` by 31 of a 32-bit word: its sign mask. -/
theorem sra31 (y : BitVec 32) :
    shift_bits_right_arith y (0x1f#5) = if y.toNat < 2 ^ 31 then 0#32 else BitVec.allOnes 32 := by
  unfold shift_bits_right_arith
  rw [show BitVec.toNatInt (0x1f#5) = 31 by decide]
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow]
  have h1 := y.toInt_lt
  have h2 := y.le_toInt
  have hc := BitVec.toInt_eq_toNat_cond y
  simp only [show Int.toNat 31 = 31 from rfl] at *
  split
  · rw [show (0#32 : BitVec 32).toInt = 0 by decide]
    split at hc <;> omega
  · rw [show (BitVec.allOnes 32).toInt = -1 by decide]
    split at hc <;> omega

/-- `__floatsidf`'s sign: `srliw a0, 31`. -/
theorem sign32_nf {x : BitVec 64} (hx : (x.setWidth 32).signExtend 64 = x) :
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb x 31 0) (0x1f#5)) =
      BitVec.ofNat 64 (x.toNat / 2 ^ 63) := by
  have hr := canon_range hx
  apply BitVec.eq_of_toNat_eq
  rw [sext_eq, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  simp only [shift_bits_right, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    ext32_toNat, BitVec.toNat_ofNat, show BitVec.toNatInt (0x1f#5) = 31 by decide, show Int.toNat 31 = 31 from rfl]
  simp only [BitVec.ushiftRight_eq', BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, ext32_toNat,
    BitVec.reduceToNat, Nat.sub_zero, Nat.reduceAdd, Nat.reduceSub]
  have := x.isLt
  split <;> rename_i h <;> simp at h <;> omega

/-- `__floatsidf`'s magnitude: `((x ^ (x >>s 31)) - (x >>s 31))` in 32 bits,
zero-extended. -/
theorem mag32_nf {x : BitVec 64} (hx : (x.setWidth 32).signExtend 64 = x) :
    shift_bits_right (shift_bits_left (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb (x ^^^ (sign_extend (m := 64) (shift_bits_right_arith (Sail.BitVec.extractLsb x 31 0)
        (0x1f#5)))) 31 0) - (Sail.BitVec.extractLsb (sign_extend (m := 64)
          (shift_bits_right_arith (Sail.BitVec.extractLsb x 31 0) (0x1f#5))) 31 0)))
      (Sail.BitVec.extractLsb (0x20#6) 5 0)) (Sail.BitVec.extractLsb (0x20#6) 5 0) =
      BitVec.ofNat 64 x.toInt.natAbs := by
  have hr := canon_range hx
  have hxl := x.isLt
  have hc := BitVec.toInt_eq_toNat_cond x
  rw [sra31, ext32_toNat]
  split
  · rw [show sign_extend (m := 64) (0#32) = 0#64 by decide, BitVec.xor_zero]
    apply BitVec.eq_of_toNat_eq
    simp only [sll_lit, srl_lit, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, sext_eq, BitVec.toNat_signExtend, BitVec.toNat_sub, ext32_toNat,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.reduceToNat, BitVec.msb_eq_decide]
    simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.zero_mod, Nat.sub_zero] at *
    split <;> rename_i h <;> simp at h <;> split at hc <;> omega
  · rw [show sign_extend (m := 64) (BitVec.allOnes 32) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
    apply BitVec.eq_of_toNat_eq
    simp only [sll_lit, srl_lit, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow, sext_eq, BitVec.toNat_signExtend, BitVec.toNat_sub, ext32_toNat,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat, BitVec.reduceToNat, BitVec.msb_eq_decide, BitVec.toNat_not,
      BitVec.toNat_allOnes]
    simp only [Nat.reducePow, Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd, Nat.zero_mod, Nat.sub_zero] at *
    split <;> rename_i h <;> simp at h <;> split at hc <;> omega

open Lua.Num in
/-- **Level (b1) for `__floatsidf`**: on a canonical `int` argument the
lifted function is `SfRef.ofInt` (`_FP_FROM_INT` of a 32-bit magnitude: always
the exact branch). -/
theorem F_eq_sfref (m : Mem) (s : Nat) (r x : BitVec 64) (hsp : Lua.Vm.Sim.FnSp s 32)
    (hx : (x.setWidth 32).signExtend 64 = x) : F m s r x = SfRef.ofInt x := by
  have hs1 : 32 ≤ s := by have := hsp.lo; unfold Vsa.Sim.tohostAddr at this; omega
  have hs2 : s ≤ 2 ^ 32 := hsp.hi
  by_cases hx0 : x = 0#64
  · subst hx0; unfold F N_8002f16c; simp only [beq_self_eq_true, ite_true]; decide
  have hr := canon_range hx
  unfold F
  rw [if_neg (by simpa using hx0)]
  unfold N_8002f0fc
  rw [mag32_nf hx, sign32_nf hx]
  unfold N_8002f12c
  simp only [sext64_self, Lua.Vm.Sim.sdData_id]
  simp (disch := first | omega | decide) only [Lua.Vm.Fn.Floatdidf.frame_addr32]
  simp only [BitVec.reduceToNat]
  simp (disch := omega) only [Lua.Vm.Sim.bytesT8_wm8_same, Lua.Vm.Sim.bytesT8_wm8_far]
  have hn0 : 0 < x.toInt.natAbs := by
    have : x.toInt ≠ 0 := fun h => hx0 (by
      apply BitVec.eq_of_toInt_eq; rw [h]; decide)
    omega
  have hn1 : x.toInt.natAbs ≤ 2 ^ 31 := by
    have hc := BitVec.toInt_eq_toNat_cond x
    have := x.isLt
    split at hc <;> omega
  have hsg : decide (x.toInt < 0) = decide (x.toNat / 2 ^ 63 = 1) := by
    have hc := BitVec.toInt_eq_toNat_cond x
    have := x.isLt
    split at hc
    · rw [decide_eq_false (by omega), decide_eq_false (by omega)]
    · rw [decide_eq_true (by omega), decide_eq_true (by omega)]
  have hneg : x.toNat / 2 ^ 63 < 2 := by have := x.isLt; omega
  unfold SfRef.ofInt
  rw [hsg]
  generalize x.toInt.natAbs = n at *
  generalize x.toNat / 2 ^ 63 = neg at *
  simp (disch := omega) only [BitVec.add_zero, sext_eq, BitVec.reduceSignExtend, nf_clz]
  have hL : n.log2 < 32 := (Nat.log2_lt (by omega)).2 (by omega)
  unfold SfRef.fromNat
  rw [if_neg (show ¬ n = 0 by omega), if_pos (show 8 ≤ 63 - n.log2 by omega)]
  have hLn : n.log2 = 63 - (63 - n.log2) := by omega
  rw [exact_pack hneg (by omega) (by omega) hn0 hLn]
  have hz32 : 32 ≤ 63 - n.log2 := by omega
  have hz63 : 63 - n.log2 ≤ 63 := by omega
  have hB := exact_pack_lt (by omega) hz63 hn0 hLn
  generalize 63 - n.log2 = z at *
  sf_nf
  rw [nf_or3 (by omega) (by omega) (by omega) hneg]

open Lua.Num in
/-- **`SoftFloatSpec.floatsidf`, proved**: (b1) `F_eq_sfref`, (b2)
`SfRef.ofInt_eq` (a canonical argument is its own sign extension). -/
theorem spec_proved (m : Mem) (s : Nat) (r x : BitVec 64) (hsp : Lua.Vm.Sim.FnSp s 32)
    (hx : (x.setWidth 32).signExtend 64 = x) : F m s r x = S x := by
  rw [F_eq_sfref m s r x hsp hx, SfRef.ofInt_eq, S, hx]

end Lua.Vm.Fn.Floatsidf

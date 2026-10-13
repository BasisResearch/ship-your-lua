import Lua.Vm.Fn.Muldf3
import Lua.Vm.Fn.SfRefCmp
import Lua.Num.SfRefMul

/-!
# `__muldf3` against `SfRef.mul` (lane float-sf3, (b1))
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens

namespace Lua.Vm.Fn.MulLens

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- An exponent word: a signed `Int` as the machine's 64-bit word, opaque to
unification (`BitVec.ofInt` unfolds into `2^64` arithmetic, past
`maxRecDepth`, when a lemma about `BitVec.ofNat` is tried on it). -/
def ew (x : Int) : BitVec 64 := BitVec.ofInt 64 x

theorem ew_def (x : Int) : ew x = BitVec.ofInt 64 x := rfl

attribute [irreducible] ew

/-- An exponent word plus a literal. -/
theorem nf_ew_addc (x : Int) (c : Nat) : ew x + BitVec.ofNat 64 c = ew (x + c) := by
  rw [ew_def, ew_def, ← nf_ofInt_nat c]
  apply BitVec.eq_of_toInt_eq
  simp only [BitVec.toInt_add, BitVec.toInt_ofInt]
  rw [Int.add_bmod_bmod, Int.bmod_add_bmod]

/-- A non-negative exponent word in the `ofNat` normal form. -/
theorem nf_ew_nn (x : Int) (h : 0 ≤ x) : ew x = BitVec.ofNat 64 x.toNat := by
  rw [ew_def]
  conv => lhs; rw [show x = ((x.toNat : Nat) : Int) by omega]
  exact nf_ofInt_nat _

theorem ofInt_negNat (D : Nat) (h : D ≤ 2 ^ 62) :
    BitVec.ofInt 64 (-(D : Int)) = BitVec.ofNat 64 (18446744073709551616 - D) := by
  rcases Nat.eq_zero_or_pos D with h0 | h0
  · subst h0; decide
  · apply BitVec.eq_of_toInt_eq
    rw [toInt_ofInt_small (by omega) (by omega), BitVec.toInt_eq_toNat_cond]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    split <;> omega

/-- `blt E, -55` on a negative exponent word `-D`. -/
theorem nf_slt_m55 {D : Nat} (h2 : D < 2 ^ 62) :
    zopz0zI_s (ew (-(D : Int))) 18446744073709551561#64 = decide (55 < D) := by
  rw [ew_def, slt_int', toInt_ofInt_small (by omega) (by omega)]
  simp only [decide_eq_decide]
  show -(D : Int) < -55 ↔ 55 < D
  omega
/-- `beqz E` on a negative exponent word `-D`. -/
theorem nf_beq0_neg {D : Nat} (h2 : D < 2 ^ 62) :
    (ew (-(D : Int)) == 0#64) = decide (D = 0) := by
  rw [ew_def, beq_toNat]
  simp only [decide_eq_decide]
  constructor
  · intro h
    have := congrArg BitVec.toInt (BitVec.eq_of_toNat_eq h)
    rw [toInt_ofInt_small (by omega) (by omega)] at this
    simp at this; omega
  · intro h; subst h; rfl
/-- `blez E` on a negative exponent word `-D`. -/
theorem nf_sge0_neg {D : Nat} (h2 : D < 2 ^ 62) : zopz0zKzJ_s 0#64 (ew (-(D : Int))) = true := by
  rw [ew_def, sge_int, toInt_ofInt_small (by omega) (by omega)]
  simp only [BitVec.toInt_zero, ge_iff_le, decide_eq_true_eq]; omega

theorem wsub_neg {c D : Nat} (h : c + D < 2 ^ 31) (hD : D ≤ 2 ^ 31) :
    BitVec.signExtend 64 ((Sail.BitVec.extractLsb (BitVec.ofNat 64 c) 31 0) -
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 (18446744073709551616 - D)) 31 0)) = BitVec.ofNat 64 (c + D) := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofNat_small (by omega), BitVec.toInt_signExtend_of_le (by decide)]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, Nat.shiftRight_zero,
    BitVec.toInt_eq_toNat_bmod, Nat.reduceSub, Nat.reduceAdd, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have e1 : (2 ^ 32 - ((18446744073709551616 - D) % 2 ^ 64 % 2 ^ 32) + c % 2 ^ 64 % 2 ^ 32) % 2 ^ 32 = c + D := by
    omega
  rw [e1]; simp only [Int.bmod]; split <;> omega

/-- `subw c, E` on a negative exponent word `-D`: `c + D`. -/
theorem nf_wsub_negw {c D : Nat} (h : c + D < 2 ^ 30) :
    BitVec.signExtend 64 ((Sail.BitVec.extractLsb (BitVec.ofNat 64 c) 31 0) -
      (Sail.BitVec.extractLsb (ew (-(D : Int))) 31 0)) = BitVec.ofNat 64 (c + D) := by
  rw [ew_def, ofInt_negNat D (by omega), wsub_neg (by omega) (by omega)]

/-- `slli 9; srli 12`: the fraction field of a working mantissa. -/
theorem nf_frac9 (a : Nat) : BitVec.ofNat 64 (a * 512) >>> 12 = BitVec.ofNat 64 (a % 2 ^ 55 / 8) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega
/-- `bgez (x << 7)`: bit 56 of `x` clear. -/
theorem nf_bit56_ge (a : Nat) : zopz0zKzJ_s (BitVec.ofNat 64 (a * 128)) 0#64 = decide (a % 2 ^ 57 < 2 ^ 56) := by
  rw [sge_int, BitVec.toInt_eq_toNat_cond]; simp; split <;> omega
theorem nf_bit56_lt (a : Nat) : zopz0zI_s (BitVec.ofNat 64 (a * 128)) 0#64 = decide (2 ^ 56 ≤ a % 2 ^ 57) := by
  rw [slt_int', BitVec.toInt_eq_toNat_cond]; simp; split <;> omega

theorem toNat_E (E a b : Nat) (h : a ≤ E + b) : ((E : Int) - a + b).toNat = E + b - a := by omega
theorem toNat_E0 (E a : Nat) (h : a ≤ E) : ((E : Int) - a).toNat = E - a := by omega
theorem toNat_E2 (E a b c : Nat) (h : a ≤ E + b + c) : ((E : Int) - a + b + c).toNat = E + b + c - a := by omega
/-- A biased exponent word back at its bias. -/
theorem ew_lin_d (D a : Nat) : ew (-(a : Int) - D + a) = ew (-(D : Int)) := by
  congr 1; omega
/-- Clearing bit 56 (`_FP_FRAC_CLEAR_OVERP`). -/
theorem nf_clr56 (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& 18374686479671623679#64 = BitVec.ofNat 64 (2 ^ 57 * (x / 2 ^ 57) + x % 2 ^ 56) := by
  have := land_clear x 56 64 (by decide) hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  rw [show (18374686479671623679 : Nat) % 2 ^ 64 = 2 ^ (56 + 1) * (2 ^ (64 - (56 + 1)) - 1) + (2 ^ 56 - 1) by decide,
    this]
  omega

/-- `_FP_FRAC_SRS (X, 1)` as the denormalisation at `E = 0` writes it
(`sll 63` for the sticky bit). -/
theorem nf_sticky63 (Y : Nat) :
    zopz0zI_u (BitVec.ofNat 64 0) (BitVec.ofNat 64 (Y * 9223372036854775808)) = decide (¬ Y % 2 = 0) := by
  have := nf_sticky (Y := Y) (d := 1) (by decide)
  simpa using this
/-- `_FP_FRAC_SRS (R, 1)` as the overflow renormalisation writes it. -/
theorem nf_srs1' (Y : Nat) (hY : Y < 2 ^ 64) :
    BitVec.ofNat 64 Y >>> 1 ||| BitVec.ofNat 64 (Y % 2) = BitVec.ofNat 64 (Lua.Num.SfRef.rto Y 1) := by
  rw [nf_shr 1 hY, nf_or_low _ _ (by omega), Lua.Num.SfRef.rto_one]
  congr 1; split <;> omega
theorem nf_srs1 {Y : Nat} {inst : Decidable (¬ Y % 2 = 0)} (hY0 : Y < 2 ^ 64) :
    BitVec.ofNat 64 (Y / 2) ||| BitVec.ofNat 64 (@ite _ (¬ Y % 2 = 0) inst 1 0) =
      BitVec.ofNat 64 (Lua.Num.SfRef.rto Y 1) := by
  have := nf_srs (Y := Y) (d := 1) (inst := inst) hY0
  simpa using this

/-- `umul_ppmm`'s low word: the middle sum's low half above the low
product's low half (`(mid << 32) + ((t << 32) >> 32)`). -/
theorem nf_lo64 (mid t : Nat) :
    BitVec.ofNat 64 (mid * 4294967296) + BitVec.ofNat 64 (t * 4294967296) >>> 32 =
      BitVec.ofNat 64 (mid % 4294967296 * 4294967296 + t % 4294967296) := by
  have e1 : mid * 4294967296 % 2 ^ 64 = mid % 4294967296 * 4294967296 := by
    rw [show (2 : Nat) ^ 64 = 4294967296 * 4294967296 by decide, Nat.mul_mod_mul_right]
  have e2 : t * 4294967296 % 2 ^ 64 / 4294967296 = t % 4294967296 := by
    rw [show (2 : Nat) ^ 64 = 4294967296 * 4294967296 by decide, Nat.mul_mod_mul_right,
      Nat.mul_div_cancel _ (by decide)]
  have h1 := Nat.mod_lt mid (show 4294967296 > 0 by decide)
  have h2 := Nat.mod_lt t (show 4294967296 > 0 by decide)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, e1, show (2 : Nat) ^ 32 = 4294967296 by decide, e2]

/-- `_FP_FRAC_SRS_2`'s sticky test on the low word (`lo << 9 != 0`). -/
theorem nf_sticky9 (Y : Nat) :
    zopz0zI_u (BitVec.ofNat 64 0) (BitVec.ofNat 64 (Y * 512)) = decide (¬ Y % 2 ^ 55 = 0) := by
  rw [ult_nat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_decide]
  omega
/-- `_FP_FRAC_SRS_2 (Z, 55, 112)` of the double word `A · 2^64 + L`: the high
word shifted left by 9, the low word's top 9 bits, the sticky bit. -/
theorem nf_umul_srs {A L : Nat} {inst : Decidable (¬ L % 2 ^ 55 = 0)} (hA : A < 2 ^ 55) (hL : L < 2 ^ 64) :
    BitVec.ofNat 64 (A * 512) ||| (BitVec.ofNat 64 (@ite _ (¬ L % 2 ^ 55 = 0) inst 1 0) |||
      BitVec.ofNat 64 (L / 36028797018963968)) =
      BitVec.ofNat 64 (Lua.Num.SfRef.rto (A * 2 ^ 64 + L) 55) := by
  have hl : L / 36028797018963968 < 512 := by omega
  have hB : ∀ b, b < 512 → A * 512 ||| b = A * 512 + b := fun b hb => or_add A b 9 hb
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : A * 512 < 2 ^ 64), Nat.mod_eq_of_lt (by omega : L / 36028797018963968 < 2 ^ 64)]
  by_cases h : L % 2 ^ 55 = 0
  · rw [Lua.Num.SfRef.rto_exact (by omega), if_neg (by simp [h])]
    simp only [Nat.zero_mod, Nat.zero_or]
    rw [hB _ hl, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [Lua.Num.SfRef.rto_jam (by omega), if_pos h, show (1 : Nat) % 2 ^ 64 = 1 by decide]
    have h1 : 1 ||| L / 36028797018963968 = 2 * (L / 36028797018963968 / 2) + 1 := by
      rw [Nat.or_comm, lor_low _ 1 (by decide), if_neg (by decide)]
    rw [h1, hB _ (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The exponent-word and mantissa-word steps `sf_nf` does not know. -/
macro "sm_own" : tactic => `(tactic| (
  try simp only [Lua.Vm.Fn.MulLens.nf_ew_addc]
  try simp only [Lua.Vm.Fn.MulLens.ew_lin_d]
  try simp (disch := omega) only [Lua.Vm.Fn.MulLens.nf_ew_nn]
  try simp (disch := omega) only [Lua.Vm.Fn.MulLens.toNat_E, Lua.Vm.Fn.MulLens.toNat_E0, Lua.Vm.Fn.MulLens.toNat_E2]
  try simp only [Lua.Vm.Fn.MulLens.nf_sticky63, Lua.Vm.Fn.MulLens.nf_lo64, decide_eq_true_eq]
  try simp only [Lua.Vm.Fn.MulLens.nf_sticky9, decide_eq_true_eq]
  try simp (disch := omega) only [Lua.Vm.Fn.MulLens.nf_srs1, Lua.Vm.Fn.MulLens.nf_umul_srs]
  try simp only [BitVec.ofNat_eq_ofNat]
  try simp (disch := omega) only [Lua.Vm.Fn.MulLens.nf_srs1', Lua.Vm.Fn.SfLens.nf_and1]
  try simp (disch := omega) only [Lua.Vm.Fn.MulLens.nf_wsub_negw, Lua.Vm.Fn.MulLens.nf_clr56,
    Lua.Vm.Fn.MulLens.nf_slt_m55, Lua.Vm.Fn.MulLens.nf_sge0_neg, Lua.Vm.Fn.MulLens.nf_beq0_neg]
  try simp only [Lua.Vm.Fn.MulLens.nf_frac9, Lua.Vm.Fn.MulLens.nf_bit56_ge, Lua.Vm.Fn.MulLens.nf_bit56_lt,
    decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true]
  try simp (disch := omega) only [if_pos, if_neg]))

macro "sm_nf" : tactic => `(tactic| (
  try simp only [sll_lit, srl_lit, sext_eq, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat]
  sm_own
  sf_nf
  sm_own
  sf_nf))

macro "sm_go" "[" cuts:ident,* "]" : tactic => `(tactic| (
  sm_nf; repeat' (first | (unfold_node [$cuts,*]; sm_nf) | (split <;> (try (exfalso; omega))))))

open Lean Elab Command in
/-- `local irreducible` for every node `N_<pc>` of the namespace `ns` (a node
unfolded by unification evaluates the machine's guards on the chamber's atoms,
past `maxRecDepth`; `unfold_node` unfolds by the equation lemmas). -/
elab "irreducible_nodes " ns:ident : command => do
  let env ← getEnv
  let pre := ns.getId
  let mut ids : Array Ident := #[]
  for n in env.constants.map₁.keys do
    if n.getPrefix == pre && (n.getString!.startsWith "N_") then ids := ids.push (mkIdent n)
  if ids.isEmpty then throwError "irreducible_nodes: no node in {pre}"
  elabCommand (← `(attribute [local irreducible] $ids*))

/-- Close a pack leaf against `SfRef.roundPack`: the leaf's pack word, the
reference's rounding and pack unfolded, the cases the path's facts leave. -/
macro "sm_close" "[" packs:ident,* "]" : tactic => `(tactic| (
  try simp (disch := omega) only [$[$packs:ident],*]
  try simp only [Lua.Num.SfRef.roundPack, Lua.Num.SfRef.rne3]
  repeat' split
  all_goals (try simp only [Lua.Vm.Fn.SfLens.infty_nf, Lua.Vm.Fn.SfLens.bits_nf, decide_eq_true_eq] at *)
  all_goals (repeat' split)
  all_goals (first | (exfalso; omega) | (refine congrArg (BitVec.ofNat 64) ?_; omega))))

end Lua.Vm.Fn.MulLens

namespace Lua.Vm.Fn.Muldf3
open Lua.Vm.Fn.MulLens Lua.Num

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- The pack leaf (`_FP_PACK_RAW_D`). -/
theorem nf_e77c (s : Nat) (r : BitVec 64) {F E S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002e77c s r (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002e77c; exact pack_eq hE hF hS

-- the reference's packs stay folded while the machine's DAG is explored (a
-- unification against `BitVec.ofNat` would evaluate them)
attribute [local irreducible] SfRef.roundPack SfRef.rto
irreducible_nodes Lua.Vm.Fn.Muldf3

/-! ## The pack stage (`_FP_PACK_CANONICAL`): round, carry, overflow, denormalise -/

/-- From the denormalisation's entry (`0x8002e8ec`) at biased exponent `0`. -/
theorem g_e8ec0 (s : Nat) (r : BitVec 64) {R S : Nat} (hS : S < 2) (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e8ec s r (ew (-((0 : Nat) : Int))) (BitVec.ofNat 64 R) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R 1) := by
  have hF : SfRef.rto R 1 < 2 ^ 55 := SfRef.rto_lt (by decide) (by simpa using hR2)
  sm_go []
  all_goals sm_close [nf_e77c]

/-- From the denormalisation's entry (`0x8002e8ec`) at biased exponent `-D < 0`. -/
theorem g_e8ec1 (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD0 : 1 ≤ D) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e8ec s r (ew (-(D : Int))) (BitVec.ofNat 64 R) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  have hF : SfRef.rto R (1 + D) < 2 ^ 55 :=
    SfRef.rto_lt (by decide) (Nat.lt_of_lt_of_le hR2 (Nat.pow_le_pow_right (by decide) (by omega)))
  have hF1 : D ≤ 55 ∨ SfRef.rto R (1 + D) = 1 := by
    by_cases h : D ≤ 55
    · exact Or.inl h
    · exact Or.inr (SfRef.rto_big (by omega)
        (Nat.lt_of_lt_of_le hR2 (Nat.pow_le_pow_right (by decide) (by omega))))
  sm_go []
  all_goals sm_close [nf_e77c]

theorem g_e8ec (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e8ec s r (ew (-(D : Int))) (BitVec.ofNat 64 R) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD0
  · exact g_e8ec0 s r hS hR1 hR2
  · exact g_e8ec1 s r hS hD0 hD hR1 hR2

/-- The no-overflow entry (`0x8002e660`) at a biased exponent `E ≥ 1`. -/
theorem g_e660_n (s : Nat) (r : BitVec 64) {R E S : Nat} (hS : S < 2) (hE1 : 1 ≤ E) (hE : E ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e660 s r (BitVec.ofNat 64 R) (ew ((E : Int) - ((1023 : Nat) : Int))) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E R := by
  sm_go []
  all_goals sm_close [nf_e77c]

/-- The no-overflow entry (`0x8002e660`) at a biased exponent `-D ≤ 0`. -/
theorem g_e660_d (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e660 s r (BitVec.ofNat 64 R) (ew (-((1023 : Nat) : Int) - (D : Int))) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  sm_go [N_8002e8ec]
  all_goals rw [g_e8ec s r hS hD hR1 hR2]

/-- The overflow entry (`0x8002e7a4`, after the extra sticky shift) at a biased exponent `E ≥ 1`. -/
theorem g_e7a4_n (s : Nat) (r : BitVec 64) {R E S : Nat} (hS : S < 2) (hE1 : 1 ≤ E) (hE : E ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e7a4 s r (BitVec.ofNat 64 R) (ew ((E : Int) - ((1024 : Nat) : Int))) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E R := by
  sm_go []
  all_goals sm_close [nf_e77c]

theorem g_e7a4_d (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e7a4 s r (BitVec.ofNat 64 R) (ew (-((1024 : Nat) : Int) - (D : Int))) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  sm_go [N_8002e8ec]
  all_goals rw [g_e8ec s r hS hD hR1 hR2]

/-- The no-overflow entry is `_FP_PACK_CANONICAL` (`SfRef.packCanon`). -/
theorem g_e660 (s : Nat) (r : BitVec 64) {R S : Nat} (e : Int) (hS : S < 2) (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e660 s r (BitVec.ofNat 64 R) (ew e) (BitVec.ofNat 64 S) = SfRef.packCanon (S = 1) e R := by
  unfold SfRef.packCanon
  by_cases h : 0 < e + 1023
  · obtain ⟨E, rfl⟩ : ∃ E : Nat, e = (E : Int) - ((1023 : Nat) : Int) := ⟨(e + 1023).toNat, by omega⟩
    rw [if_pos h, g_e660_n s r hS (by omega) (by omega) hR1 hR2]
    congr 1; omega
  · obtain ⟨D, rfl⟩ : ∃ D : Nat, e = -((1023 : Nat) : Int) - (D : Int) := ⟨(-(e + 1023)).toNat, by omega⟩
    rw [if_neg h, g_e660_d s r hS (by omega) hR1 hR2]
    congr 2; omega

/-- The overflow entry is `_FP_PACK_CANONICAL` one exponent up. -/
theorem g_e7a4 (s : Nat) (r : BitVec 64) {R S : Nat} (e : Int) (hS : S < 2) (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e7a4 s r (BitVec.ofNat 64 R) (ew e) (BitVec.ofNat 64 S) = SfRef.packCanon (S = 1) (e + 1) R := by
  unfold SfRef.packCanon
  by_cases h : 0 < e + 1 + 1023
  · obtain ⟨E, rfl⟩ : ∃ E : Nat, e = (E : Int) - ((1024 : Nat) : Int) := ⟨(e + 1024).toNat, by omega⟩
    rw [if_pos h, g_e7a4_n s r hS (by omega) (by omega) hR1 hR2]
    congr 1; omega
  · obtain ⟨D, rfl⟩ : ∃ D : Nat, e = -((1024 : Nat) : Int) - (D : Int) := ⟨(-(e + 1024)).toNat, by omega⟩
    rw [if_neg h, g_e7a4_d s r hS (by omega) hR1 hR2]
    congr 2; omega

end Lua.Vm.Fn.Muldf3

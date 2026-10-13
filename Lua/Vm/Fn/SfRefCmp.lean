import Lua.Vm.Fn.SfLens
import Lua.Vm.Fn.Spec
import Lua.Num.SfRefCmp

/-!
# `__eqdf2`, `__ledf2`, `__gedf2` against `SfRef` (lane float-sf2, (b1))

The comparison routines' lifted functions (`Lua/Vm/Fn/{Eqdf2,Ledf2,Gedf2}`,
generated, equal to the machine by level (a)) are the soft-fp-shaped
references `SfRef.cmpFields`/`SfRef.eqFields` (`Lua/Num/SfRefCmp.lean`) over
the operands' fields; with (b2) (`SfRef.cmp_eq`, `SfRef.eqv_eq`) each
`SoftFloatSpec` field is a theorem (`<R>.spec_proved`).

The route is B-SFREF's, with its statement cost generated: the **chamber
generator** `sfc_chambers F r [refs]` emits, for a two-operand routine `F`
and its reference `r` over the fields, the eleven chamber lemmas (a NaN
operand; zero operands by the other's sign; both nonzero by both signs), the
cover `G_eq` and `F_eq_ref`. A chamber (`sfc_chamber`) unpacks the operands
(`P`, `argA_P`/`argE_P`/`argF_P`), decides the reference's branches under the
chamber's facts once, explores the DAG (`sfc_go`, over the `Nat` lens of
`SfLens` plus the comparison guards here) and closes each leaf, a closed
word, by `decide`. No rounding is involved.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens

namespace Lua.Vm.Fn.SfCmpLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

theorem uge_nat (x y : BitVec 64) : zopz0zKzJ_u x y = decide (x.toNat ≥ y.toNat) := by
  unfold zopz0zKzJ_u; simp [BitVec.toNatInt]
theorem nf_uge {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  rw [uge_nat]; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem beq_or0 (x y : BitVec 64) : (x ||| y == BitVec.ofNat 64 0) = (x == BitVec.ofNat 64 0 && y == BitVec.ofNat 64 0) := by
  have h1 : ∀ z : BitVec 64, (z == BitVec.ofNat 64 0) = decide (z.toNat = 0) := fun z => by
    rw [beq_toNat]; simp
  rw [h1, h1, h1, BitVec.toNat_or]; simp only [Nat.or_eq_zero_iff, Bool.decide_and]
theorem bne_or0 (x y : BitVec 64) : (x ||| y != BitVec.ofNat 64 0) = (x != BitVec.ofNat 64 0 || y != BitVec.ofNat 64 0) := by
  simp only [bne, beq_or0, Bool.not_and]
/-- `sltu` against zero of or-ed words (`_FP_CMP_EQ`'s "not both zero"). -/
theorem ult0_or (x y : BitVec 64) : zopz0zI_u (BitVec.ofNat 64 0) (x ||| y) = (x != BitVec.ofNat 64 0 || y != BitVec.ofNat 64 0) := by
  rw [ult_nat, ← bne_or0, bne, beq_toNat]
  have e : (BitVec.ofNat 64 0 : BitVec 64).toNat = 0 := rfl
  rw [e]
  by_cases h : (x ||| y).toNat = 0
  · rw [h]; rfl
  · rw [decide_eq_true (Nat.pos_of_ne_zero h), decide_eq_false h]; rfl
theorem nf_beq_c {x c : Nat} (hx : x < 2 ^ 63) (hc : 2 ^ 63 ≤ c) (hc2 : c < 2 ^ 64) :
    (BitVec.ofNat 64 (x + c) == BitVec.ofNat 64 0) = decide (x = 2 ^ 64 - c) := by
  rw [beq_toNat]; simp; omega
theorem nf_bne_c {x c : Nat} (hx : x < 2 ^ 63) (hc : 2 ^ 63 ≤ c) (hc2 : c < 2 ^ 64) :
    (BitVec.ofNat 64 (x + c) != BitVec.ofNat 64 0) = !decide (x = 2 ^ 64 - c) := by
  simp only [bne, nf_beq_c hx hc hc2]

/-- The comparison routines' normal form: the literal and `ofNat` steps of
`sf_nf`, the comparison guards (fields or-ed against zero, `e - 2047`
against zero, unsigned `≥`), then the guards decided by `omega`. `sf_nf`
itself is not used: its `nf_mod_lit` (discharged by `omega`) loops inside a
branch whose condition contradicts the path's facts (`maxRecDepth`), which
an undecided guard leaves in the goal. -/
macro "sfc_nf" : tactic => `(tactic| (
  try simp only [Lua.Vm.Fn.SfLens.sll_lit, Lua.Vm.Fn.SfLens.srl_lit, Lua.Vm.Fn.SfLens.sext_eq,
    BitVec.reduceSignExtend, BitVec.reduceToNat, BitVec.reduceAdd, BitVec.add_zero, BitVec.zero_add,
    Lua.Vm.Fn.SfLens.nf_zext_bool, Bool.false_eq_true, ite_true, ite_false]
  try simp only [BitVec.ofNat_eq_ofNat]
  try simp only [Lua.Vm.Fn.SfLens.nf_add]
  try simp only [Lua.Vm.Fn.SfCmpLens.beq_or0, Lua.Vm.Fn.SfCmpLens.bne_or0, Lua.Vm.Fn.SfCmpLens.ult0_or,
    BitVec.reduceOr]
  try simp (disch := omega) only [Lua.Vm.Fn.SfCmpLens.nf_beq_c, Lua.Vm.Fn.SfCmpLens.nf_bne_c,
    Lua.Vm.Fn.SfCmpLens.nf_uge, Lua.Vm.Fn.SfLens.nf_beq, Lua.Vm.Fn.SfLens.nf_bne, Lua.Vm.Fn.SfLens.nf_ult,
    Lua.Vm.Fn.SfLens.nf_slt, Lua.Vm.Fn.SfLens.nf_sge]
  try simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true',
    Bool.not_eq_true, Bool.not_eq_false', Bool.not_true, Bool.not_false, Bool.not_not, decide_true,
    decide_false, Bool.false_eq_true, and_self, and_true, true_and, and_false, false_and, not_true_eq_false,
    not_false_eq_true, ite_true, ite_false, ↓reduceIte, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd,
    Nat.reduceMul]
  try simp (disch := omega) only [if_pos, if_neg]
  try simp only [ite_true, ite_false, ↓reduceIte]))

/-- `sf_go` with `sfc_nf`. -/
macro "sfc_go" : tactic => `(tactic| (
  sfc_nf
  repeat' (first
    | (unfold_node []; sfc_nf)
    | (split <;> (try (exfalso; omega))))))

/-- An operand packed from its fields (`_FP_PACK_RAW_D`). -/
abbrev P (s e f : Nat) : BitVec 64 := BitVec.ofNat 64 (s * 2 ^ 63 + e * 2 ^ 52 + f)

theorem P_toNat {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    (P s e f).toNat = s * 2 ^ 63 + e * 2 ^ 52 + f := by
  unfold P; rw [BitVec.toNat_ofNat]; omega
theorem argA_P {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    shift_bits_right (P s e f) (Sail.BitVec.extractLsb (0x3f#6) 5 0) = BitVec.ofNat 64 s := by
  rw [argA, P_toNat hs he hf]; congr 1; omega
theorem argE_P {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    (shift_bits_right (P s e f) (Sail.BitVec.extractLsb (0x34#6) 5 0) &&& sign_extend (m := 64) (0x7ff#12)) =
      BitVec.ofNat 64 e := by
  rw [argE, P_toNat hs he hf]; congr 1; omega
theorem argF_P {s e f : Nat} (hs : s < 2) (he : e < 2048) (hf : f < 2 ^ 52) :
    (shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0) &&& P s e f) =
      BitVec.ofNat 64 f := by
  rw [argF, P_toNat hs he hf]; congr 1; omega

/-- Every word is the pack of its fields. -/
theorem P_fields (a : BitVec 64) : a = P (a.toNat / 2 ^ 63) (a.toNat / 2 ^ 52 % 2048) (a.toNat % 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq; unfold P; rw [BitVec.toNat_ofNat]; have := a.isLt; omega

/-- Close a leaf: the routine's return node unfolded, the reference's
branches decided by the path's facts, the two words compared. -/
macro "sfc_close" "[" refs:ident,* "]" : tactic => `(tactic| (
  unfold_lhs
  sfc_nf
  simp only [$[$refs:ident],*]
  try simp only [decide_eq_true_eq, ne_eq, decide_eq_decide]
  repeat (simp (disch := omega) only [if_pos, if_neg])
  decide))

/-- One chamber of a two-operand comparison routine: the operands' fields
unpacked, the reference's branches decided by the chamber's facts once, the
DAG explored (`sfc_go`), each leaf a closed word (`decide`). -/
macro "sfc_chamber" f:ident "[" refs:ident,* "]" : tactic => `(tactic| (
  unfold $f:ident
  simp (disch := omega) only [Lua.Vm.Fn.SfCmpLens.argA_P, Lua.Vm.Fn.SfCmpLens.argE_P, Lua.Vm.Fn.SfCmpLens.argF_P]
  simp only [$[$refs:ident],*, decide_eq_true_eq, Nat.zero_ne_one, Nat.one_ne_zero, decide_false, decide_true,
    Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, ne_eq, not_true_eq_false, not_false_eq_true,
    decide_eq_decide, and_true, true_and, and_false, false_and, or_false, false_or, true_or, or_true]
  try simp (disch := omega) only [if_pos, if_neg]
  sfc_go
  all_goals (unfold_lhs; (try sfc_nf); decide)))

open Lean in
/-- **The chamber generator** of the comparison routines (the abstraction
both round-5 winners named, for the comparison family): for the lifted
routine `F` (two `double` operands) and its reference `r` over the operands'
fields, it emits the chamber lemmas (`ch_na`, `ch_nb`: a NaN operand;
`ch_zz`, `ch_z<s>`, `ch_<s>z`: zero operands, by the other's sign; `ch_<s><t>`:
both nonzero, by both signs), the cover `G_eq` (the case split over the
chambers) and `F_eq_ref : F a b = r (fields a) (fields b)`. `refs` are the
reference's definitions to unfold. -/
macro "sfc_chambers " f:ident r:term:max " [" refs:ident,* "]" : command => do
  let id (s : String) : Ident := mkIdent (Name.mkSimple s)
  let lit (n : Nat) : TSyntax `term := Syntax.mkNumLit (toString n)
  let mut cmds : Array (TSyntax `command) := #[]
  let P := mkIdent `Lua.Vm.Fn.SfCmpLens.P
  let stmt ← `(term| $f ($P sa ea fa) ($P sb eb fb) = $r sa ea fa sb eb fb)
  -- a NaN operand
  cmds := cmds.push (← `(command|
    theorem $(id "ch_na") (sa ea fa sb eb fb : Nat) (hsa : sa < 2) (hfa : fa < 2 ^ 52) (hsb : sb < 2)
        (heb : eb < 2048) (hfb : fb < 2 ^ 52) (he : ea = 2047) (hfa0 : fa ≠ 0) : $stmt := by
      subst he; sfc_chamber $f [$refs,*]))
  cmds := cmds.push (← `(command|
    theorem $(id "ch_nb") (sa ea fa sb eb fb : Nat) (hsa : sa < 2) (hea : ea < 2048) (hfa : fa < 2 ^ 52)
        (hsb : sb < 2) (hfb : fb < 2 ^ 52) (hna : ¬ (ea = 2047 ∧ fa ≠ 0)) (he : eb = 2047) (hfb0 : fb ≠ 0) :
        $stmt := by
      subst he; sfc_chamber $f [$refs,*]))
  -- zero operands
  cmds := cmds.push (← `(command|
    theorem $(id "ch_zz") (sa ea fa sb eb fb : Nat) (hsa : sa < 2) (hsb : sb < 2)
        (h1 : ea = 0) (h2 : fa = 0) (h3 : eb = 0) (h4 : fb = 0) : $stmt := by
      subst h1 h2 h3 h4; sfc_chamber $f [$refs,*]))
  for t in [0, 1] do
    cmds := cmds.push (← `(command|
      theorem $(id s!"ch_z{t}") (sa ea fa sb eb fb : Nat) (hsa : sa < 2) (heb : eb < 2048) (hfb : fb < 2 ^ 52)
          (hnb : ¬ (eb = 2047 ∧ fb ≠ 0)) (hzb : ¬ (eb = 0 ∧ fb = 0)) (h1 : ea = 0) (h2 : fa = 0)
          (h3 : sb = $(lit t)) : $stmt := by
        subst h1 h2 h3; sfc_chamber $f [$refs,*]))
    cmds := cmds.push (← `(command|
      theorem $(id s!"ch_{t}z") (sa ea fa sb eb fb : Nat) (hsb : sb < 2) (hea : ea < 2048) (hfa : fa < 2 ^ 52)
          (hna : ¬ (ea = 2047 ∧ fa ≠ 0)) (hza : ¬ (ea = 0 ∧ fa = 0)) (h1 : eb = 0) (h2 : fb = 0)
          (h3 : sa = $(lit t)) : $stmt := by
        subst h1 h2 h3; sfc_chamber $f [$refs,*]))
  -- both nonzero, by both signs
  for u in [0, 1] do
    for t in [0, 1] do
      cmds := cmds.push (← `(command|
        theorem $(id s!"ch_{u}{t}") (sa ea fa sb eb fb : Nat) (hea : ea < 2048) (hfa : fa < 2 ^ 52)
            (heb : eb < 2048) (hfb : fb < 2 ^ 52)
            (hna : ¬ (ea = 2047 ∧ fa ≠ 0)) (hnb : ¬ (eb = 2047 ∧ fb ≠ 0))
            (hza : ¬ (ea = 0 ∧ fa = 0)) (hzb : ¬ (eb = 0 ∧ fb = 0)) (h1 : sa = $(lit u)) (h2 : sb = $(lit t)) :
            $stmt := by
          subst h1 h2; sfc_chamber $f [$refs,*]))
  -- the cover
  cmds := cmds.push (← `(command|
    theorem $(id "G_eq") (sa ea fa sb eb fb : Nat) (hsa : sa < 2) (hea : ea < 2048) (hfa : fa < 2 ^ 52)
        (hsb : sb < 2) (heb : eb < 2048) (hfb : fb < 2 ^ 52) : $stmt := by
      by_cases hna : ea = 2047 ∧ fa ≠ 0
      · exact $(id "ch_na") sa ea fa sb eb fb hsa hfa hsb heb hfb hna.1 hna.2
      by_cases hnb : eb = 2047 ∧ fb ≠ 0
      · exact $(id "ch_nb") sa ea fa sb eb fb hsa hea hfa hsb hfb hna hnb.1 hnb.2
      by_cases hza : ea = 0 ∧ fa = 0
      · by_cases hzb : eb = 0 ∧ fb = 0
        · exact $(id "ch_zz") sa ea fa sb eb fb hsa hsb hza.1 hza.2 hzb.1 hzb.2
        · by_cases hs : sb = 0
          · exact $(id "ch_z0") sa ea fa sb eb fb hsa heb hfb hnb hzb hza.1 hza.2 hs
          · exact $(id "ch_z1") sa ea fa sb eb fb hsa heb hfb hnb hzb hza.1 hza.2 (by omega)
      · by_cases hzb : eb = 0 ∧ fb = 0
        · by_cases hs : sa = 0
          · exact $(id "ch_0z") sa ea fa sb eb fb hsb hea hfa hna hza hzb.1 hzb.2 hs
          · exact $(id "ch_1z") sa ea fa sb eb fb hsb hea hfa hna hza hzb.1 hzb.2 (by omega)
        · by_cases hs : sa = 0 <;> by_cases ht : sb = 0
          · exact $(id "ch_00") sa ea fa sb eb fb hea hfa heb hfb hna hnb hza hzb hs ht
          · exact $(id "ch_01") sa ea fa sb eb fb hea hfa heb hfb hna hnb hza hzb hs (by omega)
          · exact $(id "ch_10") sa ea fa sb eb fb hea hfa heb hfb hna hnb hza hzb (by omega) ht
          · exact $(id "ch_11") sa ea fa sb eb fb hea hfa heb hfb hna hnb hza hzb (by omega) (by omega)))
  -- the routine on words
  cmds := cmds.push (← `(command|
    theorem $(id "F_eq_ref") (a b : BitVec 64) :
        $f a b = $r (a.toNat / 2 ^ 63) (a.toNat / 2 ^ 52 % 2048) (a.toNat % 2 ^ 52)
          (b.toNat / 2 ^ 63) (b.toNat / 2 ^ 52 % 2048) (b.toNat % 2 ^ 52) := by
      have ha := a.isLt
      have hb := b.isLt
      conv => lhs; rw [Lua.Vm.Fn.SfCmpLens.P_fields a, Lua.Vm.Fn.SfCmpLens.P_fields b]
      exact $(id "G_eq") _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)))
  return ⟨mkNullNode cmds⟩

end Lua.Vm.Fn.SfCmpLens

namespace Lua.Vm.Fn.SfCmpLens
open Lua.Num

theorem sign_fields (a : BitVec 64) : F64.sign a = decide (a.toNat / 2 ^ 63 = 1) := by
  unfold F64.sign
  have := a.isLt
  by_cases h : 2 ^ 63 ≤ a.toNat
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

/-- The reference over a word's fields is `SfRef.cmp`. -/
theorem cmp_fields (un : Int) (a b : BitVec 64) :
    SfRef.cmpFields un (decide (a.toNat / 2 ^ 63 = 1)) (a.toNat / 2 ^ 52 % 2048) (a.toNat % 2 ^ 52)
      (decide (b.toNat / 2 ^ 63 = 1)) (b.toNat / 2 ^ 52 % 2048) (b.toNat % 2 ^ 52) = SfRef.cmp un a b := by
  rw [SfRef.cmp, sign_fields, sign_fields]; rfl
theorem eqv_fields (a b : BitVec 64) :
    SfRef.eqFields (decide (a.toNat / 2 ^ 63 = 1)) (a.toNat / 2 ^ 52 % 2048) (a.toNat % 2 ^ 52)
      (decide (b.toNat / 2 ^ 63 = 1)) (b.toNat / 2 ^ 52 % 2048) (b.toNat % 2 ^ 52) = SfRef.eqv a b := by
  rw [SfRef.eqv, sign_fields, sign_fields]; rfl

end Lua.Vm.Fn.SfCmpLens

namespace Lua.Vm.Fn.Ledf2
open Lua.Vm.Fn.SfCmpLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Lua.Num in
sfc_chambers F (fun sa ea fa sb eb fb => BitVec.ofInt 64 (SfRef.cmpFields 2 (decide (sa = 1)) ea fa (decide (sb = 1)) eb fb)) [SfRef.cmpFields]

open Lua.Num in
/-- **`SoftFloatSpec.ledf2`, proved**: (b1) `F_eq_ref` (the chambers) then
(b2) `SfRef.cmp_eq`. -/
theorem spec_proved (a b : BitVec 64) : F a b = S a b := by
  rw [F_eq_ref]; dsimp only; rw [Lua.Vm.Fn.SfCmpLens.cmp_fields, SfRef.cmp_eq]
  unfold S
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

end Lua.Vm.Fn.Ledf2

namespace Lua.Vm.Fn.Gedf2
open Lua.Vm.Fn.SfCmpLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Lua.Num in
sfc_chambers F (fun sa ea fa sb eb fb =>
  BitVec.ofInt 64 (SfRef.cmpFields (-2) (decide (sa = 1)) ea fa (decide (sb = 1)) eb fb)) [SfRef.cmpFields]

open Lua.Num in
/-- **`SoftFloatSpec.gedf2`, proved**. -/
theorem spec_proved (a b : BitVec 64) : F a b = S a b := by
  rw [F_eq_ref]; dsimp only; rw [Lua.Vm.Fn.SfCmpLens.cmp_fields, SfRef.cmp_eq]
  unfold S
  generalize F64.compare a b = o
  rcases o with _ | (_ | _ | _) <;> decide

end Lua.Vm.Fn.Gedf2

namespace Lua.Vm.Fn.Eqdf2
open Lua.Vm.Fn.SfCmpLens
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

open Lua.Num in
sfc_chambers F (fun sa ea fa sb eb fb =>
  BitVec.ofInt 64 (SfRef.eqFields (decide (sa = 1)) ea fa (decide (sb = 1)) eb fb)) [SfRef.eqFields]

open Lua.Num in
/-- **`SoftFloatSpec.eqdf2`, proved**. -/
theorem spec_proved (a b : BitVec 64) : F a b = S a b := by
  rw [F_eq_ref]; dsimp only; rw [Lua.Vm.Fn.SfCmpLens.eqv_fields, SfRef.eqv_eq]
  unfold S
  cases F64.eq a b <;> decide

end Lua.Vm.Fn.Eqdf2

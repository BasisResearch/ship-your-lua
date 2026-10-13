import Lua.Vm.Sim.Kit.Fn
import Lua.Vm.Sim.Kit.Clzdi2
import Lua.Num.SfRef

/-!
# The `Nat` lens on the lifted soft-float routines (round 5, B-SFREF (b1))

The lifted functions of `__adddf3`/`__subdf3` (`Lua/Vm/Fn/{Adddf3,Subdf3}`)
are `BitVec 64` DAGs. Level (b1) relates them to `SfRef` (`Lua/Num/SfRef.lean`)
by chambers; inside a chamber the DAG is *explored*:

* `unfold_lhs` unfolds the node at the head of the goal's left side;
* a guard is split (`split`), its hypothesis normalised to `Nat`/`Int`
  arithmetic by `sf_hyp` (the lens lemmas below), and a side the chamber's
  facts refute is closed by `omega`.

The lens lemmas turn the machine's words into `Nat`: guards (`==`, `!=`,
signed and unsigned compares) into `decide` over `toNat`/`toInt`, literal
shifts and masks into `/`, `*`, `%` by constants, and the soft-fp idioms
into named functions: the sticky shift (`srs_toNat`: `SfRef.rto`) and the
packs of sign, exponent and fraction (`pack_eq`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.SfLens

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
open Lean Elab Tactic Meta

/-- Unfold the head constant of the goal's left-hand side once. -/
elab "unfold_lhs" : tactic => do
  let g ← getMainTarget
  let some (_, lhs, _) := g.eq? | throwError "unfold_lhs: not an equation"
  let .const n _ := lhs.getAppFn | throwError "unfold_lhs: the left side's head is not a constant"
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))

theorem beq_toNat {x y : BitVec 64} : (x == y) = decide (x.toNat = y.toNat) := by
  by_cases h : x = y
  · subst h; simp
  · have : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    simp [h, this]
theorem bne_toNat {x y : BitVec 64} : (x != y) = !decide (x.toNat = y.toNat) := by
  simp [bne, beq_toNat]
theorem sll_lit (x : BitVec 64) (k : BitVec 6) :
    shift_bits_left x (Sail.BitVec.extractLsb k 5 0) = x <<< k.toNat := by
  simp [shift_bits_left, Sail.BitVec.extractLsb, BitVec.shiftLeft_eq', BitVec.extractLsb, BitVec.extractLsb']
theorem srl_lit (x : BitVec 64) (k : BitVec 6) :
    shift_bits_right x (Sail.BitVec.extractLsb k 5 0) = x >>> k.toNat := by
  simp [shift_bits_right, Sail.BitVec.extractLsb, BitVec.ushiftRight_eq', BitVec.extractLsb, BitVec.extractLsb']
theorem sext_eq {n} (x : BitVec n) : sign_extend (m := 64) x = x.signExtend 64 := rfl
theorem sge_int (x y : BitVec 64) : zopz0zKzJ_s x y = decide (x.toInt ≥ y.toInt) := by
  unfold zopz0zKzJ_s; simp
theorem slt_int' (x y : BitVec 64) : zopz0zI_s x y = decide (x.toInt < y.toInt) := by
  unfold zopz0zI_s; simp
theorem ult_nat (x y : BitVec 64) : zopz0zI_u x y = decide (x.toNat < y.toNat) := by
  unfold zopz0zI_u; simp [BitVec.toNatInt]
theorem land7 (x : Nat) : x &&& 7 = x % 8 := Nat.and_two_pow_sub_one_eq_mod x 3
theorem land15 (x : Nat) : x &&& 15 = x % 16 := Nat.and_two_pow_sub_one_eq_mod x 4
theorem land2047 (x : Nat) : x &&& 2047 = x % 2048 := Nat.and_two_pow_sub_one_eq_mod x 11
theorem land52 (x : Nat) : x &&& 4503599627370495 = x % 2 ^ 52 := Nat.and_two_pow_sub_one_eq_mod x 52

theorem toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  simp [Nat.mod_eq_of_lt h]

theorem toInt_ofInt_small {i : Int} (h1 : -2 ^ 63 ≤ i) (h2 : i < 2 ^ 63) : (BitVec.ofInt 64 i).toInt = i := by
  rw [BitVec.toInt_ofInt]; simp only [Int.bmod]; split <;> omega

/-! ## The unpacked operands -/

/-- An operand's fields, as `Nat`. -/
structure Fields (a : BitVec 64) (s e f : Nat) : Prop where
  s : a.toNat / 2 ^ 63 = s
  e : a.toNat / 2 ^ 52 % 2048 = e
  f : a.toNat % 2 ^ 52 = f

theorem fields (a : BitVec 64) : Fields a (a.toNat / 2 ^ 63) (a.toNat / 2 ^ 52 % 2048) (a.toNat % 2 ^ 52) :=
  ⟨rfl, rfl, rfl⟩

/-! ## Unpacking -/

theorem argA (a : BitVec 64) :
    shift_bits_right a (Sail.BitVec.extractLsb (0x3f#6) 5 0) = BitVec.ofNat 64 (a.toNat / 2 ^ 63) := by
  rw [srl_lit]; apply BitVec.eq_of_toNat_eq; simp; omega

theorem argE (a : BitVec 64) :
    (shift_bits_right a (Sail.BitVec.extractLsb (0x34#6) 5 0) &&& sign_extend (m := 64) (0x7ff#12)) =
      BitVec.ofNat 64 (a.toNat / 2 ^ 52 % 2048) := by
  rw [srl_lit, sext_eq]; apply BitVec.eq_of_toNat_eq; simp [land2047]; omega

theorem argF (a : BitVec 64) :
    (shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0) &&& a) =
      BitVec.ofNat 64 (a.toNat % 2 ^ 52) := by
  rw [srl_lit, sext_eq]; apply BitVec.eq_of_toNat_eq; simp
  rw [Nat.and_comm, land52]; omega

theorem argX (a : BitVec 64) :
    shift_bits_left (shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0) &&& a)
      (Sail.BitVec.extractLsb (0x03#6) 5 0) = BitVec.ofNat 64 (8 * (a.toNat % 2 ^ 52)) := by
  rw [argF, sll_lit]; apply BitVec.eq_of_toNat_eq; simp; omega

theorem argM :
    shift_bits_right ((0#64) + sign_extend (m := 64) (0xfff#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0) =
      BitVec.ofNat 64 (2 ^ 52 - 1) := by
  rw [srl_lit, sext_eq]; decide

theorem wsub_ofNat (x y : Nat) (hx : x < 2 ^ 31) (hy : y < 2 ^ 31) :
    sign_extend (m := 64) ((Sail.BitVec.extractLsb (BitVec.ofNat 64 x) 31 0) -
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 y) 31 0)) = BitVec.ofInt 64 ((x : Int) - y) := by
  rw [sext_eq]
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofInt_small (by omega) (by omega)]
  rw [BitVec.toInt_signExtend_of_le (by decide)]
  simp only [Sail.BitVec.extractLsb, BitVec.toInt_sub, BitVec.extractLsb_ofNat, BitVec.toInt_ofNat]
  simp only [Nat.shiftRight_zero, BitVec.toInt_eq_toNat_bmod, BitVec.toNat_ofNat, Nat.reduceSub, Nat.reduceAdd]
  have e1 : x % 2 ^ 64 % 2 ^ 32 = x := by omega
  have e2 : y % 2 ^ 64 % 2 ^ 32 = y := by omega
  rw [e1, e2]
  have h1 : ((x : Nat) : Int).bmod (2 ^ 32) = x := by
    simp only [Int.bmod]; split <;> omega
  have h2 : ((y : Nat) : Int).bmod (2 ^ 32) = y := by
    simp only [Int.bmod]; split <;> omega
  rw [h1, h2]; simp only [Int.bmod]; split <;> omega

theorem add0 (x : BitVec 64) : x + sign_extend (m := 64) (0x000#12) = x := by
  rw [sext_eq]; simp

theorem or_add (a b i : Nat) (h : b < 2 ^ i) : a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [Nat.mul_comm]; exact (Nat.two_pow_add_eq_or_of_lt h a).symm
theorem add_or (a b i : Nat) (h : b < 2 ^ i) : b ||| a * 2 ^ i = a * 2 ^ i + b := by
  rw [Nat.or_comm]; exact or_add a b i h

theorem toInt_ofNat_small {n : Nat} (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_cond]; simp; split <;> omega

theorem zext_bool (b : Bool) : (zero_extend (m := 64) (bool_to_bit b)).toNat = if b = true then 1 else 0 := by
  cases b <;> rfl

theorem land2046 (x : Nat) : x &&& 2046 = x % 2048 - x % 2 := by
  have h1 : x &&& 2046 = (x % 2048) &&& 2046 := by
    have e := Nat.and_mod_two_pow (a := x) (b := 2046) (n := 11)
    rw [Nat.mod_eq_of_lt (Nat.and_lt_two_pow x (by decide : (2046 : Nat) < 2 ^ 11))] at e
    exact e
  have h2 : ∀ y < 2048, y &&& 2046 = y % 2048 - y % 2 := by decide +kernel
  rw [h1, h2 _ (Nat.mod_lt _ (by decide))]; omega

open Lean Elab Tactic Meta in
/-- Unfold the node at the head of the goal's left side, unless it is a leaf
(a pack) or one of the cut nodes `cuts` (a stage with its own lemma). -/
elab "unfold_node" "[" cuts:ident,* "]" : tactic => do
  let g := (← instantiateMVars (← getMainTarget)).consumeMData
  let some (_, lhs, _) := g.eq? | throwError "unfold_node: not an equation"
  let .const n _ := lhs.getAppFn | throwError "unfold_node: the left side's head is not a constant"
  for c in cuts.getElems do
    if (← realizeGlobalConstNoOverloadWithInfo c) == n then throwError "unfold_node: a cut"
  let info ← getConstInfoDefn n
  let isNode : Name → Bool := fun c => (c.toString.splitOn ".N_").length > 1
  let ok ← lambdaTelescope info.value fun _ b => do
    let h := b.getAppFn
    return h.isConstOf ``ite || (h.isConst && isNode h.constName!)
  unless ok do throwError "unfold_node: a leaf"
  evalTactic (← `(tactic| unfold $(mkIdent n):ident))


/-! ## The `ofNat` normal form

A node's arguments are kept as `BitVec.ofNat 64 n` of a `Nat` expression `n`
over the chamber's atoms; the machine's operations act on `n` (bounds by
`omega`), and a guard is a `decide` over `n`. -/

theorem nf_add (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem nf_wrap {a : Nat} (h : 2 ^ 64 ≤ a) : BitVec.ofNat 64 a = BitVec.ofNat 64 (a - 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem nf_mod_lit {a : Nat} (h : 2 ^ 64 ≤ a) : BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem nf_sub_wrap {a b : Nat} (hb : b ≤ 2 ^ 64) (ha : a < b) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a + 2 ^ 64 - b) := by
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem nf_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp; omega
theorem nf_shr {a : Nat} (k : Nat) (h : a < 2 ^ 64) : BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; rw [Nat.mod_eq_of_lt h]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h)).symm
theorem srl_var (x y : BitVec 64) :
    shift_bits_right x (Sail.BitVec.extractLsb y 5 0) = x >>> (y.toNat % 64) := by
  simp [shift_bits_right, Sail.BitVec.extractLsb, BitVec.ushiftRight_eq', BitVec.extractLsb, BitVec.extractLsb']
theorem sll_var (x y : BitVec 64) :
    shift_bits_left x (Sail.BitVec.extractLsb y 5 0) = x <<< (y.toNat % 64) := by
  simp [shift_bits_left, Sail.BitVec.extractLsb, BitVec.shiftLeft_eq', BitVec.extractLsb, BitVec.extractLsb']
theorem nf_toNat {n : Nat} (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by simp [Nat.mod_eq_of_lt h]
/-- The sticky test of `_FP_FRAC_SRS`: `x << (64 - d) != 0` is "a dropped bit was set". -/
theorem nf_sticky {Y d : Nat} (hd : d ≤ 64) :
    zopz0zI_u (BitVec.ofNat 64 0) (BitVec.ofNat 64 (Y * 2 ^ (64 - d))) = decide (¬ Y % 2 ^ d = 0) := by
  rw [ult_nat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_decide]
  have e : (2 : Nat) ^ 64 = 2 ^ d * 2 ^ (64 - d) := by rw [← Nat.pow_add]; congr 1; omega
  rw [e, Nat.mul_mod_mul_right]
  have := Nat.two_pow_pos (64 - d)
  constructor
  · intro h h0; rw [h0] at h; simp at h
  · intro h; exact Nat.mul_pos (Nat.pos_of_ne_zero h) this
theorem nf_low52 (a : Nat) : BitVec.ofNat 64 (a * 4096) >>> 12 = BitVec.ofNat 64 (a % 2 ^ 52) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega
theorem nf_low55 (a : Nat) : BitVec.ofNat 64 (a * 512) >>> 9 = BitVec.ofNat 64 (a % 2 ^ 55) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]; omega
theorem nf_shl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq; simp [Nat.shiftLeft_eq]
theorem nf_and_mask (a n : Nat) (hn : n ≤ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 (2 ^ n - 1) = BitVec.ofNat 64 (a % 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : 2 ^ n - 1 < 2 ^ 64 := by
    have := Nat.pow_le_pow_right (n := 2) (by decide) hn; omega
  have h2 : 2 ^ n ≤ 2 ^ 64 := by
    exact Nat.pow_le_pow_right (n := 2) (by decide) hn
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt h1, Nat.and_two_pow_sub_one_eq_mod]
  have : a % 2 ^ 64 % 2 ^ n = a % 2 ^ n := Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn)
  rw [this, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos n)) h2)]
theorem nf_and7 (a : Nat) : BitVec.ofNat 64 a &&& 7#64 = BitVec.ofNat 64 (a % 8) := nf_and_mask a 3 (by decide)
theorem nf_and15 (a : Nat) : BitVec.ofNat 64 a &&& 15#64 = BitVec.ofNat 64 (a % 16) := nf_and_mask a 4 (by decide)
theorem nf_and2047 (a : Nat) : BitVec.ofNat 64 a &&& 2047#64 = BitVec.ofNat 64 (a % 2048) :=
  nf_and_mask a 11 (by decide)
theorem nf_and52 (a : Nat) : BitVec.ofNat 64 a &&& 4503599627370495#64 = BitVec.ofNat 64 (a % 2 ^ 52) :=
  nf_and_mask a 52 (by decide)
theorem nf_and52' (a : Nat) : BitVec.ofNat 64 (2 ^ 52 - 1) &&& BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 52) := by
  rw [BitVec.and_comm]; exact nf_and_mask a 52 (by decide)
theorem nf_and55 (a : Nat) : BitVec.ofNat 64 a &&& 36028797018963967#64 = BitVec.ofNat 64 (a % 2 ^ 55) :=
  nf_and_mask a 55 (by decide)
theorem nf_and2046 (a : Nat) : BitVec.ofNat 64 a &&& 2046#64 = BitVec.ofNat 64 (a % 2048 - a % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
  rw [land2046]; omega

theorem nf_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  rw [beq_toNat]; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem nf_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = !decide (a = b) := by
  simp only [bne, nf_beq ha hb]
theorem nf_ult {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [ult_nat]; simp [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
theorem nf_sge {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  rw [sge_int, toInt_ofNat_small ha, toInt_ofNat_small hb]; simp
theorem nf_slt {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [slt_int', toInt_ofNat_small ha, toInt_ofNat_small hb]; simp
/-- `bltz (x << 8)`: bit 55 of `x`. -/
theorem nf_bit55_lt (a : Nat) : zopz0zI_s (BitVec.ofNat 64 (a * 2 ^ 8)) 0#64 = decide (2 ^ 55 ≤ a % 2 ^ 56) := by
  rw [slt_int', BitVec.toInt_eq_toNat_cond]; simp; split <;> omega
theorem nf_bit55_ge (a : Nat) : zopz0zKzJ_s (BitVec.ofNat 64 (a * 2 ^ 8)) 0#64 = decide (a % 2 ^ 56 < 2 ^ 55) := by
  rw [sge_int, BitVec.toInt_eq_toNat_cond]; simp; split <;> omega
theorem nf_zext_bool (b : Bool) : zero_extend (m := 64) (bool_to_bit b) = BitVec.ofNat 64 (if b then 1 else 0) := by
  cases b <;> rfl
theorem nf_sext32 {x : Nat} (h : x < 2 ^ 31) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 x) 31 0) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofNat_small (by omega), BitVec.toInt_signExtend_of_le (by decide)]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, Nat.shiftRight_zero, BitVec.toInt_eq_toNat_bmod,
    BitVec.toNat_ofNat, Nat.reduceSub, Nat.reduceAdd]
  have e1 : x % 2 ^ 64 % 2 ^ 32 = x := by omega
  rw [e1]; simp only [Int.bmod]; split <;> omega
theorem nf_sext32_c {x : Nat} (hx : x < 2048) :
    BitVec.signExtend 64 (Sail.BitVec.extractLsb (BitVec.ofNat 64 (x + 18446744073709549569)) 31 0) =
      if x = 2047 then 0#64 else BitVec.ofNat 64 (18446744073709551616 - (2047 - x)) := by
  split
  · subst_vars; decide
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_signExtend_of_le (by decide)]
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, Nat.shiftRight_zero, BitVec.toInt_eq_toNat_bmod,
      BitVec.toNat_ofNat, Nat.reduceSub, Nat.reduceAdd]
    have e1 : (x + 18446744073709549569) % 2 ^ 64 % 2 ^ 32 = 2 ^ 32 - (2047 - x) := by omega
    have e2 : (18446744073709551616 - (2047 - x)) % 2 ^ 64 = 18446744073709551616 - (2047 - x) := by omega
    rw [e1, e2]; simp only [Int.bmod]; split <;> split <;> omega
theorem nf_wsub {x y : Nat} (hy : y ≤ x) (hx : x < 2 ^ 31) :
    BitVec.signExtend 64 ((Sail.BitVec.extractLsb (BitVec.ofNat 64 x) 31 0) -
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 y) 31 0)) = BitVec.ofNat 64 (x - y) := by
  rw [← sext_eq, wsub_ofNat x y hx (by omega)]
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofInt_small (by omega) (by omega), toInt_ofNat_small (by omega)]; omega
theorem nf_ofInt_nat (x : Nat) : BitVec.ofInt 64 (x : Int) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq; simp
theorem nf_ofInt_sub {x y : Nat} (h : y ≤ x) : BitVec.ofInt 64 ((x : Int) - y) = BitVec.ofNat 64 (x - y) := by
  rw [show ((x : Int) - y) = ((x - y : Nat) : Int) by omega, nf_ofInt_nat]
/-- `x - k` written `x + (2^64 - k)`, when `k ≤ x`. -/
theorem nf_add_neg {x c : Nat} (hc2 : c < 2 ^ 64) (hx : 2 ^ 64 - c ≤ x) (hx2 : x < 2 ^ 63) :
    BitVec.ofNat 64 (x + c) = BitVec.ofNat 64 (x - (2 ^ 64 - c)) := by
  apply BitVec.eq_of_toNat_eq; simp; omega
/-- `seqz`-style `x - k <u 1`: `x = k`. -/
theorem nf_ult_neg {x c : Nat} (hc : 2 ^ 63 ≤ c) (hc2 : c < 2 ^ 64) (hx : x < 2 ^ 63) :
    zopz0zI_u (BitVec.ofNat 64 (x + c)) (BitVec.ofNat 64 1) = decide (x = 2 ^ 64 - c) := by
  rw [ult_nat]; simp; omega
theorem nf_ofInt_neg {x y : Nat} (h : x < y) (h2 : y - x < 2 ^ 63) :
    BitVec.ofInt 64 ((x : Int) - y) = BitVec.ofNat 64 (18446744073709551616 - (y - x)) := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofInt_small (by omega) (by omega), BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  split <;> omega
theorem nf_sge_neg {a n : Nat} (ha : a < 2 ^ 63) (hn : 0 < n) (hn2 : n ≤ 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 (18446744073709551616 - n)) = true := by
  rw [sge_int, toInt_ofNat_small ha, BitVec.toInt_eq_toNat_cond]
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega)]
  split <;> simp <;> omega
theorem nf_wneg {n : Nat} (hn : 0 < n) (hn2 : n < 2 ^ 31) :
    BitVec.signExtend 64 ((Sail.BitVec.extractLsb (BitVec.ofNat 64 0) 31 0) -
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 (18446744073709551616 - n)) 31 0)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toInt_eq
  rw [toInt_ofNat_small (by omega), BitVec.toInt_signExtend_of_le (by decide)]
  simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_ofNat, Nat.shiftRight_zero,
    BitVec.toInt_eq_toNat_bmod, Nat.reduceSub, Nat.reduceAdd, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have e1 : (2 ^ 32 - ((18446744073709551616 - n) % 2 ^ 64 % 2 ^ 32) + 0 % 2 ^ 64 % 2 ^ 32) % 2 ^ 32 = n := by omega
  rw [e1]; simp only [Int.bmod]; split <;> omega
theorem nf_not_neg {n : Nat} (hn : 0 < n) (hn2 : n ≤ 2 ^ 64) :
    BitVec.ofNat 64 (18446744073709551616 - n) ^^^ 18446744073709551615#64 = BitVec.ofNat 64 (n - 1) := by
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_not]
  simp only [BitVec.toNat_ofNat]
  omega
theorem nf_ofInt_zero : BitVec.ofInt 64 0 = 0#64 := by decide
theorem nf_lit (n : Nat) : (BitVec.ofNat 64 n : BitVec 64) = BitVec.ofNat 64 n := rfl

/-- Clearing bit `j` of a `w`-bit word (soft-fp's `&= ~IMPLBIT`). -/
theorem land_clear (x j w : Nat) (hj : j < w) (hx : x < 2 ^ w) :
    x &&& (2 ^ (j + 1) * (2 ^ (w - (j + 1)) - 1) + (2 ^ j - 1)) = 2 ^ (j + 1) * (x / 2 ^ (j + 1)) + x % 2 ^ j := by
  have hb1 : 2 ^ j - 1 < 2 ^ (j + 1) := by
    have := Nat.pow_lt_pow_right (a := 2) (by decide) (Nat.lt_succ_self j); omega
  have hb2 : x % 2 ^ j < 2 ^ (j + 1) := Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos j))
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ j))
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hb1, Nat.testBit_two_pow_mul_add _ hb2]
  by_cases hi : i < j + 1
  · simp only [hi, ite_true, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases hij : i < j <;> simp [hij]
  · simp only [hi, ite_false, Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
    rw [Nat.sub_add_cancel (by omega)]
    by_cases hw : i < w
    · simp [show i - (j + 1) < w - (j + 1) by omega]
    · have : x.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]

theorem nf_clr55 (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& 18410715276690587647#64 = BitVec.ofNat 64 (2 ^ 56 * (x / 2 ^ 56) + x % 2 ^ 55) := by
  have := land_clear x 55 64 (by decide) hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
  rw [show (18410715276690587647 : Nat) % 2 ^ 64 = 2 ^ (55 + 1) * (2 ^ (64 - (55 + 1)) - 1) + (2 ^ 55 - 1) by decide,
    this]
  omega
theorem nf_clr54 (x : Nat) (hx : x < 2 ^ 63) :
    BitVec.ofNat 64 x &&& 9205357638345293823#64 = BitVec.ofNat 64 (2 ^ 55 * (x / 2 ^ 55) + x % 2 ^ 54) := by
  have := land_clear x 54 63 (by decide) hx
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide) : x < 2 ^ 64)]
  rw [show (9205357638345293823 : Nat) % 2 ^ 64 = 2 ^ (54 + 1) * (2 ^ (63 - (54 + 1)) - 1) + (2 ^ 54 - 1) by decide,
    this]
  omega
theorem land_b55 (x : Nat) : x &&& 2 ^ 55 = (x / 2 ^ 55 % 2) * 2 ^ 55 := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hi : 55 = i
  · subst hi
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ 55) with h | h <;>
      simp [h, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_two_pow]
  · simp only [hi, decide_false, Bool.and_false]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ 55) with h | h
    · simp [h]
    · rw [h, Nat.one_mul, Nat.testBit_two_pow]; simp [hi]
theorem nf_and_b55 (a : Nat) :
    BitVec.ofNat 64 a &&& 36028797018963968#64 = BitVec.ofNat 64 (a / 2 ^ 55 % 2 * 2 ^ 55) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [show (36028797018963968 : Nat) % 2 ^ 64 = 2 ^ 55 by decide]
  have := land_b55 (a % 2 ^ 64)
  rw [this]
  have : a % 2 ^ 64 / 2 ^ 55 % 2 = a / 2 ^ 55 % 2 := by omega
  rw [this]; omega
theorem nf_and0 (a : BitVec 64) : a &&& 0#64 = 0#64 := BitVec.and_zero
theorem nf_and1 (a : Nat) : BitVec.ofNat 64 a &&& 1#64 = BitVec.ofNat 64 (a % 2) := nf_and_mask a 1 (by decide)
theorem lor_low (a b : Nat) (hb : b < 2) : a ||| b = if b = 0 then a else 2 * (a / 2) + 1 := by
  split
  · subst_vars; simp
  · have hb1 : b = 1 := by omega
    subst hb1
    have e : a = (a / 2) * 2 ^ 1 + a % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one a with h | h
    · rw [e, h, Nat.add_zero, or_add _ _ _ (by decide)]; omega
    · have : a ||| 1 = a := by
        apply Nat.eq_of_testBit_eq; intro i
        rw [Nat.testBit_or]
        rcases i with _ | i
        · simp [Nat.testBit_zero, h]
        · simp [Nat.testBit_succ]
      rw [this]; omega
theorem nf_or_low (a b : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 (b % 2) = BitVec.ofNat 64 (if b % 2 = 0 then a else 2 * (a / 2) + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (Nat.lt_trans (Nat.mod_lt b (by decide)) (by decide) : b % 2 < 2 ^ 64)]
  rw [lor_low a (b % 2) (Nat.mod_lt _ (by decide))]
  split <;> omega

/-- `_FP_FRAC_SRS`: the shifted word or-ed with the sticky bit is round to odd. -/
theorem nf_srs {Y d : Nat} {inst : Decidable (¬ Y % 2 ^ d = 0)} (hY0 : Y < 2 ^ 64) :
    BitVec.ofNat 64 (Y / 2 ^ d) ||| BitVec.ofNat 64 (@ite _ (¬ Y % 2 ^ d = 0) inst 1 0) =
      BitVec.ofNat 64 (Lua.Num.SfRef.rto Y d) := by
  have hY : Y / 2 ^ d < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hY0
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hY]
  by_cases h : Y % 2 ^ d = 0
  · rw [Lua.Num.SfRef.rto_exact h, if_neg (by simp [h])]
    simp only [Nat.zero_mod, Nat.or_zero]; exact (Nat.mod_eq_of_lt hY).symm
  · rw [Lua.Num.SfRef.rto_jam h, if_pos h, show (1 : Nat) % 2 ^ 64 = 1 by decide,
      lor_low _ 1 (by decide), if_neg (by decide), Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    omega
theorem nf_or55 {a : Nat} (h : a < 2 ^ 55) :
    BitVec.ofNat 64 a ||| 36028797018963968#64 = BitVec.ofNat 64 (2 ^ 55 + a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : a < 2 ^ 64), show (36028797018963968 : Nat) % 2 ^ 64 = 1 * 2 ^ 55 by decide,
    add_or _ _ _ h]
  omega
/-- The normal form of the goal: literals, then the operations on `ofNat`
(side conditions by `omega`), then the `Bool` guards to `Prop`. -/
macro "sf_nfB" : tactic => `(tactic| (
  try simp (disch := omega) only [nf_add, nf_sub, nf_sub_wrap, nf_shr, nf_shl, nf_and7, nf_and15, nf_and2047, nf_and52, nf_and52',
    nf_and55, nf_and2046, nf_beq, nf_bne, nf_ult, nf_sge, nf_slt, nf_bit55_lt, nf_bit55_ge, nf_sext32, nf_wsub,
    nf_ofInt_sub, nf_ofInt_nat, Nat.mul_div_cancel, nf_add_neg, nf_ult_neg, nf_clr55, nf_clr54, nf_and1,
    nf_or_low, nf_low52, nf_low55, nf_and_b55, nf_and0, nf_ofInt_neg, nf_sge_neg, nf_wneg, nf_not_neg, nf_toNat, Nat.mod_eq_of_lt, nf_sticky, nf_srs, nf_or55, decide_eq_true_eq, nf_sext32_c]
  try simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.reduceMod, Nat.reduceDiv,
    Nat.sub_zero, Nat.add_zero, Nat.zero_add]
))

macro "sf_nf" : tactic => `(tactic| (
  try simp only [sll_lit, srl_lit, srl_var, sll_var, sext_eq, BitVec.reduceSignExtend, BitVec.reduceToNat, BitVec.reduceAdd,
    BitVec.add_zero, BitVec.zero_add, nf_zext_bool, Bool.false_eq_true, ite_true, ite_false, nf_ofInt_zero,
    Int.sub_self, BitVec.reduceHShiftLeft, BitVec.reduceHShiftRight]
  try simp only [BitVec.ofNat_eq_ofNat]
  try simp (disch := omega) only [nf_mod_lit]
  try simp only [Nat.reduceMod, Nat.reducePow]
  sf_nfB
  sf_nfB
  try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true, Bool.not_eq_false',
    Bool.not_true, Bool.not_false, Bool.not_not, decide_true, decide_false, Bool.false_eq_true]
  try simp (disch := omega) only [if_pos, if_neg]
  try simp only [ite_true, ite_false, ↓reduceIte]
  sf_nfB
  try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_true, Bool.not_eq_false',
    Bool.not_true, Bool.not_false, Bool.not_not, decide_true, decide_false, Bool.false_eq_true]
  try simp (disch := omega) only [if_pos, if_neg]))

/-- One exploration step: unfold the head node, or split its guard and drop
a side the chamber's facts refute. -/
macro "sf_step" "[" cuts:ident,* "]" : tactic => `(tactic| first
  | (unfold_node [$cuts,*]; sf_nf)
  | (split <;> (try (exfalso; omega))))

/-- Explore the DAG under the chamber's facts down to its leaves. -/
macro "sf_go" "[" cuts:ident,* "]" : tactic => `(tactic| (
  (try simp only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd] at *); sf_nf; repeat' sf_step [$cuts,*]))

/-! ## Leaves -/

/-- `_FP_PACK_RAW_D` as the machine computes it: sign, exponent and fraction or-ed. -/
theorem pack_eq {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    ((shift_bits_left (BitVec.ofNat 64 E) (Sail.BitVec.extractLsb (0x34#6) 5 0)) ||| BitVec.ofNat 64 F) |||
      (shift_bits_left (BitVec.ofNat 64 S) (Sail.BitVec.extractLsb (0x3f#6) 5 0)) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  rw [sll_lit, sll_lit]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have h1 : E % 2 ^ 64 * 2 ^ (52 % 2 ^ 6) % 2 ^ 64 = E * 2 ^ 52 := by simp; omega
  have h2 : S % 2 ^ 64 * 2 ^ (63 % 2 ^ 6) % 2 ^ 64 = S * 2 ^ 63 := by simp; omega
  have h3 : F % 2 ^ 64 = F := by omega
  rw [h1, h2, h3, or_add _ _ _ hF, add_or _ _ _ (by omega)]
  omega

theorem bits_nf (neg : Bool) (be f : Nat) :
    Lua.Num.F64.bits neg be f = BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + be * 2 ^ 52 + f) := by
  unfold Lua.Num.F64.bits; exact Eq.refl _

theorem qnan_nf : Lua.Num.F64.qnan = BitVec.ofNat 64 9221120237041090560 := by
  unfold Lua.Num.F64.qnan; exact BitVec.ofNat_eq_ofNat
theorem infty_nf (neg : Bool) :
    Lua.Num.F64.infty neg = BitVec.ofNat 64 ((if neg then 2 ^ 63 else 0) + 2047 * 2 ^ 52 + 0) := by
  unfold Lua.Num.F64.infty; exact bits_nf neg 2047 0
/-- `omega` after the literal arithmetic is evaluated (`omega` on `(1 - 1) * 2^52`
with a large bound in context exceeds the recursion depth). -/
macro "sf_omega" : tactic => `(tactic| ((try simp only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow,
  Nat.reduceAdd, Nat.zero_mul, Nat.zero_add, Nat.add_zero, Nat.mul_zero, Nat.sub_self]); omega))

/-- The reference side of a leaf, by cases decided from the path's facts:
`addAligned`/`subMag` unfolded, `rto` at the shifts the path fixed, the
carry and the rounding by `omega`, `roundPack` to `bits`. -/
macro "sf_ref" : tactic => `(tactic| (
  try simp only [Lua.Num.SfRef.addAligned, Lua.Num.SfRef.subMag, Lua.Num.SfRef.carryPack, Lua.Num.SfRef.subPack]
  try simp only [Lua.Num.SfRef.rto_zero, Lua.Num.SfRef.rto_one, Lua.Num.SfRef.rto_zero_n]))

/-- The reference's `roundPack` at a leaf whose path fixed the rounding. -/
macro "sf_ref2" : tactic => `(tactic| (
  try simp (disch := omega) only [Lua.Num.SfRef.normPack_one]
  try simp (disch := sf_omega) only [Lua.Num.SfRef.roundPack_keep, Lua.Num.SfRef.roundPack_up,
    Lua.Num.SfRef.roundPack_inf_keep, Lua.Num.SfRef.roundPack_inf_up, Lua.Num.SfRef.roundPack_inf_any]
  try simp only [Lua.Vm.Fn.SfLens.infty_nf, Lua.Vm.Fn.SfLens.qnan_nf, Lua.Num.F64.zero]
  try simp only [Lua.Vm.Fn.SfLens.bits_nf]))

theorem rp_congr {n : Bool} {E E' F F' : Nat} (h1 : E = E') (h2 : F = F') :
    Lua.Num.SfRef.roundPack n E F = Lua.Num.SfRef.roundPack n E' F' := by rw [h1, h2]

/-- Close a leaf: the routine's pack nodes (`packs`) and the reference both
as `ofNat`, or both as `roundPack` (a cut stage's lemma already applied). -/
macro "sf_close" "[" packs:ident,* "]" : tactic => `(tactic| (
  try simp (disch := omega) only [$[$packs:ident],*]
  all_goals sf_ref
  all_goals (repeat' split) <;> (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
    not_true_eq_false] at *) <;> (try (exfalso; omega)) <;> sf_ref2 <;>
  (repeat' split) <;> (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
    not_true_eq_false, Bool.false_eq_true] at *) <;>
    (first | (exfalso; omega) | (refine congrArg (BitVec.ofNat 64) ?_; omega) | (apply rp_congr <;> omega) | (apply Lua.Num.SfRef.cp_congr <;> omega) | (apply Lua.Num.SfRef.sp_congr <;> omega) | (apply Lua.Num.SfRef.np_congr <;> omega))))

/-! ## Frame reloads (`reload_forward`): a reload of the routine's own spill
reads the stored word through the later stores of the frame. -/

theorem sext64_self (x : BitVec (8 * 8)) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- A slot of the 48-byte frame below `sp = s` (`FnSp s 48` keeps it in RAM,
so the address does not wrap). -/
theorem frame_addr {s : Nat} (o : BitVec 12) (h1 : 48 ≤ s) (h2 : s ≤ 2 ^ 32) (ho : o.toNat < 2048) :
    (BitVec.ofNat 64 s + sign_extend (m := 64) (0xfd0#12) + sign_extend (m := 64) o).toNat = s - 48 + o.toNat := by
  have e1 : (sign_extend (m := 64) (0xfd0#12)).toNat = 2 ^ 64 - 48 := by decide
  have e2 : (sign_extend (m := 64) o).toNat = o.toNat := by
    rw [sext_eq, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
    have : ¬ 2 ^ (12 - 1) ≤ o.toNat := by omega
    simp [this]; omega
  rw [BitVec.toNat_add, BitVec.toNat_add, e1, e2, BitVec.toNat_ofNat]
  omega

/-- `__clzdi2`'s summary on a normal-form word. -/
theorem nf_clz {f : Nat} (h0 : 0 < f) (h : f < 2 ^ 64) :
    Lua.Vm.Sim.clz64 (BitVec.ofNat 64 f) = BitVec.ofNat 64 (63 - f.log2) := by
  unfold Lua.Vm.Sim.clz64 Lua.Vm.Sim.bitlen
  rw [nf_toNat h, if_neg (by omega)]
  congr 1; omega

/-- Forward every reload through the frame's stores (addresses by `frame_addr`). -/
macro "sf_reload" : tactic => `(tactic| (
  try simp only [sext64_self, Lua.Vm.Sim.sdData_id]
  try simp (disch := first | omega | decide) only [frame_addr]
  try simp only [BitVec.reduceToNat]
  try simp (disch := omega) only [Lua.Vm.Sim.bytesT8_wm8_same, Lua.Vm.Sim.bytesT8_wm8_far]
  try simp (disch := omega) only [BitVec.add_zero, sext_eq, BitVec.reduceSignExtend, nf_clz]))

/-- `sf_close` for a stage whose reference rounds at biased exponent `0`:
the literal `(0 - 1) · 2^52` is evaluated before the final `omega`. -/
macro "sf_close0" "[" packs:ident,* "]" : tactic => `(tactic| (
  try simp (disch := omega) only [$[$packs:ident],*]
  all_goals sf_ref
  all_goals (repeat' split) <;> (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
    not_true_eq_false] at *) <;> (try (exfalso; omega)) <;> sf_ref2 <;>
  (try simp only [Nat.zero_sub, Nat.zero_mul, Nat.zero_add]) <;>
  (repeat' split) <;> (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true,
    not_true_eq_false, Bool.false_eq_true] at *) <;>
    (first | (exfalso; omega) | (refine congrArg (BitVec.ofNat 64) ?_; omega))))

/-- The reference's branches, with the fields' classes decided. -/
macro "sf_rhs" : tactic => `(tactic| (
  unfold Lua.Num.SfRef.addFields
  dsimp only
  try simp only [eq_self_iff_true, ite_true, ite_false, decide_eq_decide]
  try simp (disch := omega) only [if_pos, if_neg]
  try simp only [Lua.Num.SfRef.mant]
  try simp (disch := omega) only [if_pos, if_neg, Nat.max_eq_left, Nat.max_eq_right]))

end Lua.Vm.Fn.SfLens

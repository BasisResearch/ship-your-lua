import Lua.Vm.Fn.SqrtNorm

/-!
# `__ieee754_sqrt` at level (b) (lane float-sf6)

* (b1) `Ieee754Sqrt.F_eq_ref`: the lifted machine function is `SfRef.sqrt`
  (`Lua/Num/SfRefSqrt.lean`), and its termination function `T` holds, on
  every operand: the class tests of `e_sqrt.c:100-111` on the high word, then
  `core_478` (normal), `sub_5b0` (a subnormal with `ix0 != 0`), `sub_590`
  (`ix0 == 0`), or the `x*x+x` / `(x-x)/(x-x)` call nodes.
* (b2) `SfRef.sqrt_eq`: `SfRef.sqrt = F64.sqrt`.
* `spec_proved : F m s r g x = F64.sqrt x`, so `Float.Model.sqrt` by
  `F64.sqrt_eq_model`; `sum_ref`: the summary with `F64.sqrt` as its result
  and no termination premise.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Logic

namespace Lua.Vm.Fn.Ieee754Sqrt

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim Lua.Num.SfRef

set_option linter.unusedVariables false

/-- `srai` by a literal: the signed value's floor quotient. -/
theorem sra64 {w : Nat} (a : Int) (k : BitVec w) (h1 : -2 ^ 63 ≤ a) (h2 : a < 2 ^ 63) :
    shift_bits_right_arith (BitVec.ofInt 64 a) k = BitVec.ofInt 64 (a / 2 ^ k.toNat) := by
  unfold shift_bits_right_arith
  rw [BitVec.sshiftRight_eq, ofInt_toInt a h1 h2]
  simp [BitVec.toNatInt, Int.shiftRight_eq_div_pow]

/-- A mask below `2^32` sees the low word only. -/
theorem and_lo32 (n m : Nat) (hm : m < 2 ^ 32) : n &&& m = (n % 2 ^ 32) &&& m := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow]
  by_cases hi : i < 32
  · simp [hi]
  · have : m.testBit i = false := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hm (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [this]

/-- `and` with the exponent mask `0x7ff00000`, of any sign. -/
theorem and_exp (a : Int) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 2146435072 = BitVec.ofInt 64 (a % 4294967296 / 1048576 % 2048 * 1048576) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 2146435072).toNat = (2 ^ 11 - 1) * 2 ^ 20 by decide,
    and_lo32 _ _ (by decide), land_field]
  have h1 := ofInt_toNat a
  have h2 := ofInt_toNat (a % 4294967296 / 1048576 % 2048 * 1048576)
  omega

/-- The core's high word: only its fraction bits matter (`(ix0 & 0xfffff) | 0x100000`). -/
theorem sqCore_mask (h h' l : Nat) (M : Int) (e : h % 2 ^ 20 = h' % 2 ^ 20) : sqCore h l M = sqCore h' l M := by
  unfold sqCore; rw [e]

/-- A subnormal's whole-word shifts leave a nonzero high word alone. -/
theorem sqWords_hi (h l : Nat) (M : Int) (h0 : h ≠ 0) : sqWords 3 h l M = (h, l, M) := by
  unfold sqWords; rw [if_neg h0]

/-- The operand as a signed integer, by its fields. -/
theorem toInt_fields (x : Lua.Num.F64) :
    x.toInt = if x.sign then (2 ^ 63 + (x.bexp : Int) * 2 ^ 52 + x.frac) - 2 ^ 64
      else (x.bexp : Int) * 2 ^ 52 + x.frac := by
  have hs := Lua.Num.F64.toNat_split x
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  rw [BitVec.toInt_eq_toNat_cond]
  unfold Lua.Num.F64.sign at hs ⊢
  by_cases h : 2 ^ 63 ≤ x.toNat
  · simp only [h, decide_true, if_true] at hs ⊢
    rw [if_neg (by omega)]; omega
  · simp only [h, decide_false, Bool.false_eq_true, if_false] at hs ⊢
    rw [if_pos (by omega)]; omega

variable {m : Mem} (s : Nat) (r : BitVec 64) (g : SFrame) (hro : RodataRead m) (hs : FnSp s 160)

include hro hs in
/-- **The routine past its `∞`/NaN test** (`0x8002d464`, `e_sqrt.c:106-121`). -/
theorem mid_464 (x : Lua.Num.F64) (h1 : x.bexp ≠ 2047) :
    N_8002d464 m s r g (BitVec.ofInt 64 x.toInt) (BitVec.ofInt 64 x.toInt) (BitVec.ofInt 64 (x.toInt / 4294967296)) =
      Lua.Num.SfRef.sqrt x ∧
    T_8002d464 m s r g (BitVec.ofInt 64 x.toInt) (BitVec.ofInt 64 x.toInt) (BitVec.ofInt 64 (x.toInt / 4294967296)) =
      true := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hX := toInt_fields x
  have hx : BitVec.ofInt 64 x.toInt = x := BitVec.ofInt_toInt
  have hXb : -2 ^ 63 ≤ x.toInt ∧ x.toInt < 2 ^ 63 := by split at hX <;> omega
  unfold Lua.Num.SfRef.sqrt sqrtFields
  rw [if_neg h1]
  generalize x.toInt = X at hX hx hXb
  generalize x.sign = sg at hX
  generalize x.bexp = e at hX hb h1 ⊢
  generalize x.frac = f at hX hf ⊢
  -- the subnormals' bounds (`SfRef.sqNorm_spec`)
  have nb : ∀ f : Nat, 0 < f → f < 2 ^ 52 →
      -51 ≤ (sqNorm (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
        (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2).2.2 ∧
      (sqNorm (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
        (sqWords 3 (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2).2.2 ≤ 2046 := by
    intro f hf0 hf
    obtain ⟨j, _, hm, hj1, hj2⟩ := sqNorm_spec f hf0 hf
    have hj : j ≤ 52 := by
      refine Nat.le_of_not_lt fun hc' => ?_
      have : 2 ^ 53 ≤ f * 2 ^ j :=
        calc 2 ^ 53 ≤ 1 * 2 ^ j := by rw [Nat.one_mul]; exact Nat.pow_le_pow_right (by decide) hc'
          _ ≤ f * 2 ^ j := Nat.mul_le_mul_right _ hf0
      omega
    rw [hm]; omega
  have hfuel : fnFuel = (fnFuel - 2) + 1 + 1 := by unfold fnFuel; omega
  by_cases hz : e = 0 ∧ f = 0
  · -- `±0`: `x`
    rw [if_pos hz]
    have hH : X / 4294967296 ≤ 0 := by split at hX <;> omega
    rw [N_8002d464, T_8002d464]
    fm_nf
    rw [N_8002d578, T_8002d578]
    fm_nf
    rw [N_8002d640]
    fm_nf
    exact ⟨hx, trivial⟩
  rw [if_neg hz]
  by_cases hsg : sg = true
  · -- a negative: `(x-x)/(x-x)`
    rw [if_pos hsg]
    rw [hsg] at hX
    simp only [if_true] at hX
    generalize hR : (x.sub x).div (x.sub x) = R
    rw [N_8002d464, T_8002d464]
    fm_nf
    rw [N_8002d578, T_8002d578]
    fm_nf
    rw [N_8002d58c, T_8002d58c]
    fm_nf
    rw [N_8002d754, N_8002d758, N_8002d760, N_8002d640]
    fm_nf
    rw [hx, ← hR]
    exact ⟨rfl, trivial⟩
  rw [if_neg hsg]
  have hsg' : sg = false := by simpa using hsg
  rw [hsg'] at hX
  simp only [Bool.false_eq_true, if_false] at hX
  by_cases he : e = 0
  · rw [if_pos he]
    have hf0 : 0 < f := by omega
    have ⟨r1, r2⟩ := nb f hf0 hf
    dsimp only
    by_cases hh0 : f / 2 ^ 32 = 0
    · -- `ix0 == 0`
      rw [hh0, show f % 2 ^ 32 = f by omega] at r1 r2 ⊢
      have sub := sub_590 s r g hro hs (fnFuel - 2) f X (by omega) hf0 (by omega) r1 r2
      generalize sqCore (sqNorm (sqWords 3 0 f 0).1 (sqWords 3 0 f 0).2.1 (sqWords 3 0 f 0).2.2).1
        (sqNorm (sqWords 3 0 f 0).1 (sqWords 3 0 f 0).2.1 (sqWords 3 0 f 0).2.2).2.1
        (sqNorm (sqWords 3 0 f 0).1 (sqWords 3 0 f 0).2.1 (sqWords 3 0 f 0).2.2).2.2 = R at sub ⊢
      rw [N_8002d464, T_8002d464]
      fm_nf
      rw [N_8002d578, T_8002d578]
      fm_nf
      have hX0 : X / 4294967296 = 0 := by omega
      rw [hX0]
      have hc : ¬ (0 * 8589934592 % 18446744073709551616 / 8589934592 + X).bmod 4294967296 % 18446744073709551616 = 0 := by
        have := bm_facts (0 * 8589934592 % 18446744073709551616 / 8589934592 + X)
        omega
      rw [if_neg hc, if_neg hc, N_8002d58c, T_8002d58c]
      fm_nf
      rw [hfuel]
      exact sub
    · -- `ix0 != 0` without bit 20
      rw [sqWords_hi _ _ _ hh0] at r1 r2 ⊢
      have sub := sub_5b0 s r g hro hs (f / 2 ^ 32) (f % 2 ^ 32) X 0 (by omega) (by omega) (by omega)
        (Nat.mod_lt _ (by decide)) (by decide) (by decide) r1 r2
      generalize sqCore (sqNorm (f / 2 ^ 32) (f % 2 ^ 32) 0).1 (sqNorm (f / 2 ^ 32) (f % 2 ^ 32) 0).2.1
        (sqNorm (f / 2 ^ 32) (f % 2 ^ 32) 0).2.2 = R at sub ⊢
      rw [N_8002d464, T_8002d464]
      fm_nf
      rw [N_8002d470, T_8002d470]
      fm_nf
      rw [show X / 4294967296 = ((f / 2 ^ 32 : Nat) : Int) by omega,
        show ((f / 2 ^ 32 : Nat) : Int) / 1048576 = 0 by omega]
      exact sub
  · -- normal
    rw [if_neg he]
    have core := core_478 s r g hro hs (e * 2 ^ 20 + f / 2 ^ 32) (f % 2 ^ 32) X e (by omega) (by omega)
      (Nat.mod_lt _ (by decide)) (by omega) (by omega)
    rw [sqCore_mask (e * 2 ^ 20 + f / 2 ^ 32) (f / 2 ^ 32) _ _ (by omega)] at core
    generalize sqCore (f / 2 ^ 32) (f % 2 ^ 32) (e : Int) = R at core ⊢
    rw [N_8002d464, T_8002d464]
    fm_nf
    rw [N_8002d470, T_8002d470]
    fm_nf
    rw [show X / 4294967296 = ((e * 2 ^ 20 + f / 2 ^ 32 : Nat) : Int) by omega,
      show ((e * 2 ^ 20 + f / 2 ^ 32 : Nat) : Int) / 1048576 = (e : Int) by omega]
    exact core

include hro hs in
/-- **(b1)**: the lifted `__ieee754_sqrt` is `SfRef.sqrt` (`e_sqrt.c` over the fields), and
its termination function holds, on every operand. -/
theorem F_eq_ref (x : Lua.Num.F64) : F m s r g x = Lua.Num.SfRef.sqrt x ∧ T m s r g x = true := by
  have hb : x.bexp < 2048 := Nat.mod_lt _ (by decide)
  have hf : x.frac < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hX := toInt_fields x
  have hx : BitVec.ofInt 64 x.toInt = x := BitVec.ofInt_toInt
  have hXb : -2 ^ 63 ≤ x.toInt ∧ x.toInt < 2 ^ 63 := by split at hX <;> omega
  have hro' : RodataRead (writeMap8 m ((((BitVec.ofNat 64 s) + sign_extend (m := 64) (0xfd0#12)) +
      sign_extend (m := 64) (0x028#12)).toNat) (sdData_val r)) := RodataRead.wm8 hro (by fn_sp_facts; kit_disch)
  have hmid := mid_464 s r g hro' hs
  fm_nf at hmid
  rw [show F m s r g x = F m s r g (BitVec.ofInt 64 x.toInt) by rw [hx],
    show T m s r g x = T m s r g (BitVec.ofInt 64 x.toInt) by rw [hx]]
  unfold F T
  simp (disch := fm_disch) only [sra64]
  fm_nf
  simp only [and_exp]
  fm_nf
  by_cases h1 : x.bexp = 2047
  · have hc : x.toInt / 4294967296 % 4294967296 / 1048576 % 2048 * 1048576 % 18446744073709551616 = 2146435072 := by
      split at hX <;> omega
    rw [if_pos hc, if_pos hc, N_8002d730, N_8002d738, N_8002d740]
    fm_nf
    simp only [Lua.Vm.Sim.sdData_id, hx]
    unfold Lua.Num.SfRef.sqrt sqrtFields
    rw [if_pos h1]
    exact ⟨rfl, trivial⟩
  · have hc : ¬ x.toInt / 4294967296 % 4294967296 / 1048576 % 2048 * 1048576 % 18446744073709551616 = 2146435072 := by
      split at hX <;> omega
    rw [if_neg hc, if_neg hc]
    exact hmid x h1

include hro hs in
/-- Every operand terminates within the loops' fuel. -/
theorem T_true (x : Lua.Num.F64) : T m s r g x = true := (F_eq_ref s r g hro hs x).2

include hro hs in
/-- **Level 2 of `__ieee754_sqrt`**: the lifted function is `F64.sqrt`, correctly rounded
(`Float.Model.sqrt` by `F64.sqrt_eq_model`). -/
theorem spec_proved (x : Lua.Num.F64) : F m s r g x = Lua.Num.F64.sqrt x :=
  (F_eq_ref s r g hro hs x).1.trans (Lua.Num.SfRef.sqrt_eq x)

/-- **`__ieee754_sqrt`'s summary with `F64.sqrt` as its result**, no premise. -/
theorem sum_ref (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 : BitVec 64)
    (hs : FnSp s 160) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002d448#64 [⟨Register.x10, v10⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Num.F64.sqrt v10⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm (m) s r g v10) (s - 160) 160) o)) := by
  have h := sum m o s r g v10 hs hr hrod (T_true s r g hrod hs v10)
  rwa [spec_proved s r g hrod hs v10] at h

/-- The summary's value is the model's correctly rounded square root. -/
theorem spec_model (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (hrod : RodataRead m) (hs : FnSp s 160)
    (x : Lua.Num.F64) :
    F m s r g x = (Float.Model.sqrt (Lua.Num.F64.toModel x)).toBits.toBitVec := by
  rw [spec_proved s r g hrod hs x, Lua.Num.F64.sqrt_eq_model]

end Lua.Vm.Fn.Ieee754Sqrt


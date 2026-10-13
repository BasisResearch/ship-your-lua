import Lua.Vm.Sim.Kit.FltValLt
import Lua.Vm.Fn.SfRefFloorSpec

/-!
# `EqiFlt_Statement` proved (lane F1-F5)

`OP_EQI` on a float compares `luai_numeq(fltvalue(ra), cast_num(sB))`; the
kernel's test is `δ .eq`, `luaV_equalobj`'s mixed case: the float through
`luaV_tointegerns(F2Ieq)` (`floor`, integral, in range, `(lua_Integer)`)
against the integer. For an 8-bit immediate the two agree:

* the `F64` view (`f2iEqW`): `x` is `F64.toModel X`; `floor` is
  `SfRef.floor` (`SfRef.floor_model`), `==` is `F64.eq` (`eq_eq_model`),
  `(lua_Integer)` is `__fixdfdi` (`fixdfdi_model`), `cast_num` is `F64.ofInt`;
* `F64.eq X Y` forces one class, or two zeros (`eq_cls`), and a non-NaN word
  is its class (`cls_inj`): `X == (double)sB` pins `X` to one of 257 words,
  each decided once per immediate (`ImmFacts`);
* conversely an integral `X` (`floor X = X`) whose conversion is `sB` is
  `normalize sB 0` (`floor_cls`, `ofInt_exact`), so `X == (double)sB`.
-/

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Num Lua.Num.F64 Lua.Bytecode

/-- A non-NaN word is determined by its class. -/
theorem cls_inj {x y : F64} (h : x.cls = y.cls) (hn : x.cls ≠ .nan) : x = y := by
  rw [← pack_cls x hn, ← pack_cls y (h ▸ hn), h]

theorem ord_then_swap_eq {a b : Ordering} (h : (a.then b).swap = .eq) : a = .eq ∧ b = .eq := by
  cases a <;> cases b <;> simp_all [Ordering.then, Ordering.swap]

theorem ord_then_eq {a b : Ordering} (h : a.then b = .eq) : a = .eq ∧ b = .eq := by
  cases a <;> cases b <;> simp_all [Ordering.then]

/-- `==` on words: one class (not NaN), or both zeros. -/
theorem eq_cls {x y : F64} (h : F64.eq x y = true) :
    x.cls ≠ .nan ∧ (x.cls = y.cls ∨ (∃ a b, x.cls = .zero a ∧ y.cls = .zero b)) := by
  unfold F64.eq F64.compare at h
  rcases hx : x.cls with _ | a | a | ⟨a, m, e⟩ <;> rcases hy : y.cls with _ | b | b | ⟨b, n, f⟩ <;>
    rw [hx, hy] at h <;> (try cases a) <;> (try cases b) <;>
    simp only [beq_iff_eq, Option.some.injEq, reduceCtorEq] at h
  all_goals first
    | exact ⟨by simp, .inr ⟨_, _, rfl, rfl⟩⟩
    | exact ⟨by simp, .inl rfl⟩
    | (obtain ⟨h1, h2⟩ := ord_then_swap_eq h
       rw [Std.compare_eq_iff_eq] at h1 h2; subst h1 h2; exact ⟨by simp, .inl rfl⟩)
    | (obtain ⟨h1, h2⟩ := ord_then_eq h
       rw [Std.compare_eq_iff_eq] at h1 h2; subst h1 h2; exact ⟨by simp, .inl rfl⟩)
    | (revert h; decide)

/-- An 8-bit immediate (`sB`). -/
abbrev immW (b : Nat) : BitVec 64 := BitVec.ofInt 64 ((b : Int) - 127)

/-- `F2Ieq` then `==` with an integer, on words. -/
def f2iEqW (X : F64) (i : BitVec 64) : Bool :=
  if F64.eq X (SfRef.floor X) = true ∧ F64.le 0xc3e0000000000000#64 (SfRef.floor X) = true ∧
      F64.lt (SfRef.floor X) 0x43e0000000000000#64 = true
  then decide (Lua.Vm.Fn.Fixdfdi.S (SfRef.floor X) = i) else false

/-- What one immediate needs, decided: its word's answers, the zeros', and
`__fixdfdi`'s saturated values differ from it. -/
structure ImmFacts (b : Nat) : Prop where
  ofInt_ok : f2iEqW (F64.ofInt (immW b)) (immW b) = true
  ofInt_refl : F64.eq (F64.ofInt (immW b)) (F64.ofInt (immW b)) = true
  zero_ok : ∀ a, F64.eq (F64.zero a) (F64.ofInt (immW b)) = f2iEqW (F64.zero a) (immW b)
  sat_lo : BitVec.ofNat 64 (2 ^ 63) ≠ immW b
  sat_hi : BitVec.ofNat 64 (2 ^ 63 - 1) ≠ immW b

theorem immFacts (b : Nat) (hb : b < 256) : ImmFacts b := by
  have h1 : ∀ b, b < 256 → f2iEqW (F64.ofInt (immW b)) (immW b) = true := by decide +kernel
  have h2 : ∀ b, b < 256 → F64.eq (F64.ofInt (immW b)) (F64.ofInt (immW b)) = true := by decide +kernel
  have h3 : ∀ b, b < 256 → ∀ a, F64.eq (F64.zero a) (F64.ofInt (immW b)) = f2iEqW (F64.zero a) (immW b) := by
    decide +kernel
  have h4 : ∀ b, b < 256 → BitVec.ofNat 64 (2 ^ 63) ≠ immW b := by decide +kernel
  have h5 : ∀ b, b < 256 → BitVec.ofNat 64 (2 ^ 63 - 1) ≠ immW b := by decide +kernel
  exact ⟨h1 b hb, h2 b hb, h3 b hb, h4 b hb, h5 b hb⟩

theorem zero_cls (a : Bool) : (F64.zero a).cls = .zero a := by cases a <;> decide

/-- `F2Ieq`'s answer against the immediate is `==` with it, on words. -/
theorem f2iEqW_eq (X : F64) (b : Nat) (hb : b < 256) :
    f2iEqW X (immW b) = F64.eq X (F64.ofInt (immW b)) := by
  have H := immFacts b hb
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hl
    have hl0 := hl
    unfold f2iEqW at hl
    split at hl
    case isFalse => cases hl
    rename_i hc
    obtain ⟨hE, -, -⟩ := hc
    have hfix := of_decide_eq_true hl
    obtain ⟨hn, hcl⟩ := eq_cls hE
    -- the floor is the word itself
    have hF : SfRef.floor X = X := by
      rcases hcl with h | ⟨a, c, hx, -⟩
      · exact (cls_inj h hn).symm
      · rw [SfRef.floor_cls, hx]
    rw [hF] at hfix
    rcases hc : X.cls with _ | s | s | ⟨s, m, e⟩
    · exact absurd hc hn
    · -- `±∞` saturates
      exfalso
      have ht : truncInt? X = none := by unfold truncInt?; rw [hc]
      unfold Lua.Vm.Fn.Fixdfdi.S at hfix
      rw [ht] at hfix
      dsimp only at hfix
      split at hfix
      · exact H.sat_lo hfix
      · exact H.sat_hi hfix
    · have hX : X = F64.zero s := cls_inj (by rw [hc, zero_cls]) (by rw [hc]; simp)
      subst hX
      rw [H.zero_ok]; exact hl0
    · obtain ⟨hok, -⟩ := cls_fin hc
      by_cases he : 0 ≤ e
      · -- `|X| ≥ 2^52`: its conversion is no immediate
        exfalso
        have hm : 2 ^ 52 ≤ m := hok.canon.resolve_right (by omega)
        have hv : 2 ^ 52 ≤ m <<< e.toNat := by
          rw [Nat.shiftLeft_eq]; exact Nat.le_trans hm (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
        unfold Lua.Vm.Fn.Fixdfdi.S truncInt? at hfix
        rw [hc] at hfix
        simp only [he, ite_true] at hfix
        split at hfix
        · rename_i hr
          have h2 := congrArg BitVec.toInt hfix
          rw [BitVec.toInt_ofInt, toInt_imm b hb] at h2
          rw [Int.bmod_eq_of_le (by omega) (by omega)] at h2
          unfold sgnApply at h2; split at h2 <;> omega
        · split at hfix
          · exact H.sat_lo hfix
          · exact H.sat_hi hfix
      · -- integral below `2^53`: `X` is `normalize n 0`
        have hfl := SfRef.floor_cls X
        rw [hc, hF] at hfl
        simp only [he, ite_false] at hfl
        generalize hN : m / 2 ^ (-e).toNat + (if s = true ∧ m % 2 ^ (-e).toNat ≠ 0 then 1 else 0) = N at hfl
        have hNm : N ≤ m := by
          have hP2 : 2 ≤ 2 ^ (-e).toNat := by
            calc 2 = 2 ^ 1 := rfl
              _ ≤ 2 ^ (-e).toNat := Nat.pow_le_pow_right (by decide) (by omega)
          rw [← hN]
          generalize 2 ^ (-e).toNat = P at hP2 ⊢
          have hd := Nat.div_add_mod m P
          have hr : m % P < P := Nat.mod_lt m (by omega)
          have hq := Nat.mul_le_mul_right (m / P) hP2
          generalize m / P = q at hd hq ⊢
          generalize m % P = r at hd hr ⊢
          split <;> rename_i hs
          · have := hs.2; omega
          · omega
        have hlt := hok.lt
        have hjn : (BitVec.ofInt 64 (sgnApply s N)).toInt = sgnApply s N := by
          rw [BitVec.toInt_ofInt, Int.bmod_eq_of_le] <;> (unfold sgnApply; split <;> omega)
        have hj : X = F64.ofInt (BitVec.ofInt 64 (sgnApply s N)) := by
          rw [hfl]; unfold F64.ofInt; rw [hjn]
        have hfx := ofInt_exact (BitVec.ofInt 64 (sgnApply s N)) (by
          rw [hjn]; unfold sgnApply; split <;> omega)
        rw [hj] at hfix
        unfold Lua.Vm.Fn.Fixdfdi.S at hfix
        rw [hfx] at hfix
        dsimp only at hfix
        rw [if_pos (by rw [hjn]; unfold sgnApply; split <;> omega), BitVec.ofInt_toInt] at hfix
        rw [hj, hfix]; exact H.ofInt_refl
  · intro hr
    obtain ⟨hn, hcl⟩ := eq_cls hr
    rcases hcl with h | ⟨a, c, hx, -⟩
    · rw [cls_inj h hn]; exact H.ofInt_ok
    · have hX : X = F64.zero a := cls_inj (by rw [hx, zero_cls]) (by rw [hx]; simp)
      subst hX; rw [← H.zero_ok]; exact hr

/-- **`EqiFlt_Statement`**: `δ .eq` of a float and an 8-bit immediate is
`luai_numeq` with the immediate's conversion. -/
theorem eqiFlt_proved : EqiFlt_Statement := by
  intro x n b hb
  have hx := toModel_toBits x
  generalize x.toBits.toBitVec = X at hx
  subst hx
  have hofI : ofI (immW b) = F64.toModel (F64.ofInt (immW b)) := (toModel_ofInt _).symm
  rw [hofI, ← F64.eq_eq_model, ← f2iEqW_eq X b hb]
  simp only [δ, Value.rawEq, eqNum, Numeral.tointegerns]
  unfold flttointeger numberToInteger f2iEqW
  dsimp only
  rw [← SfRef.floor_model X, ← F64.eq_eq_model, ← toModel_max, ← toModel_min, ← F64.le_eq_model,
    ← F64.lt_eq_model]
  by_cases h1 : F64.eq X (SfRef.floor X) = true <;>
    by_cases h2 : F64.le 0xc3e0000000000000#64 (SfRef.floor X) = true <;>
    by_cases h3 : F64.lt (SfRef.floor X) 0x43e0000000000000#64 = true <;>
    simp only [h1, h2, h3, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true,
      ite_true, ite_false, and_self, and_true, and_false]
  rw [← fixdfdi_model _ (by rw [← toModel_min, ← F64.le_eq_model]; exact h2)]

end Lua.Vm.Sim.At

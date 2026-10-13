import Lua.Vm.Fn.Divdf3
import Lua.Vm.Fn.SfRefMul
import Lua.Num.SfRefDiv

/-!
# `__divdf3` against `SfRef.div` (lane float-sf4, (b1))

The lifted function `Lua.Vm.Fn.Divdf3.F` (`scripts/gen_lua_fn.py`: 77 nodes,
`__udivdi3`/`__umoddi3`/`__muldi3`/`__clzdi2` as call nodes, the class switch
through two jump tables; `Divdf3.sum` says the machine computes it) is
`SfRef.div` (`Lua/Num/SfRefDiv.lean`, soft-fp's `_FP_DIV`); with (b2)
`SfRef.div_eq` it is `F64.div` (`spec_proved`).

* **The word lens** (`DivLens`): `SfLens`/`MulLens`'s normal form plus the
  word operations `udiv_qrnnd` runs, each to the reference's own form
  (`nf_wsub`, `nf_wadd`, `nf_wmul`, `nf_udivT`, `nf_umod`, `nf_shl32`), so a
  half step of the machine and `SfRef.qrHalf` meet leaf by leaf.
* **Stages**: the pack (`g_e258`, `g_e0c8`, `g_e22c`: `SfRef.packCanon`),
  the low digit (`g_e1c4`), the high digit (`g_e178`), the divide's entry
  (`g_e114`: `SfRef.divNorm`).
* **Chambers**: one per pair of operand classes, emitted by the class-pair
  chamber generator `sdc_chambers`, the cover `G_eq` and `F_eq_ref`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens Lua.Vm.Fn.MulLens

namespace Lua.Vm.Fn.Divdf3
open Lua.Num

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-- The pack leaf (`_FP_PACK_RAW_D`). -/
theorem nf_df4c (s : Nat) (r : BitVec 64) {F E S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002df4c s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002df4c; exact pack_eq hE hF hS

/-- The signed infinity leaf. -/
theorem nf_df68 (s : Nat) (r : BitVec 64) {S : Nat} (hS : S < 2) :
    N_8002df68 s r (BitVec.ofNat 64 S) = BitVec.ofNat 64 (S * 2 ^ 63 + 2047 * 2 ^ 52 + 0) := by
  unfold N_8002df68
  rw [show ((0#64) + sign_extend (m := 64) (0x7ff#12) : BitVec 64) = BitVec.ofNat 64 2047 by decide,
    show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = BitVec.ofNat 64 0 by decide]
  exact pack_eq (by decide) (by decide) hS

attribute [local irreducible] SfRef.roundPack SfRef.rto
irreducible_nodes Lua.Vm.Fn.Divdf3

/-! ## The pack stage (`_FP_PACK_CANONICAL`) -/

theorem g_e258_0 (s : Nat) (r : BitVec 64) {R S : Nat} (hS : S < 2) (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e258 s r (BitVec.ofNat 64 S) (ew (-((0 : Nat) : Int))) (BitVec.ofNat 64 R) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R 1) := by
  have hF : SfRef.rto R 1 < 2 ^ 55 := SfRef.rto_lt (by decide) (by simpa using hR2)
  sm_go []
  all_goals sm_close [nf_df4c]

theorem g_e258_1 (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD0 : 1 ≤ D) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e258 s r (BitVec.ofNat 64 S) (ew (-(D : Int))) (BitVec.ofNat 64 R) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  have hF : SfRef.rto R (1 + D) < 2 ^ 55 :=
    SfRef.rto_lt (by decide) (Nat.lt_of_lt_of_le hR2 (Nat.pow_le_pow_right (by decide) (by omega)))
  have hF1 : D ≤ 55 ∨ SfRef.rto R (1 + D) = 1 := by
    by_cases h : D ≤ 55
    · exact Or.inl h
    · exact Or.inr (SfRef.rto_big (by omega)
        (Nat.lt_of_lt_of_le hR2 (Nat.pow_le_pow_right (by decide) (by omega))))
  sm_go []
  all_goals sm_close [nf_df4c]

theorem g_e258 (s : Nat) (r : BitVec 64) {R D S : Nat} (hS : S < 2) (hD : D ≤ 2 ^ 20)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    N_8002e258 s r (BitVec.ofNat 64 S) (ew (-(D : Int))) (BitVec.ofNat 64 R) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto R (1 + D)) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD0
  · exact g_e258_0 s r hS hR1 hR2
  · exact g_e258_1 s r hS hD0 hD hR1 hR2

/-- `addi a1, a2, 1023` on an exponent word. -/
theorem ew_bias (x : Int) : ew x + sign_extend (m := 64) (0x3ff#12) = ew (x + 1023) := by
  rw [show (sign_extend (m := 64) (0x3ff#12) : BitVec 64) = BitVec.ofNat 64 1023 by decide]
  exact nf_ew_addc' x 1023

/-- `bgtz` on a non-positive exponent word. -/
theorem slt0_ew_neg {D : Nat} (h : D < 2 ^ 62) : zopz0zI_s (0#64) (ew (-(D : Int))) = false := by
  rw [ew_def, slt_int', toInt_ofInt_small (by omega) (by omega)]
  simp only [BitVec.toInt_zero, decide_eq_false_iff_not]; omega

/-- **The pack stage** (`0x8002e22c`'s exponent test `bgtz R_e + 1023`, then
`0x8002e0c8` or `0x8002e258`) is `_FP_PACK_CANONICAL`. -/
theorem g_pack (s : Nat) (r : BitVec 64) {R S : Nat} (e : Int) (hS : S < 2) (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19)
    (hR1 : 2 ^ 55 ≤ R) (hR2 : R < 2 ^ 56) :
    (if zopz0zI_s (0#64) (ew e + sign_extend (m := 64) (0x3ff#12)) = true then
      N_8002e0c8 s r (BitVec.ofNat 64 S) (ew e + sign_extend (m := 64) (0x3ff#12)) (ew e) (BitVec.ofNat 64 R)
    else N_8002e258 s r (BitVec.ofNat 64 S) (ew e + sign_extend (m := 64) (0x3ff#12)) (BitVec.ofNat 64 R)) =
      SfRef.packCanon (S = 1) e R := by
  unfold SfRef.packCanon
  by_cases h : 0 < e + 1023
  · obtain ⟨E, rfl⟩ : ∃ E : Nat, e = (E : Int) - ((1023 : Nat) : Int) := ⟨(e + 1023).toNat, by omega⟩
    rw [if_pos h]
    sm_go []
    all_goals sm_close [nf_df4c, nf_df68]
  · obtain ⟨D, rfl⟩ : ∃ D : Nat, e = -((1023 : Nat) : Int) - (D : Int) := ⟨(-(e + 1023)).toNat, by omega⟩
    rw [if_neg h, ew_bias, show -((1023 : Nat) : Int) - (D : Int) + 1023 = -(D : Int) by omega,
      if_neg (by rw [slt0_ew_neg (by omega)]; decide), g_e258 s r hS (by omega) hR1 hR2]
    congr 2; omega

theorem pow32_mul {q : Nat} (h : q < 2 ^ 32) : q * 2 ^ 32 < 2 ^ 64 := by
  have := Nat.mul_lt_mul_of_pos_right h (Nat.two_pow_pos 32)
  rwa [← Nat.pow_add] at this

/-- Two 32-bit digits make a word (`omega` sees `q1 · 2^32` as one atom). -/
theorem digits_lt {q1 q0 : Nat} (hq1 : q1 < 2 ^ 32) (hq0 : q0 < 2 ^ 32) : q1 * 2 ^ 32 + q0 < 2 ^ 64 := by
  have h := Nat.mul_le_mul_right (2 ^ 32) (show q1 + 1 ≤ 2 ^ 32 by omega)
  rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_add] at h
  obtain ⟨X, hX⟩ : ∃ X, q1 * 2 ^ 32 = X := ⟨_, rfl⟩
  rw [hX] at h ⊢
  omega

/-- `slli 32`. -/
theorem nf_sll32 (q : Nat) :
    shift_bits_left (BitVec.ofNat 64 q) (Sail.BitVec.extractLsb (0x20#6) 5 0) = BitVec.ofNat 64 (q * 2 ^ 32) := by
  rw [sll_lit, show (0x20#6 : BitVec 6).toNat = 32 from rfl, nf_shl]

/-- `or` of two disjoint words. -/
theorem nf_or_disj {a b : Nat} (h : a ||| b < 2 ^ 64) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt h]

/-- `sub` of two words. -/
theorem nf_wsub {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 ((x + 2 ^ 64 - y) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    BitVec.toNat_ofNat, Nat.mod_mod]
  congr 1; omega

/-- `snez` of a word. -/
theorem nf_snez (z : Nat) (hz : z < 2 ^ 64) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (BitVec.ofNat 64 z))) =
      BitVec.ofNat 64 (if z = 0 then 0 else 1) := by
  rw [nf_zext_bool, ult_nat]
  by_cases h : z = 0
  · subst h; rfl
  · rw [if_neg h, if_pos]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq, Nat.mod_eq_of_lt hz]; omega

/-- `0x8002e22c`'s word: the two digits, `R_f = q | (r != 0)`. -/
theorem w_e22c {q1 q0 x y : Nat} (hq1 : q1 < 2 ^ 32) (hq0 : q0 < 2 ^ 32) (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    ((shift_bits_left (BitVec.ofNat 64 q1) (Sail.BitVec.extractLsb (0x20#6) 5 0)) ||| BitVec.ofNat 64 q0) |||
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (BitVec.ofNat 64 x - BitVec.ofNat 64 y)))) =
      BitVec.ofNat 64 ((q1 * 2 ^ 32 + q0) ||| (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1)) := by
  have h1 := pow32_mul hq1
  have hQ : q1 * 2 ^ 32 + q0 < 2 ^ 64 := digits_lt hq1 hq0
  have hb : (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1) < 2 ^ 64 := by split <;> decide
  have hQb : (q1 * 2 ^ 32 + q0) ||| (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1) < 2 ^ 64 := by
    split
    · rw [Nat.or_zero]; exact hQ
    · rw [SfRef.lor_one]; omega
  rw [nf_sll32, nf_or_disj (by rw [SfRef.or_low32 _ _ hq0]; exact hQ) h1 (by omega), SfRef.or_low32 _ _ hq0,
    nf_wsub hx hy, nf_snez _ (Nat.mod_lt _ (by decide)), nf_or_disj hQb hQ hb]

/-- **The quotient's word and the pack** (`0x8002e22c`): `_FP_PACK_CANONICAL`
of `R_f = (q1 · 2^32 + q0) | (r != 0)`. -/
theorem g_e22c (s : Nat) (r : BitVec 64) (v8 v9 v19 : BitVec 64) {S q1 q0 x y : Nat} (e : Int) (hS : S < 2)
    (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19) (hq1 : q1 < 2 ^ 32) (hq0 : q0 < 2 ^ 32) (hx : x < 2 ^ 64)
    (hy : y < 2 ^ 64) (hR1 : 2 ^ 55 ≤ q1 * 2 ^ 32 + q0) (hR2 : q1 * 2 ^ 32 + q0 < 2 ^ 56) :
    N_8002e22c s r (BitVec.ofNat 64 S) v8 v9 (ew e) (BitVec.ofNat 64 q0) (BitVec.ofNat 64 x) (BitVec.ofNat 64 y)
        (BitVec.ofNat 64 q1) v19 =
      SfRef.packCanon (S = 1) e ((q1 * 2 ^ 32 + q0) ||| (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1)) := by
  unfold N_8002e22c
  rw [w_e22c hq1 hq0 hx hy]
  have hb : 2 ^ 55 ≤ (q1 * 2 ^ 32 + q0) ||| (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1) ∧
      (q1 * 2 ^ 32 + q0) ||| (if (x + 2 ^ 64 - y) % 2 ^ 64 = 0 then 0 else 1) < 2 ^ 56 := by
    split
    · simp only [Nat.or_zero]; omega
    · rw [SfRef.lor_one]; omega
  exact g_pack s r e hS he1 he2 hb.1 hb.2

/-! ## The word lens of `udiv_qrnnd` -/

theorem nf_wadd (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 ((a + b) % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem nf_wmul (a b : Nat) : BitVec.ofNat 64 a * BitVec.ofNat 64 b = BitVec.ofNat 64 (a * b % 2 ^ 64) := by
  apply BitVec.eq_of_toNat_eq; simp
theorem nf_udivT {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (hb0 : 0 < b) :
    Lua.Vm.Sim.Kit.udivT (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (a / b) := by
  rw [Lua.Vm.Sim.Kit.udivT_ne (fun h => by
    have := congrArg BitVec.toNat h; simp [Nat.mod_eq_of_lt hb] at this; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_udiv, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) ha)]
theorem nf_umod {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a % BitVec.ofNat 64 b = BitVec.ofNat 64 (a % b) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) ha)]
theorem sx_sd (x : BitVec 64) : sign_extend (m := 64) (Vsa.Sim.sdData_val x : BitVec (8 * 8)) = x := by
  rw [sext64_self, Lua.Vm.Sim.sdData_id]

/-- `0x8002e22c` reads the remainder's words only through their difference. -/
theorem e22c_diff (s : Nat) (r : BitVec 64) (v6 v8 v9 v12 v13 v14 v16 v18 v19 : BitVec 64) :
    N_8002e22c s r v6 v8 v9 v12 v13 v14 v16 v18 v19 = N_8002e22c s r v6 v8 v9 v12 v13 (v14 - v16) 0#64 v18 v19 := by
  unfold N_8002e22c; rw [BitVec.sub_zero]

/-- `0x8002e1c4` reads the first digit's remainder words only through their difference. -/
theorem e1c4_diff (s : Nat) (r : BitVec 64) (v6 v8 v9 v12 v14 v15 v18 v19 : BitVec 64) :
    N_8002e1c4 s r v6 v8 v9 v12 v14 v15 v18 v19 = N_8002e1c4 s r v6 v8 v9 v12 0#64 (v15 - v14) v18 v19 := by
  unfold N_8002e1c4; rw [BitVec.sub_zero]

theorem nf_dec1 (q : Nat) :
    BitVec.ofNat 64 q + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 ((q + (2 ^ 64 - 1)) % 2 ^ 64) := by
  rw [show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 1) by decide, nf_wadd]
theorem nf_dec2 (q : Nat) :
    BitVec.ofNat 64 q + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 ((q + (2 ^ 64 - 2)) % 2 ^ 64) := by
  rw [show (sign_extend (m := 64) (0xffe#12) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - 2) by decide, nf_wadd]
theorem nf_carry {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b))) == 0#64) =
      decide (¬ a < b) := by
  rw [nf_zext_bool, nf_ult ha hb]
  by_cases h : a < b <;> simp [h]

theorem fcongr2 {α β γ : Type} (f : α → β → γ) {a a' : α} {b b' : β} (h1 : a = a') (h2 : b = b') :
    f a b = f a' b' := by rw [h1, h2]

/-- **The machine's corrections of a digit estimate** (both halves of
`udiv_qrnnd` test `R ≥ m`, then `R + d ≥ m`, then the carry of `R + d`): for
an estimate `q` at most two too large (`N + m = q · d + R`, `R < d`,
`m < 2^64 ≤ 2 d`), every leaf the machine reaches is the exact digit and
remainder (`SfRef.qr_fix`'s argument in the machine's order). -/
theorem qr_fix_m {α : Type} (g : Nat → Nat → α) {N d q R m : Nat} (hd1 : 2 ^ 63 ≤ d) (hd2 : d < 2 ^ 64)
    (hR : R < d) (hm : m < 2 ^ 64) (hq : q < 2 ^ 64) (hNq : N + m = q * d + R) :
    (if m ≤ R then g q ((R + 2 ^ 64 - m) % 2 ^ 64)
     else if m ≤ (R + d) % 2 ^ 64 then g ((q + (2 ^ 64 - 1)) % 2 ^ 64) (((R + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64)
     else if ¬ (R + d) % 2 ^ 64 < R then
       g ((q + (2 ^ 64 - 2)) % 2 ^ 64) ((((R + d) % 2 ^ 64 + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64)
     else g ((q + (2 ^ 64 - 1)) % 2 ^ 64) (((R + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64)) = g (N / d) (N % d) := by
  have hd : 0 < d := by omega
  by_cases h1 : m ≤ R
  · rw [if_pos h1]
    obtain ⟨e1, e2⟩ := Prod.mk.inj (SfRef.divmod_of hd (show N = q * d + (R - m) by omega) (by omega))
    rw [e1, e2]; exact fcongr2 g rfl (by omega)
  rw [if_neg h1]
  have hq1 : 1 ≤ q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hNq; omega
    · exact h
  have e2 : (q - 1) * d = q * d - 1 * d := by rw [Nat.sub_mul]
  have e3 : 1 * d ≤ q * d := Nat.mul_le_mul_right d hq1
  -- one correction: `q - 1`, `R + d - m`
  have hone : m ≤ R + d → g ((q + (2 ^ 64 - 1)) % 2 ^ 64) (((R + d) % 2 ^ 64 + 2 ^ 64 - m) % 2 ^ 64) =
      g (N / d) (N % d) := by
    intro hge
    obtain ⟨f1, f2⟩ := Prod.mk.inj (SfRef.divmod_of hd (show N = (q - 1) * d + (R + d - m) by omega) (by omega))
    rw [f1, f2]
    refine fcongr2 g (by omega) ?_
    by_cases hc : R + d < 2 ^ 64
    · rw [Nat.mod_eq_of_lt hc]; omega
    · rw [show (R + d) % 2 ^ 64 = R + d - 2 ^ 64 by omega]; omega
  by_cases h2 : m ≤ (R + d) % 2 ^ 64
  · rw [if_pos h2]
    exact hone (by
      by_cases hc : R + d < 2 ^ 64
      · rw [Nat.mod_eq_of_lt hc] at h2; omega
      · omega)
  rw [if_neg h2]
  by_cases h3 : ¬ (R + d) % 2 ^ 64 < R
  · rw [if_pos h3]
    -- no carry, `R + d < m`: two corrections
    have hnc : R + d < 2 ^ 64 := by
      refine Classical.byContradiction fun hc => ?_
      apply h3; rw [show (R + d) % 2 ^ 64 = R + d - 2 ^ 64 by omega]; omega
    rw [Nat.mod_eq_of_lt hnc] at h2 ⊢
    have hq2 : 2 ≤ q := by
      refine Classical.byContradiction fun hc => ?_
      have : q = 1 := by omega
      subst this; simp at hNq; omega
    have f2 : (q - 2) * d = q * d - 2 * d := by rw [Nat.sub_mul]
    have f3 : 2 * d ≤ q * d := Nat.mul_le_mul_right d hq2
    obtain ⟨g1, g2⟩ := Prod.mk.inj (SfRef.divmod_of hd (show N = (q - 2) * d + (R + 2 * d - m) by omega)
      (by omega))
    rw [g1, g2]; exact fcongr2 g (by omega) (by omega)
  · rw [if_neg h3]
    -- a carry: `R + d ≥ 2^64 > m`
    exact hone (by
      refine Classical.byContradiction fun hc => ?_
      apply h3; rw [Nat.mod_eq_of_lt (by omega)]; omega)

/-- `R = ρ · 2^32 | 0`. -/
theorem lo_word {ρ : Nat} (h : ρ < 2 ^ 32) : ρ * 2 ^ 32 % 2 ^ 64 ||| 0 = ρ * 2 ^ 32 := by
  rw [Nat.or_zero, Nat.mod_eq_of_lt (pow32_mul h)]

/-- `0x8002e22c` with the remainder as one word. -/
theorem g_e22c0 (s : Nat) (r : BitVec 64) (v8 v9 v19 : BitVec 64) {S q1 q0 x : Nat} (e : Int) (hS : S < 2)
    (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19) (hq1 : q1 < 2 ^ 32) (hq0 : q0 < 2 ^ 32) (hx : x < 2 ^ 64)
    (hR1 : 2 ^ 55 ≤ q1 * 2 ^ 32 + q0) (hR2 : q1 * 2 ^ 32 + q0 < 2 ^ 56) :
    N_8002e22c s r (BitVec.ofNat 64 S) v8 v9 (ew e) (BitVec.ofNat 64 q0) (BitVec.ofNat 64 x) 0#64
        (BitVec.ofNat 64 q1) v19 =
      SfRef.packCanon (S = 1) e ((q1 * 2 ^ 32 + q0) ||| (if x = 0 then 0 else 1)) := by
  rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    g_e22c s r v8 v9 v19 e hS he1 he2 hq1 hq0 hx (by decide) hR1 hR2,
    show (x + 2 ^ 64 - 0) % 2 ^ 64 = x by omega]

/-- `0x8002e22c` reads the remainder's words only through their difference. -/
theorem e22c_sub (s : Nat) (r : BitVec 64) (v6 v8 v9 v12 v13 v18 v19 : BitVec 64) {x y : Nat}
    (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    N_8002e22c s r v6 v8 v9 v12 v13 (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) v18 v19 =
      N_8002e22c s r v6 v8 v9 v12 v13 (BitVec.ofNat 64 ((x + 2 ^ 64 - y) % 2 ^ 64)) 0#64 v18 v19 := by
  unfold N_8002e22c; rw [BitVec.sub_zero, nf_wsub hx hy]

/-- **The low digit** (`0x8002e1c4`: `__udivdi3`, `__muldi3`, `__umoddi3` and
the corrections): `udiv_qrnnd`'s second half, the exact digit and remainder
of `r1 · 2^32` by `d`, then the pack. -/
theorem g_e1c4 (s : Nat) (r : BitVec 64) {S d r1 q1 : Nat} (e : Int) (hS : S < 2) (hd1 : 2 ^ 63 ≤ d)
    (hd2 : d < 2 ^ 64) (hr1 : r1 < d) (hq1 : q1 < 2 ^ 32) (he1 : -2 ^ 19 ≤ e) (he2 : e ≤ 2 ^ 19)
    (hQ1 : 2 ^ 55 ≤ q1 * 2 ^ 32 + r1 * 2 ^ 32 / d) (hQ2 : q1 * 2 ^ 32 + r1 * 2 ^ 32 / d < 2 ^ 56) :
    N_8002e1c4 s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 (d / 2 ^ 32)) (BitVec.ofNat 64 d) (ew e) 0#64
        (BitVec.ofNat 64 r1) (BitVec.ofNat 64 q1) (BitVec.ofNat 64 (d % 2 ^ 32)) =
      SfRef.packCanon (S = 1) e ((q1 * 2 ^ 32 + r1 * 2 ^ 32 / d) ||| (if r1 * 2 ^ 32 % d = 0 then 0 else 1)) := by
  have hdp : 0 < d / 2 ^ 32 := by omega
  have k := SfRef.qr_setup hd1 hd2 hr1 (show 0 < 2 ^ 32 by decide)
  have hRw := lo_word k.hρ
  have hNq := k.hNq
  have hR := k.hR
  have hlt := k.hlt
  rw [hRw, Nat.add_zero] at hNq
  rw [hRw] at hR
  rw [Nat.add_zero] at hlt
  unfold N_8002e1c4 N_8002e1e0 N_8002e1ec N_8002e1f0 N_8002e1fc N_8002e214 N_8002e224 N_8002e228 N_8002e338
  simp only [sx_sd, add0, BitVec.sub_zero]
  rw [nf_udivT (by omega) (by omega) hdp, nf_umod (by omega) (by omega), nf_wmul, nf_sll32, nf_wadd, nf_wadd,
    nf_dec1, nf_dec2]
  have hRl : r1 % (d / 2 ^ 32) * 2 ^ 32 < 2 ^ 64 := pow32_mul k.hρ
  have hMl : r1 / (d / 2 ^ 32) * (d % 2 ^ 32) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hRd : (r1 % (d / 2 ^ 32) * 2 ^ 32 + d) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  have hRdd : ((r1 % (d / 2 ^ 32) * 2 ^ 32 + d) % 2 ^ 64 + d) % 2 ^ 64 < 2 ^ 64 := Nat.mod_lt _ (by decide)
  rw [Lua.Vm.Fn.SfCmpLens.nf_uge hRl hMl, Lua.Vm.Fn.SfCmpLens.nf_uge hRd hMl, nf_carry hRd hRl, e22c_sub _ _ _ _ _ _ _ _ _ hRl hMl,
    e22c_sub _ _ _ _ _ _ _ _ _ hRd hMl, e22c_sub _ _ _ _ _ _ _ _ _ hRdd hMl]
  simp only [decide_eq_true_eq]
  refine (qr_fix_m (fun q0 x => N_8002e22c s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 (d / 2 ^ 32))
      (BitVec.ofNat 64 d) (ew e) (BitVec.ofNat 64 q0) (BitVec.ofNat 64 x) 0#64 (BitVec.ofNat 64 q1)
      (BitVec.ofNat 64 (d % 2 ^ 32))) (N := r1 * 2 ^ 32) hd1 hd2 hR hMl k.hq hNq).trans ?_
  exact g_e22c0 s r _ _ _ e hS he1 he2 hq1 hlt (Nat.lt_trans (Nat.mod_lt _ (by omega)) hd2)
    hQ1 hQ2

end Lua.Vm.Fn.Divdf3

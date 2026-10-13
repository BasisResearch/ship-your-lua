import Lua.Vm.Fn.Subdf3
import Lua.Vm.Fn.SfLens
import Lua.Vm.Fn.Spec
import Lua.Num.SfRefSpec

/-!
# `__subdf3` against `SfRef.sub` (round 5, B-SFREF (b1))

The same chamber route as `__adddf3` (`Lua/Vm/Fn/SfRefAdd.lean`) on the
separately compiled `__subdf3` DAG: soft-fp's `_FP_SUB` tests `b` for NaN,
flips `b`'s sign, and runs `_FP_ADD_INTERNAL`'s code again at other
addresses. The stages are the add ones at this DAG's nodes (pack `ea8c`,
join `ea50`, rounds `efc8`/`ee98`/`ed4c`/`ed38`, difference `ecd4`, clz
`eaf4`, renormalised rounds `ec00`/`eb28`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens

namespace Lua.Vm.Fn.Subdf3
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedVariables false

theorem ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by rw [h]

/-! ## Packs and joins -/

theorem nf_ea8c (m : Mem) (s : Nat) (r : BitVec 64) {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002ea8c m s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002ea8c; exact pack_eq hE hF hS
theorem nf_eb90 (m : Mem) (s : Nat) (r : BitVec 64) {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002eb90 m s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002eb90; exact pack_eq hE hF hS
theorem nf_ec40 (m : Mem) (s : Nat) (r : BitVec 64) {E S : Nat} (hE : E < 2048) (hS : S < 2) :
    N_8002ec40 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) = BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + 0) := by
  unfold N_8002ec40
  rw [show ((0#64) + sign_extend (m := 64) (0x000#12)) = BitVec.ofNat 64 0 by decide, add0]
  exact pack_eq hE (by decide) hS
theorem nf_ec8c (m : Mem) (s : Nat) (r : BitVec 64) : N_8002ec8c m s r = BitVec.ofNat 64 9221120237041090560 := by
  unfold N_8002ec8c; decide

theorem nf_ea50_inf (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E = 2047) (hf : f / 8 = 0)
    (hf2 : f < 2 ^ 64) (hS : S < 2) :
    N_8002ea50 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) =
      BitVec.ofNat 64 (S * 2 ^ 63 + 2047 * 2 ^ 52) := by
  sf_go []
  all_goals sf_close [nf_ea8c]
theorem nf_ea50_nan (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E = 2047) (hf : f / 8 ≠ 0)
    (hf2 : f < 2 ^ 64) (hS : S < 2) :
    N_8002ea50 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) = 9221120237041090560#64 := by
  sf_go []
  all_goals sf_close [nf_ea8c]
theorem nf_ea50 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E ≤ 2046) (hf : f < 2 ^ 64)
    (hS : S < 2) :
    N_8002ea50 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + f / 8 % 2 ^ 52) := by
  sf_go []
  all_goals sf_close [nf_ea8c]

/-! ## Round stages -/

open Lua.Num in
theorem g_efc8 (m : Mem) (s : Nat) (r : BitVec 64) {E fa S fb : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hX : fa < 2 ^ 52) (hY : fb < 2 ^ 52) :
    N_8002efc8 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.roundPack (S = 1) E (2 ^ 55 + (8 * fa + 8 * fb) / 2) := by
  sf_go [N_8002ea50]
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem g_ee98 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 55) :
    N_8002ee98 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) =
      SfRef.roundPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002ea50]
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem g_ed4c (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 2 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf1 : 2 ^ 55 ≤ f) (hf : f < 2 ^ 56) :
    N_8002ed4c m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) =
      SfRef.roundPack (S = 1) E (SfRef.rto (2 ^ 55 + f) 1) := by
  sf_go [N_8002ea50]
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem g_ed38 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 56) :
    N_8002ed38 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 f) =
      SfRef.carryPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002ee98, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ee98, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem g_ec00 (m : Mem) (s : Nat) (r : BitVec 64) {z F E S : Nat} (hz : z < E) (hE : E ≤ 2046) (hS : S < 2)
    (hF1 : 2 ^ 55 ≤ F) (hF : F < 2 ^ 56) :
    N_8002ec00 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) (E - z) F := by
  sf_go []
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
/-- The subnormal round (`0x8002ec64`), no rounding increment. -/
theorem g_ec64 (m : Mem) (s : Nat) (r : BitVec 64) {R S : Nat} (hR : R ≤ 2 ^ 55) (hS : S < 2)
    (h8 : R % 8 = 0 ∨ R % 16 = 4) :
    N_8002ec64 m s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 R) = SfRef.roundPack (S = 1) 0 R := by
  sf_go []
  all_goals sf_close0 [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
/-- The subnormal round (`0x8002eb50`), `R % 8 ≠ 0`. -/
theorem g_eb50 (m : Mem) (s : Nat) (r : BitVec 64) {R S : Nat} (hR : R ≤ 2 ^ 55) (hS : S < 2)
    (h8 : R % 8 ≠ 0) :
    N_8002eb50 m s r (BitVec.ofNat 64 S) (BitVec.ofNat 64 R) = SfRef.roundPack (S = 1) 0 R := by
  sf_go [N_8002ec64]
  all_goals (try simp (disch := omega) only [g_ec64])
  all_goals (try simp (disch := omega) only [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan])
  all_goals (try rw [Nat.div_eq_of_lt (by omega : R + 4 < 72057594037927936), Nat.mul_zero, Nat.zero_add])
  all_goals (rw [SfRef.roundPack_up (by omega) (by omega) (by omega), bits_nf]
             apply ofNat_congr
             rw [Nat.zero_sub, Nat.zero_mul, Nat.zero_add]
             rcases (by omega : S = 0 ∨ S = 1) with h | h <;> subst h <;> simp only [decide_true, decide_false,
               ite_true, ite_false, Bool.false_eq_true, Nat.zero_mul, Nat.one_mul, show ¬ (0 : Nat) = 1 by decide] <;>
               omega)

open Lua.Num in
theorem g_eb28 (m : Mem) (s : Nat) (r : BitVec 64) {z F E S : Nat} (hz : E ≤ z) (hz2 : z ≤ 55) (hE1 : 1 ≤ E)
    (hS : S < 2) (hF : F < 2 ^ 56) :
    N_8002eb28 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto F (z - E + 1)) := by
  have hR := SfRef.rto_le_half (n := F) (k := z - E + 1) (by omega)
  sf_go [N_8002ec64, N_8002eb50]
  all_goals (try simp (disch := omega) only [g_ec64, g_eb50])

open Lua.Num in
theorem g_eaf4 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hf0 : 0 < f) (hf : f < 2 ^ 55) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2) :
    N_8002eaf4 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) = SfRef.normPack (S = 1) E f := by
  have hL : f.log2 < 55 := (Nat.log2_lt (by omega)).2 hf
  have hN := SfRef.norm_bounds hf0 (by omega)
  unfold N_8002eaf4 N_8002eb10
  sf_reload
  sf_nf
  rw [show 63 - f.log2 - 8 = 55 - f.log2 by omega]
  unfold SfRef.normPack
  split
  · rw [g_ec00 _ _ _ (by omega) hE hS hN.1 hN.2, if_pos (by omega)]
  · rw [g_eb28 _ _ _ (by omega) (by omega) hE1 hS hN.2, if_neg (by omega),
      SfRef.rto_mul_pow _ _ _ (by omega), show 55 - f.log2 - (55 - f.log2 - E + 1) = E - 1 by omega]

open Lua.Num in
theorem g_ecd4 (m : Mem) (s : Nat) (r : BitVec 64) {f E Sg : Nat} (S : Nat) (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hS0 : 0 < S) (hS : S < 2 ^ 56) (hS8 : S % 8 = 0 ∨ S + 8 < 2 ^ 56) (hf : f < 2 ^ 64)
    (hfS : (f + 2 ^ 55) % 2 ^ 64 = S) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hSg : Sg < 2) :
    N_8002ecd4 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 Sg) (BitVec.ofNat 64 f) = SfRef.subPack (Sg = 1) E S := by
  sf_go [N_8002eaf4, N_8002ea50]
  all_goals (try simp (disch := omega) only [g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem g_ecd4s (m : Mem) (s : Nat) (r : BitVec 64) {X R E Sg : Nat} (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hR : R < 2 ^ 55 + X) (hS : 2 ^ 55 + X - R < 2 ^ 56) (hS8 : (2 ^ 55 + X - R) % 8 = 0 ∨ 2 ^ 55 + X - R + 8 < 2 ^ 56)
    (hX : X < 2 ^ 64) (hR2 : R ≤ 2 ^ 64) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hSg : Sg < 2) :
    N_8002ecd4 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 Sg) (BitVec.ofNat 64 X - BitVec.ofNat 64 R) =
      SfRef.subPack (Sg = 1) E (2 ^ 55 + X - R) := by
  rcases Nat.lt_or_ge X R with h | h
  · rw [nf_sub_wrap hR2 h]
    exact g_ecd4 m s r _ hs1 hs2 (by omega) hS hS8 (by omega) (by omega) hE1 hE hSg
  · rw [nf_sub h hX]
    exact g_ecd4 m s r _ hs1 hs2 (by omega) hS hS8 (by omega) (by omega) hE1 hE hSg

/-! ## Chambers (the effective operation after `_FP_SUB`'s sign flip) -/

open Lua.Num in
theorem ch_add_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 2047) (h2 : eb = 2047) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 ∧ fb = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_sub0 (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 0) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) 1 (8 * fa) (8 * fb) 0 := by
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_eq_norm (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (he : ea = eb) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) 0 := by
  subst he
  sf_go [N_8002efc8, N_8002ea50]
  all_goals (try simp (disch := omega) only [g_efc8])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_gt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb < ea) (h2 : ea = 2047) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ eb) (h2 : eb < ea) (h3 : ea ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) (ea - eb) := by
  have hR := SfRef.rto_lt_of (n := 2 ^ 55 + 8 * fb) (k := ea - eb) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ ea - eb → SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_gt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb : Nat) (hs : sa < 2) (hfa : fa < 2 ^ 52) (h1 : eb = 0) (h2 : 0 < ea) (h3 : ea ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * 0)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) 0 (ea - 1) := by
  try simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_gt0a (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (hb : 0 < fb) (h1 : eb = 0) (h2 : ea = 1) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h2; simp only [Nat.sub_self, SfRef.rto_zero]
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_gt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (hb : 0 < fb) (h1 : eb = 0) (h2 : 2 ≤ ea) (h3 : ea ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h1
  have hR := SfRef.rto_lt_of (n := 8 * fb) (k := ea - 1) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ ea - 1 → SfRef.rto (8 * fb) (ea - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_lt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea < eb) (h2 : eb = 2047) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      if fb = 0 then F64.infty (sa = 1) else F64.qnan := by
  subst h2
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea < eb) (h3 : eb ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) (eb - ea) := by
  have hR := SfRef.rto_lt_of (n := 2 ^ 55 + 8 * fa) (k := eb - ea) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ eb - ea → SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_lt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea eb fb : Nat) (hs : sa < 2) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 0 < eb) (h3 : eb ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 0) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * 0)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) 0 (eb - 1) := by
  subst h1
  try simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_lt0a (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha : 0 < fa) (h1 : ea = 0) (h2 : eb = 1) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_add_lt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha : 0 < fa) (h1 : ea = 0) (h2 : 2 ≤ eb) (h3 : eb ≤ 2046) :
    N_8002eaa0 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb)
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst h1
  have hR := SfRef.rto_lt_of (n := 8 * fa) (k := eb - 1) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ eb - 1 → SfRef.rto (8 * fa) (eb - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ed38, N_8002ea50, N_8002ed4c]
  all_goals (try simp (disch := omega) only [g_ed38, g_ed4c])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 2047) (h2 : eb = 2047) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      F64.qnan := by
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb < ea) (h2 : ea = 2047) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ eb) (h2 : eb < ea) (h3 : ea ≤ 2046) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) (ea - eb) := by
  have hR := SfRef.rto_le_half (n := 2 ^ 55 + 8 * fb) (k := ea - eb) (by omega)
  have hR0 : 1 ≤ SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ ea - eb → SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_eq_z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fa = fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      F64.zero false := by
  subst he hf
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_eq_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fb < fa) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) 0 := by
  subst he
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_eq_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fa < fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) 0 := by
  subst he
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub0_z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fa = fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      F64.zero false := by
  subst hf
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub0_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fb < fa) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) 1 (8 * fa) (8 * fb) 0 := by
  have hlog : (8 * fa - 8 * fb).log2 < 55 := (Nat.log2_lt (by omega)).2 (by omega)
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub0_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fa < fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) 1 (8 * fb) (8 * fa) 0 := by
  have hlog : (8 * fb - 8 * fa).log2 < 55 := (Nat.log2_lt (by omega)).2 (by omega)
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea < eb) (h2 : eb = 2047) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      if fb = 0 then F64.infty (sb = 1) else F64.qnan := by
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : 0 < ea) (h3 : ea ≤ 2046) (hb : fb = 0) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst hb
  simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt0a_ge (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : ea = 1) (hb : 0 < fb) (hf : fb ≤ fa) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  have hk : ea - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt0a_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : ea = 1) (hf : fa < fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  have hk : ea - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_gt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : 2 ≤ ea) (h3 : ea ≤ 2046) (hb : 0 < fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h1
  have hR := SfRef.rto_le_half (n := 8 * fb) (k := ea - 1) (by omega)
  have hR0 : 1 ≤ SfRef.rto (8 * fb) (ea - 1) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ ea - 1 → SfRef.rto (8 * fb) (ea - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea < eb) (h3 : eb ≤ 2046) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) (eb - ea) := by
  have hR := SfRef.rto_le_half (n := 2 ^ 55 + 8 * fa) (k := eb - ea) (by omega)
  have hR0 : 1 ≤ SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ eb - ea → SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 0 < eb) (h3 : eb ≤ 2046) (ha : fa = 0) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst ha
  simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt0a_ge (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 1) (ha : 0 < fa) (hf : fa ≤ fb) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt0a_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 1) (hf : fb < fa) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

open Lua.Num in
theorem ch_sub_lt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 2 ≤ eb) (h3 : eb ≤ 2046) (ha : 0 < fa) :
    N_8002ea44 m s r (BitVec.ofNat 64 1) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sb)
          (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofNat 64 sa) (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst h1
  have hR := SfRef.rto_le_half (n := 8 * fa) (k := eb - 1) (by omega)
  have hR0 : 1 ≤ SfRef.rto (8 * fa) (eb - 1) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ eb - 1 → SfRef.rto (8 * fa) (eb - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002ecd4, N_8002ea50, N_8002eaf4]
  all_goals (try simp (disch := omega) only [g_ecd4s, g_eaf4])
  all_goals sf_close [nf_ea8c, nf_eb90, nf_ec40, nf_ec8c, nf_ea50, nf_ea50_inf, nf_ea50_nan]

end Lua.Vm.Fn.Subdf3

import Lua.Vm.Fn.Adddf3
import Lua.Vm.Fn.SfLens

/-!
# `__adddf3` against `SfRef.add` (round 5, B-SFREF (b1))

The lifted function `Lua.Vm.Fn.Adddf3.F` (generated, equal to the machine by
level (a)) is `SfRef.add` (`Lua/Num/SfRef.lean`). The proof is by chambers of
`SfRef.addFields`; inside a chamber the DAG is explored by `sf_go`
(`Lua/Vm/Fn/SfLens.lean`) under the chamber's facts, down to its pack leaves
(`sf_close`) or to a round stage cut (`g_<pc>`, a lemma per machine round
site: the node equals `SfRef.roundPack` of its working mantissa).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Lua.Vm.Fn.SfLens

namespace Lua.Vm.Fn.Adddf3
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

/-! ## The unpacked entry -/

theorem F_unpack (m : Mem) (s : Nat) (r a b : BitVec 64) {sa ea fa sb eb fb : Nat}
    (hA : Fields a sa ea fa) (hB : Fields b sb eb fb) :
    F m s r a b =
      if sa = sb then
        N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb))
      else
        N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) := by
  obtain ⟨hsa, hea, hfa⟩ := hA
  obtain ⟨hsb, heb, hfb⟩ := hB
  unfold F
  rw [argX a, argX b, argF a, argF b, argA a, argA b, argE a, argE b, argM, add0,
    wsub_ofNat _ _ (by omega : a.toNat / 2 ^ 52 % 2048 < 2 ^ 31) (by omega : b.toNat / 2 ^ 52 % 2048 < 2 ^ 31)]
  simp only [hsa, hea, hfa, hsb, heb, hfb, beq_toNat]
  have : sa < 2 := by omega
  have : sb < 2 := by omega
  simp only [toNat_ofNat_lt (by omega : sa < 2 ^ 64), toNat_ofNat_lt (by omega : sb < 2 ^ 64), decide_eq_true_eq]


open Lua.Num in
/-! ## Pack leaves -/

theorem nf_db68 (m : Mem) (s : Nat) (r : BitVec 64) {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002db68 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 F) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002db68; exact pack_eq hE hF hS
theorem nf_d8b8 (m : Mem) (s : Nat) (r : BitVec 64) {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002d8b8 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 F) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002d8b8; exact pack_eq hE hF hS
theorem nf_da9c (m : Mem) (s : Nat) (r : BitVec 64) {E F S : Nat} (hE : E < 2048) (hF : F < 2 ^ 52) (hS : S < 2) :
    N_8002da9c m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 F) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + F) := by
  unfold N_8002da9c; exact pack_eq hE hF hS

theorem nf_dae0 (m : Mem) (s : Nat) (r : BitVec 64) : N_8002dae0 m s r = BitVec.ofNat 64 9221120237041090560 := by
  unfold N_8002dae0; decide

/-! ## The pack join (`_FP_PACK_SEMIRAW`'s pack, `0x8002d92c`) -/

theorem nf_d92c_inf (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E = 2047) (hf : f / 8 = 0)
    (hf2 : f < 2 ^ 64) (hS : S < 2) :
    N_8002d92c m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + 2047 * 2 ^ 52) := by
  sf_go []
  all_goals sf_close [nf_db68]
theorem nf_d92c_nan (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E = 2047) (hf : f / 8 ≠ 0)
    (hf2 : f < 2 ^ 64) (hS : S < 2) :
    N_8002d92c m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) = 9221120237041090560#64 := by
  sf_go []
  all_goals sf_close [nf_db68]
theorem nf_d92c (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE : E ≤ 2046) (hf : f < 2 ^ 64)
    (hS : S < 2) :
    N_8002d92c m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      BitVec.ofNat 64 (S * 2 ^ 63 + E * 2 ^ 52 + f / 8 % 2 ^ 52) := by
  sf_go []
  all_goals sf_close [nf_db68]

/-! ## Round stages: each node is `SfRef.roundPack` of its working mantissa -/

open Lua.Num in
theorem g_dc60 (m : Mem) (s : Nat) (r : BitVec 64) {E fa S fb : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hX : fa < 2 ^ 52) (hY : fb < 2 ^ 52) :
    N_8002dc60 m s r (BitVec.ofNat 64 E) (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 S) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.roundPack (S = 1) E (2 ^ 55 + (8 * fa + 8 * fb) / 2) := by
  sf_go [N_8002d92c]
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- `_FP_ROUND` with the carry out of the mantissa (`0x8002dd48`). -/
theorem g_dd48 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 55) :
    N_8002dd48 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002d92c]
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- The carry renormalisation then `_FP_ROUND` (`0x8002dbcc`). -/
theorem g_dbcc (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 2 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf1 : 2 ^ 55 ≤ f) (hf : f < 2 ^ 56) :
    N_8002dbcc m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E (SfRef.rto (2 ^ 55 + f) 1) := by
  sf_go [N_8002d92c]
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- The aligned-sum stage (`0x8002dbb8`): bit 55 set is the carry (`_FP_FRAC_SRS (R, 1)`,
then `R_e++`, ±∞ at `2047`), then `_FP_ROUND` and the pack. -/
theorem g_dbb8 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 56) :
    N_8002dbb8 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 S) =
      SfRef.carryPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002dd48, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dd48, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
theorem ch_eq_norm (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa fb : Nat) (hs : sa < 2) (he1 : 1 ≤ ea) (he2 : ea ≤ 2046)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - ea)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 ea) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) 0 := by
  sf_go [N_8002dc60]
  · sf_close [nf_db68, nf_d8b8, nf_da9c]
  · rw [g_dc60 _ _ _ (by omega) (by omega) hs hfa hfb]
    sf_close [nf_db68, nf_d8b8, nf_da9c]

open Lua.Num in
/-- Same signs, `eb < ea`, both normal: `B` aligned by `_FP_FRAC_SRS` (`k ≤ 56`) or
collapsed to its sticky bit (`k ≥ 57`, the folded `x + 5`). -/
theorem ch_add_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2) (h1 : 1 ≤ eb)
    (h2 : eb < ea) (h3 : ea ≤ 2046) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) (ea - eb) := by
  have hR := SfRef.rto_lt_of (n := 2 ^ 55 + 8 * fb) (k := ea - eb) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ ea - eb → SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fb < 2 ^ 57)
      (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002dbb8, N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_d92c]

open Lua.Num in
/-- Same signs, both exponents all ones. -/
theorem ch_add_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 2047) (h2 : eb = 2047) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 ∧ fb = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, both subnormal or zero. -/
theorem ch_add_sub0 (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 0) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) 1 (8 * fa) (8 * fb) 0 := by
  sf_go [N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `eb < ea = 2047`. -/
theorem ch_add_gt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb < ea) (h2 : ea = 2047) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `0 = eb < ea`, `b = 0`. -/
theorem ch_add_gt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (h1 : eb = 0) (h2 : 0 < ea) (h3 : ea ≤ 2046) :
    N_8002d904 m s r (BitVec.ofNat 64 0) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * 0)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) 0 (ea - 1) := by
  try simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `eb = 0 < ea = 1`: `b` subnormal, no shift. -/
theorem ch_add_gt0a (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (hb : 0 < fb) (h1 : eb = 0) (h2 : ea = 1) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h2; simp only [Nat.sub_self, SfRef.rto_zero]
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `eb = 0`, `2 ≤ ea`: `b` subnormal, aligned by `ea - 1`. -/
theorem ch_add_gt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (hb : 0 < fb) (h1 : eb = 0) (h2 : 2 ≤ ea) (h3 : ea ≤ 2046) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h1
  have hR := SfRef.rto_lt_of (n := 8 * fb) (k := ea - 1) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ ea - 1 → SfRef.rto (8 * fb) (ea - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `ea < eb = 2047`. -/
theorem ch_add_lt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea < eb) (h2 : eb = 2047) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      if fb = 0 then F64.infty (sa = 1) else F64.qnan := by
  subst h2
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `1 ≤ ea < eb ≤ 2046`: `A` aligned by `_FP_FRAC_SRS`. -/
theorem ch_add_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea < eb) (h3 : eb ≤ 2046) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) (eb - ea) := by
  have hR := SfRef.rto_lt_of (n := 2 ^ 55 + 8 * fa) (k := eb - ea) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ eb - ea → SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fa < 2 ^ 57)
      (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `ea = 0 < eb`, `a = 0`. -/
theorem ch_add_lt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea eb fb : Nat) (hs : sa < 2)
    (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 0 < eb) (h3 : eb ≤ 2046) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * 0))
          (BitVec.ofNat 64 0) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) 0 (eb - 1) := by
  subst h1
  try simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `ea = 0`, `eb = 1`: `a` subnormal, no shift. -/
theorem ch_add_lt0a (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha : 0 < fa) (h1 : ea = 0) (h2 : eb = 1) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Same signs, `ea = 0`, `2 ≤ eb`: `a` subnormal, aligned by `eb - 1`. -/
theorem ch_add_lt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa eb fb : Nat) (hs : sa < 2)
    (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (ha : 0 < fa) (h1 : ea = 0) (h2 : 2 ≤ eb) (h3 : eb ≤ 2046) :
    N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb)) =
      SfRef.addAligned (sa = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst h1
  have hR := SfRef.rto_lt_of (n := 8 * fa) (k := eb - 1) (m := 55) (by omega) (by omega)
  have hR1 : 57 ≤ eb - 1 → SfRef.rto (8 * fa) (eb - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002dbb8, N_8002d92c, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dbb8, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

/-! ## Different signs: the renormalisation stages -/

open Lua.Num in
/-- `_FP_ROUND` after the clz renormalisation (`0x8002da50`): `F` with its hidden
bit at `E - z`. -/
theorem g_da50 (m : Mem) (s : Nat) (r : BitVec 64) {z F E S : Nat} (hz : z < E) (hE : E ≤ 2046) (hS : S < 2)
    (hF1 : 2 ^ 55 ≤ F) (hF : F < 2 ^ 56) :
    N_8002da50 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) (E - z) F := by
  sf_go []
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- The subnormal result after the clz renormalisation (`0x8002d854`): a second
`_FP_FRAC_SRS` by `z - E + 1`, then `_FP_ROUND` at exponent `0`. -/
theorem g_d854 (m : Mem) (s : Nat) (r : BitVec 64) {z F E S : Nat} (hz : E ≤ z) (hz2 : z ≤ 55) (hE1 : 1 ≤ E)
    (hS : S < 2) (hF : F < 2 ^ 56) :
    N_8002d854 m s r (BitVec.ofNat 64 z) (BitVec.ofNat 64 F) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) 0 (SfRef.rto F (z - E + 1)) := by
  have hR := SfRef.rto_lt_of (n := F) (k := z - E + 1) (m := 55) (by omega) (by omega)
  sf_go []
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- The clz renormalisation (`0x8002d820`): `__clzdi2` (`clz64`) across the
frame spills, then the normal (`0x8002da50`) or subnormal (`0x8002d854`) round. -/
theorem g_d820 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hf0 : 0 < f) (hf : f < 2 ^ 55) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2) :
    N_8002d820 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) = SfRef.normPack (S = 1) E f := by
  have hL : f.log2 < 55 := (Nat.log2_lt (by omega)).2 hf
  have hN := SfRef.norm_bounds hf0 (by omega)
  unfold N_8002d820 N_8002d83c
  sf_reload
  sf_nf
  rw [show 63 - f.log2 - 8 = 55 - f.log2 by omega]
  unfold SfRef.normPack
  split
  · rw [g_da50 _ _ _ (by omega) hE hS hN.1 hN.2, if_pos (by omega)]
  · rw [g_d854 _ _ _ (by omega) (by omega) hE1 hS hN.2, if_neg (by omega),
      SfRef.rto_mul_pow _ _ _ (by omega), show 55 - f.log2 - (55 - f.log2 - E + 1) = E - 1 by omega]

open Lua.Num in
/-- The difference stage (`0x8002db28`): the machine's `f` is `S - 2^55` modulo
`2^64` (the hidden bit kept out); bit 55 set is the cancellation, renormalised
by `0x8002d820`; else `_FP_ROUND` (`0x8002db30`). -/
theorem g_db28 (m : Mem) (s : Nat) (r : BitVec 64) {f E Sg : Nat} (S : Nat) (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hS0 : 0 < S) (hS : S < 2 ^ 56) (hS8 : S % 8 = 0 ∨ S + 8 < 2 ^ 56) (hf : f < 2 ^ 64)
    (hfS : (f + 2 ^ 55) % 2 ^ 64 = S)
    (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hSg : Sg < 2) :
    N_8002db28 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 Sg) = SfRef.subPack (Sg = 1) E S := by
  sf_go [N_8002d820, N_8002d92c]
  all_goals (try simp (disch := omega) only [g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- The difference stage on the machine's `X - R` (a borrow wraps). -/
theorem g_db28s (m : Mem) (s : Nat) (r : BitVec 64) {X R E Sg : Nat} (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32)
    (hR : R < 2 ^ 55 + X) (hS : 2 ^ 55 + X - R < 2 ^ 56) (hS8 : (2 ^ 55 + X - R) % 8 = 0 ∨ 2 ^ 55 + X - R + 8 < 2 ^ 56)
    (hX : X < 2 ^ 64) (hR2 : R ≤ 2 ^ 64) (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hSg : Sg < 2) :
    N_8002db28 m s r (BitVec.ofNat 64 X - BitVec.ofNat 64 R) (BitVec.ofNat 64 E) (BitVec.ofNat 64 Sg) =
      SfRef.subPack (Sg = 1) E (2 ^ 55 + X - R) := by
  rcases Nat.lt_or_ge X R with h | h
  · rw [nf_sub_wrap hR2 h]
    exact g_db28 m s r _ hs1 hs2 (by omega) hS hS8 (by omega) (by omega) hE1 hE hSg
  · rw [nf_sub h hX]
    exact g_db28 m s r _ hs1 hs2 (by omega) hS hS8 (by omega) (by omega) hE1 hE hSg

open Lua.Num in
/-- Different signs, both exponents all ones. -/
theorem ch_sub_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 2047) (h2 : eb = 2047) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) = F64.qnan := by
  sf_go [N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `eb < ea = 2047`. -/
theorem ch_sub_gt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb < ea) (h2 : ea = 2047) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      if fa = 0 then F64.infty (sa = 1) else F64.qnan := by
  sf_go [N_8002d92c]
  all_goals (try simp (disch := omega) only [g_dbb8])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `1 ≤ eb < ea ≤ 2046`: `A − rto B k`. -/
theorem ch_sub_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ eb) (h2 : eb < ea) (h3 : ea ≤ 2046) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) (ea - eb) := by
  have hR := SfRef.rto_le_half (n := 2 ^ 55 + 8 * fb) (k := ea - eb) (by omega)
  have hR0 : 1 ≤ SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ ea - eb → SfRef.rto (2 ^ 55 + 8 * fb) (ea - eb) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fb < 2 ^ 57)
      (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, equal normal exponents, equal fractions: `+0`. -/
theorem ch_sub_eq_z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fa = fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      F64.zero false := by
  subst he hf
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, equal normal exponents, `fb < fa`. -/
theorem ch_sub_eq_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fb < fa) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (2 ^ 55 + 8 * fb) 0 := by
  subst he
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, equal normal exponents, `fa < fb`: the sign of `b`. -/
theorem ch_sub_eq_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea ≤ 2046) (he : ea = eb) (hf : fa < fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) 0 := by
  subst he
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, both subnormal or zero, equal fractions: `+0`. -/
theorem ch_sub0_z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fa = fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      F64.zero false := by
  subst hf
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, both subnormal, `fb < fa`. -/
theorem ch_sub0_gt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fb < fa) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) 1 (8 * fa) (8 * fb) 0 := by
  have hlog : (8 * fa - 8 * fb).log2 < 55 := (Nat.log2_lt (by omega)).2 (by omega)
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, both subnormal, `fa < fb`. -/
theorem ch_sub0_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (he : eb = 0) (hf : fa < fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) 1 (8 * fb) (8 * fa) 0 := by
  have hlog : (8 * fb - 8 * fa).log2 < 55 := (Nat.log2_lt (by omega)).2 (by omega)
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `ea < eb = 2047`. -/
theorem ch_sub_lt_nan (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea < eb) (h2 : eb = 2047) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      if fb = 0 then F64.infty (sb = 1) else F64.qnan := by
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `eb = 0 < ea`, `b = 0`. -/
theorem ch_sub_gt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : 0 < ea) (h3 : ea ≤ 2046) (hb : fb = 0) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst hb
  simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `eb = 0`, `ea = 1`, `fb ≤ fa`. -/
theorem ch_sub_gt0a_ge (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : ea = 1) (hb : 0 < fb) (hf : fb ≤ fa) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  have hk : ea - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `eb = 0`, `ea = 1`, `fa < fb`: the cancellation. -/
theorem ch_sub_gt0a_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : ea = 1) (hf : fa < fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  have hk : ea - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `eb = 0`, `2 ≤ ea`: `b` subnormal, aligned by `ea - 1`. -/
theorem ch_sub_gt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : eb = 0) (h2 : 2 ≤ ea) (h3 : ea ≤ 2046) (hb : 0 < fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sa = 1) ea (2 ^ 55 + 8 * fa) (8 * fb) (ea - 1) := by
  subst h1
  have hR := SfRef.rto_le_half (n := 8 * fb) (k := ea - 1) (by omega)
  have hR0 : 1 ≤ SfRef.rto (8 * fb) (ea - 1) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ ea - 1 → SfRef.rto (8 * fb) (ea - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fb < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `1 ≤ ea < eb ≤ 2046`: `B − rto A k`, the sign of `b`. -/
theorem ch_sub_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : 1 ≤ ea) (h2 : ea < eb) (h3 : eb ≤ 2046) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (2 ^ 55 + 8 * fa) (eb - ea) := by
  have hR := SfRef.rto_le_half (n := 2 ^ 55 + 8 * fa) (k := eb - ea) (by omega)
  have hR0 : 1 ≤ SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ eb - ea → SfRef.rto (2 ^ 55 + 8 * fa) (eb - ea) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 2 ^ 55 + 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `ea = 0 < eb`, `a = 0`. -/
theorem ch_sub_lt0z (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 0 < eb) (h3 : eb ≤ 2046) (ha : fa = 0) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst ha
  simp only [Nat.mul_zero, SfRef.rto_zero_n]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `ea = 0`, `eb = 1`, `fa ≤ fb`. -/
theorem ch_sub_lt0a_ge (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 1) (ha : 0 < fa) (hf : fa ≤ fb) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `ea = 0`, `eb = 1`, `fb < fa`: the cancellation. -/
theorem ch_sub_lt0a_lt (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : eb = 1) (hf : fb < fa) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  have hk : eb - 1 = 0 := by omega
  rw [hk]
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

open Lua.Num in
/-- Different signs, `ea = 0`, `2 ≤ eb`: `a` subnormal, aligned by `eb - 1`. -/
theorem ch_sub_lt0b (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2) (hss : sa ≠ sb)
    (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (h1 : ea = 0) (h2 : 2 ≤ eb) (h3 : eb ≤ 2046) (ha : 0 < fa) :
    N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb)) =
      SfRef.subMag (sb = 1) eb (2 ^ 55 + 8 * fb) (8 * fa) (eb - 1) := by
  subst h1
  have hR := SfRef.rto_le_half (n := 8 * fa) (k := eb - 1) (by omega)
  have hR0 : 1 ≤ SfRef.rto (8 * fa) (eb - 1) := SfRef.rto_pos (by omega)
  have hR1 : 57 ≤ eb - 1 → SfRef.rto (8 * fa) (eb - 1) = 1 := fun h =>
    SfRef.rto_big (by omega) (Nat.lt_of_lt_of_le (by omega : 8 * fa < 2 ^ 57) (Nat.pow_le_pow_right (by decide) h))
  sf_go [N_8002db28, N_8002d92c, N_8002d820]
  all_goals (try simp (disch := omega) only [g_db28s, g_d820])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_dae0, nf_d92c, nf_d92c_inf, nf_d92c_nan]

/-! ## The chamber cover -/

/-- The reference's branches, with the fields' classes decided. -/
macro "sf_rhs" : tactic => `(tactic| (
  unfold Lua.Num.SfRef.addFields
  dsimp only
  try simp only [eq_self_iff_true, ite_true, ite_false, decide_eq_decide]
  try simp (disch := omega) only [if_pos, if_neg]
  try simp only [Lua.Num.SfRef.mant]
  try simp (disch := omega) only [if_pos, if_neg, Nat.max_eq_left, Nat.max_eq_right]))

open Lua.Num in
/-- **(b1) for `__adddf3`**: below the unpacking, the lifted function is the
reference on the operands' fields, chamber by chamber. -/
theorem cover (m : Mem) (s : Nat) (r : BitVec 64) (sa ea fa sb eb fb : Nat) (hs : sa < 2) (hsb : sb < 2)
    (hea : ea < 2048) (heb : eb < 2048) (hfa : fa < 2 ^ 52) (hfb : fb < 2 ^ 52) (hs1 : 48 ≤ s) (hs2 : s ≤ 2 ^ 32) :
    (if sa = sb then
        N_8002d904 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 (2 ^ 52 - 1)) (BitVec.ofNat 64 (8 * fa))
          (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea) (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 (8 * fb))
      else
        N_8002d7e4 m s r (BitVec.ofNat 64 fb) (BitVec.ofNat 64 sb) (BitVec.ofNat 64 (2 ^ 52 - 1))
          (BitVec.ofNat 64 (8 * fa)) (BitVec.ofNat 64 fa) (BitVec.ofNat 64 ea)
          (BitVec.ofInt 64 ((ea : Int) - eb)) (BitVec.ofNat 64 sa) (BitVec.ofNat 64 eb) (BitVec.ofNat 64 sa)
          (BitVec.ofNat 64 (8 * fb))) =
      SfRef.addFields (sa = 1) ea fa (sb = 1) eb fb := by
  by_cases hss : sa = sb
  · subst hss
    rw [if_pos rfl]
    rcases Nat.lt_trichotomy ea eb with h | h | h
    · by_cases hb : eb = 2047
      · rw [ch_add_lt_nan m s r sa ea fa eb fb hs hfa hfb h hb]; sf_rhs
      by_cases ha : ea = 0
      · by_cases hfa0 : fa = 0
        · subst hfa0; rw [ch_add_lt0z m s r sa ea eb fb hs hfb ha (by omega) (by omega)]; sf_rhs
        by_cases he1 : eb = 1
        · rw [ch_add_lt0a m s r sa ea fa eb fb hs hfa hfb (by omega) ha he1]; sf_rhs
        · rw [ch_add_lt0b m s r sa ea fa eb fb hs hfa hfb (by omega) ha (by omega) (by omega)]; sf_rhs
      · rw [ch_add_lt m s r sa ea fa eb fb hs hfa hfb (by omega) h (by omega)]; sf_rhs
    · subst h
      by_cases ha : ea = 2047
      · rw [ch_add_nan m s r sa ea fa ea fb hs hfa hfb ha ha]; sf_rhs
      by_cases ha0 : ea = 0
      · rw [ch_add_sub0 m s r sa ea fa ea fb hs hfa hfb ha0 ha0]; sf_rhs
      · rw [ch_eq_norm m s r sa ea fa fb hs (by omega) (by omega) hfa hfb]; sf_rhs
    · by_cases ha : ea = 2047
      · rw [ch_add_gt_nan m s r sa ea fa eb fb hs hfa hfb h ha]; sf_rhs
      by_cases hb : eb = 0
      · by_cases hfb0 : fb = 0
        · subst hfb0; rw [ch_add_gt0z m s r sa ea fa eb hs hfa hb (by omega) (by omega)]; sf_rhs
        by_cases he1 : ea = 1
        · rw [ch_add_gt0a m s r sa ea fa eb fb hs hfa hfb (by omega) hb he1]; sf_rhs
        · rw [ch_add_gt0b m s r sa ea fa eb fb hs hfa hfb (by omega) hb (by omega) (by omega)]; sf_rhs
      · rw [ch_add_gt m s r sa ea fa eb fb hs (by omega) h (by omega) hfa hfb]; sf_rhs
  · rw [if_neg hss]
    rcases Nat.lt_trichotomy ea eb with h | h | h
    · by_cases hb : eb = 2047
      · rw [ch_sub_lt_nan m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb h hb]; sf_rhs
      by_cases ha : ea = 0
      · by_cases hfa0 : fa = 0
        · rw [ch_sub_lt0z m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb ha (by omega) (by omega) hfa0]; sf_rhs
        by_cases he1 : eb = 1
        · rcases Nat.lt_or_ge fb fa with hf | hf
          · rw [ch_sub_lt0a_lt m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb ha he1 hf]; sf_rhs
          · rw [ch_sub_lt0a_ge m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb ha he1 (by omega) hf]; sf_rhs
        · rw [ch_sub_lt0b m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb ha (by omega) (by omega) (by omega)]
          sf_rhs
      · rw [ch_sub_lt m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb (by omega) h (by omega)]; sf_rhs
    · subst h
      by_cases ha : ea = 2047
      · rw [ch_sub_nan m s r sa ea fa sb ea fb hs hsb hss hs1 hs2 hfa hfb ha ha]; sf_rhs
      rcases Nat.lt_trichotomy fa fb with hf | hf | hf
      · by_cases ha0 : ea = 0
        · rw [ch_sub0_lt m s r sa ea fa sb ea fb hs hsb hss hs1 hs2 hfa hfb ha0 ha0 hf]; sf_rhs
        · rw [ch_sub_eq_lt m s r sa ea fa sb ea fb hs hsb hss hs1 hs2 hfa hfb (by omega) (by omega) rfl hf]; sf_rhs
      · subst hf
        by_cases ha0 : ea = 0
        · rw [ch_sub0_z m s r sa ea fa sb ea fa hs hsb hss hs1 hs2 hfa hfb ha0 ha0 rfl]; sf_rhs
        · rw [ch_sub_eq_z m s r sa ea fa sb ea fa hs hsb hss hs1 hs2 hfa hfb (by omega) (by omega) rfl rfl]; sf_rhs
      · by_cases ha0 : ea = 0
        · rw [ch_sub0_gt m s r sa ea fa sb ea fb hs hsb hss hs1 hs2 hfa hfb ha0 ha0 hf]; sf_rhs
        · rw [ch_sub_eq_gt m s r sa ea fa sb ea fb hs hsb hss hs1 hs2 hfa hfb (by omega) (by omega) rfl hf]; sf_rhs
    · by_cases ha : ea = 2047
      · rw [ch_sub_gt_nan m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb h ha]; sf_rhs
      by_cases hb : eb = 0
      · by_cases hfb0 : fb = 0
        · rw [ch_sub_gt0z m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb hb (by omega) (by omega) hfb0]; sf_rhs
        by_cases he1 : ea = 1
        · rcases Nat.lt_or_ge fa fb with hf | hf
          · rw [ch_sub_gt0a_lt m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb hb he1 hf]; sf_rhs
          · rw [ch_sub_gt0a_ge m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb hb he1 (by omega) hf]; sf_rhs
        · rw [ch_sub_gt0b m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb hb (by omega) (by omega) (by omega)]
          sf_rhs
      · rw [ch_sub_gt m s r sa ea fa sb eb fb hs hsb hss hs1 hs2 hfa hfb (by omega) h (by omega)]; sf_rhs

open Lua.Num in
theorem sign_nf (a : BitVec 64) : F64.sign a = decide (a.toNat / 2 ^ 63 = 1) := by
  unfold F64.sign
  have := a.isLt
  by_cases h : 2 ^ 63 ≤ a.toNat
  · rw [decide_eq_true h, decide_eq_true (by omega)]
  · rw [decide_eq_false h, decide_eq_false (by omega)]

open Lua.Num in
/-- **Level (b1) for `__adddf3`**: the lifted function is the soft-fp-shaped
reference `SfRef.add` (on any stack pointer the routine's frame fits below). -/
theorem F_eq_sfref (m : Mem) (s : Nat) (r a b : BitVec 64) (hsp : Lua.Vm.Sim.FnSp s 48) :
    F m s r a b = SfRef.add a b := by
  have hs1 : 48 ≤ s := by have := hsp.lo; omega
  have hs2 : s ≤ 2 ^ 32 := hsp.hi
  have ha := a.isLt
  have hb := b.isLt
  rw [F_unpack m s r a b (fields a) (fields b)]
  unfold SfRef.add
  rw [sign_nf a, sign_nf b]
  exact cover m s r _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hs1 hs2

end Lua.Vm.Fn.Adddf3

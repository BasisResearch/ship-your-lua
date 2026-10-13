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

/-! ## The pack join (`_FP_PACK_SEMIRAW`'s pack, `0x8002d92c`) -/

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
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_d92c]

open Lua.Num in
/-- `_FP_ROUND` with the carry out of the mantissa (`0x8002dd48`). -/
theorem g_dd48 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 55) :
    N_8002dd48 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002d92c]
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_d92c]

open Lua.Num in
/-- The carry renormalisation then `_FP_ROUND` (`0x8002dbcc`). -/
theorem g_dbcc (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 2 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf1 : 2 ^ 55 ≤ f) (hf : f < 2 ^ 56) :
    N_8002dbcc m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) =
      SfRef.roundPack (S = 1) E (SfRef.rto (2 ^ 55 + f) 1) := by
  sf_go [N_8002d92c]
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_d92c]

open Lua.Num in
/-- The aligned-sum stage (`0x8002dbb8`): bit 55 set is the carry (`_FP_FRAC_SRS (R, 1)`,
then `R_e++`, ±∞ at `2047`), then `_FP_ROUND` and the pack. -/
theorem g_dbb8 (m : Mem) (s : Nat) (r : BitVec 64) {f E S : Nat} (hE1 : 1 ≤ E) (hE : E ≤ 2046) (hS : S < 2)
    (hf : f < 2 ^ 56) :
    N_8002dbb8 m s r (BitVec.ofNat 64 f) (BitVec.ofNat 64 E) (BitVec.ofNat 64 S) (BitVec.ofNat 64 S) =
      SfRef.carryPack (S = 1) E (2 ^ 55 + f) := by
  sf_go [N_8002dd48, N_8002dbcc]
  all_goals (try simp (disch := omega) only [g_dd48, g_dbcc])
  all_goals sf_close [nf_db68, nf_d8b8, nf_da9c, nf_d92c]

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

end Lua.Vm.Fn.Adddf3

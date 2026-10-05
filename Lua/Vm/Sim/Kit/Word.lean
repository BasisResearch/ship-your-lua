import Lua.Vm.Sim.Kit.Scan

/-!
# Word-at-a-time string scans: lanes and observations (round-4 bake-off, S-SCAN)

The newlib string routines (`strcmp`, `strlen`) read 8 bytes at a time and
test them with the "has a zero byte" trick
`((x & 0x7f…7f) + 0x7f…7f) | x | 0x7f…7f ≠ -1`. This file proves, once:

* **lanes** (`hzW_lanes`): the trick is lane-wise (8 independent byte
  lanes, no carries), each lane by one 256-case `decide` (`lane_hz`,
  `lane_noovf`);
* **byte atoms** (`bytesT8_toNat`): a word's value as its 8 bytes, so
  every shift, mask and subtraction of the word routines is linear
  arithmetic over byte atoms (`omega`);
* **the observation** (`CmpObs`): what `l_strcmp` observes of a comparison
  result, zero-ness and bit 31 (`srliw 31`), proved for a byte difference
  (`cmpObs_sub`) and for `strcmp`'s halfword exits (`hw_obs`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

/-! ## Lanes -/

theorem and_app {w : Nat} (a c : BitVec w) (b d : BitVec 8) : (a ++ b) &&& (c ++ d) = (a &&& c) ++ (b &&& d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_append]
  split <;> simp

theorem or_app {w : Nat} (a c : BitVec w) (b d : BitVec 8) : (a ++ b) ||| (c ++ d) = (a ||| c) ++ (b ||| d) := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_append]
  split <;> simp

theorem toNat_app8 {w : Nat} (a : BitVec w) (b : BitVec 8) : (a ++ b).toNat = a.toNat * 256 + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

/-- A carry-free lane: the sum of two appends is the append of the sums. -/
theorem add_app {w : Nat} (a c : BitVec w) (b d : BitVec 8) (h : b.toNat + d.toNat < 256) :
    (a ++ b) + (c ++ d) = (a + c) ++ (b + d) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, toNat_app8, toNat_app8, toNat_app8, BitVec.toNat_add, BitVec.toNat_add,
    Nat.mod_eq_of_lt (a := b.toNat + d.toNat) (by omega)]
  have ha := a.isLt; have hc := c.isLt
  rw [Nat.pow_add]
  generalize a.toNat = x at *; generalize c.toNat = y at *
  generalize hp : 2 ^ w = P at *
  generalize b.toNat = r1 at *; generalize d.toNat = r2 at *
  rw [show x * 256 + r1 + (y * 256 + r2) = (x + y) * 256 + (r1 + r2) by omega,
    show (2:Nat) ^ 8 = 256 from rfl, Nat.mul_comm P 256, Nat.mod_mul,
    show ((x + y) * 256 + (r1 + r2)) / 256 = x + y by omega]
  omega

theorem append_eq_iff {w : Nat} {x1 x2 : BitVec w} {y1 y2 : BitVec 8} :
    x1 ++ y1 = x2 ++ y2 ↔ x1 = x2 ∧ y1 = y2 :=
  ⟨append_inj', fun ⟨h1, h2⟩ => h1 ▸ h2 ▸ rfl⟩

/-- **The lane lemma** (256 cases). -/
theorem lane_hz : ∀ b : BitVec 8, (((b &&& 0x7f#8) + 0x7f#8) ||| (b ||| 0x7f#8)) = 0xff#8 ↔ b ≠ 0#8 := by
  decide

/-- No lane carries (256 cases). -/
theorem lane_noovf : ∀ b : BitVec 8, (b &&& 0x7f#8).toNat + (0x7f#8 : BitVec 8).toNat < 256 := by decide

/-- The mask `0x7f…7f`, as `strcmp` loads it from `.rodata` (`mask`). -/
abbrev maskW : BitVec 64 := 0x7f7f7f7f7f7f7f7f#64

/-- "Has no zero byte": the word test of `strcmp` and `strlen`. -/
abbrev hzW (x : BitVec 64) : BitVec 64 := ((x &&& maskW) + maskW) ||| (x ||| maskW)

theorem maskW_lanes : maskW = (((((((0x7f#8 ++ 0x7f#8) ++ 0x7f#8) ++ 0x7f#8) ++ 0x7f#8) ++ 0x7f#8) ++
    0x7f#8) ++ 0x7f#8) := by decide

theorem ones_lanes : (0#64) + sign_extend (m := 64) (0xfff#12) = (((((((0xff#8 ++ 0xff#8) ++ 0xff#8) ++
    0xff#8) ++ 0xff#8) ++ 0xff#8) ++ 0xff#8) ++ 0xff#8) := by decide

/-- **The word test is lane-wise.** -/
theorem hzW_lanes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    hzW (((((((b7 ++ b6) ++ b5) ++ b4) ++ b3) ++ b2) ++ b1) ++ b0) =
      (0#64) + sign_extend (m := 64) (0xfff#12) ↔
    b0 ≠ 0#8 ∧ b1 ≠ 0#8 ∧ b2 ≠ 0#8 ∧ b3 ≠ 0#8 ∧ b4 ≠ 0#8 ∧ b5 ≠ 0#8 ∧ b6 ≠ 0#8 ∧ b7 ≠ 0#8 := by
  rw [hzW, maskW_lanes, ones_lanes]
  simp only [and_app, or_app]
  rw [add_app _ _ _ _ (lane_noovf _), add_app _ _ _ _ (lane_noovf _), add_app _ _ _ _ (lane_noovf _),
    add_app _ _ _ _ (lane_noovf _), add_app _ _ _ _ (lane_noovf _), add_app _ _ _ _ (lane_noovf _),
    add_app _ _ _ _ (lane_noovf _)]
  simp only [or_app, append_eq_iff, lane_hz]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h7, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩, h0⟩; exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩; exact ⟨⟨⟨⟨⟨⟨⟨h7, h6⟩, h5⟩, h4⟩, h3⟩, h2⟩, h1⟩, h0⟩

/-- **A word has no zero byte** iff the test is all ones (`bytesT8`'s lanes). -/
theorem hzW_bytes {m : Mem} {p : Nat} :
    hzW (bytesT8 m p) = (0#64) + sign_extend (m := 64) (0xfff#12) ↔ ∀ k, k < 8 → bytesT1 m (p + k) ≠ 0#8 := by
  rw [bytesT8]; simp only [BitVec.append_eq]; rw [hzW_lanes]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ k hk
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  · intro h
    exact ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
      h 5 (by omega), h 6 (by omega), h 7 (by omega)⟩

/-! ## Byte atoms -/

/-- **A word is its bytes.** -/
theorem bytesT8_toNat {m : Mem} {p : Nat} : (bytesT8 m p).toNat =
    (bytesT1 m p).toNat + 256 * ((bytesT1 m (p + 1)).toNat + 256 * ((bytesT1 m (p + 2)).toNat +
      256 * ((bytesT1 m (p + 3)).toNat + 256 * ((bytesT1 m (p + 4)).toNat + 256 *
        ((bytesT1 m (p + 5)).toNat + 256 * ((bytesT1 m (p + 6)).toNat + 256 *
          (bytesT1 m (p + 7)).toNat)))))) := by
  simp only [bytesT8, BitVec.append_eq, toNat_app8, bytesT1]
  omega

/-- **A loaded word, as an atom** (not reducible, so that a pin holding it is
not unfolded into its byte appends by the runner's pin matching). -/
def wordAt (m : Mem) (p : Nat) : BitVec 64 := bytesT8 m p

theorem wordAt_toNat {m : Mem} {p : Nat} : (wordAt m p).toNat =
    (bytesT1 m p).toNat + 256 * ((bytesT1 m (p + 1)).toNat + 256 * ((bytesT1 m (p + 2)).toNat +
      256 * ((bytesT1 m (p + 3)).toNat + 256 * ((bytesT1 m (p + 4)).toNat + 256 *
        ((bytesT1 m (p + 5)).toNat + 256 * ((bytesT1 m (p + 6)).toNat + 256 *
          (bytesT1 m (p + 7)).toNat)))))) := bytesT8_toNat

/-- `ld` of a word at `x + k`. -/
theorem ld_word {m : Mem} {x k : Nat} (hk : k < 2048) (h : x + k < 2 ^ 64) :
    sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 x + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat :
      BitVec (8 * 8)) = wordAt m (x + k) := by
  rw [add_imm x k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]; rfl

theorem shl_toNat (x : BitVec 64) (s : Nat) (hs : s < 64) :
    (shift_bits_left x (Sail.BitVec.extractLsb (BitVec.ofNat 6 s) 5 0)).toNat = x.toNat * 2 ^ s % 2 ^ 64 := by
  simp only [shift_bits_left, Sail.BitVec.extractLsb]
  simp [Nat.shiftLeft_eq, Nat.mod_eq_of_lt hs]

theorem shr_toNat (x : BitVec 64) (s : Nat) (hs : s < 64) :
    (shift_bits_right x (Sail.BitVec.extractLsb (BitVec.ofNat 6 s) 5 0)).toNat = x.toNat / 2 ^ s := by
  simp only [shift_bits_right, Sail.BitVec.extractLsb]
  simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hs]

theorem bne_toNat (a b : BitVec 64) : (a != b) = !decide (a.toNat = b.toNat) := by
  rw [Bool.eq_iff_iff]; simp [BitVec.toNat_inj]

/-- Byte `k` of a word, as a `Nat`. -/
abbrev wb (m : Mem) (p k : Nat) : Nat := (bytesT1 m (p + k)).toNat

/-- `strcmp`'s halfword extractions (`slli s; srli 48`, `srli 48`), as byte
atoms (each proved once). -/
theorem hw0_toNat (m : Mem) (p : Nat) :
    (shift_bits_right (shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x30#6) 5 0))
      (Sail.BitVec.extractLsb (0x30#6) 5 0)).toNat = wb m p 0 + 256 * wb m p 1 := by
  rw [shr_toNat _ 48 (by decide), shl_toNat _ 48 (by decide), wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  simp only [wb, Nat.add_zero]; omega

theorem hw1_toNat (m : Mem) (p : Nat) :
    (shift_bits_right (shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (Sail.BitVec.extractLsb (0x30#6) 5 0)).toNat = wb m p 2 + 256 * wb m p 3 := by
  rw [shr_toNat _ 48 (by decide), shl_toNat _ 32 (by decide), wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m (p + 2)).isLt; have := (bytesT1 m (p + 3)).isLt
  simp only [wb]; omega

theorem hw2_toNat (m : Mem) (p : Nat) :
    (shift_bits_right (shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x10#6) 5 0))
      (Sail.BitVec.extractLsb (0x30#6) 5 0)).toNat = wb m p 4 + 256 * wb m p 5 := by
  rw [shr_toNat _ 48 (by decide), shl_toNat _ 16 (by decide), wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m (p + 2)).isLt; have := (bytesT1 m (p + 3)).isLt
  have := (bytesT1 m (p + 4)).isLt; have := (bytesT1 m (p + 5)).isLt
  simp only [wb]; omega

theorem hw3_toNat (m : Mem) (p : Nat) :
    (shift_bits_right (wordAt m p) (Sail.BitVec.extractLsb (0x30#6) 5 0)).toNat = wb m p 6 + 256 * wb m p 7 := by
  rw [shr_toNat _ 48 (by decide), wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m (p + 2)).isLt; have := (bytesT1 m (p + 3)).isLt
  have := (bytesT1 m (p + 4)).isLt; have := (bytesT1 m (p + 5)).isLt
  have := (bytesT1 m (p + 6)).isLt; have := (bytesT1 m (p + 7)).isLt
  simp only [wb]; omega

/-- `bne` of the shifted words: the low halfwords, words, six bytes. -/
theorem shl48_eq (m : Mem) (p q : Nat) :
    shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x30#6) 5 0) =
      shift_bits_left (wordAt m q) (Sail.BitVec.extractLsb (0x30#6) 5 0)
      ↔ (wb m p 0 = wb m q 0 ∧ wb m p 1 = wb m q 1) := by
  rw [← BitVec.toNat_inj, shl_toNat _ 48 (by decide), shl_toNat _ 48 (by decide), wordAt_toNat, wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m q).isLt; have := (bytesT1 m (q + 1)).isLt
  simp only [wb, Nat.add_zero]; constructor <;> intro <;> omega

theorem shl32_eq (m : Mem) (p q : Nat) :
    shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x20#6) 5 0) =
      shift_bits_left (wordAt m q) (Sail.BitVec.extractLsb (0x20#6) 5 0)
      ↔ (wb m p 0 = wb m q 0 ∧ wb m p 1 = wb m q 1 ∧ wb m p 2 = wb m q 2 ∧ wb m p 3 = wb m q 3) := by
  rw [← BitVec.toNat_inj, shl_toNat _ 32 (by decide), shl_toNat _ 32 (by decide), wordAt_toNat, wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m (p + 2)).isLt; have := (bytesT1 m (p + 3)).isLt
  have := (bytesT1 m q).isLt; have := (bytesT1 m (q + 1)).isLt
  have := (bytesT1 m (q + 2)).isLt; have := (bytesT1 m (q + 3)).isLt
  simp only [wb, Nat.add_zero]; constructor <;> intro <;> omega

theorem shl16_eq (m : Mem) (p q : Nat) :
    shift_bits_left (wordAt m p) (Sail.BitVec.extractLsb (0x10#6) 5 0) =
      shift_bits_left (wordAt m q) (Sail.BitVec.extractLsb (0x10#6) 5 0)
      ↔ (wb m p 0 = wb m q 0 ∧ wb m p 1 = wb m q 1 ∧ wb m p 2 = wb m q 2 ∧ wb m p 3 = wb m q 3 ∧
        wb m p 4 = wb m q 4 ∧ wb m p 5 = wb m q 5) := by
  rw [← BitVec.toNat_inj, shl_toNat _ 16 (by decide), shl_toNat _ 16 (by decide), wordAt_toNat, wordAt_toNat]
  have := (bytesT1 m p).isLt; have := (bytesT1 m (p + 1)).isLt
  have := (bytesT1 m (p + 2)).isLt; have := (bytesT1 m (p + 3)).isLt
  have := (bytesT1 m (p + 4)).isLt; have := (bytesT1 m (p + 5)).isLt
  have := (bytesT1 m q).isLt; have := (bytesT1 m (q + 1)).isLt
  have := (bytesT1 m (q + 2)).isLt; have := (bytesT1 m (q + 3)).isLt
  have := (bytesT1 m (q + 4)).isLt; have := (bytesT1 m (q + 5)).isLt
  simp only [wb, Nat.add_zero]; constructor <;> intro <;> omega

/-! ## The observation -/

/-- **What `l_strcmp` observes of a comparison result** `v` of the bytes `x`
and `y`: zero iff equal (`bnez`), bit 31 (`srliw 31`) iff `x < y`. -/
structure CmpObs (v : BitVec 64) (x y : Nat) : Prop where
  zero : v = 0#64 ↔ x = y
  neg : v.getLsbD 31 = decide (x < y)

/-- A difference of two small values. -/
theorem cmpObs_sub {x y : Nat} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16) :
    CmpObs (BitVec.ofNat 64 x - BitVec.ofNat 64 y) x y := by
  constructor
  · constructor
    · intro h; have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at this; omega
    · rintro rfl; simp
  · rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
    constructor <;> intro <;> omega

end Lua.Vm.Sim

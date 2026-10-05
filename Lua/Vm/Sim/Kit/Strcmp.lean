import Lua.Vm.Sim.Kit.Word
import Lua.Vm.Sim.Kit.Memcmp
import Lua.Vm.Arms.Segs.Hstrcmp

/-!
# `strcmp` at the Lua ELF's address (round-4 bake-off, S-SCAN)

newlib's `strcmp` (`0x8003b920`; `strcoll` is `j strcmp` in the "C"
locale) as read-only scans (`scan_loop`): a byte loop (`0x8003ba04`), and
for two 8-aligned strings a word loop unrolled three times (`0x8003b938`)
that tests `P`'s word for a zero byte (`hzW_bytes`, the lane lemma) and
compares the words. A word with a zero byte relays to the byte loop at that
word (`relay`); a differing word without one exits through the halfword
compare (`0x8003b9a0`), whose answer is a byte or a halfword difference.

The summary is quotiented by `l_strcmp`'s observation (`CmpObs`: zero-ness
and bit 31) of the first position where the strings differ or `P`'s ends
(`ScAns`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- Position `j` is not an event: the bytes agree and `P`'s does not end. -/
def ScOk (m : Mem) (P Q j : Nat) : Prop :=
  bytesT1 m (P + j) = bytesT1 m (Q + j) ∧ bytesT1 m (P + j) ≠ 0#8

/-- **`strcmp`'s answer** `v`: at the first event `k` (the strings differ, or
`P`'s ends), `v` is observed as the comparison of the two bytes. -/
structure ScAns (m : Mem) (P Q : Nat) (v : BitVec 64) : Prop where
  intro ::
  ans : ∃ k, (∀ j, j < k → ScOk m P Q j) ∧ ¬ ScOk m P Q k ∧
    CmpObs v (bytesT1 m (P + k)).toNat (bytesT1 m (Q + k)).toNat

/-- A return with `strcmp`'s answer. -/
structure ScRet (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String) (P Q : Nat) (c : Config) :
    Prop where
  intro ::
  ret : ∃ v, RetAt r sp f m o v c ∧ ScAns m P Q v

/-- The facts every path uses: `P`'s terminator at `t`, the reads in RAM. -/
structure ScCtx (m : Mem) (P Q t : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  p_lo : tohostAddr + 16 ≤ P
  q_lo : tohostAddr + 16 ≤ Q
  p_hi : P + t + 16 ≤ 2 ^ 32
  q_hi : Q + t + 16 ≤ 2 ^ 32
  term : bytesT1 m (P + t) = 0#8

/-- The byte loop's state at `0x8003ba04`, position `j`. -/
abbrev scB (P Q j : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + j)⟩ :: ⟨Register.x11, BitVec.ofNat 64 (Q + j)⟩ ::
    ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

theorem zext8_ofNat (x : BitVec 8) : zero_extend (m := 64) (x : BitVec (8 * 1)) = BitVec.ofNat 64 x.toNat := by
  apply BitVec.eq_of_toNat_eq
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.toNat_ofNat]


/-- `bne a2, a3` and `bnez a2` on the bytes at `j`. -/
theorem sc_byte_ne {m : Mem} {P Q j : Nat} (hp : P + j < 2 ^ 64) (hq : Q + j < 2 ^ 64) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 (P + j) + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 1))) != (zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 (Q + j) +
        sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 1)))) =
      !decide (bytesT1 m (P + j) = bytesT1 m (Q + j)) := by
  rw [addr0 hp, addr0 hq, bne, zext8_beq]

theorem sc_byte_nz {m : Mem} {P j : Nat} (hp : P + j < 2 ^ 64) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 (P + j) + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 1))) != 0#64) = !decide (bytesT1 m (P + j) = 0#8) := by
  rw [addr0 hp, show (0#64 : BitVec 64) = zero_extend (m := 64) ((0#8 : BitVec 8) : BitVec (8 * 1)) by decide,
    bne, zext8_beq]

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

set_option hygiene false in
/-- The context's numeric facts, for `kit_disch`. -/
local macro "sc_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := ($hx).ra; have := ($hx).p_lo; have := ($hx).p_hi; have := ($hx).q_lo; have := ($hx).q_hi))

/-- The byte answer: `sub a0, a2, a3` of the two zero-extended bytes. -/
theorem sc_sub_obs (x y : BitVec 8) :
    CmpObs (zero_extend (m := 64) (x : BitVec (8 * 1)) - zero_extend (m := 64) (y : BitVec (8 * 1)))
      x.toNat y.toNat := by
  rw [zext8_ofNat, zext8_ofNat]
  exact cmpObs_sub (by have := x.isLt; omega) (by have := y.isLt; omega)

/-- **The byte loop** from position `j` (`0x8003ba04`), no event before. -/
theorem strcmp_bytes (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) : ∀ j, j < t + 1 → (∀ i, i < j → ScOk m P Q i) →
    Triple (SegSt 0x8003ba04#64 (scB P Q j r sp f) (ArmPay m o)) (ScRet r sp f m o P Q) :=
  scan_loop (t + 1) (ScOk m P Q) fun j hj hok c h => by
    have acc := Steps.refl c
    sc_ctx hx
    have hg := sc_byte_ne (m := m) (P := P) (Q := Q) (j := j) (by omega) (by omega)
    by_cases he : bytesT1 m (P + j) = bytesT1 m (Q + j)
    · simp only [he, decide_true, Bool.not_true] at hg
      have hz := sc_byte_nz (m := m) (P := P) (j := j) (by omega)
      by_cases h0 : bytesT1 m (P + j) = 0#8
      · simp only [h0, decide_true, Bool.not_true] at hz
        kit_run h acc
        have h := h.at (Vsa.Sim.ret_tgt r hra)
        refine ⟨_, acc, .inr ⟨⟨_, h.repin (by pins_of h), ⟨⟨j, hok, fun h' => h'.2 h0, ?_⟩⟩⟩⟩⟩
        rw [addr0 (by omega), addr0 (by omega)]; exact sc_sub_obs _ _
      · simp only [h0, decide_false, Bool.not_false] at hz
        have hjt : j ≠ t := fun e => h0 (e ▸ hx.term)
        kit_run h acc until [0x8003ba04]
        refine ⟨_, acc, .inl ⟨j + 1, by omega, by omega, fun i hi => ?_, h.repin (by pins_of h)⟩⟩
        rcases Nat.lt_or_ge i j with hi' | hi'
        · exact hok i hi'
        · rw [show i = j by omega]; exact ⟨he, h0⟩
    · simp only [he, decide_false, Bool.not_false] at hg
      kit_run h acc
      have h := h.at (Vsa.Sim.ret_tgt r hra)
      refine ⟨_, acc, .inr ⟨⟨_, h.repin (by pins_of h), ⟨⟨j, hok, fun h' => he h'.1, ?_⟩⟩⟩⟩⟩
      rw [addr0 (by omega), addr0 (by omega)]; exact sc_sub_obs _ _

/-! ## The halfword exit (`0x8003b9a0`) -/

theorem sext_ff_toNat : (sign_extend (m := 64) (0x0ff#12)).toNat = 255 := by decide

theorem and_ff_toNat (x : BitVec 64) : (x &&& sign_extend (m := 64) (0x0ff#12)).toNat = x.toNat % 256 := by
  rw [show sign_extend (m := 64) (0x0ff#12) = BitVec.ofNat 64 (2 ^ 8 - 1) by decide, BitVec.toNat_and,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide), Nat.and_two_pow_sub_one_eq_mod]

/-- An observation from the result's value. -/
theorem cmpObs_toNat {v : BitVec 64} {x y : Nat} (hx : x < 2 ^ 16) (hy : y < 2 ^ 16)
    (h : v.toNat = (2 ^ 64 - y + x) % 2 ^ 64) : CmpObs v x y := by
  have e : v = BitVec.ofNat 64 x - BitVec.ofNat 64 y := by
    apply BitVec.eq_of_toNat_eq; rw [h, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega
  rw [e]; exact cmpObs_sub hx hy

/-- **The answer from the first differing lane** `k0` of a word with no zero
byte. -/
theorem sc_ans_lane {m : Mem} {P Q i k0 : Nat} {v : BitVec 64} (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8) (hk0 : k0 < 8)
    (heq : ∀ k, k < k0 → (bytesT1 m (P + i + k)).toNat = (bytesT1 m (Q + i + k)).toNat)
    (hne : (bytesT1 m (P + i + k0)).toNat ≠ (bytesT1 m (Q + i + k0)).toNat)
    (hobs : CmpObs v (bytesT1 m (P + i + k0)).toNat (bytesT1 m (Q + i + k0)).toNat) : ScAns m P Q v := by
  refine ⟨⟨i + k0, fun j hj => ?_, fun h => hne ?_, by simpa only [Nat.add_assoc] using hobs⟩⟩
  · rcases Nat.lt_or_ge j i with h | h
    · exact hok j h
    · have e := heq (j - i) (by omega); have z := hnz (j - i) (by omega)
      rw [show P + i + (j - i) = P + j by omega, show Q + i + (j - i) = Q + j by omega] at e
      rw [show P + i + (j - i) = P + j by omega] at z
      exact ⟨BitVec.eq_of_toNat_eq e, z⟩
  · have e := h.1; rw [← Nat.add_assoc, ← Nat.add_assoc] at e; rw [e]

/-- The halfword exit's state at `0x8003b9a0`: the two words. -/
abbrev scH (x y : BitVec 64) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x12, x⟩ :: ⟨Register.x13, y⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

theorem bne_dec (a b : BitVec 64) : (a != b) = !decide (a = b) := rfl

/-- A value guard of the halfword exit, decided over the byte atoms: the
shifted-word compares (`shl48_eq`, …), then the halfword differences
(`hw0_toNat`, …). -/
macro "sc_guard" : tactic => `(tactic| first
  | (simp only [bne_dec, shl48_eq, shl32_eq, shl16_eq, Bool.not_eq_true', Bool.not_eq_false',
      decide_eq_true_eq, decide_eq_false_iff_not, wb, Nat.add_zero]
     omega)
  | (simp only [bne_toNat, BitVec.toNat_sub, and_ff_toNat, hw0_toNat, hw1_toNat, hw2_toNat, hw3_toNat,
      BitVec.toNat_ofNat, Nat.zero_mod, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, wb, Nat.add_zero]
     omega))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra)
      | sc_guard)

/-- The halfword answer `h1 - h2` when the low bytes agree: the high bytes'. -/
theorem cmpObs_hw {v : BitVec 64} {lo1 hi1 lo2 hi2 : Nat} (h1 : lo1 < 256) (h2 : hi1 < 256)
    (h3 : lo2 < 256) (h4 : hi2 < 256) (he : lo1 = lo2)
    (h : v.toNat = (2 ^ 64 - (lo2 + 256 * hi2) + (lo1 + 256 * hi1)) % 2 ^ 64) : CmpObs v hi1 hi2 := by
  have c := cmpObs_toNat (v := v) (x := lo1 + 256 * hi1) (y := lo2 + 256 * hi2) (by omega) (by omega) h
  exact ⟨c.zero.trans (by omega), c.neg.trans (by subst he; simp only [decide_eq_decide]; omega)⟩

set_option hygiene false in
/-- One leaf of the halfword exit: the run to `ret`, the answer at lane `k0`
(`B`: a byte difference, `H`: a halfword difference). -/
local macro "sc_leaf" k0:num obs:term : tactic => `(tactic| (
  kit_run h acc
  have h := h.at (Vsa.Sim.ret_tgt r hra)
  refine ⟨_, acc, ⟨_, h.repin (by pins_of h), sc_ans_lane (k0 := $k0) hok hnz (by decide)
    (fun k hk => by
      rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero]) <;> omega)
    (by (try simp only [Nat.add_zero]); omega)
    ($obs (by omega) (by omega) (by omega) (by omega) (by (try simp only [Nat.add_zero]); omega) (by
      simp only [BitVec.toNat_sub, and_ff_toNat, hw0_toNat, hw1_toNat, hw2_toNat, hw3_toNat, wb, Nat.add_zero]
        <;> omega))⟩⟩))

/-- The byte answer at a halfword's low lane. -/
theorem cmpObs_lo {v : BitVec 64} {lo1 hi1 lo2 hi2 : Nat} (h1 : lo1 < 256) (_h2 : hi1 < 256)
    (h3 : lo2 < 256) (_h4 : hi2 < 256) (_he : lo1 ≠ lo2)
    (h : v.toNat = (2 ^ 64 - lo2 % 256 + lo1 % 256) % 2 ^ 64) : CmpObs v lo1 lo2 :=
  cmpObs_toNat (by omega) (by omega) (by rw [h, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h3])

set_option hygiene false in
/-- The byte atoms of the two words. -/
local macro "sc_hw_setup" : tactic => `(tactic| (
  intro c h
  have acc := Steps.refl c
  have := (bytesT1 m (P + i)).isLt; have := (bytesT1 m (P + i + 1)).isLt
  have := (bytesT1 m (P + i + 2)).isLt; have := (bytesT1 m (P + i + 3)).isLt
  have := (bytesT1 m (P + i + 4)).isLt; have := (bytesT1 m (P + i + 5)).isLt
  have := (bytesT1 m (P + i + 6)).isLt; have := (bytesT1 m (P + i + 7)).isLt
  have := (bytesT1 m (Q + i)).isLt; have := (bytesT1 m (Q + i + 1)).isLt
  have := (bytesT1 m (Q + i + 2)).isLt; have := (bytesT1 m (Q + i + 3)).isLt
  have := (bytesT1 m (Q + i + 4)).isLt; have := (bytesT1 m (Q + i + 5)).isLt
  have := (bytesT1 m (Q + i + 6)).isLt; have := (bytesT1 m (Q + i + 7)).isLt))

/-- The words' lane `k` agrees. -/
abbrev LaneEq (m : Mem) (P Q i k : Nat) : Prop := wb m (P + i) k = wb m (Q + i) k

/-- The halfword exit, the first halfword differing. -/
theorem strcmp_hw0 (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8) (hd : ¬ (LaneEq m P Q i 0 ∧ LaneEq m P Q i 1)) :
    Triple (SegSt 0x8003b9a0#64 (scH (wordAt m (P + i)) (wordAt m (Q + i)) r sp f) (ArmPay m o))
      (ScRet r sp f m o P Q) := by
  sc_hw_setup
  simp only [LaneEq, wb, Nat.add_zero] at hd
  by_cases e0 : (bytesT1 m (P + i)).toNat = (bytesT1 m (Q + i)).toNat
  · sc_leaf 1 (cmpObs_hw (lo1 := wb m (P + i) 0) (lo2 := wb m (Q + i) 0))
  · sc_leaf 0 (cmpObs_lo (hi1 := wb m (P + i) 1) (hi2 := wb m (Q + i) 1))

/-- The second halfword differing. -/
theorem strcmp_hw1 (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8) (he : LaneEq m P Q i 0 ∧ LaneEq m P Q i 1)
    (hd : ¬ (LaneEq m P Q i 2 ∧ LaneEq m P Q i 3)) :
    Triple (SegSt 0x8003b9a0#64 (scH (wordAt m (P + i)) (wordAt m (Q + i)) r sp f) (ArmPay m o))
      (ScRet r sp f m o P Q) := by
  sc_hw_setup
  simp only [LaneEq, wb, Nat.add_zero] at hd he
  obtain ⟨e0, e1⟩ := he
  by_cases e2 : (bytesT1 m (P + i + 2)).toNat = (bytesT1 m (Q + i + 2)).toNat
  · sc_leaf 3 (cmpObs_hw (lo1 := wb m (P + i) 2) (lo2 := wb m (Q + i) 2))
  · sc_leaf 2 (cmpObs_lo (hi1 := wb m (P + i) 3) (hi2 := wb m (Q + i) 3))

/-- The third halfword differing. -/
theorem strcmp_hw2 (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8)
    (he : LaneEq m P Q i 0 ∧ LaneEq m P Q i 1 ∧ LaneEq m P Q i 2 ∧ LaneEq m P Q i 3)
    (hd : ¬ (LaneEq m P Q i 4 ∧ LaneEq m P Q i 5)) :
    Triple (SegSt 0x8003b9a0#64 (scH (wordAt m (P + i)) (wordAt m (Q + i)) r sp f) (ArmPay m o))
      (ScRet r sp f m o P Q) := by
  sc_hw_setup
  simp only [LaneEq, wb, Nat.add_zero] at hd he
  obtain ⟨e0, e1, e2, e3⟩ := he
  by_cases e4 : (bytesT1 m (P + i + 4)).toNat = (bytesT1 m (Q + i + 4)).toNat
  · sc_leaf 5 (cmpObs_hw (lo1 := wb m (P + i) 4) (lo2 := wb m (Q + i) 4))
  · sc_leaf 4 (cmpObs_lo (hi1 := wb m (P + i) 5) (hi2 := wb m (Q + i) 5))

/-- The last halfword differing. -/
theorem strcmp_hw3 (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8)
    (he : LaneEq m P Q i 0 ∧ LaneEq m P Q i 1 ∧ LaneEq m P Q i 2 ∧ LaneEq m P Q i 3 ∧
      LaneEq m P Q i 4 ∧ LaneEq m P Q i 5)
    (hd : ¬ (LaneEq m P Q i 6 ∧ LaneEq m P Q i 7)) :
    Triple (SegSt 0x8003b9a0#64 (scH (wordAt m (P + i)) (wordAt m (Q + i)) r sp f) (ArmPay m o))
      (ScRet r sp f m o P Q) := by
  sc_hw_setup
  simp only [LaneEq, wb, Nat.add_zero] at hd he
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := he
  by_cases e6 : (bytesT1 m (P + i + 6)).toNat = (bytesT1 m (Q + i + 6)).toNat
  · sc_leaf 7 (cmpObs_hw (lo1 := wb m (P + i) 6) (lo2 := wb m (Q + i) 6))
  · sc_leaf 6 (cmpObs_lo (hi1 := wb m (P + i) 7) (hi2 := wb m (Q + i) 7))

/-- **The halfword exit**: two differing words, `P`'s without a zero byte;
the answer is at the first differing lane. -/
theorem strcmp_hw (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hok : ∀ j, j < i → ScOk m P Q j)
    (hnz : ∀ k, k < 8 → bytesT1 m (P + i + k) ≠ 0#8) (hne : wordAt m (P + i) ≠ wordAt m (Q + i)) :
    Triple (SegSt 0x8003b9a0#64 (scH (wordAt m (P + i)) (wordAt m (Q + i)) r sp f) (ArmPay m o))
      (ScRet r sp f m o P Q) := by
  by_cases h01 : LaneEq m P Q i 0 ∧ LaneEq m P Q i 1
  · by_cases h23 : LaneEq m P Q i 2 ∧ LaneEq m P Q i 3
    · by_cases h45 : LaneEq m P Q i 4 ∧ LaneEq m P Q i 5
      · refine strcmp_hw3 P Q i r sp f m o hra hok hnz ⟨h01.1, h01.2, h23.1, h23.2, h45.1, h45.2⟩
          fun h67 => hne (BitVec.eq_of_toNat_eq ?_)
        rw [wordAt_toNat, wordAt_toNat]
        simp only [LaneEq, wb, Nat.add_zero] at h01 h23 h45 h67
        omega
      · exact strcmp_hw2 P Q i r sp f m o hra hok hnz ⟨h01.1, h01.2, h23.1, h23.2⟩ h45
    · exact strcmp_hw1 P Q i r sp f m o hra hok hnz h01 h23
  · exact strcmp_hw0 P Q i r sp f m o hra hok hnz h01

end Lua.Vm.Sim.Kit

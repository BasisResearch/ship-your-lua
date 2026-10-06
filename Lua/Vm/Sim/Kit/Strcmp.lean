import Lua.Vm.Sim.Kit.Word
import Lua.Vm.Sim.Kit.Memcmp
import Lua.Vm.Sim.Kit.Lngstr
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
  ro : RodataRead m
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
  exact ⟨c.zero.trans (by omega), c.neg.trans (by subst he; simp only [decide_eq_decide]; omega), c.small⟩

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

/-! ## The word loop (`0x8003b938`, unrolled three times) -/

/-- The mask register, an atom. -/
def maskV : BitVec 64 := 0x7f7f7f7f7f7f7f7f#64

/-- `li t2, -1`, an atom. -/
def onesV : BitVec 64 := (0#64) + sign_extend (m := 64) (0xfff#12)

theorem ones_eq : (0#64) + sign_extend (m := 64) (0xfff#12) = onesV := rfl

/-- The bytes of `mask` (one kernel check). -/
theorem mask_bytes : ∀ j, j < 8 → Image.rodataByte (0x8005c620 - Image.rodataBase + j) = 0x7f#8 := by
  decide +kernel

/-- `ld a5, mask` (`.rodata` at `0x8005c620`). -/
theorem mask_ld {m : Mem} (hro : RodataRead m) :
    sign_extend (m := 64) (bytesT8 m (((0x8003b930#64) + sign_extend (m := 64) ((0x00021#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xcf0#12)).toNat : BitVec (8 * 8)) = maskV := by
  rw [sext64_id, show ((((0x8003b930#64) + sign_extend (m := 64) ((0x00021#20) +++ 0x000#12)) +
      sign_extend (m := 64) (0xcf0#12)).toNat) = 0x8005c620 by decide]
  have hb : ∀ j, j < 8 → bytesT1 m (0x8005c620 + j) = 0x7f#8 := by
    intro j hj
    have := hro (0x8005c620 - Image.rodataBase + j) (by simp only [Image.rodataBase, Image.rodataSize]; omega)
    rw [show Image.rodataBase + (0x8005c620 - Image.rodataBase + j) = 0x8005c620 + j by
      simp only [Image.rodataBase]; omega] at this
    rw [this]; exact mask_bytes j hj
  have h0 := hb 0 (by omega)
  simp only [bytesT1, Nat.add_zero] at h0 hb
  simp only [bytesT8, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega),
    hb 5 (by omega), hb 6 (by omega), hb 7 (by omega), maskV]
  decide

/-- `ld` of a word through its 8 bytes. -/
theorem ld_word0 {m : Mem} {y : Nat} : sign_extend (m := 64) (bytesT8 m y : BitVec (8 * 8)) = wordAt m y :=
  sext64_id _

/-- The zero-byte test of the word at `x + k` (`hzW_bytes`): no zero byte. -/
theorem sc_hz_ok {m : Mem} {x k : Nat} (hk : k < 2048) (h : x + k < 2 ^ 64)
    (hz : ∀ j, j < 8 → bytesT1 m (x + k + j) ≠ 0#8) :
    (((((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 x + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat :
      BitVec (8 * 8))) &&& maskV) + maskV) ||| ((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 x +
        sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat : BitVec (8 * 8))) ||| maskV)) != onesV) = false := by
  rw [addr_imm hk h, sext64_id]
  have e := (hzW_bytes (m := m) (p := x + k)).2 hz
  simp only [hzW, maskW] at e
  rw [show maskV = 0x7f7f7f7f7f7f7f7f#64 from rfl, show onesV = (0#64) + sign_extend (m := 64) (0xfff#12) from rfl,
    e]; simp

/-- … and with a zero byte. -/
theorem sc_hz_zero {m : Mem} {x k : Nat} (hk : k < 2048) (h : x + k < 2 ^ 64)
    (hz : ¬ ∀ j, j < 8 → bytesT1 m (x + k + j) ≠ 0#8) :
    (((((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 x + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat :
      BitVec (8 * 8))) &&& maskV) + maskV) ||| ((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 x +
        sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat : BitVec (8 * 8))) ||| maskV)) != onesV) = true := by
  rw [addr_imm hk h, sext64_id]
  have e := hzW_bytes (m := m) (p := x + k)
  simp only [hzW, maskW] at e
  rw [show maskV = 0x7f7f7f7f7f7f7f7f#64 from rfl, show onesV = (0#64) + sign_extend (m := 64) (0xfff#12) from rfl,
    bne_iff_ne]
  exact fun e' => hz (e.1 e')

theorem bne_of_eq {a b : BitVec 64} (h : a = b) : (a != b) = false := by simp [h]
theorem bne_of_ne {a b : BitVec 64} (h : a ≠ b) : (a != b) = true := by simp [h]

/-- The first of a decidable property below `n`. -/
theorem exists_first {P : Nat → Prop} [DecidablePred P] (n : Nat) :
    (∃ z, z < n ∧ P z) → ∃ z, z < n ∧ P z ∧ ∀ y, y < z → ¬ P y := by
  induction n with
  | zero => exact fun ⟨_, h, _⟩ => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro ⟨z, hz, hp⟩
    by_cases h : ∃ y, y < n ∧ P y
    · obtain ⟨y, hy, hpy, hmin⟩ := ih h
      exact ⟨y, by omega, hpy, hmin⟩
    · exact ⟨z, hz, hp, fun y hy hpy => h ⟨y, by omega, hpy⟩⟩

/-- **The answer at a word with a zero byte, equal to the other**: the
first zero, `a0 = 0`. -/
theorem sc_ans_zero {m : Mem} {P Q p : Nat} (hok : ∀ j, j < p → ScOk m P Q j)
    (hz : ¬ ∀ k, k < 8 → bytesT1 m (P + p + k) ≠ 0#8) (he : wordAt m (P + p) = wordAt m (Q + p)) :
    ScAns m P Q ((0#64) + sign_extend (m := 64) (0x000#12)) := by
  have hl := mc_lanes.1 he
  obtain ⟨z, hz8, hz0, hmin⟩ := exists_first (P := fun k => bytesT1 m (P + p + k) = 0#8) 8
    (by simp only [Classical.not_forall, Classical.not_not] at hz; obtain ⟨k, hk, e⟩ := hz; exact ⟨k, hk, e⟩)
  have hlz := hl z hz8; simp only [McEq] at hlz
  refine ⟨⟨p + z, fun j hj => ?_, fun h' => h'.2 ?_, ?_⟩⟩
  · rcases Nat.lt_or_ge j p with h | h
    · exact hok j h
    · have e1 := hl (j - p) (by omega); have e2 := hmin (j - p) (by omega)
      simp only [McEq] at e1
      rw [show P + (p + (j - p)) = P + j by omega, show Q + (p + (j - p)) = Q + j by omega] at e1
      rw [show P + p + (j - p) = P + j by omega] at e2
      exact ⟨e1, e2⟩
  · rw [← Nat.add_assoc]; exact hz0
  · rw [← Nat.add_assoc, ← Nat.add_assoc] at hlz
    rw [Vsa.Sim.sext_zero, BitVec.add_zero, ← Nat.add_assoc, ← Nat.add_assoc, ← hlz, hz0]
    exact ⟨by simp, by decide, by decide⟩

/-- The word loop's state: `a0 = P + i`, `a1 = Q + i`, the mask and `-1`. -/
abbrev scW (P Q i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + i)⟩ :: ⟨Register.x11, BitVec.ofNat 64 (Q + i)⟩ ::
    ⟨Register.x15, maskV⟩ :: ⟨Register.x7, onesV⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, ld_word0, Nat.add_zero,
    ones_eq, mask_ld hro] at $h:ident)

set_option hygiene false in
/-- The guard facts of one word at `P + i + k`. -/
local macro "sc_word" k:num : tactic => `(tactic| (
  have hk8 : P + i + $k < 2 ^ 64 := by omega))

/-- No event before `p` puts `p` at or before `P`'s terminator. -/
theorem sc_le_term {m : Mem} {P Q t p : Nat} {r : BitVec 64} (hx : ScCtx m P Q t r)
    (hok : ∀ j, j < p → ScOk m P Q j) : p ≤ t :=
  Nat.not_lt.1 fun h => (hok t h).2 hx.term

/-- A word without a zero byte, equal to the other: no event in it. -/
theorem sc_ok_word {m : Mem} {P Q p : Nat} (hok : ∀ j, j < p → ScOk m P Q j)
    (hzk : ∀ k, k < 8 → bytesT1 m (P + p + k) ≠ 0#8) (he : wordAt m (P + p) = wordAt m (Q + p)) :
    ∀ j, j < p + 8 → ScOk m P Q j := fun j hj => by
  rcases Nat.lt_or_ge j p with h | h
  · exact hok j h
  · have e1 := mc_lanes.1 he (j - p) (by omega); have e2 := hzk (j - p) (by omega)
    simp only [McEq] at e1
    rw [show P + (p + (j - p)) = P + j by omega, show Q + (p + (j - p)) = Q + j by omega] at e1
    rw [show P + p + (j - p) = P + j by omega] at e2
    exact ⟨e1, e2⟩

set_option hygiene false in
/-- A word with a zero byte: equal (answer `0`) or relayed to the byte loop. -/
local macro "sc_zero_exit" k:num : tactic => `(tactic| (
  have hz := sc_hz_zero (m := m) (x := P + i) (k := $k) (by decide) hk8 hzk
  by_cases he : wordAt m (P + i + $k) = wordAt m (Q + i + $k)
  · have hw := bne_of_eq he
    kit_run h acc
    have h := h.at (Vsa.Sim.ret_tgt r hra)
    exact ⟨_, acc, .inl ⟨⟨_, h.repin (by pins_of h), sc_ans_zero (p := i + $k) hok hzk he⟩⟩⟩
  · have hw := bne_of_ne he
    kit_run h acc until [0x8003ba04]
    obtain ⟨c', hs, h'⟩ := strcmp_bytes P Q t r sp f m o hx (i + $k)
      (Nat.lt_succ_of_le (sc_le_term hx hok)) hok _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, .inl h'⟩))

set_option hygiene false in
/-- The common start of a word step. -/
local macro "sc_wstart" : tactic => `(tactic| (
  intro c h
  have acc := Steps.refl c
  sc_ctx hx
  have hro := hx.ro
  have hit := sc_le_term hx hok))

/-- **The first word of the loop's body** (`0x8003b938`). -/
theorem strcmp_w0 (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) (i : Nat) (hok : ∀ j, j < i + 0 → ScOk m P Q j) :
    Triple (SegSt 0x8003b938#64 (scW P Q i r sp f) (ArmPay m o))
      (fun c => ScRet r sp f m o P Q c ∨
        ((∀ j, j < i + 8 → ScOk m P Q j) ∧ SegSt 0x8003b958#64 (scW P Q i r sp f) (ArmPay m o) c)) := by
  sc_wstart
  sc_word 0
  by_cases hzk : ∀ j, j < 8 → bytesT1 m (P + i + 0 + j) ≠ 0#8
  · have hz := sc_hz_ok (m := m) (x := P + i) (k := 0) (by decide) hk8 hzk
    by_cases he : wordAt m (P + i + 0) = wordAt m (Q + i + 0)
    · have hw := bne_of_eq he
      kit_run h acc until [0x8003b958]
      exact ⟨_, acc, .inr ⟨sc_ok_word hok hzk he, h.repin (by pins_of h)⟩⟩
    · have hw := bne_of_ne he
      kit_run h acc until [0x8003b9a0]
      obtain ⟨c', hs, h'⟩ := strcmp_hw P Q (i + 0) r sp f m o hra hok hzk he _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, .inl h'⟩
  · sc_zero_exit 0

/-- **The second word** (`0x8003b958`). -/
theorem strcmp_w1 (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) (i : Nat) (hok : ∀ j, j < i + 8 → ScOk m P Q j) :
    Triple (SegSt 0x8003b958#64 (scW P Q i r sp f) (ArmPay m o))
      (fun c => ScRet r sp f m o P Q c ∨
        ((∀ j, j < i + 16 → ScOk m P Q j) ∧ SegSt 0x8003b978#64 (scW P Q i r sp f) (ArmPay m o) c)) := by
  sc_wstart
  sc_word 8
  by_cases hzk : ∀ j, j < 8 → bytesT1 m (P + i + 8 + j) ≠ 0#8
  · have hz := sc_hz_ok (m := m) (x := P + i) (k := 8) (by decide) hk8 hzk
    by_cases he : wordAt m (P + i + 8) = wordAt m (Q + i + 8)
    · have hw := bne_of_eq he
      kit_run h acc until [0x8003b978]
      exact ⟨_, acc, .inr ⟨fun j hj => sc_ok_word hok hzk he j (by omega), h.repin (by pins_of h)⟩⟩
    · have hw := bne_of_ne he
      kit_run h acc until [0x8003b9a0]
      obtain ⟨c', hs, h'⟩ := strcmp_hw P Q (i + 8) r sp f m o hra hok hzk he _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, .inl h'⟩
  · sc_zero_exit 8

/-- **The third word** (`0x8003b978`), then the loop's back edge. -/
theorem strcmp_w2 (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) (i : Nat) (hok : ∀ j, j < i + 16 → ScOk m P Q j) :
    Triple (SegSt 0x8003b978#64 (scW P Q i r sp f) (ArmPay m o))
      (fun c => ScRet r sp f m o P Q c ∨
        ((∀ j, j < i + 24 → ScOk m P Q j) ∧ SegSt 0x8003b938#64 (scW P Q (i + 24) r sp f) (ArmPay m o) c)) := by
  sc_wstart
  sc_word 16
  by_cases hzk : ∀ j, j < 8 → bytesT1 m (P + i + 16 + j) ≠ 0#8
  · have hz := sc_hz_ok (m := m) (x := P + i) (k := 16) (by decide) hk8 hzk
    by_cases he : wordAt m (P + i + 16) = wordAt m (Q + i + 16)
    · have hw := bne_of_eq he
      have hw' : (wordAt m (P + i + 16) == wordAt m (Q + i + 16)) = true := by simp [he]
      kit_run h acc until [0x8003b938]
      exact ⟨_, acc, .inr ⟨fun j hj => sc_ok_word hok hzk he j (by omega), h.repin (by pins_of h)⟩⟩
    · have hw := bne_of_ne he
      have hw' : (wordAt m (P + i + 16) == wordAt m (Q + i + 16)) = false := by simp [he]
      kit_run h acc until [0x8003b9a0]
      obtain ⟨c', hs, h'⟩ := strcmp_hw P Q (i + 16) r sp f m o hra hok hzk he _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, .inl h'⟩
  · sc_zero_exit 16

/-- **The word loop** (`scan_loop`, 24 bytes a pass). -/
theorem strcmp_words (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) : ∀ i, i < t + 1 → (∀ j, j < i → ScOk m P Q j) →
    Triple (SegSt 0x8003b938#64 (scW P Q i r sp f) (ArmPay m o)) (ScRet r sp f m o P Q) :=
  scan_loop (t + 1) (ScOk m P Q) fun i _ hok c h => by
    obtain ⟨c1, hs1, h1⟩ := strcmp_w0 P Q t r sp f m o hx i hok c h
    rcases h1 with h1 | ⟨hok1, h1⟩
    · exact ⟨c1, hs1, .inr h1⟩
    obtain ⟨c2, hs2, h2⟩ := strcmp_w1 P Q t r sp f m o hx i hok1 c1 h1
    rcases h2 with h2 | ⟨hok2, h2⟩
    · exact ⟨c2, hs1.trans hs2, .inr h2⟩
    obtain ⟨c3, hs3, h3⟩ := strcmp_w2 P Q t r sp f m o hx i hok2 c2 h2
    rcases h3 with h3 | ⟨hok3, h3⟩
    · exact ⟨c3, (hs1.trans hs2).trans hs3, .inr h3⟩
    exact ⟨c3, (hs1.trans hs2).trans hs3,
      .inl ⟨i + 24, by omega, Nat.lt_succ_of_le (sc_le_term hx hok3), hok3, h3⟩⟩

/-- `strcmp`'s entry pins. -/
abbrev scPre (P Q : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x11, BitVec.ofNat 64 Q⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, sp⟩ :: f.pins

/-- **`strcmp`, the call-node summary**: the answer at the first position
where the strings differ or `P`'s ends, observed by `CmpObs`. -/
theorem strcmp_sum (P Q t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : ScCtx m P Q t r) :
    Triple (SegSt 0x8003b920#64 (scPre P Q r sp f) (ArmPay m o)) (ScRet r sp f m o P Q) := by
  intro c h
  have acc := Steps.refl c
  sc_ctx hx
  have hro := hx.ro
  have hnil : ∀ j, j < 0 → ScOk m P Q j := fun j hj => absurd hj (Nat.not_lt_zero j)
  by_cases hal : (((BitVec.ofNat 64 P ||| BitVec.ofNat 64 Q) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true
  · kit_run h acc until [0x8003ba04]
    obtain ⟨c', hs, h'⟩ := strcmp_bytes P Q t r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩
  · simp only [Bool.not_eq_true] at hal
    kit_run h acc until [0x8003b938]
    obtain ⟨c', hs, h'⟩ := strcmp_words P Q t r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.Strcmp
import Lua.Vm.Arms.Segs.Hstrlen

/-!
# `strlen` at the Lua ELF's address (round-4 bake-off, S-SCAN)

newlib's `strlen` (`0x8003b770`): a byte scan (`0x8003b7f8`) up to the first
8-aligned address, then a word scan (`0x8003b790`) with the zero-byte test
(`hzW_bytes`, the lane lemma), relaying to the zero byte's lane (`0x8003b7ac`,
eight exits). On a string whose first zero byte is at `t` it returns `t`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- The string at `P` has its first zero byte at `t`; the reads in RAM. -/
structure SlCtx (m : Mem) (P t : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  p_lo : tohostAddr + 16 ≤ P
  p_hi : P + t + 16 ≤ 2 ^ 32
  term : bytesT1 m (P + t) = 0#8
  nz : ∀ j, j < t → bytesT1 m (P + j) ≠ 0#8

/-- `addi` of a negative immediate `k - 4096`. -/
theorem sl_neg {y k : Nat} (hk : 2048 ≤ k ∧ k < 4096) (hy : 4096 - k ≤ y) (hy2 : y < 2 ^ 64) :
    BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (y - (4096 - k)) := by
  rw [imm_neg_add y k hk.1 hk.2]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

theorem sl_sub {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega

/-- `strlen`'s mask, built by `lui; addi; slli 32; add`. -/
theorem sl_mask : (shift_bits_left ((sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0xf7f#12)) (Sail.BitVec.extractLsb (0x20#6) 5 0)) +
    ((sign_extend (m := 64) ((0x7f7f8#20) +++ 0x000#12)) + sign_extend (m := 64) (0xf7f#12)) = maskV := by
  decide

/-- The zero-byte test, `strlen`'s association: no zero byte. -/
theorem sl_hz_ok {m : Mem} {y : Nat} (h : y < 2 ^ 64) (hz : ∀ j, j < 8 → bytesT1 m (y + j) ≠ 0#8) :
    ((((((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 y + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 8))) &&& maskV) + maskV) ||| (sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 y +
        sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)))) ||| maskV) == onesV) = true := by
  rw [addr0 h, sext64_id]
  have e := (hzW_bytes (m := m) (p := y)).2 (by simpa using hz)
  simp only [hzW, maskW] at e
  rw [show maskV = 0x7f7f7f7f7f7f7f7f#64 from rfl, show onesV = (0#64) + sign_extend (m := 64) (0xfff#12) from rfl,
    BitVec.or_assoc, e]; simp

/-- … and with one. -/
theorem sl_hz_zero {m : Mem} {y : Nat} (h : y < 2 ^ 64) (hz : ¬ ∀ j, j < 8 → bytesT1 m (y + j) ≠ 0#8) :
    ((((((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 y + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 8))) &&& maskV) + maskV) ||| (sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 y +
        sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)))) ||| maskV) == onesV) = false := by
  rw [addr0 h, sext64_id]
  have e := hzW_bytes (m := m) (p := y)
  simp only [hzW, maskW] at e
  rw [show maskV = 0x7f7f7f7f7f7f7f7f#64 from rfl, show onesV = (0#64) + sign_extend (m := 64) (0xfff#12) from rfl,
    BitVec.or_assoc, beq_eq_false_iff_ne]
  exact fun e' => hz fun j hj => by simpa using e.1 e' j hj

/-- A byte of the word just read (`lbu (k - 4096)(a4)`), against zero. -/
theorem sl_bz_t {m : Mem} {y k : Nat} (hk : 2048 ≤ k ∧ k < 4096) (hy : 4096 - k ≤ y) (hy2 : y < 2 ^ 64)
    (hz : bytesT1 m (y - (4096 - k)) = 0#8) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat :
      BitVec (8 * 1))) == (0#64)) = true := by
  rw [sl_neg hk hy hy2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), hz]; decide

theorem sl_bz_f {m : Mem} {y k : Nat} (hk : 2048 ≤ k ∧ k < 4096) (hy : 4096 - k ≤ y) (hy2 : y < 2 ^ 64)
    (hz : bytesT1 m (y - (4096 - k)) ≠ 0#8) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat :
      BitVec (8 * 1))) == (0#64)) = false := by
  rw [sl_neg hk hy hy2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    show (0#64 : BitVec 64) = zero_extend (m := 64) ((0#8 : BitVec 8) : BitVec (8 * 1)) by decide, zext8_beq]
  simp [hz]

/-- The byte scan's state at `0x8003b7f8`, position `j`. -/
abbrev slB (P j : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x14, BitVec.ofNat 64 (P + j)⟩ :: ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, sp⟩ :: f.pins

/-- The word scan's state at `0x8003b790`, position `i`. -/
abbrev slW (P i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x14, BitVec.ofNat 64 (P + i)⟩ :: ⟨Register.x13, maskV⟩ :: ⟨Register.x11, onesV⟩ ::
    ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, sl_sub, ones_eq, sl_mask, Nat.add_zero] at $h:ident)

set_option hygiene false in
local macro "sl_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := ($hx).ra; have := ($hx).p_lo; have := ($hx).p_hi))

/-- The first zero byte bounds a scan's position. -/
theorem sl_le {m : Mem} {P t j : Nat} {r : BitVec 64} (hx : SlCtx m P t r) (hj : ∀ i, i < j → bytesT1 m (P + i) ≠ 0#8) :
    j ≤ t := Nat.not_lt.1 fun h => hj t h hx.term

theorem sl_nz_at {m : Mem} {P t : Nat} {r : BitVec 64} (hx : SlCtx m P t r) {a : Nat} (h1 : P ≤ a)
    (h2 : a < P + t) : bytesT1 m a ≠ 0#8 := by
  have := hx.nz (a - P) (by omega); rwa [show P + (a - P) = a by omega] at this

theorem sl_z_at {m : Mem} {P t : Nat} {r : BitVec 64} (hx : SlCtx m P t r) {a : Nat} (h : a = P + t) :
    bytesT1 m a = 0#8 := h ▸ hx.term

theorem sl_byte_t {m : Mem} {y : Nat} (hy : y < 2 ^ 64) (h : bytesT1 m y ≠ 0#8) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 y + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 1))) != 0#64) = true := by
  have := sc_byte_nz (m := m) (P := y) (j := 0) (by omega); simp only [Nat.add_zero] at this
  rw [this]; simp [h]

theorem sl_byte_f {m : Mem} {y : Nat} (hy : y < 2 ^ 64) (h : bytesT1 m y = 0#8) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 y + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 1))) != 0#64) = false := by
  have := sc_byte_nz (m := m) (P := y) (j := 0) (by omega); simp only [Nat.add_zero] at this
  rw [this]; simp [h]

set_option hygiene false in
/-- The value guards of `strlen`, from the string's first zero byte `t`. -/
local macro "sl_guard" : tactic => `(tactic| first
  | exact sl_bz_f (by decide) (by omega) (by omega) (sl_nz_at hx (by omega) (by omega))
  | exact sl_bz_t (by decide) (by omega) (by omega) (sl_z_at hx (by omega))
  | exact sl_byte_t (by omega) (sl_nz_at hx (by omega) (by omega))
  | exact sl_byte_f (by omega) (sl_z_at hx (by omega)))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | sl_guard
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

/-- The word scan's state after a word with a zero byte (`0x8003b7ac`): `a4`
past the word. -/
abbrev slZ (P i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x14, BitVec.ofNat 64 (P + i + 8)⟩ :: ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, sp⟩ :: f.pins

set_option hygiene false in
/-- **One exit of the word scan**: the first zero byte at lane `k`. -/
local macro "sl_lane_thm " n:ident k:num : command => `(
  theorem $n (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
      (hx : SlCtx m P t r) (i : Nat) (e : t = i + $k) :
      Triple (SegSt 0x8003b7ac#64 (slZ P i r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) := by
    intro c h
    have acc := Steps.refl c
    sl_ctx hx
    kit_run h acc
    have h := h.at (Vsa.Sim.ret_tgt r hra)
    exact ⟨_, acc, h.repin (by pins_of h)⟩)

sl_lane_thm strlen_lane0 0
sl_lane_thm strlen_lane1 1
sl_lane_thm strlen_lane2 2
sl_lane_thm strlen_lane3 3
sl_lane_thm strlen_lane4 4
sl_lane_thm strlen_lane5 5

/-- `snez` of a loaded byte. -/
theorem sl_snez (b : BitVec 8) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) (b : BitVec (8 * 1))))) =
      if b = 0#8 then 0#64 else 1#64 := by
  rw [zext8_ofNat, bitb]
  by_cases h : b = 0#8
  · subst h; decide
  · have : b.toNat ≠ 0 := fun e => h (BitVec.eq_of_toNat_eq e)
    have hb := b.isLt
    rw [ite_eq_right_iff.2 (fun e => absurd e h), if_pos]
    simp only [zopz0zI_u, BitVec.toNatInt, BitVec.toNat_ofNat, Nat.zero_mod, decide_eq_true_eq]
    exact Int.ofNat_lt.2 (by rw [Nat.mod_eq_of_lt (by omega)]; omega)

/-- Lanes 6 and 7's answer: `snez(byte 6) + (i + 8) - 2`. -/
theorem sl_val67 {m : Mem} {P i t : Nat} (h6 : bytesT1 m (P + i + 6) = 0#8 → t = i + 6)
    (h7 : bytesT1 m (P + i + 6) ≠ 0#8 → t = i + 7) (hP : P + i + 8 < 2 ^ 64) :
    ((if bytesT1 m (P + i + 6) = 0#8 then 0#64 else 1#64) + BitVec.ofNat 64 (P + i + 8 - P)) +
      sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 t := by
  apply BitVec.eq_of_toNat_eq
  have e2 : (sign_extend (m := 64) (0xffe#12)).toNat = 2 ^ 64 - 2 := by decide
  by_cases hb : bytesT1 m (P + i + 6) = 0#8
  · rw [if_pos hb, BitVec.toNat_add, BitVec.toNat_add, e2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, h6 hb]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]; omega
  · rw [ite_eq_right_iff.2 (fun e => absurd e hb), BitVec.toNat_add, BitVec.toNat_add, e2, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, h7 hb]
    have : (1#64 : BitVec 64).toNat = 1 := rfl
    simp only [BitVec.toNat_ofNat] at *; omega

set_option hygiene false in
/-- Lanes 6 and 7: `a0 = snez(byte 6) + (a4 - a0) - 2`. -/
local macro "sl_lane67" : tactic => `(tactic| (
  intro c h
  have acc := Steps.refl c
  sl_ctx hx
  kit_run h acc until [0x8003b7e0]
  kit_seg h acc Lua.Vm.Arms.seg_8003b7e0_8003b7f4
  have h := h.at (Vsa.Sim.ret_tgt r hra)
  rw [sl_neg (y := P + i + 8) (k := 4094) (by decide) (by omega) (by omega), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), show P + i + 8 - (4096 - 4094) = P + i + 6 by omega, sl_snez,
    sl_val67 (t := t) (fun hb => by first | omega | exact absurd hb (sl_nz_at hx (by omega) (by omega)))
      (fun hb => by first | omega | exact absurd (sl_z_at hx (show P + i + 6 = P + t by omega)) hb)
      (by omega)] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩))

theorem strlen_lane6 (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : SlCtx m P t r) (i : Nat) (e : t = i + 6) :
    Triple (SegSt 0x8003b7ac#64 (slZ P i r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) := by
  sl_lane67

theorem strlen_lane7 (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : SlCtx m P t r) (i : Nat) (e : t = i + 7) :
    Triple (SegSt 0x8003b7ac#64 (slZ P i r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) := by
  sl_lane67

/-- **The word scan** from position `i` (`0x8003b790`): a word with a zero
byte relays to its lane (`strlen_lane0` … `strlen_lane7`). -/
theorem strlen_words (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : SlCtx m P t r) : ∀ i, i < t + 1 → (∀ j, j < i → bytesT1 m (P + j) ≠ 0#8) →
    Triple (SegSt 0x8003b790#64 (slW P i r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) :=
  scan_loop (t + 1) (fun j => bytesT1 m (P + j) ≠ 0#8) fun i hi hok c h => by
    have acc := Steps.refl c
    sl_ctx hx
    by_cases hzk : ∀ j, j < 8 → bytesT1 m (P + i + j) ≠ 0#8
    · have hz := sl_hz_ok (m := m) (y := P + i) (by omega) hzk
      have hok' : ∀ j, j < i + 8 → bytesT1 m (P + j) ≠ 0#8 := fun j hj => by
        rcases Nat.lt_or_ge j i with h' | h'
        · exact hok j h'
        · have := hzk (j - i) (by omega); rwa [show P + i + (j - i) = P + j by omega] at this
      have := sl_le hx hok'
      kit_run h acc until [0x8003b790]
      exact ⟨_, acc, .inl ⟨i + 8, by omega, by omega, hok', h.repin (by pins_of h)⟩⟩
    · have hz := sl_hz_zero (m := m) (y := P + i) (by omega) hzk
      have hit := sl_le hx hok
      have hti : t < i + 8 := Nat.not_le.1 fun h' => hzk fun j hj => sl_nz_at hx (by omega) (by omega)
      kit_run h acc until [0x8003b7ac]
      have h := h.repin (L' := slZ P i r sp f) (by pins_of h)
      rcases (by omega : t = i ∨ t = i + 1 ∨ t = i + 2 ∨ t = i + 3 ∨ t = i + 4 ∨ t = i + 5 ∨ t = i + 6 ∨
        t = i + 7) with e | e | e | e | e | e | e | e
      · obtain ⟨c', hs, h'⟩ := strlen_lane0 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane1 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane2 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane3 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane4 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane5 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane6 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩
      · obtain ⟨c', hs, h'⟩ := strlen_lane7 P t r sp f m o hx i e _ h; exact ⟨c', acc.trans hs, .inr h'⟩

/-- **The byte scan** from position `j` (`0x8003b7f8`) up to the first
aligned address, relaying to the word scan (`relay`). -/
theorem strlen_bytes (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : SlCtx m P t r) : ∀ j, j < t + 1 → (∀ i, i < j → bytesT1 m (P + i) ≠ 0#8) →
    Triple (SegSt 0x8003b7f8#64 (slB P j r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) :=
  fun j hj hok => relay (R := fun i => i < t + 1 ∧ ∀ k, k < i → bytesT1 m (P + k) ≠ 0#8)
    (S := fun i => SegSt 0x8003b790#64 (slW P i r sp f) (ArmPay m o))
    (scan_loop (S := fun j => SegSt 0x8003b7f8#64 (slB P j r sp f) (ArmPay m o))
      (X := fun c => (∃ i, (i < t + 1 ∧ ∀ k, k < i → bytesT1 m (P + k) ≠ 0#8) ∧
        SegSt 0x8003b790#64 (slW P i r sp f) (ArmPay m o) c) ∨ RetAt r sp f m o (BitVec.ofNat 64 t) c)
      (t + 1) (fun k => bytesT1 m (P + k) ≠ 0#8) (fun j hj hok c h => by
      have acc := Steps.refl c
      sl_ctx hx
      by_cases h0 : bytesT1 m (P + j) = 0#8
      · have hjt : j = t := Nat.le_antisymm (Nat.le_of_lt_succ hj) (Nat.not_lt.1 fun h' => hx.nz j h' h0)
        kit_run h acc
        have h := h.at (Vsa.Sim.ret_tgt r hra)
        exact ⟨_, acc, .inr (.inr (h.repin (by pins_of h)))⟩
      · have hok' : ∀ k, k < j + 1 → bytesT1 m (P + k) ≠ 0#8 := fun k hk => by
          rcases Nat.lt_or_ge k j with h' | h'
          · exact hok k h'
          · rwa [show k = j by omega]
        have := sl_le hx hok'
        by_cases hal : ((BitVec.ofNat 64 (P + j + 1) &&& sign_extend (m := 64) (0x007#12)) == 0#64) = true
        · kit_run h acc until [0x8003b790]
          exact ⟨_, acc, .inr (.inl ⟨j + 1, ⟨by omega, hok'⟩, h.repin (by pins_of h)⟩)⟩
        · simp only [Bool.not_eq_true] at hal
          kit_run h acc until [0x8003b7f8]
          exact ⟨_, acc, .inl ⟨j + 1, by omega, by omega, hok', h.repin (by pins_of h)⟩⟩) j hj hok)
    (fun i ⟨hi, hok⟩ => strlen_words P t r sp f m o hx i hi hok)

/-- `strlen`'s entry pins. -/
abbrev slPre (P : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

/-- **`strlen`, the call-node summary**: the index of the first zero byte. -/
theorem strlen_sum (P t : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : SlCtx m P t r) :
    Triple (SegSt 0x8003b770#64 (slPre P r sp f) (ArmPay m o)) (RetAt r sp f m o (BitVec.ofNat 64 t)) := by
  intro c h
  have acc := Steps.refl c
  sl_ctx hx
  have hnil : ∀ j, j < 0 → bytesT1 m (P + j) ≠ 0#8 := fun j hj => absurd hj (Nat.not_lt_zero j)
  by_cases hal : ((BitVec.ofNat 64 P &&& sign_extend (m := 64) (0x007#12)) != 0#64) = true
  · kit_run h acc until [0x8003b7f8]
    obtain ⟨c', hs, h'⟩ := strlen_bytes P t r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩
  · simp only [Bool.not_eq_true] at hal
    kit_run h acc until [0x8003b790]
    obtain ⟨c', hs, h'⟩ := strlen_words P t r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit

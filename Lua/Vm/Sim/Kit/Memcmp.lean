import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Arms.Segs.Hmemcmp

/-!
# `memcmp` at the Lua ELF's address (round-4 bake-off, S-SCAN)

`memcmp(P, Q, n)` (`0x80036198`) as two read-only scans (`scan_loop`): the
word loop (`0x800361dc`, both pointers 8-aligned and `n > 7`) and the byte
loop (`0x800361c0`, rotated: entered by `j` into its middle). The word loop
exits on a differing word *into* the byte loop at that word's position
(`relay`). The summary is quotiented by what `luaS_eqlngstr` observes
(`seqz`): `a0 = 0` iff the `n` bytes agree (`ZRet`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- A string helper's return to `r`: `a0 = v`, `sp` and the caller's frame
`f` kept, memory and console unchanged. -/
abbrev RetAt (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String) (v : BitVec 64) :
    Config → Prop :=
  SegSt r (⟨Register.x10, v⟩ :: ⟨Register.x2, sp⟩ :: f.pins) (ArmPay m o)

/-- **A return observed through `a0 = 0`**: some `a0`, zero iff `Z`. -/
structure ZRet (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String) (Z : Prop) (c : Config) :
    Prop where
  intro ::
  ret : ∃ v, RetAt r sp f m o v c ∧ (v = 0#64 ↔ Z)

/-- Byte `j` of the two ranges agrees. -/
def McEq (m : Mem) (P Q j : Nat) : Prop := bytesT1 m (P + j) = bytesT1 m (Q + j)

instance (m : Mem) (P Q j : Nat) : Decidable (McEq m P Q j) := inferInstanceAs (Decidable (_ = _))

/-- An address plus the zero immediate. -/
theorem addr0 {x : Nat} (h : x < 2 ^ 64) :
    (BitVec.ofNat 64 x + sign_extend (m := 64) (0x000#12)).toNat = x := by
  rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The facts every path uses: the two ranges in RAM apart from `tohost`,
and the return address aligned. -/
structure McCtx (P Q n : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  p_lo : tohostAddr + 16 ≤ P
  p_hi : P + n + 8 ≤ 2 ^ 32
  q_lo : tohostAddr + 16 ≤ Q
  q_hi : Q + n + 8 ≤ 2 ^ 32

/-- The byte loop's state at `0x800361c0`, position `i`. -/
abbrev mcB (P Q n i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + i)⟩ :: ⟨Register.x11, BitVec.ofNat 64 (Q + i)⟩ ::
    ⟨Register.x12, BitVec.ofNat 64 (P + n)⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first | guard_assumption |
      (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

set_option hygiene false in
/-- The context's numeric facts, for `kit_disch`. -/
local macro "mc_ctx" hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := ($hx).ra; have := ($hx).p_lo; have := ($hx).p_hi; have := ($hx).q_lo; have := ($hx).q_hi))

/-- The byte guard `beq a5, a4` on byte `i`. -/
theorem mc_byte_guard {m : Mem} {P Q i : Nat} (hp : P + i < 2 ^ 64) (hq : Q + i < 2 ^ 64) :
    ((zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 (P + i) + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 1))) == (zero_extend (m := 64) (bytesT1 m (BitVec.ofNat 64 (Q + i) +
        sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 1)))) = decide (McEq m P Q i) := by
  rw [addr0 hp, addr0 hq, zext8_beq]; rfl

/-- `beq a2, a0` against the end `P + n`. -/
theorem mc_end_guard {P n i : Nat} (h : P + n < 2 ^ 64) (hi : i < n) :
    (BitVec.ofNat 64 (P + n) == BitVec.ofNat 64 (P + i) + sign_extend (m := 64) (0x001#12)) =
      decide (i + 1 = n) := by
  rw [add_imm _ 1 (by decide)]
  by_cases e : i + 1 = n
  · subst e; simp [Nat.add_assoc]
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro h2; have := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (by omega)] at this; omega

/-- **The byte loop** from position `i` (`0x800361c0`), no difference
before `i`. -/
theorem memcmp_bytes (P Q n : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : McCtx P Q n r) : ∀ i, i < n → (∀ j, j < i → McEq m P Q j) →
    Triple (SegSt 0x800361c0#64 (mcB P Q n i r sp f) (ArmPay m o))
      (ZRet r sp f m o (∀ j, j < n → McEq m P Q j)) :=
  scan_loop n (McEq m P Q) fun i hi hok c h => by
    have acc := Steps.refl c
    mc_ctx hx
    have hg := mc_byte_guard (m := m) (P := P) (Q := Q) (i := i) (by omega) (by omega)
    by_cases he : McEq m P Q i
    · simp only [he, decide_true] at hg
      have hg2 := mc_end_guard (P := P) (n := n) (i := i) (by omega) hi
      by_cases hend : i + 1 = n
      · simp only [hend, decide_true] at hg2
        kit_run h acc
        have h := h.at (Vsa.Sim.ret_tgt r hx.ra)
        refine ⟨_, acc, .inr ⟨⟨_, h.repin (by pins_of h), ?_⟩⟩⟩
        simp only [Vsa.Sim.sext_zero, BitVec.add_zero, true_iff]
        intro j hj; rcases Nat.lt_or_ge j i with hj' | hj'
        · exact hok j hj'
        · rwa [show j = i by omega]
      · simp only [hend, decide_false] at hg2
        kit_run h acc until [0x800361c0]
        refine ⟨_, acc, .inl ⟨i + 1, by omega, by omega, fun j hj => ?_, h.repin (by pins_of h)⟩⟩
        rcases Nat.lt_or_ge j i with hj' | hj'
        · exact hok j hj'
        · rwa [show j = i by omega]
    · simp only [he, decide_false] at hg
      kit_run h acc
      have h := h.at (Vsa.Sim.ret_tgt r hx.ra)
      refine ⟨_, acc, .inr ⟨⟨_, h.repin (by pins_of h), ?_⟩⟩⟩
      simp only [McEq] at he
      rw [addr0 (by omega), addr0 (by omega)]
      exact ⟨fun e => absurd e (subw_bytes_ne he), fun hall => absurd (hall i hi) he⟩

/-! ## The word loop and the entry -/

/-- `li a3, 7`. -/
abbrev seven : BitVec 64 := (0#64) + sign_extend (m := 64) (0x007#12)

/-- The state at `0x800361ac` (the byte loop's set-up), position `i`. -/
abbrev mcA (P Q n i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x12, BitVec.ofNat 64 (n - i)⟩ :: ⟨Register.x10, BitVec.ofNat 64 (P + i)⟩ ::
    ⟨Register.x11, BitVec.ofNat 64 (Q + i)⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

/-- The word loop's state at `0x800361dc`, position `i`. -/
abbrev mcW (P Q n i : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + i)⟩ :: ⟨Register.x11, BitVec.ofNat 64 (Q + i)⟩ ::
    ⟨Register.x12, BitVec.ofNat 64 (n - i)⟩ :: ⟨Register.x13, seven⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, sp⟩ :: f.pins

/-- `add a2, a0, a2` after `addi a2,-1; addi a2,1`: the end. -/
theorem mc_end (a d : Nat) :
    BitVec.ofNat 64 a + ((BitVec.ofNat 64 d + sign_extend (m := 64) (0xfff#12)) +
      sign_extend (m := 64) (0x001#12)) = BitVec.ofNat 64 (a + d) := by
  rw [BitVec.add_assoc (BitVec.ofNat 64 d), show sign_extend (m := 64) (0xfff#12) +
    sign_extend (m := 64) (0x001#12) = 0#64 by decide, BitVec.add_zero, BitVec.ofNat_add_ofNat]

/-- `addi a2, a2, -8`. -/
theorem mc_sub8 {d : Nat} (h : 8 ≤ d) :
    BitVec.ofNat 64 d + sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (d - 8) := by
  rw [show sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) by decide,
    BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- The word guard `bne a4, a5`. -/
theorem mc_word_guard {m : Mem} {P Q i : Nat} (hp : P + i < 2 ^ 64) (hq : Q + i < 2 ^ 64) :
    ((sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 (P + i) + sign_extend (m := 64) (0x000#12)).toNat :
      BitVec (8 * 8))) != (sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 (Q + i) +
        sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)))) =
      !decide (bytesT8 m (P + i) = bytesT8 m (Q + i)) := by
  rw [addr0 hp, addr0 hq, sext64_id, sext64_id]; rfl

/-- A word's lanes, as positions `i + k`. -/
theorem mc_lanes {m : Mem} {P Q i : Nat} :
    bytesT8 m (P + i) = bytesT8 m (Q + i) ↔ ∀ k, k < 8 → McEq m P Q (i + k) := by
  rw [bytesT8_eq_iff]; simp only [McEq, Nat.add_assoc]

/-- `bltu a3, a2` after the decrement: another word. -/
theorem mc_ult_guard {d : Nat} (h : 8 ≤ d) (h2 : d < 2 ^ 64) :
    zopz0zI_u seven (BitVec.ofNat 64 d + sign_extend (m := 64) (0xff8#12)) = decide (16 ≤ d) := by
  rw [mc_sub8 h]
  simp only [zopz0zI_u, BitVec.toNatInt, show seven.toNat = 7 by decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show d - 8 < 2 ^ 64 by omega)]
  by_cases e : 16 ≤ d <;> simp [e] <;> omega

/-- `bgeu a3, a2` at the entry: at most 7 bytes. -/
theorem mc_uge_guard {n : Nat} (h : n < 2 ^ 64) :
    zopz0zKzJ_u seven (BitVec.ofNat 64 n) = decide (n ≤ 7) := by
  simp only [zopz0zKzJ_u, BitVec.toNatInt, show seven.toNat = 7 by decide, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt h]
  by_cases e : n ≤ 7 <;> simp [e] <;> omega

/-- `bnez a2`. -/
theorem mc_nz_guard {d : Nat} (h : d < 2 ^ 64) : (BitVec.ofNat 64 d != 0#64) = !decide (d = 0) := by
  by_cases e : d = 0
  · subst e; rfl
  · simp only [e, decide_false, Bool.not_false, bne_iff_ne, ne_eq]
    intro h2; have := congrArg BitVec.toNat h2; simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt h] at this; exact e this

/-- **The byte loop's set-up** (`0x800361ac`): the end `P + n`, then the
byte loop from `i`. -/
theorem memcmp_tail (P Q n : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : McCtx P Q n r) (i : Nat) (hi : i < n) (hok : ∀ j, j < i → McEq m P Q j) :
    Triple (SegSt 0x800361ac#64 (mcA P Q n i r sp f) (ArmPay m o))
      (ZRet r sp f m o (∀ j, j < n → McEq m P Q j)) := by
  intro c h
  have acc := Steps.refl c
  kit_run h acc until [0x800361c0]
  rw [mc_end, show P + i + (n - i) = P + n by omega] at h
  obtain ⟨c', hs, h'⟩ := memcmp_bytes P Q n r sp f m o hx i hi hok _ (h.repin (by pins_of h))
  exact ⟨c', acc.trans hs, h'⟩

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic| simp only [mc_sub8 h8] at $h:ident)

/-- **The word loop** from position `i` (`0x800361dc`): a differing word
relays to the byte loop at its position (`memcmp_tail`). -/
theorem memcmp_words (P Q n : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : McCtx P Q n r) : ∀ i, i < n → (∀ j, j < i → McEq m P Q j) →
    Triple (fun c => 8 ≤ n - i ∧ SegSt 0x800361dc#64 (mcW P Q n i r sp f) (ArmPay m o) c)
      (ZRet r sp f m o (∀ j, j < n → McEq m P Q j)) :=
  scan_loop n (McEq m P Q) fun i hi hok c ⟨h8, h⟩ => by
    have acc := Steps.refl c
    mc_ctx hx
    have hw := mc_word_guard (m := m) (P := P) (Q := Q) (i := i) (by omega) (by omega)
    by_cases hall : bytesT8 m (P + i) = bytesT8 m (Q + i)
    · simp only [hall, decide_true, Bool.not_true] at hw
      have hok' : ∀ j, j < i + 8 → McEq m P Q j := fun j hj => by
        rcases Nat.lt_or_ge j i with hj' | hj'
        · exact hok j hj'
        · have := mc_lanes.1 hall (j - i) (by omega); rwa [show i + (j - i) = j by omega] at this
      have hu := mc_ult_guard (d := n - i) h8 (by omega)
      by_cases h16 : 16 ≤ n - i
      · simp only [h16, decide_true] at hu
        kit_run h acc until [0x800361dc]
        exact ⟨_, acc, .inl ⟨i + 8, by omega, by omega, hok', by omega,
          h.repin (by pins_of h)⟩⟩
      · simp only [h16, decide_false] at hu
        by_cases hz0 : n - i - 8 = 0
        · have hz : (BitVec.ofNat 64 (n - i - 8) != 0#64) = false := by
            rw [mc_nz_guard (by omega)]; simp [hz0]
          kit_run h acc until [0x800361f8]
          kit_run h acc
          have h := h.at (Vsa.Sim.ret_tgt r hx.ra)
          refine ⟨_, acc, .inr ⟨⟨_, h.repin (by pins_of h), ?_⟩⟩⟩
          simp only [Vsa.Sim.sext_zero, BitVec.add_zero, true_iff]
          exact fun j hj => hok' j (by omega)
        · have hz : (BitVec.ofNat 64 (n - i - 8) != 0#64) = true := by
            rw [mc_nz_guard (by omega)]; simp [hz0]
          kit_run h acc until [0x800361ac]
          obtain ⟨c', hs, h'⟩ := memcmp_tail P Q n r sp f m o hx (i + 8) (by omega) hok' _
            (h.repin (by pins_of h))
          exact ⟨c', acc.trans hs, .inr h'⟩
    · simp only [hall, decide_false, Bool.not_false] at hw
      kit_run h acc until [0x800361ac]
      obtain ⟨c', hs, h'⟩ := memcmp_tail P Q n r sp f m o hx i hi hok _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, .inr h'⟩

/-- `memcmp`'s entry pins. -/
abbrev mcPre (P Q n : Nat) (r sp : BitVec 64) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x11, BitVec.ofNat 64 Q⟩ ::
    ⟨Register.x12, BitVec.ofNat 64 n⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x2, sp⟩ :: f.pins

/-- **`memcmp`, the call-node summary**: `a0 = 0` iff the `n` bytes at `P`
and `Q` agree. -/
theorem memcmp_sum (P Q n : Nat) (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String)
    (hx : McCtx P Q n r) :
    Triple (SegSt 0x80036198#64 (mcPre P Q n r sp f) (ArmPay m o))
      (ZRet r sp f m o (∀ j, j < n → McEq m P Q j)) := by
  intro c h
  have acc := Steps.refl c
  mc_ctx hx
  have hu := mc_uge_guard (n := n) (by omega)
  have hnil : ∀ j, j < 0 → McEq m P Q j := fun j hj => absurd hj (Nat.not_lt_zero j)
  by_cases h7 : n ≤ 7
  · simp only [h7, decide_true] at hu
    by_cases hz0 : n = 0
    · have hz : (BitVec.ofNat 64 n != 0#64) = false := by rw [mc_nz_guard (by omega)]; simp [hz0]
      kit_run h acc
      have h := h.at (Vsa.Sim.ret_tgt r hx.ra)
      refine ⟨_, acc, ⟨_, h.repin (by pins_of h), ?_⟩⟩
      simp only [Vsa.Sim.sext_zero, BitVec.add_zero, true_iff]
      exact fun j hj => absurd hj (by omega)
    · have hz : (BitVec.ofNat 64 n != 0#64) = true := by rw [mc_nz_guard (by omega)]; simp [hz0]
      kit_run h acc until [0x800361ac]
      obtain ⟨c', hs, h'⟩ := memcmp_tail P Q n r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩
  · simp only [h7, decide_false] at hu
    by_cases hal : (((BitVec.ofNat 64 Q ||| BitVec.ofNat 64 P) &&& sign_extend (m := 64) (0x007#12)) ==
        (0#64)) = true
    · kit_run h acc until [0x800361dc]
      obtain ⟨c', hs, h'⟩ := memcmp_words P Q n r sp f m o hx 0 (by omega) hnil _
        ⟨by omega, h.repin (by pins_of h)⟩
      exact ⟨c', acc.trans hs, h'⟩
    · simp only [Bool.not_eq_true] at hal
      kit_run h acc until [0x800361ac]
      obtain ⟨c', hs, h'⟩ := memcmp_tail P Q n r sp f m o hx 0 (by omega) hnil _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit

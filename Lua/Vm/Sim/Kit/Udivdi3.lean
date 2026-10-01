import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms.Segs.Hhidden___udivdi3
import Vsa.Sim.DivLoops
import Vsa.Sim.Muldi3Spec

/-!
# `__udivdi3` at the Lua ELF's address: the call-node summary (M5)

`udivdi3_sum`: from `0x8002f734` with `a0 = n`, `a1 = d ≠ 0`, `ra = r`, `t0`
and the caller's frame, the helper returns to `r` with `a0 = n / d` and
`a1 = n % d`, the rest unchanged. Two loops over the generated helper
segments: the normalise loop (`udiv_norm`, `a2 = d·2^k`, `a3 = 2^k` doubling
until `n < 2·a2`) and the restoring divide loop (`udiv_div`, ship-your-
interpreter's invariant `n = d·a0 + a1`, `a1 < 2·a2`). The arithmetic lemmas
are ship-your-interpreter's (`Vsa/Sim/DivLoops.lean`, `Vsa/Sim/DivSpec.lean`,
copied; ATTRIBUTION.md); the machine runs are `kit_run`'s.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [Vsa.Sim.sext_zero, Vsa.Sim.sext_one,
      BitVec.add_zero, Vsa.Sim.shr_shamt, Vsa.Sim.shl_shamt])

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- The pins of `__udivdi3`'s loops: `a1`, `a2`, `a3`, `ra`, `t0`, the frame. -/
abbrev udPins (a1 a2 a3 r t : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x11, a1⟩ :: ⟨Register.x12, a2⟩ :: ⟨Register.x13, a3⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x5, t⟩ :: f.pins

/-- The normalise loop's exit: `a2 = d·2^k`, `a3 = 2^k`, and `n < 2·a2`. -/
structure NormOut (d n a2 a3 : BitVec 64) : Prop where
  k : NrmK d a2 a3
  cover : n.toNat < 2 * a2.toNat

/-- The normalise loop from its head `0x8002f74c` (`blez a2`), by the
measure `2^64 - a2`. -/
theorem udiv_norm (n d r t : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hd : 0 < d.toNat) : ∀ N (a2 a3 : BitVec 64), 2^64 - a2.toNat < N → NrmK d a2 a3 →
    a2.toNat < n.toNat →
    Triple (SegSt 0x8002f74c#64 (udPins n a2 a3 r t f) (ArmPay m o))
      (fun c => ∃ a2 a3, SegSt 0x8002f75c#64 (udPins n a2 a3 r t f) (ArmPay m o) c ∧
        NormOut d n a2 a3)
  | 0, _, _, hN, _, _ => absurd hN (Nat.not_lt_zero _)
  | N + 1, a2, a3, hN, ⟨k, hk2, hk3, hkb⟩, hlt => by
    intro c h
    have acc := Steps.refl c
    have ha2pos : 0 < a2.toNat := by rw [hk2]; exact Nat.mul_pos hd (Nat.two_pow_pos k)
    have ha2ne : a2 ≠ 0#64 := fun e => by rw [e] at ha2pos; simp at ha2pos
    rcases blez_cases a2 with g | g
    · have htop := toInt_nonpos_top a2 (blez_true a2 g) ha2ne
      kit_run h acc until [0x8002f75c]
      exact ⟨_, acc, a2, a3, h.repin (by pins_of h), ⟨k, hk2, hk3, hkb⟩, by omega⟩
    · have hnotop := toInt_pos_notop a2 (blez_false a2 g)
      have hpk : (2:Nat)^(k+1) = 2 * 2^k := by rw [Nat.pow_succ, Nat.mul_comm]
      have hd2 : (a2 <<< (1:Nat)).toNat = d.toNat * 2^(k+1) := by
        rw [shl_double a2 hnotop, hk2, hpk, Nat.mul_left_comm]
      have hd3 : (a3 <<< (1:Nat)).toNat = 2^(k+1) := by
        have : 2^k ≤ d.toNat * 2^k := Nat.le_mul_of_pos_left _ hd
        rw [shl_double a3 (by omega), hk3, hpk]
      have hK : NrmK d (a2 <<< (1:Nat)) (a3 <<< (1:Nat)) :=
        ⟨k + 1, hd2, hd3, by rw [hd2] at *; rw [hpk, Nat.mul_left_comm]; omega⟩
      rcases bltu_cases (a2 <<< (1:Nat)) n with g' | g'
      · kit_run h acc until [0x8002f74c]
        obtain ⟨c', hs, h'⟩ := udiv_norm n d r t f m o hd N (shift_bits_left a2 sh1)
          (shift_bits_left a3 sh1) (by rw [shl_shamt]; have := normMeasure_lt a2 ha2pos hnotop; omega)
          (by rw [shl_shamt, shl_shamt]; exact hK) (by rw [shl_shamt]; exact bltu_true _ _ g') _
          (h.repin (by pins_of h))
        exact ⟨c', acc.trans hs, h'⟩
      · kit_run h acc until [0x8002f75c]
        have := bltu_false _ _ g'
        refine ⟨_, acc, _, _, h.repin (by pins_of h), ?_, ?_⟩
        · rw [shl_shamt, shl_shamt]; exact hK
        · rw [shl_shamt]; omega

/-- The divide loop's invariant at its head `0x8002f760`, bit `j`. -/
structure DivInv (d n a0 a1 a2 a3 : BitVec 64) (j : Nat) : Prop where
  k : DivK d a2 a3 j
  low : a0.toNat % 2^(j+1) = 0
  eq : n.toNat = d.toNat * a0.toNat + a1.toNat
  lt : a1.toNat < 2 * a2.toNat

/-- ... after the iteration's compare-and-subtract, at `0x8002f76c`. -/
structure DivMid (d n a0 a1 a2 a3 : BitVec 64) (j : Nat) : Prop where
  k : DivK d a2 a3 j
  low : a0.toNat % 2^j = 0
  eq : n.toNat = d.toNat * a0.toNat + a1.toNat
  lt : a1.toNat < a2.toNat

/-- The loop's result: quotient and remainder. -/
abbrev udPost (n d r t : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, n / d⟩ :: ⟨Register.x11, n % d⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x5, t⟩ :: f.pins

/-- The division result from `n = d·a0 + a1`, `a1 < d`. -/
theorem udiv_of (n d a0 a1 : BitVec 64) (hd : 0 < d.toNat) (he : n.toNat = d.toNat * a0.toNat + a1.toNat)
    (hl : a1.toNat < d.toNat) : n / d = a0 ∧ n % d = a1 := by
  have := (Nat.div_mod_unique (a := n.toNat) (d := a0.toNat) (c := a1.toNat) hd).2 ⟨by omega, hl⟩
  refine ⟨BitVec.eq_of_toNat_eq ?_, BitVec.eq_of_toNat_eq ?_⟩
  · rw [BitVec.toNat_udiv]; exact this.1
  · rw [BitVec.toNat_umod]; exact this.2

/-- The loop's tail from `0x8002f76c` (the halvings and `bnez a3`), given the
loop from its head one bit lower. -/
theorem udiv_tail (n d r t : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hd : 0 < d.toNat) (j : Nat)
    (ih : 1 ≤ j → ∀ a0 a1 a2 a3, DivInv d n a0 a1 a2 a3 (j - 1) →
      Triple (SegSt 0x8002f760#64 (⟨Register.x10, a0⟩ :: udPins a1 a2 a3 r t f) (ArmPay m o))
        (SegSt 0x8002f778#64 (udPost n d r t f) (ArmPay m o)))
    (a0 a1 a2 a3 : BitVec 64) (hm : DivMid d n a0 a1 a2 a3 j) :
    Triple (SegSt 0x8002f76c#64 (⟨Register.x10, a0⟩ :: udPins a1 a2 a3 r t f) (ArmPay m o))
      (SegSt 0x8002f778#64 (udPost n d r t f) (ArmPay m o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨⟨hk2, hk3, hkb⟩, hlow, heq, hlt⟩ := hm
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have hz : a3 >>> (1:Nat) = 0#64 := by
      apply BitVec.eq_of_toNat_eq; rw [a3_half a3 0 hk3]; decide
    kit_run h acc until [0x8002f778]
    obtain ⟨e1, e2⟩ := udiv_of n d a0 a1 hd heq (by simp at hk2; omega)
    simp only [udPost, e1, e2]
    exact ⟨_, acc, h.repin (by pins_of h)⟩
  · have ha3h : (a3 >>> (1:Nat)).toNat = 2^(j-1) := by rw [a3_half a3 j hk3, half_pow j hj]
    have hz : ¬ a3 >>> (1:Nat) = 0#64 := fun e => by
      rw [e] at ha3h; have := Nat.two_pow_pos (j-1); simp at ha3h; omega
    kit_run h acc until [0x8002f760]
    have hle : d.toNat * 2^(j-1) ≤ d.toNat * 2^j :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega))
    obtain ⟨c', hs, h'⟩ := ih hj a0 a1 (shift_bits_right a2 sh1) (shift_bits_right a3 sh1)
      ⟨⟨by rw [shr_shamt]; exact a2_half d a2 j hj hk2, by rw [shr_shamt]; exact ha3h, by omega⟩,
        by rw [show j - 1 + 1 = j by omega]; exact hlow, heq,
        by rw [shr_shamt, a2_half d a2 j hj hk2, two_mul_pow_pred d.toNat j hj, ← hk2]; exact hlt⟩
      _ (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩

/-- The divide loop from its head `0x8002f760` (`bltu a1,a2`), by `j`. -/
theorem udiv_div (n d r t : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hd : 0 < d.toNat) : ∀ j a0 a1 a2 a3, DivInv d n a0 a1 a2 a3 j →
    Triple (SegSt 0x8002f760#64 (⟨Register.x10, a0⟩ :: udPins a1 a2 a3 r t f) (ArmPay m o))
      (SegSt 0x8002f778#64 (udPost n d r t f) (ArmPay m o))
  | j, a0, a1, a2, a3, ⟨⟨hk2, hk3, hkb⟩, hlow, heq, hlt⟩ => by
    intro c h
    have acc := Steps.refl c
    have ih : 1 ≤ j → ∀ a0 a1 a2 a3, DivInv d n a0 a1 a2 a3 (j - 1) → _ :=
      fun hj => udiv_div n d r t f m o hd (j - 1)
    rcases bltu_cases a1 a2 with g | g
    · kit_run h acc until [0x8002f76c]
      obtain ⟨c', hs, h'⟩ := udiv_tail n d r t f m o hd j ih a0 a1 a2 a3
        ⟨⟨hk2, hk3, hkb⟩, mod_drop_pow a0.toNat j hlow, heq, bltu_true _ _ g⟩ _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩
    · have hge := bltu_false _ _ g
      have hsub : (a1 - a2).toNat = a1.toNat - a2.toNat := BitVec.toNat_sub_of_le (BitVec.le_def.mpr hge)
      have hor := or_a3_toNat a0 a3 j hk3 hlow
      kit_run h acc until [0x8002f76c]
      obtain ⟨c', hs, h'⟩ := udiv_tail n d r t f m o hd j ih (a0 ||| a3) (a1 - a2) a2 a3
        ⟨⟨hk2, hk3, hkb⟩, by rw [hor]; exact mod_add_pow a0.toNat j hlow,
          by rw [hor, hsub, Nat.mul_add, ← hk2]; omega, by rw [hsub]; omega⟩ _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩
  termination_by j => j
  decreasing_by omega

/-- **`__udivdi3`, the call-node summary.** -/
theorem udivdi3_sum (n d r t : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hd : d ≠ 0#64) (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f734#64 (⟨Register.x10, n⟩ :: ⟨Register.x11, d⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x5, t⟩ :: f.pins) (ArmPay m o))
      (SegSt r (udPost n d r t f) (ArmPay m o)) := by
  intro c h
  have acc := Steps.refl c
  have hd' : 0 < d.toNat := Nat.pos_of_ne_zero fun e => hd (BitVec.eq_of_toNat_eq e)
  -- to the divide loop's entry, with the normalised divisor
  have hn : ∃ c1 a2 a3, Steps c c1 ∧ SegSt 0x8002f75c#64 (udPins n a2 a3 r t f) (ArmPay m o) c1 ∧
      NormOut d n a2 a3 := by
    have hK : NrmK d d 1#64 := ⟨0, by simp, by simp, by simpa using d.isLt⟩
    rcases bgeu_cases d n with g | g
    · kit_run h acc until [0x8002f75c]
      simp only [Vsa.Sim.sext_zero, Vsa.Sim.sext_one, BitVec.add_zero, BitVec.zero_add] at h
      exact ⟨_, _, _, acc, h.repin (by pins_of h), hK, by have := bgeu_true _ _ g; omega⟩
    · kit_run h acc until [0x8002f74c]
      simp only [Vsa.Sim.sext_zero, Vsa.Sim.sext_one, BitVec.add_zero, BitVec.zero_add] at h
      obtain ⟨c1, hs, a2, a3, h1, hno⟩ := udiv_norm n d r t f m o hd' (2^64 + 1) d 1#64
        (by omega) hK (bgeu_false _ _ g) _ (h.repin (by pins_of h))
      exact ⟨c1, a2, a3, acc.trans hs, h1, hno⟩
  obtain ⟨c1, a2, a3, acc, h, ⟨⟨k, hk2, hk3, hkb⟩, hcov⟩⟩ := hn
  kit_run h acc until [0x8002f760]
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  obtain ⟨c2, hs, h⟩ := udiv_div n d r t f m o hd' k 0#64 n a2 a3
    ⟨⟨hk2, hk3, hkb⟩, by simp, by simp, hcov⟩ _ (h.repin (by pins_of h))
  have acc := acc.trans hs
  kit_run h acc
  exact ⟨_, acc, (h.at (Vsa.Sim.ret_tgt r hr)).repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit

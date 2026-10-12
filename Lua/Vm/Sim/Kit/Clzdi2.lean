import Lua.Vm.Sim.Kit.Fn
import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Sim.Kit.Shift
import Lua.Vm.Arms.Segs.Hclzdi2

/-!
# `__clzdi2` at the Lua ELF's address: the call-node summary (lane float-m0)

libgcc's table-driven count of leading zeros (`libgcc2.c` `__clzDI2`, the
generic `count_leading_zeros` over `__clz_tab`): the loop scans the bytes of
`x` from the top (`a5 = 56, 48, …, 8`) for a nonzero one, then adds the bit
length of that byte from `__clz_tab` (`.rodata`). The scan is `scan_loop`
over the byte positions (`Kit/Scan.lean`, S-SCAN), the event "byte `j` is
zero" (`clzZero`); the summary `clzdi2_sum` returns `clz64 x = 64 - bitlen x`
(`bitlen 0 = 0`, so `clz64 0 = 64`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Vsa.Machine (MState Config Steps)

/-- The number of bits of `n` (`0` for `0`). -/
def bitlen (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- **Count leading zeros** of a 64-bit word (`64` for `0`). -/
def clz64 (x : BitVec 64) : BitVec 64 := BitVec.ofNat 64 (64 - bitlen x.toNat)

theorem bitlen_le (n k : Nat) (h : n < 2 ^ k) : bitlen n ≤ k := by
  unfold bitlen; split
  · omega
  · have := (Nat.log2_lt (by omega)).2 h; omega

/-- The bit length of `k · 2^s + r`, `0 < k`, `r < 2^s`. -/
theorem bitlen_shift (k s r : Nat) (hk : k ≠ 0) (hr : r < 2 ^ s) :
    bitlen (k * 2 ^ s + r) = bitlen k + s := by
  have hp : 0 < 2 ^ s := Nat.two_pow_pos s
  have hn : k * 2 ^ s + r ≠ 0 := by
    have := Nat.mul_le_mul_right (2 ^ s) (Nat.one_le_iff_ne_zero.2 hk); omega
  unfold bitlen
  rw [if_neg hn, if_neg hk]
  have hl := (Nat.log2_eq_iff (n := k * 2 ^ s + r) (k := k.log2 + s) hn).2 ⟨?_, ?_⟩
  · omega
  · rw [Nat.pow_add]
    exact Nat.le_trans (Nat.mul_le_mul_right _ (Nat.log2_self_le hk)) (Nat.le_add_right _ _)
  · have h1 : k < 2 ^ (k.log2 + 1) := (Nat.log2_lt hk).1 (Nat.lt_succ_self _)
    have h2 : (k + 1) * 2 ^ s ≤ 2 ^ (k.log2 + 1) * 2 ^ s := Nat.mul_le_mul_right _ h1
    rw [show k.log2 + s + 1 = (k.log2 + 1) + s by omega, Nat.pow_add]
    rw [Nat.add_mul, Nat.one_mul] at h2
    omega

/-! ## `__clz_tab` -/

/-- `__clz_tab`'s address, as the tail's `auipc`/`addi` computes it. -/
def clzTab : Nat :=
  (((0x8002f804#64) + sign_extend (m := 64) ((0x00025#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0x8bc#12)).toNat

theorem clzTab_a1 : ((0x8002f804#64) + sign_extend (m := 64) ((0x00025#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0x8bc#12) = BitVec.ofNat 64 clzTab := by decide

/-- The found branch's `auipc`/`addi` computes the same address. -/
theorem clzTab_a2 : ((0x8002f82c#64) + sign_extend (m := 64) ((0x00025#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0x894#12) = BitVec.ofNat 64 clzTab := by decide

/-- The table lies in `.rodata`. -/
theorem clzTab_in : Image.rodataBase ≤ clzTab ∧ clzTab + 256 ≤ Image.rodataBase + Image.rodataSize ∧
    0x80000000 ≤ Image.rodataBase := by decide

/-- **`__clz_tab[i]` is the bit length of `i`** (one kernel check of the 256
bytes of the image). -/
theorem clzTab_byte : ∀ i, i < 256 →
    Image.rodataByte (clzTab - Image.rodataBase + i) = BitVec.ofNat 8 (bitlen i) := by
  decide +kernel

theorem clzTab_read {m : Mem} (hrod : RodataRead m) {i : Nat} (hi : i < 256) :
    bytesT1 m (clzTab + i) = BitVec.ofNat 8 (bitlen i) := by
  have := clzTab_in
  have h := hrod (clzTab - Image.rodataBase + i) (by omega)
  rw [show Image.rodataBase + (clzTab - Image.rodataBase + i) = clzTab + i by omega] at h
  rw [h, clzTab_byte i hi]

theorem tab_addr' (k : BitVec 64) (hk : k.toNat < 256) :
    ((BitVec.ofNat 64 clzTab + (k + sign_extend (m := 64) (0x000#12))) + sign_extend (m := 64) (0x000#12)).toNat =
      clzTab + k.toNat := by
  have := clzTab_in
  have : Image.rodataBase + Image.rodataSize < 2 ^ 64 := by decide
  rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem tab_addr (k : BitVec 64) (hk : k.toNat < 256) :
    ((BitVec.ofNat 64 clzTab + k) + sign_extend (m := 64) (0x000#12)).toNat = clzTab + k.toNat := by
  have := clzTab_in
  have : Image.rodataBase + Image.rodataSize < 2 ^ 64 := by decide
  rw [Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-! ## The scan -/

/-- The loop head `0x8002f7f0` scanning byte `i` from the top (`a5 = 56 - 8i`). -/
abbrev clzSt (x r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String) (i : Nat) :
    Config → Prop :=
  SegSt 0x8002f7f0#64 (⟨Register.x10, x⟩ :: ⟨Register.x15, BitVec.ofNat 64 (56 - 8 * i)⟩ ::
    ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o)

/-- Byte `j` from the top of `x` is zero. -/
def clzZero (x : BitVec 64) (j : Nat) : Prop := x.toNat / 2 ^ (56 - 8 * j) % 256 = 0

/-- No set bit in the top `i` bytes. -/
theorem clz_lt (x : BitVec 64) : ∀ i, i ≤ 8 → (∀ j, j < i → clzZero x j) → x.toNat < 2 ^ (64 - 8 * i)
  | 0, _, _ => x.isLt
  | i + 1, hi, h => by
    have ih := clz_lt x i (by omega) fun j hj => h j (by omega)
    have hz := h i (by omega)
    unfold clzZero at hz
    have e1 : 64 - 8 * i = (56 - 8 * i) + 8 := by omega
    have e2 : 64 - 8 * (i + 1) = 56 - 8 * i := by omega
    rw [e1, Nat.pow_add] at ih
    rw [e2]
    have hq : x.toNat / 2 ^ (56 - 8 * i) < 2 ^ 8 := (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      (by rw [Nat.mul_comm]; exact ih)
    have hq0 : x.toNat / 2 ^ (56 - 8 * i) = 0 := by
      rw [← Nat.mod_eq_of_lt (show x.toNat / 2 ^ (56 - 8 * i) < 256 from hq)]; exact hz
    exact (Nat.div_eq_zero_iff_lt (Nat.two_pow_pos _)).1 hq0

/-- The byte test `(x >> a5) & 0xff ≠ 0` as a `Nat` fact. -/
theorem clz_byte (x : BitVec 64) (s : Nat) (hs : s < 64) :
    ((shift_bits_right x (Sail.BitVec.extractLsb (BitVec.ofNat 64 s) 5 0)) &&&
      sign_extend (m := 64) (0x0ff#12)) = BitVec.ofNat 64 (x.toNat / 2 ^ s % 256) := by
  rw [srl_eq, show sign_extend (m := 64) (0x0ff#12) = 255#64 by decide]
  apply BitVec.eq_of_toNat_eq
  have : x.toNat / 2 ^ s % 2 ^ 8 < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt hs,
    show (255 : Nat) % 2 ^ 64 = 2 ^ 8 - 1 by decide, Nat.and_two_pow_sub_one_eq_mod]
  rw [Nat.mod_eq_of_lt (show x.toNat / 2 ^ s % 256 < 2 ^ 64 by omega)]

theorem clz_shr (x : BitVec 64) (s : Nat) (hs : s < 64) :
    (shift_bits_right x (Sail.BitVec.extractLsb (BitVec.ofNat 64 s) 5 0)).toNat = x.toNat / 2 ^ s := by
  simp only [srl_eq, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show s < 2 ^ 64 by omega), Nat.mod_eq_of_lt hs]

/-- `addi a5, a5, -8` at the loop's bottom. -/
theorem clz_step (i : Nat) (hi : i < 7) :
    BitVec.ofNat 64 (56 - 8 * i) + sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (56 - 8 * (i + 1)) := by
  rw [show sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) by decide,
    BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- The found branch's `subw` (`64 - a5 - __clz_tab[x >> a5]`). -/
theorem clz_sub_found : ∀ i, i < 8 → ∀ b, b < 9 →
    sign_extend (m := 64) ((Sail.BitVec.extractLsb (((0#64) + sign_extend (m := 64) (0x040#12)) -
      BitVec.ofNat 64 (56 - 8 * i)) 31 0) - (Sail.BitVec.extractLsb (zero_extend (m := 64)
      (BitVec.ofNat 8 b : BitVec (8 * 1))) 31 0)) = BitVec.ofNat 64 (8 + 8 * i - b) := by
  decide

/-- The tail's `subw` (`64 - __clz_tab[x]`, `x < 256`). -/
theorem clz_sub_tail : ∀ b, b < 9 →
    sign_extend (m := 64) ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) -
      (Sail.BitVec.extractLsb (zero_extend (m := 64) (BitVec.ofNat 8 b : BitVec (8 * 1))) 31 0)) =
      BitVec.ofNat 64 (64 - b) := by
  decide

/-- **`__clzdi2`, the call-node summary.** -/
theorem clzdi2_sum (x r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String) (hrod : RodataRead m)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f7ec#64 (⟨Register.x10, x⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, clz64 x⟩ :: f.pins) (ArmPay m o)) := by
  have hT := clzTab_in
  have hR := Lua.Vm.Sim.rodata_below_tohost
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  -- the scan from byte `i`
  have scan := scan_loop (S := clzSt x r f m o) (X := SegSt r (⟨Register.x10, clz64 x⟩ :: f.pins)
    (ArmPay m o)) 7 (clzZero x) (fun i hi hok c h => by
    dsimp only [clzSt] at h
    have acc := Vsa.Machine.Steps.refl c
    have hlt := clz_lt x i (by omega) hok
    have hs : 56 - 8 * i < 64 := by omega
    by_cases hz : x.toNat / 2 ^ (56 - 8 * i) % 256 = 0
    · -- byte `i` is zero: next byte, or the tail at `a5 = 0`
      obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
        (Lua.Vm.Arms.seg_8002f7f0_8002f7fc_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (by rw [clz_byte x _ hs, hz]; decide))
      by_cases h7 : i < 6
      · obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
          (Lua.Vm.Arms.seg_8002f7fc_8002f804_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [clz_step i (by omega)]; simp only [bne_iff_ne, ne_eq]
                intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega))
        rw [clz_step i (by omega)] at h
        refine ⟨_, acc, .inl ⟨i + 1, by omega, by omega, fun j hj => ?_, h.repin (by pins_of h)⟩⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact hok j hj
        · exact hz
      · have h7 : i = 6 := by omega
        subst h7
        obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
          (Lua.Vm.Arms.seg_8002f7fc_8002f804_n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by decide))
        have hx : x.toNat < 256 := by
          have := clz_lt x 7 (by omega) fun j hj => ?_
          · simpa using this
          · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact hok j hj
            · exact hz
        have ha := tab_addr x hx
        rw [← clzTab_a1] at ha
        obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
          (Lua.Vm.Arms.seg_8002f804_8002f820 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
            (by rw [ha]; omega) (by rw [ha]; omega) (by rw [ha]; omega)
            (by rw [fn_tgt0 hr]; exact hr))
        rw [ha, clzTab_read hrod hx, clz_sub_tail _ (by have := bitlen_le x.toNat 8 hx; omega)] at h
        exact ⟨_, acc, .inr ((h.at (fn_tgt0 hr)).repin (by pins_of h))⟩
    · -- byte `i` is set: the found branch
      obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
        (Lua.Vm.Arms.seg_8002f7f0_8002f7fc_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (by rw [clz_byte x _ hs]; simp only [bne_iff_ne, ne_eq]
              intro e; have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega))
      have hk : x.toNat / 2 ^ (56 - 8 * i) < 256 := by
        have e1 : 64 - 8 * i = (56 - 8 * i) + 8 := by omega
        rw [e1, Nat.pow_add] at hlt
        exact (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2 (by rw [Nat.mul_comm]; exact hlt)
      have hk' : (shift_bits_right x (Sail.BitVec.extractLsb (BitVec.ofNat 64 (56 - 8 * i)) 5 0)).toNat < 256 := by
        rw [clz_shr x _ hs]; exact hk
      have ha := tab_addr' _ hk'
      rw [← clzTab_a2] at ha
      obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
        (Lua.Vm.Arms.seg_8002f820_8002f844 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
          (by rw [ha]; omega) (by rw [ha]; omega) (by rw [ha]; omega)
          (by rw [fn_tgt0 hr]; exact hr))
      rw [ha, clzTab_read hrod hk', clz_shr x _ hs] at h
      have hb := bitlen_le _ 8 hk
      rw [clz_sub_found i (by omega) _ (by omega)] at h
      have hnz : x.toNat / 2 ^ (56 - 8 * i) ≠ 0 := by
        intro e; rw [e] at hz; exact hz rfl
      have hlen : 8 + 8 * i - bitlen (x.toNat / 2 ^ (56 - 8 * i)) = 64 - bitlen x.toNat := by
        have := bitlen_shift (x.toNat / 2 ^ (56 - 8 * i)) (56 - 8 * i) (x.toNat % 2 ^ (56 - 8 * i)) hnz
          (Nat.mod_lt _ (Nat.two_pow_pos _))
        rw [Nat.div_add_mod'] at this
        omega
      rw [hlen] at h
      exact ⟨_, acc, .inr ((h.at (fn_tgt0 hr)).repin (by pins_of h))⟩)
  intro c h
  have acc := Vsa.Machine.Steps.refl c
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (by pins_of h)
    (Lua.Vm.Arms.seg_8002f7ec_8002f7f0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
  rw [show ((0#64) + sign_extend (m := 64) (0x038#12)) = BitVec.ofNat 64 (56 - 8 * 0) by decide] at h
  obtain ⟨c', hs, h'⟩ := scan 0 (by omega) (fun j hj => absurd hj (Nat.not_lt_zero _)) _
    (h.repin (by pins_of h))
  exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim

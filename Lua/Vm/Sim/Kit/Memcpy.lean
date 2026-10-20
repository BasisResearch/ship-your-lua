import Lua.Vm.Sim.Kit.Memmove
import Lua.Vm.Sim.Kit.FmtLib
import Lua.Vm.AtF.Memcpy

/-!
# `memcpy(dst, src, n)` on 8-aligned disjoint ranges (lane F1-20)

`internshrstr`'s creation path copies the new string's contents with `memcpy`
(`0x8003b648`) from `luaO_pushvfstring`'s buffer (its frame, 16-aligned) into
the new object (`_malloc_r`'s block, 16-aligned, plus 24). Its at-lemmas are
generated (`Lua/Vm/AtF/Memcpy.lean`, `scripts/gen_lua_at.py --fn memcpy`):
the entry's paths, the word loop and the byte loop as roots. This file runs
the loops by `seg_loop` with the copy so far as the invariant (`MoveOut`,
`Kit/Memmove.lean`), the guards the generator leaves symbolic by the size
arithmetic below.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-! ## The size arithmetic -/

/-- `andi rd, rs, -8` on a Nat-valued register: the value rounded down to 8. -/
theorem andm8 (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (8 * (x / 8)) := by
  rw [show sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 18446744073709551608 by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  rw [show 8 * (x / 8) = 2 ^ 3 * (x / 2 ^ 3) by rfl, Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases h3 : 3 ≤ i
  · have e : (18446744073709551608 : Nat) = 2 ^ 3 * (2 ^ 61 - 1) := by decide
    rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
    simp only [h3, decide_true, Bool.true_and, show i - 3 + 3 = i by omega]
    have : i - 3 < 61 := by omega
    simp [this]
  · have e : (18446744073709551608 : Nat) = 2 ^ 3 * (2 ^ 61 - 1) := by decide
    rw [e, Nat.testBit_two_pow_mul]
    simp [h3]

/-- Two 8-aligned addresses: their `xor`'s low three bits are zero. -/
theorem xor_al (s d : Nat) (hs : s % 8 = 0) (hd : d % 8 = 0) :
    (((BitVec.ofNat 64 s) ^^^ (BitVec.ofNat 64 d)) &&& sign_extend (m := 64) (0x007#12) != (0#64)) = false := by
  rw [show sign_extend (m := 64) (0x007#12) = BitVec.ofNat 64 7 by decide]
  simp only [bne_eq_false_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  by_cases h3 : i < 3
  · have e1 : s = 2 ^ 3 * (s / 8) := by omega
    have e2 : d = 2 ^ 3 * (d / 8) := by omega
    rw [e1, e2, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
    simp [show ¬ (3 ≤ i) by omega]
  · have : (7 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by
      calc 7 < 2 ^ 3 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
    simp [this]

/-- The `n < 8` test (`sltiu a2, a2, 8; bnez`). -/
theorem sltiu8 (n : Nat) (hn : n < 2 ^ 64) :
    ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (BitVec.ofNat 64 n) (sign_extend (m := 64) (0x008#12))))) !=
      (0#64)) = decide (n < 8) := by
  rw [show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 by decide, fult hn (by decide)]
  by_cases h : n < 8 <;> simp [h] <;> decide

/-- The word loop's bound from the entry (`andi a2, a7, -8` of `dst + n`). -/
theorem endW (d n : Nat) (hd : d % 8 = 0) (h : d + n < 2 ^ 64) :
    BitVec.ofNat 64 (d + n) &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (d + 8 * (n / 8)) := by
  rw [andm8 _ h]; congr 1; omega

/-- The 64-byte test (`blt 64, a3`) on the word span. -/
theorem blt64 (d n : Nat) (hd : d % 8 = 0) (h : d + n < 2 ^ 64) (hn : n ≤ 64) :
    zopz0zI_s ((0#64) + sign_extend (m := 64) (0x040#12))
      (((BitVec.ofNat 64 (d + n)) &&& sign_extend (m := 64) (0xff8#12)) - (BitVec.ofNat 64 d)) = false := by
  rw [endW d n hd h, show (0#64 : BitVec 64) + sign_extend (m := 64) (0x040#12) = BitVec.ofNat 64 64 by decide,
    show BitVec.ofNat 64 (d + 8 * (n / 8)) - BitVec.ofNat 64 d = BitVec.ofNat 64 (8 * (n / 8)) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]; omega]
  simp only [zopz0zI_s, fmt_toInt_ofNat (show 64 < 2 ^ 63 by decide),
    fmt_toInt_ofNat (show 8 * (n / 8) < 2 ^ 63 by omega), decide_eq_false_iff_not]
  omega

/-- `(d + 8 w - 1 - d) & -8 = 8 (w - 1)` (the word loop's exit arithmetic). -/
theorem tailD (d w : Nat) (hw : 1 ≤ w) (h : d + 8 * w < 2 ^ 64) :
    ((((BitVec.ofNat 64 (d + 8 * w)) + sign_extend (m := 64) (0xfff#12)) - (BitVec.ofNat 64 d)) &&&
      sign_extend (m := 64) (0xff8#12)) = BitVec.ofNat 64 (8 * (w - 1)) := by
  have e : (BitVec.ofNat 64 (d + 8 * w)) + sign_extend (m := 64) (0xfff#12) - BitVec.ofNat 64 d =
      BitVec.ofNat 64 (8 * w - 1) := by
    rw [show sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 18446744073709551615 by decide]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have h1 : (d + 8 * w) % 2 ^ 64 = d + 8 * w := Nat.mod_eq_of_lt h
    have h2 : d % 2 ^ 64 = d := Nat.mod_eq_of_lt (by omega)
    have h3 : (8 * w - 1) % 2 ^ 64 = 8 * w - 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1, h2, h3]
    generalize hT : (2 : Nat) ^ 64 = T at *
    have : T = 18446744073709551616 := by rw [← hT]
    subst this
    omega
  rw [e, andm8 _ (by omega)]; congr 1; omega

/-- The cursors after the words (`+ 8 + 8 (w - 1)`). -/
theorem tailW (s d w : Nat) (hw : 1 ≤ w) (h : d + 8 * w < 2 ^ 64) :
    ((BitVec.ofNat 64 s) + sign_extend (m := 64) (0x008#12)) + ((((BitVec.ofNat 64 (d + 8 * w)) +
      sign_extend (m := 64) (0xfff#12)) - (BitVec.ofNat 64 d)) &&& sign_extend (m := 64) (0xff8#12)) =
      BitVec.ofNat 64 (s + 8 * w) := by
  rw [tailD d w hw h, show sign_extend (m := 64) (0x008#12) = BitVec.ofNat 64 8 by decide,
    BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  congr 1; omega

/-! ## The loops -/

/-- A context of `memcpy`'s rows: `sp`, the Nat atoms, `ra`, the frame. -/
@[at_row] abbrev mcpCx (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] M o

/-- What `memcpy(dst, src, n)` needs: both 8-aligned, the ranges apart, in
RAM, off `tohost`, `n ≤ 64`, the return target aligned. -/
structure McpCtx (sp dst src n : Nat) (r : BitVec 64) : Prop where
  span : MmSpan dst src n
  sp_hi : sp ≤ 2 ^ 32
  ra : r.toNat % 4 = 0
  n_hi : n ≤ 64
  d_al : dst % 8 = 0
  s_al : src % 8 = 0

/-- **The byte loop** (`0x8003b6c8`) from `i` of the `n` bytes. -/
theorem mcp_bytes (sp d s n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : McpCtx sp d s n r) :
    ∀ i M, i < n → MoveOut m M d s i →
      Triple (SegSt 0x8003b6c8#64 (Lua.Vm.AtF.Memcpy.r14 (mcpCx [sp, d, s, n, i] r f M o))
          (ArmPay (mcpCx [sp, d, s, n, i] r f M o).m (mcpCx [sp, d, s, n, i] r f M o).o))
        (fun c => ∃ M', mmRet r sp (BitVec.ofNat 64 d) f M' o c ∧ MoveOut m M' d s n) := by
  intro i₀ M₀ hi₀ hM₀ c₀ h₀
  obtain ⟨hk, hsp, hra, hn64, hda, hsa⟩ := hx
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < n ∧ MoveOut m p.2 d s p.1 ∧
      SegSt 0x8003b6c8#64 (Lua.Vm.AtF.Memcpy.r14 (mcpCx [sp, d, s, n, p.1] r f p.2 o))
        (ArmPay (mcpCx [sp, d, s, n, p.1] r f p.2 o).m (mcpCx [sp, d, s, n, p.1] r f p.2 o).o) c)
    (fun p => n - p.1) (fun ⟨i, M⟩ c ⟨hi, hM, h⟩ => ?_) (i₀, M₀) c₀ ⟨hi₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memcpy.Ok_B (mcpCx [sp, d, s, n, i] r f M o) := by fcx_ok
  have acc := Steps.refl c
  have hb : bytesT1 M (s + i) = bytesT1 m (s + i) := hM.rd1 (by omega)
  have hM' := hM.ins (a := d + i) (b := bytesT1 m (s + i)) (by omega) rfl
  by_cases he : i + 1 = n
  · fat_run Lua.Vm.AtF.Memcpy h acc
    fcx_unfold at h
    rw [hb, stData_zext] at h
    exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memcpy h acc until [0x8003b6c8]
    fcx_unfold at h
    rw [hb, stData_zext] at h
    refine ⟨_, acc, .inl ⟨(i + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

/-- **The word loop** (`0x8003b688`) from `i` of `w = n / 8` words, then the
`n % 8` byte tail, then the return. -/
theorem mcp_words (sp d s n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : McpCtx sp d s n r) (hw : 1 ≤ n / 8) :
    ∀ i M, i < n / 8 → MoveOut m M d s (8 * i) →
      Triple (SegSt 0x8003b688#64 (Lua.Vm.AtF.Memcpy.r9 (mcpCx [sp, d, s, n, i, n / 8] r f M o))
          (ArmPay (mcpCx [sp, d, s, n, i, n / 8] r f M o).m (mcpCx [sp, d, s, n, i, n / 8] r f M o).o))
        (fun c => ∃ M', mmRet r sp (BitVec.ofNat 64 d) f M' o c ∧ MoveOut m M' d s n) := by
  intro i₀ M₀ hi₀ hM₀ c₀ h₀
  have hx' := hx
  obtain ⟨hk, hsp, hra, hn64, hda, hsa⟩ := hx'
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < n / 8 ∧ MoveOut m p.2 d s (8 * p.1) ∧
      SegSt 0x8003b688#64 (Lua.Vm.AtF.Memcpy.r9 (mcpCx [sp, d, s, n, p.1, n / 8] r f p.2 o))
        (ArmPay (mcpCx [sp, d, s, n, p.1, n / 8] r f p.2 o).m (mcpCx [sp, d, s, n, p.1, n / 8] r f p.2 o).o) c)
    (fun p => n / 8 - p.1) (fun ⟨i, M⟩ c ⟨hi, hM, h⟩ => ?_) (i₀, M₀) c₀ ⟨hi₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memcpy.Ok_W (mcpCx [sp, d, s, n, i, n / 8] r f M o) := by fcx_ok
  have acc := Steps.refl c
  have hv : bytesT8 M (s + 8 * i) = bytesT8 m (s + 8 * i) := hM.rd8 (by omega)
  have hM' := hM.wm8 (a := d + 8 * i) (v := bytesT8 m (s + 8 * i)) (by omega) rfl
  by_cases he : i + 1 = n / 8
  · have hgt : zopz0zI_u ((((BitVec.ofNat 64 d) + sign_extend (m := 64) (0x008#12)) + ((((BitVec.ofNat 64
        (d + 8 * (n / 8))) + sign_extend (m := 64) (0xfff#12)) - (BitVec.ofNat 64 d)) &&& sign_extend (m := 64)
        (0xff8#12)))) (BitVec.ofNat 64 (d + n)) = decide (8 * (n / 8) < n) := by
      rw [tailW d d (n / 8) hw (by omega), fult (by omega) (by omega)]; simp only [decide_eq_decide]; omega
    by_cases h8 : 8 * (n / 8) < n
    · have hg1 := hgt.trans (decide_eq_true h8)
      fat_run Lua.Vm.AtF.Memcpy h acc until [0x8003b6c8]
      fcx_unfold at h
      rw [hv, tailW d d (n / 8) hw (by omega), tailW s d (n / 8) hw (by omega)] at h
      obtain ⟨c2, s2, M2, hr, hMo⟩ := mcp_bytes sp d s n r f m o hx (8 * (n / 8))
        (writeMap8 M (d + 8 * i) (sdData_val (bytesT8 m (s + 8 * i)))) h8 (hM'.mono (by omega)) _
        (by fcx_unfold; exact h.repin (by at_pins h))
      exact ⟨c2, acc.trans s2, .inr ⟨M2, hr, hMo⟩⟩
    · have hg1 := hgt.trans (decide_eq_false h8)
      fat_run Lua.Vm.AtF.Memcpy h acc
      fcx_unfold at h
      rw [hv] at h
      exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memcpy h acc until [0x8003b688]
    fcx_unfold at h
    rw [hv] at h
    refine ⟨_, acc, .inl ⟨(i + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

/-! ## The entry -/

/-- **`memcpy(dst, src, n)` on 8-aligned disjoint ranges** (`n ≤ 64`): `dst`
returned, the `n` source bytes at `dst`, every other byte unchanged
(`MoveOut`). -/
theorem memcpy_sum (sp dst src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : McpCtx sp dst src n r) :
    Triple (SegSt 0x8003b648#64 (callPre [⟨Register.x10, BitVec.ofNat 64 dst⟩,
        ⟨Register.x11, BitVec.ofNat 64 src⟩, ⟨Register.x12, BitVec.ofNat 64 n⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', mmRet r sp (BitVec.ofNat 64 dst) f m' o c ∧ MoveOut m m' dst src n) := by
  intro c h
  have hx' := hx
  obtain ⟨hk, hsp, hra, hn64, hda, hsa⟩ := hx'
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hX : Lua.Vm.AtF.Memcpy.Ok (mcpCx [sp, dst, src, n] r f m o) := by fcx_ok
  have h : SegSt 0x8003b648#64 (Lua.Vm.AtF.Memcpy.r0 (mcpCx [sp, dst, src, n] r f m o))
      (ArmPay (mcpCx [sp, dst, src, n] r f m o).m (mcpCx [sp, dst, src, n] r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  have hg4 := xor_al src dst hsa hda
  have hg2 := sltiu8 n (by omega)
  by_cases hn0 : n = 0
  · subst hn0
    rw [decide_eq_true (show 0 < 8 by decide)] at hg2
    fat_run Lua.Vm.AtF.Memcpy h acc
    exact ⟨_, acc, _, h.repin (by pins_of h), MoveOut.zero m dst src⟩
  by_cases hs8 : n < 8
  · rw [decide_eq_true hs8] at hg2
    fat_run Lua.Vm.AtF.Memcpy h acc until [0x8003b6c8]
    obtain ⟨c2, s2, M2, hr, hMo⟩ := mcp_bytes sp dst src n r f m o hx 0 m (by omega) (MoveOut.zero m dst src) _
      (by fcx_unfold at h ⊢; exact h.repin (by at_pins h))
    exact ⟨c2, acc.trans s2, M2, hr, hMo⟩
  · rw [decide_eq_false hs8] at hg2
    have hg4' := blt64 dst n hda (by omega) hn64
    have hg3 : zopz0zKzJ_u (BitVec.ofNat 64 dst) (((BitVec.ofNat 64 (dst + n)) &&&
        sign_extend (m := 64) (0xff8#12))) = false := by
      rw [endW dst n hda (by omega), fuge (by omega) (by omega)]; simp only [decide_eq_false_iff_not]; omega
    fat_run Lua.Vm.AtF.Memcpy h acc until [0x8003b688]
    fcx_unfold at h
    rw [endW dst n hda (by omega)] at h
    obtain ⟨c2, s2, M2, hr, hMo⟩ := mcp_words sp dst src n r f m o hx (by omega) 0 m (by omega)
      (MoveOut.zero m dst src) _ (by fcx_unfold; exact h.repin (by at_pins h))
    exact ⟨c2, acc.trans s2, M2, hr, hMo⟩

end Lua.Vm.Sim.Kit

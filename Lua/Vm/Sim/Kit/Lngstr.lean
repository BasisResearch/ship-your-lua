import Lua.Vm.Sim.Kit.Memcmp
import Lua.Vm.Sim.Kit.Str
import Lua.Vm.Arms.Segs.HluaS_eqlngstr

/-!
# `luaS_eqlngstr` at the Lua ELF's address (round-4 bake-off, S-SCAN)

`luaS_eqlngstr(a, b)` (`0x80017184`, lstring.c): the same object is equal;
different `lnglen`s are unequal; otherwise `memcmp` of the contents (the
call node `memcmp_sum`), seen through `seqz`. On two viewed long strings
(`StrView`, M-str) the result is `δ .eq`'s answer as 0/1. The memory changes
only in the callee frame `[sp - 16, sp)` (`ra` saved for the call):
`RetOut`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **A return with the memory changed only in `[lo, hi)`**: some memory
`m'` agreeing with `m` outside, `a0 = v`. -/
structure RetOut (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String) (lo hi : Nat)
    (v : BitVec 64) (c : Config) : Prop where
  intro ::
  out : ∃ m', AgreeOut m' m lo hi ∧ RetAt r sp f m' o v c

/-- What `luaS_eqlngstr` needs: two viewed long strings apart from the
callee frames below `sp`, the same object only for one content. -/
structure LngCtx (m : Mem) (sp : Nat) (r : BitVec 64) (t1 t2 : Nat) (s1 s2 : List UInt8) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 48 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  v1 : StrView m t1 s1
  v2 : StrView m t2 s2
  long1 : maxShortLen < s1.length
  long2 : maxShortLen < s2.length
  ap1 : StrApart t1 s1 (sp - 64) sp
  ap2 : StrApart t2 s2 (sp - 64) sp
  inj : t1 = t2 → s1 = s2

/-- `luaS_eqlngstr`'s entry pins. -/
abbrev lsPre (t1 t2 : Nat) (r : BitVec 64) (sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 t1⟩ :: ⟨Register.x11, BitVec.ofNat 64 t2⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins

theorem ofNat_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a = b) := by
  by_cases h : a = b
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this; exact h this

theorem addr_imm {x k : Nat} (hk : k < 2048) (h : x + k < 2 ^ 64) :
    (BitVec.ofNat 64 x + sign_extend (m := 64) (BitVec.ofNat 12 k)).toNat = x + k := by
  rw [add_imm x k hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- `addi sp, sp, -16` then `+16`. -/
theorem sp_back16 (x : BitVec 64) :
    x + sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x010#12) = x := by
  rw [BitVec.add_assoc, show sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x010#12)
    = 0#64 by decide, BitVec.add_zero]

/-- `seqz` of `memcmp`'s answer. -/
theorem seqz_ite (v : BitVec 64) (P : Prop) [Decidable P] (h : v = 0#64 ↔ P) :
    zero_extend (m := 64) (bool_to_bit (zopz0zI_u v (sign_extend (m := 64) (0x001#12)))) +
      sign_extend (m := 64) (0x000#12) = if P then 1#64 else 0#64 := by
  have e1 : zopz0zI_u v (sign_extend (m := 64) (0x001#12)) = decide (v = 0#64) := by
    have := ult_one_sub v 0#64; rwa [BitVec.sub_zero] at this
  rw [e1, bitb, Vsa.Sim.sext_zero, BitVec.add_zero]
  by_cases hp : P <;> simp [hp, h]

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra)
      | (rw [ld_ra, Vsa.Sim.ret_tgt _ hra]; exact hra))

/-- **`luaS_eqlngstr`, the call-node summary**: on two viewed long strings,
`a0` is `1` iff their contents are equal. -/
theorem eqlngstr_sum (t1 t2 : Nat) (s1 s2 : List UInt8) (r : BitVec 64) (sp : Nat) (f : KFrame)
    (m : Mem) (o : Array String) (hx : LngCtx m sp r t1 t2 s1 s2) :
    Triple (SegSt 0x80017184#64 (lsPre t1 t2 r sp f) (ArmPay m o))
      (RetOut r (BitVec.ofNat 64 sp) f m o (sp - 16) sp (if s1 = s2 then 1#64 else 0#64)) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := hx.ra; have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al
  have h1 := hx.v1; have h2 := hx.v2
  have := h1.lo; have := h1.hi; have := h2.lo; have := h2.hi
  simp only [DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at *
  have hg := ofNat_beq (a := t1) (b := t2) (by omega) (by omega)
  by_cases he : t1 = t2
  · simp only [he, decide_true] at hg
    subst he
    kit_run h acc
    have h := h.at (Vsa.Sim.ret_tgt r hra)
    rw [ite_eq_left_iff.2 (fun e => absurd (hx.inj rfl) e)]
    exact ⟨_, acc, ⟨⟨_, AgreeOut.refl _ _ _, h.repin (by pins_of h)⟩⟩⟩
  · simp only [he, decide_false] at hg
    have hl := (h2.lnglen_eq h1 hx.long2 hx.long1)
    have hl' : (sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 t2 + sign_extend (m := 64) (0x010#12)).toNat :
        BitVec (8 * 8)) == sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 t1 +
          sign_extend (m := 64) (0x010#12)).toNat : BitVec (8 * 8))) = decide (s2.length = s1.length) := by
      rw [addr_imm (by decide) (by omega), addr_imm (by decide) (by omega), sext64_id, sext64_id]
      simp only [tstringLnglenOff] at hl
      by_cases e : s2.length = s1.length
      · rw [hl.2 e]; simp [e]
      · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]; exact fun h' => e (hl.1 h')
    by_cases hlen : s2.length = s1.length
    · simp only [hlen, decide_true] at hl'
      kit_run h acc until [0x80036198]
      have hL : sign_extend (m := 64) (bytesT8 m (BitVec.ofNat 64 t2 + sign_extend (m := 64) (0x010#12)).toNat :
          BitVec (8 * 8)) = BitVec.ofNat 64 s1.length := by
        rw [addr_imm (by decide) (by omega), sext64_id, ← hlen]; exact h2.lnglen hx.long2
      simp only [hL] at h
      -- the contents, read through the `ra` store
      have hap1 := hx.ap1; have hap2 := hx.ap2
      simp only [StrApart, tstringContentsOff] at hap1 hap2
      have hk : ((BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x008#12)).toNat
          = sp - 8 := by
        rw [BitVec.add_assoc, show sign_extend (m := 64) (0xff0#12) + sign_extend (m := 64) (0x008#12) =
          BitVec.ofNat 64 (2 ^ 64 - 8) by decide, BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat]; omega
      have w1 := h1.wm8 (lo := sp - 64) (hi := sp) hx.ap1 (a := sp - 8) (by omega) (by omega) (sdData_val r)
      have w2 := h2.wm8 (lo := sp - 64) (hi := sp) hx.ap2 (a := sp - 8) (by omega) (by omega) (sdData_val r)
      rw [← hk] at w1 w2
      obtain ⟨_, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h)
        (memcmp_sum (t1 + 24) (t2 + 24) s1.length 0x800171b4#64
          (BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12)) f _ o
          ⟨by decide, by omega, by omega, by omega, by omega⟩)
      dsimp only [RetAt] at h
      kit_run h acc
      have h := h.at (by rw [ld_ra, Vsa.Sim.ret_tgt r hra])
      rw [sp_back16, seqz_ite v (s1 = s2) (hv.trans (w1.eq_iff w2 hlen.symm).symm)] at h
      exact ⟨_, acc, ⟨⟨_, AgreeOut.writeMap8 (AgreeOut.refl m (sp - 16) sp) (sdData_val r)
        (k := ((BitVec.ofNat 64 sp + sign_extend (m := 64) (0xff0#12)) + sign_extend (m := 64) (0x008#12)).toNat)
        (by rw [hk]; omega) (by rw [hk]; omega), h.repin (by pins_of h)⟩⟩⟩
    · simp only [hlen, decide_false] at hl'
      kit_run h acc
      have h := h.at (Vsa.Sim.ret_tgt r hra)
      rw [ite_eq_right_iff.2 (fun e => absurd (by rw [e]) hlen)]
      exact ⟨_, acc, ⟨⟨_, AgreeOut.refl _ _ _, h.repin (by pins_of h)⟩⟩⟩

end Lua.Vm.Sim.Kit

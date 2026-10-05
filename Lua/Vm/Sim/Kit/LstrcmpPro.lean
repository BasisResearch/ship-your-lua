import Lua.Vm.Sim.Kit.Lstrcmp

/-!
# `l_strcmp`'s prologue and summary (round-4 bake-off, S-SCAN)

The prologue saves `ra, s0–s4` in `[sp - 48, sp)` and reads each string's
length (`shrlen`, or `lnglen` when `shrlen = 0xFF`), then enters the chunk
loop at its first call site (a long second string) or its loop call site.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout Lua.Bytecode
open Vsa.Machine (MState Config Steps)

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

/-! ## The prologue and the summary -/

/-- `l_strcmp`'s entry pins. -/
abbrev lstrPre (t1 t2 : Nat) (r : BitVec 64) (sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 t1⟩ :: ⟨Register.x11, BitVec.ofNat 64 t2⟩ :: ⟨Register.x1, r⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins

theorem ff_toNat : ((0#64) + sign_extend (m := 64) (0x0ff#12)).toNat = 255 := by decide

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_zero,
    sext64_id, bytesT1_writeMap8_out, bytesT8_wm8_out, zext8_ofNat, hsh1, hsh2, hln1, hln2] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (bool_goal
         simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, bytesT1_writeMap8_out,
          hsh1, hsh2, zext8_ofNat, bne_toNat, ff_toNat, Bool.not_eq_true', Bool.not_eq_false',
          decide_eq_true_eq, decide_eq_false_iff_not] <;> omega))

set_option hygiene false in
/-- The saved registers of the prologue's stores. -/
local macro "ls_frame" : tactic => `(tactic|
  exact ⟨rfl, fun x hx => by simp (disch := kit_disch) only [getElem?_wm8_out],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id],
    by simp (disch := kit_disch) only [bytesT8_wm8_out, bytesT8_wm8_same, sdData_id]⟩)

set_option hygiene false in
/-- The strings' C views through the prologue's stores. -/
local macro "ls_mem" : tactic => `(tactic|
  exact ⟨fun j hj => by simp (disch := kit_disch) only [bytesT1_writeMap8_out]; exact v1.cb_at hj,
    fun j hj => by simp (disch := kit_disch) only [bytesT1_writeMap8_out]; exact v2.cb_at hj,
    by omega, by omega, by show _ ≤ 0x87800000 + 8; omega, by show _ ≤ 0x87800000 + 8; omega,
    RodataRead.agree (lo := sp - 48) (hi := sp) hx.ro (fun x hx' => by simp (disch := kit_disch) only [getElem?_wm8_out])
      (by have := rodata_below_tohost; omega)⟩)

set_option hygiene false in
/-- The prologue's facts: the two strings' views and lengths. -/
local macro "ls_pro" l1:term "," l2:term : tactic => `(tactic| (
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hra := hx.ra; have hsp := hx.sp_lo; have hsp2 := hx.sp_hi; have := hx.sp_al
  have v1 := hx.a1.view; have v2 := hx.a2.view
  have ap1 := hx.a1.apart; have ap2 := hx.a2.apart
  have h1lo := v1.lo; have h1hi := v1.hi; have h2lo := v2.lo; have h2hi := v2.hi
  simp only [StrApart, DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at ap1 ap2 h1hi h2hi
  have hsh1 := v1.shrlen; have hsh2 := v2.shrlen
  have hln1 := v1.lnglen; have hln2 := v2.lnglen
  simp only [tstringShrlenOff, tstringLnglenOff, maxShortLen, $l1:term, $l2:term, ↓reduceIte] at hsh1 hsh2 hln1 hln2
  try replace hln1 := hln1 trivial
  try replace hln2 := hln2 trivial
  have hA : Agree s1 s2 0 := ⟨Nat.zero_le _, Nat.zero_le _, fun j _ _ hj => absurd hj (Nat.not_lt_zero j)⟩))

theorem _root_.Vsa.Sim.SegSt.mem_name {pc : BitVec 64} {L : List Pin} {m : Mem} {o : Array String} {c : Config}
    (h : SegSt pc L (ArmPay m o) c) : ∃ m', m' = m ∧ SegSt pc L (ArmPay m' o) c := ⟨m, rfl, h⟩

set_option hygiene false in
/-- The prologue's frame and the strings' views, for the memory `mL` it left. -/
local macro "ls_name" : tactic => `(tactic| (
  obtain ⟨mL, hmL, h⟩ := h.mem_name
  have hF : LsFrame mL m sp r f := by rw [hmL]; ls_frame
  have hM : LsMem mL (t1 + 24) (t2 + 24) s1 s2 := by rw [hmL]; ls_mem))

set_option hygiene false in
/-- A prologue variant ending at the first call site (a long second string). -/
local macro "ls_viaA" : tactic => `(tactic| (
  kit_run h acc until [0x8001a744]
  ls_name
  obtain ⟨c1, hs1, ⟨hn⟩⟩ := lstrcmp_A (t1 + 24) (t2 + 24) t2 sp r f mL m o s1 s2 hra hsp hsp2 hF hM _ _
    (by omega) (by omega) (by rw [hmL]; simp (disch := kit_disch) only [bytesT8_wm8_out]; exact hln2) _
    (h.repin (by pins_of h))
  rcases hn with hr | ⟨i', z', _, hA', h'⟩
  · exact ⟨c1, acc.trans hs1, hr⟩
  · obtain ⟨c2, hs2, h2⟩ := lstrcmp_loop (t1 + 24) (t2 + 24) sp r f mL m o s1 s2 hra hsp hsp2 hF hM
      i' z' hA' _ h'
    exact ⟨c2, (acc.trans hs1).trans hs2, h2⟩))

set_option hygiene false in
/-- A prologue variant ending at the loop's call site. -/
local macro "ls_viaB" : tactic => `(tactic| (
  kit_run h acc until [0x8001a790]
  ls_name
  obtain ⟨c2, hs2, h2⟩ := lstrcmp_loop (t1 + 24) (t2 + 24) sp r f mL m o s1 s2 hra hsp hsp2 hF hM 0 _ hA _
    (h.repin (by pins_of h))
  exact ⟨c2, acc.trans hs2, h2⟩))

set_option hygiene false in
local macro "ls_variant " n:ident l1:term "," l2:term "," via:tactic : command => `(
  theorem $n (t1 t2 : Nat) (s1 s2 : List UInt8) (r : BitVec 64) (sp : Nat) (f : KFrame) (m : Mem)
      (o : Array String) (hx : LsCtx m sp r t1 t2 s1 s2) (hl1 : $l1) (hl2 : $l2) :
      Triple (SegSt 0x8001a704#64 (lstrPre t1 t2 r sp f) (ArmPay m o))
        (LsRet r sp f m o s1 s2) := by
    ls_pro hl1, hl2
    $via)

ls_variant lstrcmp_LL 40 < s1.length, 40 < s2.length, ls_viaA
ls_variant lstrcmp_SL ¬ 40 < s1.length, 40 < s2.length, ls_viaA
ls_variant lstrcmp_LS 40 < s1.length, ¬ 40 < s2.length, ls_viaB
ls_variant lstrcmp_SS ¬ 40 < s1.length, ¬ 40 < s2.length, ls_viaB

/-- **`l_strcmp`, the call-node summary**: on two viewed strings, bit 31 of
`a0` is `lexLt`; the memory changes only in its frame `[sp - 48, sp)`. -/
theorem lstrcmp_sum (t1 t2 : Nat) (s1 s2 : List UInt8) (r : BitVec 64) (sp : Nat) (f : KFrame) (m : Mem)
    (o : Array String) (hx : LsCtx m sp r t1 t2 s1 s2) :
    Triple (SegSt 0x8001a704#64 (lstrPre t1 t2 r sp f) (ArmPay m o))
      (LsRet r sp f m o s1 s2) := by
  by_cases l1 : 40 < s1.length <;> by_cases l2 : 40 < s2.length
  · exact lstrcmp_LL t1 t2 s1 s2 r sp f m o hx l1 l2
  · exact lstrcmp_LS t1 t2 s1 s2 r sp f m o hx l1 l2
  · exact lstrcmp_SL t1 t2 s1 s2 r sp f m o hx l1 l2
  · exact lstrcmp_SS t1 t2 s1 s2 r sp f m o hx l1 l2

end Lua.Vm.Sim.Kit

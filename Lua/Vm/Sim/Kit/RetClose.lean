import Lua.Vm.Sim.Kit.RetMem
import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Arms.Segs.HluaF_close
import Lua.Vm.Arms.Segs.HluaF_closeupval

/-!
# `luaF_close` with nothing open, the call-node summary (lane F1-4)

`OP_RETURN` with `k` calls `luaF_close(L, base, CLOSEKTOP, 1)` (`0x8000c224`).
With no open upvalue (`L->openupval = NULL`) and no to-be-closed variable at
or above `base` (`L->tbclist < base`), it saves `ra`, `s0`, `s2 … s5`, `s7`
in its frame `[sp - 80, sp)`, calls `luaF_closeupval` (whose loop exits at
once, the `bnez` not taken), tests `tbclist < level` (`bltu` taken) and
returns with the saved registers restored. Two declarations: `fc1` (the
prologue, the callee, the test) and `fc2` (the epilogue, over the frame's
saved words `FcFrame`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **A caller's callee-saved registers** across a call: `gp`, `s0 … s11`. -/
structure RFrame where
  (gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : BitVec 64)

def RFrame.pins (f : RFrame) : List Pin :=
  [⟨Register.x3, f.gp⟩, ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x18, f.s2⟩,
   ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩, ⟨Register.x22, f.s6⟩,
   ⟨Register.x23, f.s7⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩, ⟨Register.x26, f.s10⟩,
   ⟨Register.x27, f.s11⟩]

/-- What `luaF_close` reads with nothing open. -/
structure FcCx (L lvl sp stack : Nat) (r : BitVec 64) (m : Mem) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 80 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  L_lo : tohostAddr + 16 ≤ L
  L_hi : L + stateSize + 80 ≤ sp
  lvl_hi : lvl < 2 ^ 32
  lt : stack < lvl
  open_ : bytesT8 m (L + stateOpenupvalOff) = 0
  tbc : bytesT8 m (L + stateTbclistOff) = BitVec.ofNat 64 stack

/-- The frame's saves (`sd s2,48(sp)` … `sd ra,72(sp)`). -/
abbrev fcMem (m : Mem) (sp : Nat) (f : RFrame) (r : BitVec 64) : Mem :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m
    (sp - 80 + 48) (sdData_val f.s2)) (sp - 80 + 64) (sdData_val f.s0)) (sp - 80 + 40)
    (sdData_val f.s3)) (sp - 80 + 32) (sdData_val f.s4)) (sp - 80 + 24) (sdData_val f.s5))
    (sp - 80 + 8) (sdData_val f.s7)) (sp - 80 + 72) (sdData_val r)

/-- The saved words of `luaF_close`'s frame. -/
structure FcFrame (mL : Mem) (sp : Nat) (f : RFrame) (r : BitVec 64) : Prop where
  ra : bytesT8 mL (sp - 80 + 72) = r
  s0 : bytesT8 mL (sp - 80 + 64) = f.s0
  s2 : bytesT8 mL (sp - 80 + 48) = f.s2
  s3 : bytesT8 mL (sp - 80 + 40) = f.s3
  s4 : bytesT8 mL (sp - 80 + 32) = f.s4
  s5 : bytesT8 mL (sp - 80 + 24) = f.s5
  s7 : bytesT8 mL (sp - 80 + 8) = f.s7

theorem fcFrame (m : Mem) (sp : Nat) (f : RFrame) (r : BitVec 64) :
    FcFrame (fcMem m sp f r) sp f r := by
  have w8 : ∀ (m : Mem) (a : Nat) (d : BitVec 64), bytesT8 (writeMap8 m a (sdData_val d)) a = d :=
    fun m a d => by rw [bytesT8_writeMap8, sdData_id]
  have o8 : ∀ {m : Mem} {a x : Nat} {d : BitVec (8 * 8)}, x + 8 ≤ a ∨ a + 8 ≤ x →
      bytesT8 (writeMap8 m a d) x = bytesT8 m x := fun h => bytesT8_wm8_out h
  refine ⟨w8 _ _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [fcMem]
  · rw [o8 (by omega), o8 (by omega), o8 (by omega), o8 (by omega), o8 (by omega), w8]
  · rw [o8 (by omega), o8 (by omega), o8 (by omega), o8 (by omega), o8 (by omega),
      o8 (by omega), w8]
  · rw [o8 (by omega), o8 (by omega), o8 (by omega), o8 (by omega), w8]
  · rw [o8 (by omega), o8 (by omega), o8 (by omega), w8]
  · rw [o8 (by omega), o8 (by omega), w8]
  · rw [o8 (by omega), w8]

/-- The unsigned compare of two small naturals. -/
theorem ult_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    zopz0zI_u (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [zopz0zI_u, BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb]
  simp

/-- The registers at the test (`0x8000c378`, `bltu` taken). -/
abbrev fcRow (lvl sp : Nat) (f : RFrame) (q2 q3 q4 q5 q7 : BitVec 64) : List Pin :=
  ⟨Register.x18, q2⟩ :: ⟨Register.x19, q3⟩ :: ⟨Register.x20, q4⟩ :: ⟨Register.x21, q5⟩ ::
    ⟨Register.x23, q7⟩ ::
    ⟨Register.x8, BitVec.ofNat 64 lvl⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 80)⟩ ::
    ⟨Register.x3, f.gp⟩ :: ⟨Register.x9, f.s1⟩ :: ⟨Register.x22, f.s6⟩ :: ⟨Register.x24, f.s8⟩ ::
    ⟨Register.x25, f.s9⟩ :: ⟨Register.x26, f.s10⟩ :: ⟨Register.x27, f.s11⟩ :: []

set_option hygiene false in
/-- The context's facts, for `kit_disch`. -/
macro "fc_facts " hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).L_lo; have := ($hx).L_hi; have := ($hx).lvl_hi; have := ($hx).lt
  have hop := ($hx).open_; have htb := ($hx).tbc
  simp only [stateSize, stateOpenupvalOff, stateTbclistOff] at *))

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id,
          bytesT8_wm8_out, hop]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id,
          bytesT8_wm8_out, htb]
         rw [ult_ofNat (by omega) (by omega)]; simp only [decide_eq_true_eq]; omega)
      | (rw [Vsa.Sim.ret_tgt _ (by decide)]; decide))

/-- **The prologue, `luaF_closeupval`, the test**: to `0x8000c378` with the
frame saved. -/
theorem fc1 {L lvl sp stack : Nat} {r : BitVec 64} {m : Mem} (hx : FcCx L lvl sp stack r m)
    (f : RFrame) (v12 v13 : BitVec 64) (o : Array String) :
    Triple (SegSt 0x8000c224#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 lvl⟩ :: ⟨Register.x12, v12⟩ :: ⟨Register.x13, v13⟩ ::
        ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay m o))
      (fun c => ∃ q2 q3 q4 q5 q7,
        SegSt 0x8000c378#64 (fcRow lvl sp f q2 q3 q4 q5 q7) (ArmPay (fcMem m sp f r) o) c) := by
  intro c h
  have acc := Steps.refl c
  fc_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [RFrame.pins, fcRow] at h ⊢
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc until [0x8000c378]
  exact ⟨_, acc, _, _, _, _, _, h.repin (by pins_of h)⟩

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, sext64_id, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat,
    Nat.reduceSub, hF.ra, hF.s0, hF.s2, hF.s3, hF.s4, hF.s5, hF.s7] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id,
          hF.ra, Vsa.Sim.sext_zero, BitVec.add_zero]
         rw [rtgt _ hra]; exact hra))

/-- **The epilogue**: `a0 = level`, the saved registers back, the return. -/
theorem fc2 {lvl sp : Nat} {r : BitVec 64} {mL : Mem} (f : RFrame) (o : Array String)
    (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 80 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : FcFrame mL sp f r) :
    Triple (fun c => ∃ q2 q3 q4 q5 q7,
        SegSt 0x8000c378#64 (fcRow lvl sp f q2 q3 q4 q5 q7) (ArmPay mL o) c)
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay mL o)) := by
  rintro c ⟨q2, q3, q4, q5, q7, h⟩
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [RFrame.pins, fcRow] at h ⊢
  kit_run h acc
  have h := h.at (rtgt _ hra)
  rw [show sp - 80 + 80 = sp by omega] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`luaF_close(L, level, …)` with nothing open, the call-node summary**:
it returns to `ra` with the caller's `sp` and callee-saved registers, having
written only its frame `[sp - 80, sp)` (`fcMem`). -/
theorem fclose_sum {L lvl sp stack : Nat} {r : BitVec 64} {m : Mem} (hx : FcCx L lvl sp stack r m)
    (f : RFrame) (v12 v13 : BitVec 64) (o : Array String) :
    Triple (SegSt 0x8000c224#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 lvl⟩ :: ⟨Register.x12, v12⟩ :: ⟨Register.x13, v13⟩ ::
        ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (fcMem m sp f r) o)) :=
  (fc1 hx f v12 v13 o).seq (fc2 f o hx.ra hx.sp_lo hx.sp_hi (fcFrame m sp f r))

end Lua.Vm.Sim.Ret

import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms.Segs.HluaV_tointeger
import Lua.Vm.Sim.Kit.Equalobj

/-!
# `luaV_tointeger` at the Lua ELF's address on an integer (lane KIT-2, M5)

`FORPREP`'s `forlimit` calls `luaV_tointeger(lim, &p, mode)`. On an integer
(tag `LUA_VNUMINT`) the helper is loop-free: the string test (`tt & 15 = 4`)
and the float test (`tt = 19`) fail, `*p = ivalue(lim)` and it returns 1. It
saves `s1` and `ra` below `sp` (`Scratch`) and writes `*p`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- The facts the helper's run uses: the frame below `sp`, the operand `n`
and the out-parameter `q` in RAM, apart from the frame. -/
structure TiCtx (n q sp : Nat) (r : BitVec 64) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 80 ≤ sp
  sp_hi : sp < 2^32
  sp_al : sp % 8 = 0
  n_lo : tohostAddr + 16 ≤ n
  n_hi : n + 16 + 80 ≤ sp
  q_lo : sp ≤ q
  q_hi : q + 8 < 2^32
  q_al : q % 8 = 0

/-- `addi sp, sp, -80` then `addi sp, sp, 80`. -/
theorem sp_back80 (x : BitVec 64) :
    x + sign_extend (m := 64) (0xfb0#12) + sign_extend (m := 64) (0x050#12) = x := by
  rw [BitVec.add_assoc, show sign_extend (m := 64) (0xfb0#12) + sign_extend (m := 64) (0x050#12)
    = 0#64 by decide, BitVec.add_zero]

theorem add_imm_m80 (n : Nat) :
    BitVec.ofNat 64 n + sign_extend (m := 64) (0xfb0#12) = BitVec.ofNat 64 (n + (2^64 - 80)) := by
  rw [show sign_extend (m := 64) (0xfb0#12) = BitVec.ofNat 64 (2^64 - 80) by decide,
    BitVec.ofNat_add_ofNat]

/-- The memory at the return: `s1`, `ra` saved below `sp` (`sd s1,56(sp)`,
`sd ra,72(sp)` after `addi sp,sp,-80`), then `*q = v`. -/
abbrev tiMem (m : Mem) (sp q : Nat) (s1 r v : BitVec 64) : Mem :=
  writeMap8 (writeMap8 (writeMap8 m
    (BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfb0#12) + sign_extend (m := 64) (0x038#12)).toNat
      (sdData_val s1))
    (BitVec.ofNat 64 sp + sign_extend (m := 64) (0xfb0#12) + sign_extend (m := 64) (0x048#12)).toNat
      (sdData_val r)) q (sdData_val v)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| (
      try simp (disch := kit_disch) only [add_imm_m80, bytesT1_writeMap8_out, bytesT1_tag n]
      try simp (disch := kit_disch) only [slotTag_wm8, ht]))

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
    | (kit_bv_norm; decide)
    | (simp (disch := kit_disch) only [add_imm_m80, bytesT8_wm8_out]
       rw [ld_ra, Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`luaV_tointeger` on an integer, the call-node summary.** -/
theorem toint_sum (n q sp : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hx : TiCtx n q sp r) (hsp : f.sp = BitVec.ofNat 64 sp) (ht : slotTag m n = 3#8) :
    Triple (SegSt 0x8001ade8#64 (⟨Register.x10, BitVec.ofNat 64 n⟩ :: ⟨Register.x11, BitVec.ofNat 64 q⟩ ::
        ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: f.pins) (ArmPay (tiMem m sp q f.s1 r (slotVal m n)) o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨hra, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  obtain ⟨sp0, gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [HFrame.pins] at h hsp ⊢
  subst hsp
  kit_run h acc
  simp (disch := kit_disch) only [Vsa.Sim.sext_zero, BitVec.add_zero, sp_back80, bytesT8_wm8_out,
    ld_ra, ld_slot_gen n] at h
  simp (disch := omega) only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt] at h
  simp only [Vsa.Sim.sext_one, BitVec.zero_add] at h
  exact ⟨_, acc, (h.at (by simpa only [Vsa.Sim.sext_zero, BitVec.add_zero] using Vsa.Sim.ret_tgt r hra)).repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit

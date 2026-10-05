import Lua.Vm.Sim.Kit.Lt
import Lua.Vm.Sim.Kit.EqLong
import Lua.Vm.Sim.Kit.LstrcmpPro

/-!
# `OP_LT` on two strings, and `sim_LT` (round-4 bake-off, S-SCAN, held out)

`lessthanothers` inlined in the arm: two string tags (`tt & 15 = 4`), the
`savestate` stores, `l_strcmp(tsvalue(ra), tsvalue(rb))` (`lstrcmp_sum`),
`srliw 31`, `docondjump`. The strings' bytes are live by M-str
(`Core.str_at`). `sim_LT` closes `sim_LT_of_str`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- A string tag, zero-extended. -/
theorem str_tag64 (s : List UInt8) :
    zero_extend (m := 64) (BitVec.ofNat 8 (strTag s) : BitVec (8 * 1)) = BitVec.ofNat 64 (strTag s) := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem str_and15 (s : List UInt8) : BitVec.ofNat 64 (strTag s) &&& sign_extend (m := 64) (0x00f#12) = 4#64 := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem str_ne_int (s : List UInt8) : (BitVec.ofNat 64 (strTag s) != BitVec.ofNat 64 vNumInt) = true := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem sext_four : (0#64) + sign_extend (m := 64) (0x004#12) = 4#64 := by decide
theorem four_ne_int : (4#64 == BitVec.ofNat 64 vNumInt) = false := by decide

/-- `srliw a0, a0, 31`: bit 31 as 0/1. -/
theorem srliw31 (v : BitVec 64) :
    sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb v 31 0) (0x1f#5)) =
      if v.getLsbD 31 then 1#64 else 0#64 := by
  have e : (shift_bits_right (Sail.BitVec.extractLsb v 31 0) (0x1f#5)).toNat = v.toNat / 2 ^ 31 % 2 := by
    simp only [shift_bits_right, Sail.BitVec.extractLsb, BitVec.toNat_ushiftRight, BitVec.extractLsb_toNat,
      Nat.shiftRight_eq_div_pow]
    simp; omega
  have hb : v.getLsbD 31 = decide (v.toNat / 2 ^ 31 % 2 = 1) := by
    rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]
  apply BitVec.eq_of_toNat_eq
  rw [hb, sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.msb_eq_decide]
  by_cases h : v.toNat / 2 ^ 31 % 2 = 1 <;> simp only [h, decide_true, decide_false, ite_true, ite_false] <;>
    simp [e, h] <;> omega

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [kraw_eq, srliw31, hv, bne_ite])

set_option hygiene false in
/-- The string path's tag guards: the tags are string tags. -/
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (
      bool_goal
      simp (disch := kit_disch) only [bytesT1_writeMap8_out, bytesT1_tag (w.slot ins.a), bytesT1_tag (w.slot ins.b),
        slotTag_wm8, hsa, hsb, str_tag64, str_and15, str_ne_int, sext_four, four_ne_int, beq_self_eq_true]))

set_option hygiene false in
/-- Reads after the call: from `l_strcmp`'s output memory `m'` back to the
arm's (`hO`, outside its frame). -/
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [AgreeOut.bytesT4 hO] at $h:ident)

set_option hygiene false in
/-- The frame through `l_strcmp`'s output memory. -/
local macro_rules | `(tactic| kit_frame) => `(tactic| (
  intro x hx
  simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget, not_or,
    not_and, Nat.not_lt] at hx
  rw [hO x (by omega)]
  simp (disch := kit_disch) only [getElem?_wm8_out, getElem?_ins_out]))

set_option hygiene false in
/-- The string path up to `l_strcmp`'s return: the call node `lstrcmp_sum`. -/
local macro "lt_str_call" : tactic => `(tactic| (
  kit_setup 0x8001c894
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  kit_reg hba va hva ins.a; kit_reg hbb vb hvb ins.b
  obtain ⟨⟨x, y, hx, hy⟩, hkk⟩ := hT
  rw [hx] at hba; rw [hy] at hbb; cases hba; cases hbb
  have hkk := hkk x y hx hy
  have hsa : slotTag c.σ.mem (w.slot ins.a) = BitVec.ofNat 8 (strTag x) := hva.tag_eq
  have hsb : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 (strTag y) := hvb.tag_eq
  kit_seg h0 acc Lua.Vm.Arms.seg_8001c894_8001c8bc_t
  kit_seg h0 acc Lua.Vm.Arms.seg_8001c8c0_8001c8c8_n
  kit_seg h0 acc Lua.Vm.Arms.seg_8001c8c8_8001c8cc
  kit_seg h0 acc Lua.Vm.Arms.seg_8001e22c_8001e240_t
  kit_seg h0 acc Lua.Vm.Arms.seg_8001e244_8001e250_t
  kit_seg h0 acc Lua.Vm.Arms.seg_8001e254_8001e260
  simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.a), ld_slot_gen (w.slot ins.b), slotVal_wm8] at h0
  rw [← bv_ofNat_toNat (slotVal c.σ.mem (w.slot ins.a)), ← bv_ofNat_toNat (slotVal c.σ.mem (w.slot ins.b))] at h0
  have hsp := hr.sp_eq
  have hse : RuntimeData.spEntry = 0x87fffe20 := rfl
  have hcb : cStackBudget = 0x10000 := rfl
  have hef : execFrame = 176 := rfl
  obtain ⟨_, acc, ⟨⟨v, m', hO, h0, hv⟩⟩⟩ := h0.call acc (by pins_of h0)
    (lstrcmp_sum _ _ x y 0x8001e260#64 w.sp (KFrame.mk _ _ _ _ _ _ _ _ _ _ _) _ _
      ⟨RodataRead.wm8 (RodataRead.wm8 hc.rodata (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch))
          (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch), by decide, by omega, by omega,
        by omega,
        (fun a => ⟨a.view, a.apart.mono (by omega) (by omega)⟩) (hc.str_at hva (by kit_frame)),
        (fun a => ⟨a.view, a.apart.mono (by omega) (by omega)⟩) (hc.str_at hvb (by kit_frame))⟩)
  dsimp only [RetAt] at h0
  have hLci := hr.L_sep_ci; simp only [stateSize, ciSize] at hLci))

/-- `OP_LT` on two strings, the test equal to `k`: the jump is taken. -/
theorem lt_str_take : ArmBody .LT fun p c s w ins => BothStrAB p c s w ins ∧
    ∀ x y, s.regs ins.a = some (.str x) → s.regs ins.b = some (.str y) → lexLt x y = ins.k :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  lt_str_call
  have hg : (ins.k != lexLt x y) = false := by rw [hkk]; exact bne_self_eq_false _
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, hkk] at hk
  subst hk
  obtain ⟨ni, hni, hjt⟩ : ∃ ni, p.fetch (s.pc + 1) = some ni ∧ jumpTo (s.pc + 2) ni.sj = some t := by
    simp only [nextJump, Option.bind_eq_some_iff] at hnj; exact hnj
  have hlt1 := fetch_lt hni
  have hjt' := jumpTo_eq hjt
  have hsj : ni.sj < 2 ^ 25 := by
    simp only [Word.sj, Word.ax, Word.field, Word.offsetSJ]; have := ni.isLt; omega
  kit_run h0 acc
  kit_trap
  rw [nextjump_pc ?_ (Core.fetch_scratch' hc (by kit_frame) hni) hjt (by kit_disch) (by kit_disch)] at h0
  · exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩
  · kit_disch

/-- `OP_LT` on two strings, the test differing from `k`: the jump is skipped. -/
theorem lt_str_skip : ArmBody .LT fun p c s w ins => BothStrAB p c s w ins ∧
    ∀ x y, s.regs ins.a = some (.str x) → s.regs ins.b = some (.str y) → lexLt x y ≠ ins.k :=
  fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  lt_str_call
  have hg : (ins.k != lexLt x y) = true := by
    simpa only [bne_iff_ne, ne_eq, eq_comm (a := ins.k)] using hkk
  simp [Opnd.fill, δ, VState.apply, writeDefs, KEdge.kills, Value.isFalse, hkk] at hk
  subst hk
  kit_run h0 acc
  kit_trap
  exact ⟨_, acc, hc.bleach_same h0 (by kit_pins h0) (by kit_frame), h0.pcAt⟩

/-- **`OP_LT` on two strings** (`l_strcmp`): both exits of `docondjump`. -/
theorem lt_str : ArmBody .LT BothStrAB := fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  obtain ⟨x, y, hx, hy⟩ := hT
  by_cases hk : lexLt x y = ins.k
  · exact lt_str_take hS hA hf hop hstep ⟨⟨x, y, hx, hy⟩, fun x' y' hx' hy' => by
      rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; exact hk⟩
  · exact lt_str_skip hS hA hf hop hstep ⟨⟨x, y, hx, hy⟩, fun x' y' hx' hy' => by
      rw [hx] at hx'; rw [hy] at hy'; cases hx'; cases hy'; exact hk⟩

/-- **`sim_LT`**: `OP_LT` simulates its kernel, every path proved. -/
theorem sim_LT : SimArm .LT := sim_LT_of_str lt_str

end Lua.Vm.Sim.Kit

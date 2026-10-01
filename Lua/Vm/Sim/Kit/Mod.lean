import Lua.Vm.Sim.Kit.Moddi3
import Lua.Vm.Sim.Kit.ModEq
import Lua.Vm.Arms

/-!
# `OP_MOD` by the direct kit (round-3 bake-off, held-out case)

`savestate` (two `Scratch` stores), then `op_arith(luaV_mod)`: the integer
path is `luaV_mod` inlined (`imodC_eq`, M1), whose general case calls
`__moddi3` (`moddi3_sum`, a call node that itself calls `__udivdi3`, M5).
`n % 0` is the kernel's stuck case (`Step.stuck`), so it needs no run.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `bgeu a4,a3` with `a4 = 1`, `a3 = n + 1`: `n` is `0` or `-1`. -/
theorem bgeu_one (y : BitVec 64) : zopz0zKzJ_u 1#64 (y + 1#64) = decide (y = 0#64 ∨ y = -1#64) := by
  have hy := y.isLt
  have e : (y + 1#64).toNat = (y.toNat + 1) % 2^64 := by simp [BitVec.toNat_add]
  have i0 : y = 0#64 ↔ y.toNat = 0 :=
    ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  have i1 : y = -1#64 ↔ y.toNat = 2^64 - 1 :=
    ⟨fun h => by subst h; decide, fun h => BitVec.eq_of_toNat_eq (by simp [h])⟩
  rcases bgeu_cases 1#64 (y + 1#64) with g | g
  · have := bgeu_true _ _ g; rw [e] at this; simp at this
    rw [g]; symm; simp only [decide_eq_true_eq, i0, i1]; omega
  · have := bgeu_false _ _ g; rw [e] at this; simp at this
    rw [g]; symm; simp only [decide_eq_false_iff_not, not_or, i0, i1]; omega

theorem srem_neg_one (x : BitVec 64) : x.srem (-1#64) = 0#64 := by
  have : (18446744073709551615#64 : BitVec 64).msb = true := by decide
  cases h : x.msb <;> simp [BitVec.srem_eq, h, this]

set_option hygiene false in
local macro_rules
  | `(tactic| kit_norm $h) => `(tactic| simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b),
      ld_slot_gen (w.slot ins.c), slotVal_wm8, Vsa.Sim.sext_zero, Vsa.Sim.sext_one, BitVec.add_zero,
      BitVec.zero_add] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [
      ld_slot_gen (w.slot ins.b), ld_slot_gen (w.slot ins.c), slotVal_wm8, Vsa.Sim.sext_zero,
      Vsa.Sim.sext_one, BitVec.add_zero, BitVec.zero_add, bgeu_one, slt_zero, BitVec.msb_xor])

theorem sim_MOD : SimArm .MOD := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001dc58
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  kit_reg hb vb hvb ins.b; kit_reg hcc vc hvc ins.c
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · obtain rfl := hvb.int_of_tag hB
    by_cases hC : slotTag c.σ.mem (w.slot ins.c) = BitVec.ofNat 8 vNumInt
    · obtain rfl := hvc.int_of_tag hC
      kit_run h0 acc until [0x8001f7e0]
      trace_state
      sorry
    · simp [Opnd.fill] at hk; split at hk
      · rename_i heq; exact absurd (pair_eq heq).2 (hvc.not_int hC _)
      kit_next; kit_same
  · simp [Opnd.fill] at hk; split at hk
    · rename_i heq; exact absurd (pair_eq heq).1 (hvb.not_int hB _)
    kit_next; kit_same

end Lua.Vm.Sim.Kit

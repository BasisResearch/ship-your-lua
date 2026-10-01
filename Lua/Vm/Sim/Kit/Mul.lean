import Lua.Vm.Sim.Kit.Muldi3
import Lua.Vm.Arms

/-!
# `OP_MUL` by the direct kit (round-3 bake-off, held-out case)

`op_arith(l_muli)`: the integer path calls `__muldi3` (`jal` at
`0x8001f094`), a call node run under its summary `muldi3_sum` (M5).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem sim_MUL : SimArm .MUL := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001dcc8
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  kit_reg hb vb hvb ins.b; kit_reg hcc vc hvc ins.c
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · obtain rfl := hvb.int_of_tag hB
    by_cases hC : slotTag c.σ.mem (w.slot ins.c) = BitVec.ofNat 8 vNumInt
    · obtain rfl := hvc.int_of_tag hC
      simp [Opnd.fill, δ, BinOp.int, VState.apply, writeDefs, KEdge.kills] at hk
      subst hk
      kit_run h0 acc until [0x8002f6c8]
      obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0) (muldi3_sum _ _ _ hframe? _ _ (by decide))
      kit_run h0 acc
      exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (fun _ _ => rfl)
        (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
        (by rw [stData_int, alu_val HMul.hMul (n1 := w.slot ins.b) ?_ (ld_slot (n := w.slot ins.c) ?_)]
            exact .int; all_goals slot_arith), h0.pcAt⟩
    · simp [Opnd.fill] at hk; split at hk
      · rename_i heq; exact absurd (pair_eq heq).2 (hvc.not_int hC _)
      kit_next; kit_same
  · simp [Opnd.fill] at hk; split at hk
    · rename_i heq; exact absurd (pair_eq heq).1 (hvb.not_int hB _)
    kit_next; kit_same

end Lua.Vm.Sim.Kit

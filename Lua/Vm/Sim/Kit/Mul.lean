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

theorem mul_int : ArmBody .MUL BothInt := fun {p} hS {c s s' w ins} hA hf hop hstep hI => by
  kit_arith_ints 0x8001dcc8
  kit_next_until [0x8002f6c8]
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0) (muldi3_sum _ _ _ hframe? _ _ (by decide))
  kit_run h0 acc
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (fun _ _ => rfl)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by rw [stData_int, alu_val HMul.hMul (n1 := w.slot ins.b) ?_ (ld_slot (n := w.slot ins.c) ?_)]
        exact .int; all_goals slot_arith), h0.pcAt⟩

theorem sim_MUL : SimArm .MUL := sim_arith (by decide) mul_int
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kit_arith_fall 0x8001dcc8

end Lua.Vm.Sim.Kit

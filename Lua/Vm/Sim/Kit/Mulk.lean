import Lua.Vm.Sim.Kit.Muldi3
import Lua.Vm.Sim.Kit.K
import Lua.Vm.Arms

/-!
# `OP_MULK` by the direct kit

`op_arithK(l_muli)`: `OP_MUL` with `K[C]` (`Kit/K.lean`); the integer path
calls `__muldi3` (`jal` at `0x8001f008`, `muldi3_sum`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem mulk_int : ArmBody .MULK BothIntK := fun {p} hS {c s s' w ins} hA hf hop hstep hI => by
  kitk_ints 0x8001db3c
  kit_next_until [0x8002f6c8]
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0) (muldi3_sum _ _ _ hframe? _ _ (by decide))
  kit_run h0 acc
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (fun _ _ => rfl)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by rw [stData_int, alu_val HMul.hMul (n1 := w.slot ins.b) ?_
          (ld_slot (n := w.k + stackValueSize * ins.c) ?_)]
        exact .int; all_goals slot_arith), h0.pcAt⟩

theorem sim_MULK : SimArm .MULK := sim_arithK (by decide) mulk_int
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kitk_fall 0x8001db3c

end Lua.Vm.Sim.Kit

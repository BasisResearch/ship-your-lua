import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms

/-!
# `OP_ADD` by the direct kit (round-3 bake-off, refactor case)

Hand-written: the kernel evaluated forward (M1), the tags decide the path
(M2), the generated segments chained by `kit_run`, one close (M3). The
fall-through to `MMBIN` is `kit_arith_fall`, shared by every `op_arith` arm.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem add_int : ArmBody .ADD BothInt := fun {p} hS {c s s' w ins} hA hf hop hstep hI => by
  kit_arith_ints 0x8001d9c8
  kit_next
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (fun _ _ => rfl)
    (slotStore_sb_sd rfl (by slot_arith) (by slot_arith))
    (by rw [stData_int, alu_val HAdd.hAdd (n1 := w.slot ins.b) ?_ (ld_slot (n := w.slot ins.c) ?_)]
        exact .int; all_goals slot_arith), h0.pcAt⟩

theorem sim_ADD : SimArmOn .ADD (Off FltBC) := sim_arith (by decide) add_int
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kit_arith_fall 0x8001d9c8

end Lua.Vm.Sim.Kit

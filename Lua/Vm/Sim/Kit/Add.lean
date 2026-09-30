import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms

/-!
# `OP_ADD` by the direct kit (round-3 bake-off, refactor case)

Hand-written: the kernel evaluated forward (M1), the tags decide the path
(M2), the generated segments chained by `kit_run`, one close (M3).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem sim_ADD : SimArm .ADD := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001d9c8
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  kit_reg hb vb hvb ins.b; kit_reg hcc vc hvc ins.c
  by_cases hB : slotTag c.σ.mem (w.slot ins.b) = BitVec.ofNat 8 vNumInt
  · obtain rfl := hvb.int_of_tag hB
    by_cases hC : slotTag c.σ.mem (w.slot ins.c) = BitVec.ofNat 8 vNumInt
    · obtain rfl := hvc.int_of_tag hC
      kit_next
      exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (fun _ _ => rfl)
        (slotStore_sb_sd rfl (by slot_arith) (by slot_arith))
        (by rw [stData_int, alu_val HAdd.hAdd (n1 := w.slot ins.b) ?_ (ld_slot (n := w.slot ins.c) ?_)]
            exact .int; all_goals slot_arith), h0.pcAt⟩
    · simp [Opnd.fill] at hk; split at hk
      · rename_i heq; exact absurd (pair_eq heq).2 (hvc.not_int hC _)
      kit_next; kit_same
  · simp [Opnd.fill] at hk; split at hk
    · rename_i heq; exact absurd (pair_eq heq).1 (hvb.not_int hB _)
    kit_next; kit_same

end Lua.Vm.Sim.Kit

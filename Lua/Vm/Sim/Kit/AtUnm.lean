import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.At.Unm

/-!
# `OP_UNM` on the location-list route

`lvm.c`'s `OP_UNM`: an integer `R[B]` is negated in place (`intop(-, 0, ib)`,
the machine's `neg`); a float is negated by the sign bit (no F1 value); any
other value goes to `luaT_trybinTM(L, rb, rb, ra, TM_UNM)` (`0x8001ec2c`, a
runtime metamethod call). The kernel (`δ .unm`) has a step for an integer and
for a string that converts to one (`str2int`: the string library's `__unm`,
reached through `luaT_trybinTM`), and none for the other values.

* the integer path is `unm_int`: the kernel forward, then `at_go`;
* the other non-string values are the kernel's stuck case (`unm_stuck`);
* the string path runs `luaT_trybinTM` and the string metamethod, a runtime
  call that belongs with the `MMBIN`/`CALL` runtime summaries: it is the
  named premise `UnmStr_Statement` of `sim_UNM_of_str`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- `R[B]` holds a string (the `luaT_trybinTM` path). -/
def UnmStr (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ t, s.regs ins.b = some (.str t)

/-- **The string path of `OP_UNM`** (open; the `MMBIN`/`CALL` runtime-summary
work supplies it): from the arm's entry with a string in `R[B]`, the machine
runs `luaT_trybinTM` (`0x800194f4`) and the string library's `__unm`
(`lstrlib.c` `arith_unm`: `tonum`, `lua_arith`) to the fetch head, related to
the kernel's successor (`str2int`). -/
def UnmStr_Statement : Prop := ArmBody .UNM UnmStr

theorem unm_int : ArmBody .UNM fun _ _ s _ ins => ∃ i, s.regs ins.b = some (.int i) := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨i, hi⟩
  kit_setup 0x8001d8a4
  simp [setR, Opnd.ports] at htop
  simp [setR, Opnd.ports, Opnd.fill, hi, δ, VState.apply, writeDefs, KEdge.kills] at hk
  kit_bound hAt ins.a; kit_bound hBt ins.b
  have hvb := hc.stack _ _ hBt hi
  have hB := hvb.tag_of_int.1
  obtain rfl := hvb.tag_of_int.2
  subst hk
  at_go Lua.Vm.At.UNM

/-- Neither an integer nor a string: no `Step` (`δ .unm` is `none`). -/
theorem unm_stuck : ArmBody .UNM fun _ _ s _ ins =>
    (∀ i, s.regs ins.b ≠ some (.int i)) ∧ ∀ t, s.regs ins.b ≠ some (.str t) := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨hi, ht⟩
  kit_setup 0x8001d8a4
  rcases hb : s.regs ins.b with _ | v
  · simp [setR, Opnd.ports, hb] at hk
  rcases v <;> simp_all [setR, Opnd.ports, Opnd.fill, δ]

/-- **`OP_UNM`** on the location-list route, given the string path. -/
theorem sim_UNM_of_str (hstr : UnmStr_Statement) : SimArm .UNM :=
  sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
    by_cases hi : ∃ i, s.regs ins.b = some (.int i)
    · exact unm_int hS hA hf hop hstep hi
    by_cases ht : ∃ t, s.regs ins.b = some (.str t)
    · exact hstr hS hA hf hop hstep ht
    exact unm_stuck hS hA hf hop hstep ⟨fun i h => hi ⟨i, h⟩, fun t h => ht ⟨t, h⟩⟩

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.Moddi3
import Lua.Vm.Sim.Kit.ModEq
import Lua.Vm.Sim.Kit.DivBits
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

set_option hygiene false in
/-- The operands' payloads, read through the `savestate` stores. -/
local macro "mod_vals" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp (disch := kit_disch) only [ld_slot_gen (w.slot ins.b), ld_slot_gen (w.slot ins.c),
    slotVal_wm8, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.zero_add] $[$loc]?)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [
      ld_slot_gen (w.slot ins.b), ld_slot_gen (w.slot ins.c), slotVal_wm8, Vsa.Sim.sext_zero,
      Vsa.Sim.sext_one, BitVec.add_zero, BitVec.zero_add, bgeu_one, slt_zero, BitVec.msb_xor])

/-- The divisor `R[C]`'s payload. -/
abbrev divisor (c : Config) (w : RelPtrs) (ins : Word) : BitVec 64 := slotVal c.σ.mem (w.slot ins.c)

/-- `n % 0`: the kernel is stuck (the `luaG_opinterror` exit), no step. -/
theorem mod_zero : ArmBody .MOD fun p c s w ins => BothInt p c s w ins ∧ divisor c w ins = 0#64 :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hz⟩ => by
  kit_arith_ints 0x8001dc58
  simp [Opnd.fill, δ, BinOp.int, imod, hz] at hk

/-- `n % -1 = 0` (`luaV_mod`'s `l_castS2U(n) + 1u <= 1u` exit). -/
theorem mod_m1 : ArmBody .MOD fun p c s w ins => BothInt p c s w ins ∧ divisor c w ins = -1#64 :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hm⟩ => by
  kit_arith_ints 0x8001dc58
  have hz : ¬ slotVal c.σ.mem (w.slot ins.c) = 0#64 := by simp only [divisor] at hm; rw [hm]; decide
  simp only [Opnd.fill, δ, BinOp.int, imodC_eq _ _ hz] at hk
  simp only [divisor] at hm
  rw [hm, srem_neg_one] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  kit_run h0 acc
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (by kit_frame)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by mod_vals; rw [stData_three, sdData_id]; exact .int),
    h0.pcAt⟩

/-- The remainder `__moddi3` returns. -/
abbrev crem (c : Config) (w : RelPtrs) (ins : Word) : BitVec 64 :=
  (slotVal c.σ.mem (w.slot ins.b)).srem (slotVal c.σ.mem (w.slot ins.c))

/-- The general case's condition: both integers, `n ∉ {0, -1}`, and the
remainder's case `q` (zero; same sign as `n`; corrected). -/
abbrev ModGen (q : Config → RelPtrs → Word → Prop) (p : Proto) (c : Config) (s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  BothInt p c s w ins ∧ ¬ (divisor c w ins = 0#64 ∨ divisor c w ins = -1#64) ∧ q c w ins

set_option hygiene false in
/-- `OP_MOD`'s general case up to `__moddi3`'s return (`0x8001f7fc`). -/
local macro "mod_call" : tactic => `(tactic| (
  kit_arith_ints 0x8001dc58
  simp only [divisor] at hy
  have hz : ¬ slotVal c.σ.mem (w.slot ins.c) = 0#64 := fun e => hy (.inl e)
  simp at hy
  simp only [Opnd.fill, δ, BinOp.int, imodC_eq _ _ hz] at hk
  simp [VState.apply, writeDefs, KEdge.kills] at hk
  subst hk
  kit_run h0 acc until [0x8002f7b0]
  mod_vals at h0
  obtain ⟨_, acc, h0⟩ := h0.call acc (by pins_of h0) (moddi3_sum _ _ _ hframe? _ _ hz (by decide))
  kit_run h0 acc))

theorem mod_rz : ArmBody .MOD (ModGen fun c w ins => crem c w ins = 0#64) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hy, hr0⟩ => by
  mod_call
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (by kit_frame)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by mod_vals; simp only [hr0, not_true_eq_false, false_and, ite_false, stData_three, sdData_id]
        exact .int),
    h0.pcAt⟩

theorem mod_same : ArmBody .MOD (ModGen fun c w ins => crem c w ins ≠ 0#64 ∧
    (divisor c w ins).msb = (crem c w ins).msb) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hy, hr0, hms⟩ => by
  mod_call
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (by kit_frame)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by mod_vals; simp only [hms, not_true_eq_false, and_false, ite_false, stData_three, sdData_id]
        exact .int),
    h0.pcAt⟩

theorem mod_corr : ArmBody .MOD (ModGen fun c w ins => crem c w ins ≠ 0#64 ∧
    ¬ (divisor c w ins).msb = (crem c w ins).msb) :=
  fun {p} hS {c s s' w ins} hA hf hop hstep ⟨hI, hy, hr0, hms⟩ => by
  mod_call
  exact ⟨_, acc, hc.bleach_store h0 (by kit_pins h0) hAt (by kit_frame)
    (slotStore_sd_sb rfl (by slot_arith) (by slot_arith))
    (by mod_vals; simp only [hr0, hms, not_false_eq_true, and_self, ite_true, stData_three, sdData_id]
        exact .int), h0.pcAt⟩

theorem sim_MOD : SimArm .MOD := sim_arith (by decide)
  (fun {p} hS {c s s' w ins} hA hf hop hstep hI => by
    by_cases hz : divisor c w ins = 0#64
    · exact mod_zero hS hA hf hop hstep ⟨hI, hz⟩
    by_cases hm : divisor c w ins = -1#64
    · exact mod_m1 hS hA hf hop hstep ⟨hI, hm⟩
    have hy : ¬ (divisor c w ins = 0#64 ∨ divisor c w ins = -1#64) := fun h => h.elim hz hm
    by_cases hr : crem c w ins = 0#64
    · exact mod_rz hS hA hf hop hstep ⟨hI, hy, hr⟩
    by_cases hs : (divisor c w ins).msb = (crem c w ins).msb
    · exact mod_same hS hA hf hop hstep ⟨hI, hy, hr, hs⟩
    · exact mod_corr hS hA hf hop hstep ⟨hI, hy, hr, hs⟩)
  fun {p} hS {c s s' w ins} hA hf hop hstep hI => by kit_arith_fall 0x8001dc58

end Lua.Vm.Sim.Kit

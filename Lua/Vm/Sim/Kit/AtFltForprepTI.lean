import Lua.Vm.Sim.Kit.AtFltForprepC
import Lua.Vm.Sim.Kit.AtForprep
import Lua.Vm.At.ForprepTI

/-!
# `OP_FORPREP`'s integer loop with a float limit (lane F1-F8)

`forprep` on an integer `init` and `step` and a float limit (`lvm.c:178`
`forlimit`): `luaV_tointeger(lim, &p, mode)` (`F2Ifloor` for a step `≥ 0`,
`F2Iceil` below), whose two outcomes are the variant call lemmas of
`Lua/Vm/At/ForprepTI.lean` (`tiOk`); on success the integer loop of
`fp_up_run` & co. on the converted limit `tiv`; on failure the float's sign
(`__gedf2(lim, 0.0)`): a positive limit is clipped to `LUA_MAXINTEGER` (or the
descending loop skipped), anything else to `LUA_MININTEGER` (or the
ascending loop skipped). Each path is the kernel's case and `at_go`, as the
integer `FORPREP` (`Kit/AtForprep.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- The coerced integer loop's class: `init`, `step` integers, the limit a
float (`FpCls false true false`), and a condition `q` on the three payloads. -/
def TiQ (q : BitVec 64 → BitVec 64 → BitVec 64 → Prop) (p : Proto) (c : Config) (s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  FpQ q p c s w ins ∧ FpCls false true false p c s w ins

set_option hygiene false in
/-- The setup: the three registers by their views (the limit's payload model
`hxm`), the kernel's integer clause with the limit's `forLimit` on the
machine's conversion (`tiOk`, `tiv`). -/
local macro "ti_setup" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hcq, hcl0, hcl1, hcl2⟩
  simp only [FpQ] at hcq
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  kit_bound hA0 ins.a; kit_bound hA3 (ins.a + 3)
  flt_views
  num_cls_s _, ins.a, hcl0
  num_cls_s _, (ins.a + 1), hcl1
  num_cls_s _, (ins.a + 2), hcl2
  clear hcl0 hcl1 hcl2
  simp [forLimit, Value.tonum?, Numeral.tointegerns, Numeral.toFloat] at hk))

/-- The fork guards over the soft-float answers (`__gedf2(lim, 0.0)`'s sign):
by its specification, then from the case's fact on the limit's model. -/
local macro_rules
  | `(tactic| at_hyp) => `(tactic| (
      simp only [Loc.den, Fld.den, Nat.add_zero, at_fspec, bgtz_gedf2, blez_gedf2, F64.lt_eq_model,
        toModel_zero]
      at_vals))

/-- One path of the integer loop with a float limit: the step's sign
(`up`/`dn`: the mode `luaV_tointeger` gets), the conversion's outcome
(`ok`/`no`), the kernel evaluated on the case's facts (`hcq`: the step
nonzero, its sign, the conversion, the compare or the float's sign), `at_go`. -/
syntax "ti_case " ident ident : tactic

set_option hygiene false in
macro_rules
  | `(tactic| ti_case $d:ident $o:ident) => do
    let up := d.getId == `up
    let ok := o.getId == `ok
    let sgn ← if up then
        `(tactic| (have hmsb := msb_of_pos hpos
                   have hn : ¬ (slotVal c.σ.mem (w.slot (ins.a + 2))).toInt < 0 := by omega))
      else
        `(tactic| (have hmsb := msb_of_neg hst hpos
                   have hn : (slotVal c.σ.mem (w.slot (ins.a + 2))).toInt < 0 := by
                     have : (slotVal c.σ.mem (w.slot (ins.a + 2))).toInt ≠ 0 := fun e =>
                       hst (BitVec.eq_of_toInt_eq (by rw [e]; rfl))
                     omega))
    let md ← if up then `(tifMode_1) else `(tifMode_2)
    let cv ← if ok then `(flt_tif_some hv) else `(flt_tif_none hv)
    `(tactic| (
      ti_setup
      obtain ⟨hst, hpos, hv, hw⟩ := hcq
      $sgn:tactic
      simp only [hn, ↓reduceIte, ← $md:term, $cv:term, hw] at hk
      simp [hst, forCount, hpos, hw, not_gt_maxInt, not_lt_minInt, VState.apply, writeDefs, KEdge.kills,
        neg_step] at hk
      subst hk
      at_go Lua.Vm.At.FORPREP_TI))

/-- **`forprep_ti_arm`**: the integer loop with a float limit, one declaration
per path (`ti_case`: the step's sign × the conversion's outcome × the compare
or the float's sign), and the zero step (the kernel stuck). -/
syntax "forprep_ti_arm" : command

set_option hygiene false in
macro_rules
  | `(forprep_ti_arm) => `(
    theorem ti_zero : ArmBody .FORPREP (TiQ (fun _ _ st => st = 0#64)) := by
      ti_setup; simp [hcq] at hk
    theorem ti_up_run : ArmBody .FORPREP
        (TiQ (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ tiOk 1 l = true ∧ ¬ (tiv 1 l).toInt < i.toInt)) := by
      ti_case up ok
    theorem ti_up_skip : ArmBody .FORPREP
        (TiQ (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ tiOk 1 l = true ∧ (tiv 1 l).toInt < i.toInt)) := by
      ti_case up ok
    theorem ti_up_clip : ArmBody .FORPREP
        (TiQ (fun _ l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ tiOk 1 l = false ∧
          Float.Model.lt zero (F64.toModel l) = true)) := by
      ti_case up no
    theorem ti_up_none : ArmBody .FORPREP
        (TiQ (fun _ l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ tiOk 1 l = false ∧
          Float.Model.lt zero (F64.toModel l) = false)) := by
      ti_case up no
    theorem ti_down_run : ArmBody .FORPREP
        (TiQ (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ tiOk 2 l = true ∧ ¬ i.toInt < (tiv 2 l).toInt)) := by
      ti_case dn ok
    theorem ti_down_skip : ArmBody .FORPREP
        (TiQ (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ tiOk 2 l = true ∧ i.toInt < (tiv 2 l).toInt)) := by
      ti_case dn ok
    theorem ti_down_none : ArmBody .FORPREP
        (TiQ (fun _ l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ tiOk 2 l = false ∧
          Float.Model.lt zero (F64.toModel l) = true)) := by
      ti_case dn no
    theorem ti_down_clip : ArmBody .FORPREP
        (TiQ (fun _ l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ tiOk 2 l = false ∧
          Float.Model.lt zero (F64.toModel l) = false)) := by
      ti_case dn no)

-- **`OP_FORPREP`'s integer loop with a float limit**, its paths (`fp_ti` joins them).
forprep_ti_arm

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtFltForprepTI
import Lua.Vm.Sim.Kit.AtCoerceS
import Lua.Vm.At.ForprepCIIS
import Lua.Vm.At.ForprepCSSS
import Lua.Vm.At.ForprepSI

/-!
# `OP_FORPREP` with a string control value `luaO_str2num` reads as an integer (lane F1-F9)

`forprep` (`lvm.c:236`) on control values among which a string `xs` with
`str2int xs` an integer (the class `S`):

* **the float loop** (a string `init` or `step`, or a string limit with a
  float among the others): each control value by its class (an integer or a
  string through `luaV_tonumber_`: `toni_at`, `tons_at`; a float read), one
  generated at-module per class (`Lua/Vm/At/ForprepC*.lean`, `gen_lua_at.py`
  `FP_CLASSES`), run as the three-float loop is;
* **the integer loop with a string limit** (`ISI`: `forlimit`'s
  `luaV_tointeger` on the string, `tois_at`: the integer, whatever the
  mode), then the integer loop's paths (`Lua/Vm/At/ForprepSI.lean`).

A string operand's view (`str_reg_s`): its tag neither the integer's nor the
float's (`hta`), the context's integer `strIntOf (rsOf X j)` the numeral's
(`hxm`), and the kernel's `str2number` (`hsn`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- Register `j` holds a string `luaO_str2num` reads as an integer. -/
def StrIReg (s : State) (j : Nat) : Prop := ∃ xs, s.regs j = some (.str xs) ∧ (str2int xs).isSome = true

/-- A control value's class: an integer, a float, or a string integer numeral. -/
inductive FCl | i | f | s

/-- Register `j` in class `k`. -/
def ClsReg : FCl → State → Nat → Prop
  | .i => IntReg
  | .f => FltReg
  | .s => StrIReg

/-- **A class of `FORPREP`'s control values** (init, limit, step). -/
def FpClsS (k0 k1 k2 : FCl) (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ClsReg k0 s ins.a ∧ ClsReg k1 s (ins.a + 1) ∧ ClsReg k2 s (ins.a + 2)

set_option hygiene false in
/-- **`str_reg_s j, hT`**: register `j`, a string integer numeral by the class
(`hT : StrIReg s j`): its tag's facts join `hta`, the context's integer
joins `hxm`, the numeral `hsn` (the kernel's `str2number`). -/
macro "str_reg_s " j:term "," hq:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  obtain ⟨xs, hsx, hxi⟩ := $hq
  rw [hsx] at hr; cases hr
  obtain ⟨iv, hiv⟩ := Option.isSome_iff_exists.mp hxi
  have hta' := hv.str_ne
  have hta := And.intro hta' hta
  have hxm' : Lua.Vm.Sim.Kit.strIntOf (Lua.Vm.Sim.Kit.rsOf ⟨p, c, s, w, ins⟩ $j) = iv := by
    rw [Lua.Vm.Sim.Kit.rsOf_eq (X := ⟨p, c, s, w, ins⟩) hsx, Lua.Vm.Sim.Kit.strIntOf_eq hiv]
  have hxm := And.intro hxm' hxm
  have hsn' : Lua.Num.str2number xs = some (.int iv) := by simp [Lua.Num.str2number, hiv]
  have hsn := And.intro hsn' hsn
  clear hta' hxm' hsn'))

set_option hygiene false in
/-- A control value's view by its class. -/
macro "cls_reg_s " j:term "," hq:term : tactic => `(tactic| (
  first
    | (have hcl' : FltReg s $j := by simpa [ClsReg] using $hq
       flt_reg_s $j, hcl')
    | (have hcl' : IntReg s $j := by simpa [ClsReg] using $hq
       int_reg_s $j, hcl')
    | (have hcl' : StrIReg s $j := by simpa [ClsReg] using $hq
       str_reg_s $j, hcl')))

set_option hygiene false in
/-- The views of the three control values, the kernel's conversions. -/
macro "fps_views" : tactic => `(tactic| (
  kit_bound hA0 ins.a; kit_bound hA3 (ins.a + 3)
  flt_views
  have hsn : True := trivial
  cls_reg_s ins.a, hcl0
  cls_reg_s (ins.a + 1), hcl1
  cls_reg_s (ins.a + 2), hcl2
  clear hcl0 hcl1 hcl2))

set_option hygiene false in
/-- **A float-loop class with a string** (`fp_flt3` with the conversions):
the views, the kernel's `tonumber`s, `at_walk`. -/
macro "fps_arm " ns:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hcl0, hcl1, hcl2⟩
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  fps_views
  simp [Value.tonumber?, Value.tonum?, Value.ofFloat, Numeral.toFloat, hsn] at hk
  at_walk $ns))

/-- `FORPREP` on (integer, integer, string). -/
theorem fp_sIIS : ArmBody .FORPREP (FpClsS .i .i .s) := by fps_arm Lua.Vm.At.FORPREP_CIIS
/-- `FORPREP` on (string, string, string). -/
theorem fp_sSSS : ArmBody .FORPREP (FpClsS .s .s .s) := by fps_arm Lua.Vm.At.FORPREP_CSSS

/-! ## The integer loop with a string limit -/

/-- The class `ISI` and a condition `q` on the integer values (init, the
limit's numeral, step). -/
def SiQ (q : BitVec 64 → BitVec 64 → BitVec 64 → Prop) (p : Proto) (c : Config) (s : State)
    (w : RelPtrs) (ins : Word) : Prop :=
  FpClsS .i .s .i p c s w ins ∧ q (slotVal c.σ.mem (w.slot ins.a))
    (strIntOf (rsOf ⟨p, c, s, w, ins⟩ (ins.a + 1))) (slotVal c.σ.mem (w.slot (ins.a + 2)))

set_option hygiene false in
/-- The setup: the views, the kernel's integer clause with the limit's
`forLimit` on the numeral. -/
local macro "si_setup" : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨⟨hcl0, hcl1, hcl2⟩, hcq⟩
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  fps_views
  try simp only [hxm] at hcq
  simp [forLimit, Value.tonum?, Numeral.tointegerns, Numeral.toFloat, hsn] at hk))

theorem si_zero : ArmBody .FORPREP (SiQ (fun _ _ st => st = 0#64)) := by
  si_setup; simp [hcq] at hk

theorem si_up_skip : ArmBody .FORPREP (SiQ (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ l.toInt < i.toInt)) := by
  si_setup; obtain ⟨hst, hpos, hgt⟩ := hcq; have hmsb := msb_of_pos hpos
  simp [hst, forCount, hpos, hgt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP_SI

theorem si_up_run : ArmBody .FORPREP (SiQ (fun i l st => st ≠ 0#64 ∧ 0 < st.toInt ∧ ¬ l.toInt < i.toInt)) := by
  si_setup; obtain ⟨hst, hpos, hgt⟩ := hcq; have hmsb := msb_of_pos hpos
  simp [hst, forCount, hpos, hgt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP_SI

theorem si_down_skip : ArmBody .FORPREP
    (SiQ (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ i.toInt < l.toInt)) := by
  si_setup; obtain ⟨hst, hpos, hlt⟩ := hcq; have hmsb := msb_of_neg hst hpos
  simp [hst, forCount, hpos, hlt, VState.apply, writeDefs, KEdge.kills] at hk; subst hk
  at_go Lua.Vm.At.FORPREP_SI

theorem si_down_run : ArmBody .FORPREP
    (SiQ (fun i l st => st ≠ 0#64 ∧ ¬ 0 < st.toInt ∧ ¬ i.toInt < l.toInt)) := by
  si_setup; obtain ⟨hst, hpos, hlt⟩ := hcq; have hmsb := msb_of_neg hst hpos
  simp [hst, forCount, hpos, hlt, VState.apply, writeDefs, KEdge.kills, neg_step] at hk; subst hk
  at_go Lua.Vm.At.FORPREP_SI

/-- **`OP_FORPREP`'s integer loop with a string limit, every path.** -/
theorem fp_sISI : ArmBody .FORPREP (FpClsS .i .s .i) := fun {p} hS {c s s' w ins} hA hf hop hstep hcl => by
  have h := fun {q : BitVec 64 → BitVec 64 → BitVec 64 → Prop} (b : ArmBody .FORPREP (SiQ q))
      (hq : q (slotVal c.σ.mem (w.slot ins.a)) (strIntOf (rsOf ⟨p, c, s, w, ins⟩ (ins.a + 1)))
        (slotVal c.σ.mem (w.slot (ins.a + 2)))) => b hS hA hf hop hstep ⟨hcl, hq⟩
  generalize slotVal c.σ.mem (w.slot ins.a) = i at h
  generalize strIntOf (rsOf ⟨p, c, s, w, ins⟩ (ins.a + 1)) = l at h
  generalize slotVal c.σ.mem (w.slot (ins.a + 2)) = st at h
  by_cases hst : st = 0#64
  · exact h si_zero hst
  by_cases hpos : 0 < st.toInt
  · by_cases hgt : l.toInt < i.toInt
    · exact h si_up_skip ⟨hst, hpos, hgt⟩
    · exact h si_up_run ⟨hst, hpos, hgt⟩
  · by_cases hlt : i.toInt < l.toInt
    · exact h si_down_skip ⟨hst, hpos, hlt⟩
    · exact h si_down_run ⟨hst, hpos, hlt⟩

end Lua.Vm.Sim.At

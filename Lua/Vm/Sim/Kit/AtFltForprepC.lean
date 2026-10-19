import Lua.Vm.Sim.Kit.AtFltForprep
import Lua.Vm.At.ForprepCIIF
import Lua.Vm.At.ForprepCIFF
import Lua.Vm.At.ForprepCFII
import Lua.Vm.At.ForprepCFIF
import Lua.Vm.At.ForprepCFFI

/-!
# `OP_FORPREP`'s coerced classes on the join route (lane F1-F8)

`forprep` (`lvm.c:236`) on control values that are numbers but neither three
integers nor three floats:

* **the float loop on integer control values** (`luaV_tonumber_` on each
  integer: `cvt2num`, `__floatdidf`; `Kit/AtCoerce.lean`'s call node): the
  classes `IIF`, `IFF`, `FII`, `FIF`, `FFI` (init, limit, step), one
  generated at-module each (`Lua/Vm/At/ForprepC*.lean`, `gen_lua_at.py`
  `FP_CLASSES`), run as the three-float loop is (`fp_flt3`);
* **the integer loop with a float limit** (`IFI`: `forlimit`'s
  `luaV_tointeger` on a float, its two outcomes; `Lua/Vm/At/ForprepTI.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- Register `j` holds an integer. -/
def IntReg (s : State) (j : Nat) : Prop := ∃ i, s.regs j = some (.int i)

/-- A control value's class: a float (`true`) or an integer. -/
def NumCls (f : Bool) (s : State) (j : Nat) : Prop := if f then FltReg s j else IntReg s j

/-- **A coerced class of `FORPREP`'s control values** (init, limit, step). -/
def FpCls (f0 f1 f2 : Bool) (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  NumCls f0 s ins.a ∧ NumCls f1 s (ins.a + 1) ∧ NumCls f2 s (ins.a + 2)

set_option hygiene false in
/-- **`int_reg_s j, hT`**: register `j`, an integer by the class
(`hT : IntReg s j`): its tag joins `hta`, the value is its payload. -/
macro "int_reg_s " j:term "," hq:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  obtain ⟨_, hst⟩ := $hq
  rw [hst] at hr; cases hr
  obtain ⟨hta', rfl⟩ := hv.tag_of_int
  have hta := And.intro hta' hta
  clear hta'))

set_option hygiene false in
/-- A control value's view by its class. -/
macro "num_cls_s " f:term "," j:term "," hq:term : tactic => `(tactic| (
  first
    | (have hcl' : FltReg s $j := by simpa [NumCls] using $hq
       flt_reg_s $j, hcl')
    | (have hcl' : IntReg s $j := by simpa [NumCls] using $hq
       int_reg_s $j, hcl')))

set_option hygiene false in
/-- **A float-loop class of `FORPREP`** (`fp_flt3` with the integers'
conversions): the views, the kernel's `tonumber`s, `at_walk`. -/
macro "fpc_arm " ns:ident : tactic => `(tactic| (
  rintro p hS c s s' w ins hA hf hop hstep ⟨hcl0, hcl1, hcl2⟩
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  kit_bound hA0 ins.a; kit_bound hA3 (ins.a + 3)
  flt_views
  num_cls_s _, ins.a, hcl0
  num_cls_s _, (ins.a + 1), hcl1
  num_cls_s _, (ins.a + 2), hcl2
  clear hcl0 hcl1 hcl2
  simp [Value.tonumber?, Value.tonum?, Value.ofFloat, Numeral.toFloat] at hk
  at_walk $ns))

/-- `FORPREP` on (integer, integer, float). -/
theorem fp_cIIF : ArmBody .FORPREP (FpCls false false true) := by fpc_arm Lua.Vm.At.FORPREP_CIIF
/-- `FORPREP` on (integer, float, float). -/
theorem fp_cIFF : ArmBody .FORPREP (FpCls false true true) := by fpc_arm Lua.Vm.At.FORPREP_CIFF
/-- `FORPREP` on (float, integer, integer). -/
theorem fp_cFII : ArmBody .FORPREP (FpCls true false false) := by fpc_arm Lua.Vm.At.FORPREP_CFII
/-- `FORPREP` on (float, integer, float). -/
theorem fp_cFIF : ArmBody .FORPREP (FpCls true false true) := by fpc_arm Lua.Vm.At.FORPREP_CFIF
/-- `FORPREP` on (float, float, integer). -/
theorem fp_cFFI : ArmBody .FORPREP (FpCls true true false) := by fpc_arm Lua.Vm.At.FORPREP_CFFI

end Lua.Vm.Sim.At

import Lua.Vm.Sim.Kit.AtJoin
import Lua.Vm.At.ForprepF

/-!
# `OP_FORPREP`'s float loop on the location-list route (round 5, A-JOIN held out)

`forprep`'s float case (`lvm.c:236`): the three control values floats; the
step against `0.0` by `__eqdf2` (zero: `luaG_runerror`), its sign by
`__gedf2`, the bound by `__ledf2` or `__gedf2` on the same pair, joined at
`0x8001c1b8` (generator `JOINS`); the kernel's test is `sgnBound lt`
(`forprep_sgnBound`). The generated at-lemmas `Lua/Vm/At/ForprepF.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- The three control values of `FORPREP` are floats. -/
def FpFlt3 (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  FltReg s ins.a ∧ FltReg s (ins.a + 1) ∧ FltReg s (ins.a + 2)

/-- **`OP_FORPREP` on three floats**: the float loop. -/
theorem fp_flt3 (hsf : SoftFloatSpec) : ArmBody .FORPREP FpFlt3 := by
  rintro p hS c s s' w ins hA hf hop hstep ⟨hq0, hq1, hq2⟩
  kit_setup 0x8001c0f8
  simp [forprepK] at hk htop
  kit_bound hA0 ins.a; kit_bound hA3 (ins.a + 3)
  flt_views; flt_reg_s ins.a, hq0; flt_reg_s (ins.a + 1), hq1; flt_reg_s (ins.a + 2), hq2
  simp [Value.tonumber?] at hk
  at_walk Lua.Vm.At.FORPREP_F
  all_goals at_leaf Lua.Vm.At.FORPREP_F

end Lua.Vm.Sim.At

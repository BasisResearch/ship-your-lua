import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Loadf

/-!
# `OP_LOADF` on the location-list route (lane float-m0, M1 training)

`setfltvalue(s2v(ra), cast_num(b))`: `sBx` converted by `__floatsidf`, stored
with the float tag; the generated at-lemmas `Lua/Vm/At/Loadf.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_LOADF`** (`FloatArms.LOADF`). -/
theorem sim_LOADF_flt (hsf : SoftFloatSpec) : SimArm .LOADF :=
  sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001d400
  have hbx := Word.bx_lt ins
  simp [move, setR, Opnd.ports, Opnd.fill, VState.apply, writeDefs, KEdge.kills] at hk htop
  kit_bound hAt ins.a
  subst hk
  at_go Lua.Vm.At.LOADF

end Lua.Vm.Sim.At

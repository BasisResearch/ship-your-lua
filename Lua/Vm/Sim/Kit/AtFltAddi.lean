import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.At.Addi

/-!
# `OP_ADDI` on a float on the location-list route (lane float-m0, M1 held out)

`op_arithI(L, l_addi, luai_numadd)`'s float case: `R[B]` a float,
`cast_num(sC)` by `__floatsidf`, the sum by `__adddf3`, stored by
`setfltvalue`; the generated at-lemmas `Lua/Vm/At/Addi.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- **`OP_ADDI` on a float** (`FloatArms.ADDI`). -/
theorem sim_ADDI_flt (hsf : SoftFloatSpec) : SimArmOn .ADDI FltB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  at_farith 0x8001ca44 Lua.Vm.At.ADDI

end Lua.Vm.Sim.At

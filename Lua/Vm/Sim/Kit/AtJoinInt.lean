import Lua.Vm.Sim.Kit.AtJoinF2I
import Lua.Vm.Sim.Kit.AtFrame
import Lua.Vm.Sim.Kit.AtOps

/-!
# Float operands converted to integers: `op_bitwiseK` (lane F3)

`op_bitwiseK` (`BANDK`, `BORK`, `BXORK`) with a float `R[B]`: `R[B]`
through `luaV_tointegerns(F2Ieq)` (`floor`, `__eqdf2`, the range,
`__fixdfdi`), `K[C]` an integer constant (the kernel `bitwiseRK` exists only
for one). The machine reads `K[C]` after `floor`'s call, through its frame:
the at-lemmas forward that load (`Kit/AtFrame.lean`).

* `at_jbitk pc NS`: the set-up before `at_walk`: `K[C]` by `kitb_const`, the
  float `R[B]` by its view, the kernel's `tointegerns` over the atoms
  (`rawArith_bit_fi`); a stored integer is `__fixdfdi`'s under the range
  fact (`at_new_ext`, `Kit/AtJoinF2I.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
/-- **`at_jbitk pc NS`**: `op_bitwiseK`'s float case (`hT : FltB`): `K[C]`
an integer (`kitb_const`), `R[B]` by its view, `δ` over the atoms
(`rawArith_bit_fi`), then `at_walk NS`. -/
macro "at_jbitk " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kitb_const
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  have hrod := hc.rodata
  flt_reg_q x ins.b, hT
  simp only [Opnd.fill, fastArith] at hk
  simp (disch := decide) [Value.toNum?, BinOp.toOp, rawArith_bit_fi, Res.ofInt, intarith, Value.ofNum,
    VState.apply, writeDefs, KEdge.kills] at hk
  at_walk $ns))

end Lua.Vm.Sim.At

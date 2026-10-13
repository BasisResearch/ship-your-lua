import Lua.Vm.Sim.Kit.AtJoin

/-!
# Kernel-shape set-ups for the join route (lane F2)

The join route (`Kit/AtJoin.lean`) runs an arm's float paths once, splits
at the machine's forks, and refutes each leaf by one closed `decide` over
the pair atoms. What is left per kernel shape is the set-up before the
walk: which registers are read through which view, and the kernel evaluated
on them. These macros name that set-up once per `opKernel` combinator, so
an arm is its jump-table target and its at-lemma namespace:

* `at_jorderI pc NS`: `op_orderI` (`LTI`, `LEI`, `GTI`, `GEI`): a float
  `R[A]` (`FltA`) against the 8-bit immediate;
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

set_option hygiene false in
/-- **`at_jorderI pc NS`**: `op_orderI` on a float `R[A]` (`hT : FltA`):
the immediate's conversion (`l_intfitsf` of an 8-bit immediate holds) and
the kernel's test evaluated, then `at_walk NS`. -/
macro "at_jorderI " pc:num ns:ident : tactic => `(tactic| (
  kit_setup $pc
  kit_nj
  try simp [immB, Opnd.ports] at htop
  try simp only [immB, Opnd.ports] at hk
  kit_bound hAt ins.a
  have hbb := Word.b_lt ins
  flt_views
  flt_reg_s ins.a, hT
  simp [Opnd.fill, Opnd.ports, immB, Word.sb, Word.offsetSC, δ, Value.toNum?, ltNum, leNum, ltIntFloat,
    leIntFloat, ltFloatInt, leFloatInt, intfitsf_imm _ hbb] at hk
  at_walk $ns))

end Lua.Vm.Sim.At

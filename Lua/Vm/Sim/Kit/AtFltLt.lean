import Lua.Vm.Sim.Kit.AtJoin
import Lua.Vm.At.LtF

/-!
# `OP_LT` with a float operand on the location-list route (round 5, A-JOIN held out)

`LTnum` (`lvm.c:480`): `R[A]` or `R[B]` a float, the other by its view
(`num_regf`): a float (`__ltdf2` = `__ledf2`, `slti 0`), an integer inside
`l_intfitsf` (`__floatdidf`, then `__gedf2`/`__ledf2`), or no number (the
kernel is stuck: `luaG_ordererror`). The machine's one fork on a soft-float
answer is `docondjump`'s test against `k` (`0x8001c900`); the leaves are
decided over the pair atom and the `k` bit. The generated at-lemmas
`Lua/Vm/At/LtF.lean`.

**Open: `LtF2I_Statement`**, an integer operand outside `l_intfitsf`
(`LTintfloat`/`LTfloatint`'s `luaV_flttointeger` chain: `floor`, `__eqdf2`,
`__adddf3`, the range tests, `__fixdfdi`, then an integer compare). It
needs `floor`'s summary (newlib `s_floor.c` calls `__adddf3` and `__gedf2`
itself; `gen_lua_fn.py` lifts no routine that calls a soft-float routine)
and the value equation `__fixdfdi (floor x) = (floor x).toInt64` under the
range atoms; the walk stops at `jal floor` (`0x8001f900`, `0x8001fb00`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps StepsN)

/-- `LT` on an integer outside `l_intfitsf` and a float. -/
def LtF2I (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  (∃ i x n, s.regs ins.a = some (.int i) ∧ s.regs ins.b = some (.flt x n) ∧ intfitsf i = false) ∨
  (∃ i x n, s.regs ins.a = some (.flt x n) ∧ s.regs ins.b = some (.int i) ∧ intfitsf i = false)

/-- **Open (round 5): `LT`'s `luaV_flttointeger` paths** (see the module
doc). Supplied by `floor`'s summary and the chain's value equation. -/
def LtF2I_Statement : Prop := ArmBody .LT LtF2I

/-- **`OP_LT` with a float operand** (`FloatArms.LT`), its f2i paths open. -/
theorem sim_LT_flt (hsf : SoftFloatSpec) (hf2i : LtF2I_Statement) : SimArmOn .LT FltAB :=
  sim_arm_on (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep hT => by
  kit_setup 0x8001c894
  kit_nj
  kit_bound hAt ins.a; kit_bound hBt ins.b
  flt_views
  refine hT.elim (fun hq => ?fa) (fun hq => ?fb)
  case' fa => flt_reg_s ins.a, hq; num_regf ins.b, hn
  case' fb => num_regf ins.a, hn; all_goals flt_reg_s ins.b, hq
  all_goals simp only [Opnd.fill] at hk
  all_goals try (rcases v with _ | _ | _ | _ | _ | _ <;> simp [δ, Value.toNum?] at hk hn <;> done)
  all_goals simp [δ, Value.toNum?, ltNum, ltIntFloat, ltFloatInt] at hk
  all_goals try simp only [hfit, ite_true] at hk
  all_goals first
    | exact hf2i hS hA hf hop hstep (by first
        | exact .inl ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩
        | exact .inr ⟨_, _, _, ‹_›, ‹_›, by simpa using hfit⟩)
    | skip
  all_goals at_walk Lua.Vm.At.LT_F
  all_goals at_leaf Lua.Vm.At.LT_F

end Lua.Vm.Sim.At

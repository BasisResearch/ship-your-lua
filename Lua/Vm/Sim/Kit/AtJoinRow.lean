import Lua.Vm.Sim.Kit.AtFloat

/-!
# Cut points at the machine's joins (round 5, A-JOIN)

Where two sides of a machine fork meet again (FORLOOP's `0x8001e194`: the
`__ledf2` side and the `__gedf2` side both leave a 0/1 bound in `a5`), the
generator (`scripts/gen_lua_at.py` `JOINS`) names the join state once:

* the joined register is the location `.fn j<k>`, `j<k> X := if G then v_t
  else v_f` with `G` the fork's guard (`@[at_fspec]`, so it unfolds where the
  call answers do);
* each side ends in a join lemma `join_<pc>[_k]`, an `AtStep` of no machine
  step from the side's row to the join row (`at_join` below), under the
  side's guard;
* the tail from the join row is walked, and emitted, once.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

set_option hygiene false in
/-- **`at_join e`**: a join lemma's proof. No step is taken; the side's pins
are the join row's, the joined register by `e : Loc.den X (.fn j<k>) = v`
(the side's value under its guard). -/
macro "at_join " e:term : tactic => `(tactic| (
  intro c h
  simp only [At] at h
  refine ⟨c, Vsa.Machine.Steps.refl c, Vsa.Sim.SegSt.repin h ?_⟩
  simp only [at_row]
  rw [$e:term]
  at_pins h))

end Lua.Vm.Sim.At

import Lua.Vm.Arms.Text
import Vsa.Sim.StoreHalf

/-!
# `.text` across a halfword store (`sh`)

The survival lemma of `TextLoaded` for `writeMap2` (`Vsa/Sim/StoreHalf.lean`),
apart from `Lua/Vm/Arms/Text.lean` so that only the segment modules with an
`sh` step import it (`scripts/gen_lua_arms.py`).
-/

namespace Lua.Vm.Arms

theorem TextLoaded.writeMap2 {m : Std.ExtHashMap Nat (BitVec 8)} (h : TextLoaded m)
    {k : Nat} (d : BitVec (8 * 2)) (hk : Vsa.Sim.tohostAddr + 16 ≤ k) :
    TextLoaded (Vsa.Sim.writeMap2 m k d) :=
  (h.insert _ hk).insert _ (by omega)

end Lua.Vm.Arms

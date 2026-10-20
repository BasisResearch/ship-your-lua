import Lua.Vm.Sim.Kit.FmtLib

/-!
# `subw` of two offsets of one atom (lane F1-24)

The callee-context generator decides `subw` of two offsets of the same atoms
(`gen_lua_at.py`: `fmt - fmt0`, `_svfprintf_r`'s digit count `s6 - s10` after
the hex loop) as a literal; a signed test of that literal is the at-lemma's
own obligation, closed here by one `fat_gnd` rule (and `fat_hyp` alike): the
32-bit difference of two `ofNat`s is the `ofNat` of the difference
(`fmt_subw_ofNat`), a literal less a positive literal by `subw_neg0`, then the
signed test of literals (`fmt_scmp`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

/-- **`subw` of two `ofNat`s a small distance apart**: the `ofNat` of the
distance. -/
theorem fmt_subw_ofNat {a b : Nat} (h1 : b ≤ a) (h2 : a < 2 ^ 64) (h3 : a - b < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0 -
      Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) = BitVec.ofNat 64 (a - b) := by
  rw [extract_ofNat, extract_ofNat, show BitVec.ofNat 32 a - BitVec.ofNat 32 b = BitVec.ofNat 32 (a - b) by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega]
  exact fmt_sext32_ofNat h3

/-- **`subw_lit`**: a `subw` of two `ofNat`s rewritten to its value (the
distance, or a literal less a positive literal), then the signed test. -/
macro "subw_lit" : tactic => `(tactic| (
  fmt_scmp_goal
  first
    | rw [fmt_subw_ofNat (by omega) (by omega) (by omega)]
    | rw [subw_neg0 (by omega) (by omega)]
  fmt_scmp))

/-- A decided signed test of such a difference (a segment's guard). -/
macro_rules
  | `(tactic| fat_gnd) => `(tactic| (subw_lit; done))

/-- The same test as a chained at-lemma's hypothesis. -/
macro_rules
  | `(tactic| fat_hyp) => `(tactic| (subw_lit; done))

end Lua.Vm.Sim.Kit

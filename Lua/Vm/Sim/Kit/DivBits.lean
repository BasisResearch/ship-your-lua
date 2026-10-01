import Lua.Vm.Sim.Kit.Run

/-!
# The division arms' bit facts

`luaV_mod`/`luaV_idiv` inlined split off `n ∈ {0, -1}` by `n + 1 ≤ 1`
(unsigned, `bgeu`): `bgeu_one`; and `m % -1 = 0`: `srem_neg_one`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim.Kit

/-- `bgeu a4,a3` with `a4 = 1`, `a3 = n + 1`: `n` is `0` or `-1`. -/
theorem bgeu_one (y : BitVec 64) : zopz0zKzJ_u 1#64 (y + 1#64) = decide (y = 0#64 ∨ y = -1#64) := by
  have hy := y.isLt
  have e : (y + 1#64).toNat = (y.toNat + 1) % 2^64 := by simp [BitVec.toNat_add]
  have i0 : y = 0#64 ↔ y.toNat = 0 :=
    ⟨fun h => by simp [h], fun h => BitVec.eq_of_toNat_eq (by simpa using h)⟩
  have i1 : y = -1#64 ↔ y.toNat = 2^64 - 1 :=
    ⟨fun h => by subst h; decide, fun h => BitVec.eq_of_toNat_eq (by simp [h])⟩
  rcases bgeu_cases 1#64 (y + 1#64) with g | g
  · have := bgeu_true _ _ g; rw [e] at this; simp at this
    rw [g]; symm; simp only [decide_eq_true_eq, i0, i1]; omega
  · have := bgeu_false _ _ g; rw [e] at this; simp at this
    rw [g]; symm; simp only [decide_eq_false_iff_not, not_or, i0, i1]; omega

theorem srem_neg_one (x : BitVec 64) : x.srem (-1#64) = 0#64 := by
  have : (18446744073709551615#64 : BitVec 64).msb = true := by decide
  cases h : x.msb <;> simp [BitVec.srem_eq, h, this]

end Lua.Vm.Sim.Kit

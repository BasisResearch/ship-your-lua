import Lua.Num.F64

/-!
# Round 5 §2b: two round-to-odd laws as closed `decide`s (cost feasibility)

Not imported by `Lua`. Run with `abstractions/checks/round5/run_lean.sh`.
Measures what a kernel `decide` costs on small instances of the laws
`rto.py` checked in Python (R5-R2-4 §4): `rto_add_even` on 8-bit operands,
the parity counterexample, and `shr_rto`'s margin (holds for `s ≥ 2`, the
counterexample at `s = 1`).
-/

namespace Lua.Num.RtoDecide

set_option profiler true
set_option profiler.threshold 200

/-- Round to odd: `n / 2^k` with the dropped bits jammed into bit 0. -/
def rto (n k : Nat) : Nat := n / 2 ^ k ||| (if n % 2 ^ k ≠ 0 then 1 else 0)

/-- `rto_add_even` on 8-bit instances: `A` even, `A < 2^4`, `B < 2^8`,
`k < 8` (4,096 cases with `A` even). -/
theorem rto_add_even_8 :
    ∀ A < 16, ∀ B < 256, ∀ k < 8, A % 2 = 0 → A + rto B k = rto (A * 2 ^ k + B) k := by
  decide +kernel

/-- The parity side condition is load-bearing: `A = 1, B = 1, k = 1`. -/
theorem rto_add_odd_cex : ¬ (1 + rto 1 1 = rto (1 * 2 ^ 1 + 1) 1) := by decide +kernel

/-- `shr_rto` (innocuous double rounding) with margin `s ∈ {2, 3}` (`s + 2`, `s < 2`), `n < 2^8`,
`k < 5`, on `F64.shr`'s full triple. -/
theorem shr_rto_8 :
    ∀ n < 256, ∀ k < 5, ∀ s < 2,
      (F64.shr (rto n k) false false (s + 2) == F64.shr n false false (s + 2 + k)) = true := by
  decide +kernel

/-- The margin is load-bearing: at `s = 1` it fails (`n = 3, k = 1`). -/
theorem shr_rto_s1_cex : F64.shr (rto 3 1) false false 1 ≠ F64.shr 3 false false (1 + 1) := by
  decide +kernel

#print axioms rto_add_even_8
#print axioms rto_add_odd_cex
#print axioms shr_rto_8
#print axioms shr_rto_s1_cex

end Lua.Num.RtoDecide

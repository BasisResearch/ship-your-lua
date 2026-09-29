import Vsa.Sim.BlockMem
import Vsa.Sim.BlockPilot

/-!
# Register-list (`GRegs`) lookups through `eraseG` and `stepGM`

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register

namespace Vsa.Sim

/-! ### From `Vsa.Sim.SegFrameFactsAuto` -/

/-- `lookupG` ignores a key erased at a different index. -/
theorem lookupG_eraseG_ne (n rd : Nat) (h : n ≠ rd) :
    ∀ L : GRegs, lookupG n (eraseG rd L) = lookupG n L := by
  intro L
  induction L with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [eraseG]
    split
    · next hkrd => rw [ih, lookupG, if_neg (by omega)]
    · next hkrd => rw [lookupG, lookupG, ih]

/-! ### From `Vsa.Sim.SegReadback` -/

/-- `lookupG n` of a `stepGM` that WRITES `n` (a non-store whose `rd = n`) is
exactly the value written, `wvalM a L bs`.  The one-instruction base case of the
readback: no fold, one match reduction on the concrete `a.kind`. -/
theorem lookupG_stepGM_writer (a : MInstr) (L : GRegs) (bs : List (BitVec 8))
    (hstore : a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh) (n : Nat)
    (hrd : a.rd = n) :
    lookupG n (stepGM a L bs) = some (wvalM a L bs) := by
  unfold stepGM
  obtain ⟨h1, h2, h3, h4⟩ := hstore
  cases hk : a.kind <;> first
    | (exact absurd hk (by assumption))
    | (subst hrd; rw [lookupG, if_pos rfl])

end Vsa.Sim

import Vsa.Sim.ExecRetEpilogue
import Vsa.Sim.Generic.MemRead
import Vsa.Sim.BlockMem

/-!
# Word reads from the image and unsigned-compare facts for the allocator runs

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.

`gpV` is the WHILE ELF's `__global_pointer$`, as in the allocator step tables
that use it; those tables are regenerated at Lua addresses in PHASES A0.5.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace VsaIris.MallocFast

open Vsa.Sim

/-! ### From `VsaIris.Vsa.MallocFastSegs` -/

/-- `__global_pointer$`. -/
abbrev gpV : BitVec 64 := 0x8001b510#64

theorem uge_iff (a b : BitVec 64) : zopz0zKzJ_u a b = true ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]

theorem ult_iff (a b : BitVec 64) : zopz0zI_u a b = true ↔ a.toNat < b.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

/-- The 8 image bytes at `a`, as a load's byte list. -/
def wordOf (f : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6), f (a + 7)]

/-- A load's value from any memory holding the image where it reads. -/
theorem wordOf_value {f : Nat → BitVec 8} {a : Nat} {m : Std.ExtHashMap Nat (BitVec 8)} {v : BitVec 64}
    (him : ∀ k, k < 8 → m[a + k]? = some (f (a + k))) (hr : Vsa.MemRepr.read64 m a = some v.toNat) :
    bytesVal .ld (wordOf f a) = v := by
  have := execRetEpilogueWord_value m a v hr
  have e : execRetEpilogueWord m a = wordOf f a := by
    simp only [execRetEpilogueWord, wordOf]
    rw [show m[a]? = some (f a) by simpa using him 0 (by omega), him 1 (by omega), him 2 (by omega),
      him 3 (by omega), him 4 (by omega), him 5 (by omega), him 6 (by omega), him 7 (by omega)]
    rfl
  rwa [e] at this

end VsaIris.MallocFast

import Vsa.Sim.ValueSites
import Vsa.Sim.Generic.MemRead
import Vsa.Triple

/-!
# `MemExtends` (populated addresses stay populated) and the `setjmp` buffer image

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr

namespace Vsa.Sim

/-! ### From `Vsa.Sim.ValueSpec` -/

/-- A single byte read at `k` disjoint from the `writeMap4`-window `[a4, a4+4)`
passes through to `mem`. -/
theorem getElem_writeMap4_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a4 k : Nat)
    (d : BitVec (8 * 4)) (hk : k < a4 ∨ a4 + 4 ≤ k) :
    (writeMap4 mem a4 d)[k]? = mem[k]? := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-- A single byte read at `k` disjoint from the `writeMap8`-window `[a8, a8+8)`
passes through to `mem`. -/
theorem getElem_writeMap8_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a8 k : Nat)
    (d : BitVec (8 * 8)) (hk : k < a8 ∨ a8 + 8 ≤ k) :
    (writeMap8 mem a8 d)[k]? = mem[k]? := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-! ### From `Vsa.Sim.EvalSimCommon` -/

/-- Every address populated in `m0` is still populated in `m`. All real machine
memory deltas are `writeMap4/8` chains (inserts), so every verified walk
preserves this; it is the fact `EvalExit` forgets and recursive callers need
(the post-call `ld`s of the unconstrained sub-result padding bytes). -/
def MemExtends (m0 m : Mem) : Prop :=
  ∀ (a : Nat) (b : BitVec 8), m0[a]? = some b → ∃ b', m[a]? = some b'

theorem MemExtends.refl (m : Mem) : MemExtends m m := fun _ b h => ⟨b, h⟩

/-- A `writeMap8` (an 8-byte insert) preserves presence: nothing is deleted, and
the 8 written bytes are present. -/
theorem memExtends_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8)) :
    MemExtends mem (writeMap8 mem a8 d) := by
  intro k b hk
  by_cases hin : a8 ≤ k ∧ k < a8 + 8
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a8 ∨ k = a8 + 1 ∨ k = a8 + 2 ∨ k = a8 + 3 ∨ k = a8 + 4 ∨
        k = a8 + 5 ∨ k = a8 + 6 ∨ k = a8 + 7 from by omega)
      with h | h | h | h | h | h | h | h
    · exact ⟨_, by rw [show k = a8 + 0 from by omega]; exact getElem_writeMap8_0 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_1 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_2 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_3 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_4 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_5 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_6 mem a8 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap8_7 mem a8 d⟩
  · exact ⟨b, by rw [getElem_writeMap8_disjoint mem a8 k d (by omega)]; exact hk⟩

/-- A `writeMap4` (a 4-byte insert) preserves presence. -/
theorem memExtends_writeMap4 (mem : Mem) (a4 : Nat) (d : BitVec (8 * 4)) :
    MemExtends mem (writeMap4 mem a4 d) := by
  intro k b hk
  by_cases hin : a4 ≤ k ∧ k < a4 + 4
  · obtain ⟨hlo, hhi⟩ := hin
    rcases (show k = a4 ∨ k = a4 + 1 ∨ k = a4 + 2 ∨ k = a4 + 3 from by omega)
      with h | h | h | h
    · exact ⟨_, by rw [show k = a4 + 0 from by omega]; exact getElem_writeMap4_0 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_1 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_2 mem a4 d⟩
    · exact ⟨_, by rw [h]; exact getElem_writeMap4_3 mem a4 d⟩
  · exact ⟨b, by rw [getElem_writeMap4_disjoint mem a4 k d (by omega)]; exact hk⟩

theorem MemExtends.trans {m0 m1 m2 : Mem}
    (h1 : MemExtends m0 m1) (h2 : MemExtends m1 m2) : MemExtends m0 m2 := by
  intro a b h
  obtain ⟨b', hb'⟩ := h1 a b h
  exact h2 a b' hb'

/-! ### From `Vsa.Sim.JmpSpec` -/

abbrev setjmpBuf (m0 : Std.ExtHashMap Nat (BitVec 8)) (jb : BitVec 64)
    (ra0 s0v s1v s2v s3v s4v s5v s6v s7v s8v s9v s10v s11v spv : BitVec 64) :
    Std.ExtHashMap Nat (BitVec 8) :=
  writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8
  (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 (writeMap8 m0
    (jb.toNat + 0)   (sdData_val ra0))
    (jb.toNat + 8)   (sdData_val s0v))
    (jb.toNat + 16)  (sdData_val s1v))
    (jb.toNat + 24)  (sdData_val s2v))
    (jb.toNat + 32)  (sdData_val s3v))
    (jb.toNat + 40)  (sdData_val s4v))
    (jb.toNat + 48)  (sdData_val s5v))
    (jb.toNat + 56)  (sdData_val s6v))
    (jb.toNat + 64)  (sdData_val s7v))
    (jb.toNat + 72)  (sdData_val s8v))
    (jb.toNat + 80)  (sdData_val s9v))
    (jb.toNat + 88)  (sdData_val s10v))
    (jb.toNat + 96)  (sdData_val s11v))
    (jb.toNat + 104) (sdData_val spv)

end Vsa.Sim

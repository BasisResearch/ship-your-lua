import Vsa.Sim.ValueSites
import Vsa.Triple

/-!
# Reads of written byte maps (`insert`, `writeMap2/4/8`)

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

namespace Vsa.Sim

/-! ### From `Vsa.Sim.ValueSpec` -/

/-- Read-over-write helper: `(mem.insert j v)[i]? = mem[i]?` when `j ≠ i`
(as a Bool disequality `(j == i) = false`). -/
theorem getElem_insert_ne (mem : Std.ExtHashMap Nat (BitVec 8)) (i j : Nat) (v : BitVec 8)
    (hne : (j == i) = false) : (mem.insert j v)[i]? = mem[i]? := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

/-- Read-over-write helper: `(mem.insert i v)[i]? = some v`. -/
theorem getElem_insert_self (mem : Std.ExtHashMap Nat (BitVec 8)) (i : Nat) (v : BitVec 8) :
    (mem.insert i v)[i]? = some v := by
  rw [Std.ExtHashMap.getElem?_insert, if_pos (by simp)]

/-- A single byte read at `k` disjoint from the width-2 store window `[a2, a2+2)`
passes through to `mem`.  Stated on the raw two-insert image — the unfolding of
`writeMap2` (`PinW`, an `abbrev`), so it applies to `writeMap2` terms directly. -/
theorem getElem_writeMap2_disjoint (mem : Std.ExtHashMap Nat (BitVec 8)) (a2 k : Nat)
    (d : BitVec (8 * 2)) (hk : k < a2 ∨ a2 + 2 ≤ k) :
    ((mem.insert a2 (d.extractLsb' 0 8)).insert (a2 + 1) (d.extractLsb' 8 8))[k]? = mem[k]? := by
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega)]

/-- The four bytes of `writeMap4 mem a d`, read back individually. -/
theorem getElem_writeMap4_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap4_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_self]

theorem getElem_writeMap4_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap4]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap4_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 4)) :
    (writeMap4 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap4]
  rw [getElem_insert_self]

/-- The eight bytes of `writeMap8 mem a d`, read back individually. -/
theorem getElem_writeMap8_0 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a]? = some (d.extractLsb' 0 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_1 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 1]? = some (d.extractLsb' 8 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_2 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 2]? = some (d.extractLsb' 16 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_3 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 3]? = some (d.extractLsb' 24 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 4]? = some (d.extractLsb' 32 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_5 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 5]? = some (d.extractLsb' 40 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega),
    getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_6 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 6]? = some (d.extractLsb' 48 8) := by
  simp only [writeMap8]
  rw [getElem_insert_ne _ _ _ _ (by simp only [beq_eq_false_iff_ne, ne_eq]; omega), getElem_insert_self]

theorem getElem_writeMap8_7 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    (writeMap8 mem a d)[a + 7]? = some (d.extractLsb' 56 8) := by
  simp only [writeMap8]
  rw [getElem_insert_self]

/-! ### From `Vsa.Sim.SnprintfSpec5` -/

/-- Reads outside an 8-byte `writeMap8` window are unchanged. -/
theorem getElem?_writeMap8_out (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat)
    (d : BitVec (8 * 8)) (a : Nat) (ha : a < k ∨ k + 8 ≤ a) :
    (writeMap8 mem k d)[a]? = mem[a]? := by
  show ((((((((mem.insert k _).insert (k+1) _).insert (k+2) _).insert (k+3) _).insert
    (k+4) _).insert (k+5) _).insert (k+6) _).insert (k+7) _)[a]? = mem[a]?
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

end Vsa.Sim

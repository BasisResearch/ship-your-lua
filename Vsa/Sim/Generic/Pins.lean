import Vsa.Sim.ValueSites
import Vsa.Sim.Generic.MapReads

/-!
# Byte-pin predicates over the memory map (`Pin4`, `Pin8`, `SlotHolds`, `MvBytes`)

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

namespace Vsa.Sim

/-! ### From `Vsa.Sim.SnprintfSpec5` -/

def SlotHolds (vsp : BitVec 64) (off : Nat) (v : BitVec 64)
    (mem : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[(vsp + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat + 7]? = some ((sdData_val v).extractLsb' 56 8)

/-! ### From `Vsa.Sim.SnprintfSpec18` -/

/-- The source-window ghost: `bs` pins the `n` source bytes in `m0`. -/
def MvBytes (m0 : Std.ExtHashMap Nat (BitVec 8)) (src : BitVec 64) (n : Nat)
    (bs : Nat → BitVec 8) : Prop :=
  ∀ k, k < n → m0[(src.toNat + k)]? = some (bs k)

/-! ### From `Vsa.Sim.SnprintfSpec19` -/

/-- The 8 little-endian bytes of `sdData_val v` pinned at `[a, a+8)`. -/
def Pin8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) : Prop :=
  mem[a]? = some ((sdData_val v).extractLsb' 0 8) ∧
  mem[a + 1]? = some ((sdData_val v).extractLsb' 8 8) ∧
  mem[a + 2]? = some ((sdData_val v).extractLsb' 16 8) ∧
  mem[a + 3]? = some ((sdData_val v).extractLsb' 24 8) ∧
  mem[a + 4]? = some ((sdData_val v).extractLsb' 32 8) ∧
  mem[a + 5]? = some ((sdData_val v).extractLsb' 40 8) ∧
  mem[a + 6]? = some ((sdData_val v).extractLsb' 48 8) ∧
  mem[a + 7]? = some ((sdData_val v).extractLsb' 56 8)

/-- The 4 little-endian bytes of a 32-bit word pinned at `[a, a+4)`. -/
def Pin4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) : Prop :=
  mem[a]? = some (w.extractLsb' 0 8) ∧
  mem[a + 1]? = some (w.extractLsb' 8 8) ∧
  mem[a + 2]? = some (w.extractLsb' 16 8) ∧
  mem[a + 3]? = some (w.extractLsb' 24 8)

theorem Pin8_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {v : BitVec 64}
    (hf : ∀ k, a ≤ k → k < a + 8 → mem'[k]? = mem[k]?) (h : Pin8 mem a v) : Pin8 mem' a v := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨(hf a (by omega) (by omega)).trans h0,
   (hf (a+1) (by omega) (by omega)).trans h1,
   (hf (a+2) (by omega) (by omega)).trans h2,
   (hf (a+3) (by omega) (by omega)).trans h3,
   (hf (a+4) (by omega) (by omega)).trans h4,
   (hf (a+5) (by omega) (by omega)).trans h5,
   (hf (a+6) (by omega) (by omega)).trans h6,
   (hf (a+7) (by omega) (by omega)).trans h7⟩

theorem Pin4_frame {mem mem' : Std.ExtHashMap Nat (BitVec 8)} {a : Nat} {w : BitVec 32}
    (hf : ∀ k, a ≤ k → k < a + 4 → mem'[k]? = mem[k]?) (h : Pin4 mem a w) : Pin4 mem' a w :=
  ⟨(hf a (by omega) (by omega)).trans h.1,
   (hf (a+1) (by omega) (by omega)).trans h.2.1,
   (hf (a+2) (by omega) (by omega)).trans h.2.2.1,
   (hf (a+3) (by omega) (by omega)).trans h.2.2.2⟩

theorem Pin8_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (v : BitVec 64) :
    Pin8 (writeMap8 mem a (sdData_val v)) a v :=
  ⟨getElem_writeMap8_0 _ _ _, getElem_writeMap8_1 _ _ _, getElem_writeMap8_2 _ _ _,
   getElem_writeMap8_3 _ _ _, getElem_writeMap8_4 _ _ _, getElem_writeMap8_5 _ _ _,
   getElem_writeMap8_6 _ _ _, getElem_writeMap8_7 _ _ _⟩

theorem Pin4_writeMap4 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (w : BitVec 32) :
    Pin4 (writeMap4 mem a w) a w :=
  ⟨getElem_writeMap4_0 _ _ _, getElem_writeMap4_1 _ _ _,
   getElem_writeMap4_2 _ _ _, getElem_writeMap4_3 _ _ _⟩

/-! ### From `Vsa.Sim.SnprintfSpec25` -/

/-- A `Pin8` at the slot's effective address *is* the `SlotHolds`. -/
theorem slotHolds_of_pin8_rt (base : BitVec 64) (off : Nat) (v : BitVec 64) (A : Nat)
    (mem : Std.ExtHashMap Nat (BitVec 8))
    (hA : (base + sign_extend (m := 64) (BitVec.ofNat 12 off)).toNat = A)
    (h : Pin8 mem A v) : SlotHolds base off v mem := by
  unfold SlotHolds
  rw [hA]
  exact h

end Vsa.Sim

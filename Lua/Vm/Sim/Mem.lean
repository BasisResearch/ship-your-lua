import Lua.Vm.Arms.Head
import Lua.Vm.Repr
import Vsa.Sim.Generic.MapReads
import Vsa.Sim.RamReadLoad

/-!
# Byte-level facts the A1 arms consume

* total reads of a stack slot's tag and payload (`slotTag`, `slotVal`, as the
  arms' `lbu`/`ld` read them), and what `sd` + `sb` (in either order) leave
  there (`store_sd_sb`, `store_sb_sd`);
* reads that only depend on the bytes they cover (`bytesT4_congr`,
  `bytesT8_congr`);
* the dispatch table in `.rodata` (`jtWord`, `armTarget`): its words read
  from any memory holding the image's `.rodata` (`jtWord_eq`), and every
  target 4-byte aligned (`armTarget_aligned`, one kernel check).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Vm.Layout

/-- The `tt_` byte of the stack slot at `a`, as `lbu` reads it. -/
def slotTag (m : Mem) (a : Nat) : BitVec 8 := bytesT1 m (a + tvalueTagOff)

/-- The 8-byte `value_` of the stack slot at `a`, as `ld` reads it. -/
def slotVal (m : Mem) (a : Nat) : BitVec 64 := bytesT8 m (a + tvalueValOff)

theorem bytesT4_congr {m m' : Mem} {a : Nat} (h : ∀ i, i < 4 → m[a + i]? = m'[a + i]?) :
    bytesT4 m a = bytesT4 m' a := by
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4, h0, h 1 (by omega), h 2 (by omega), h 3 (by omega)]

theorem bytesT8_congr {m m' : Mem} {a : Nat} (h : ∀ i, i < 8 → m[a + i]? = m'[a + i]?) :
    bytesT8 m a = bytesT8 m' a := by
  have h0 := h 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT8, h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
    h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-- A slot's tag and payload depend only on its first nine bytes. -/
theorem slot_congr {m m' : Mem} {a : Nat} (h : ∀ i, i < 9 → m[a + i]? = m'[a + i]?) :
    slotTag m a = slotTag m' a ∧ slotVal m a = slotVal m' a := by
  refine ⟨?_, bytesT8_congr fun i hi => ?_⟩
  · simp only [slotTag, bytesT1, tvalueTagOff, h 8 (by omega)]
  · simp only [tvalueValOff, Nat.add_zero]; exact h i (by omega)

theorem getElem_writeMap8 (m : Mem) (a : Nat) (d : BitVec (8 * 8)) (j : Nat) (hj : j < 8) :
    (writeMap8 m a d)[a + j]? = some (d.extractLsb' (8 * j) 8) := by
  match j, hj with
  | 0, _ => exact getElem_writeMap8_0 m a d
  | 1, _ => exact getElem_writeMap8_1 m a d
  | 2, _ => exact getElem_writeMap8_2 m a d
  | 3, _ => exact getElem_writeMap8_3 m a d
  | 4, _ => exact getElem_writeMap8_4 m a d
  | 5, _ => exact getElem_writeMap8_5 m a d
  | 6, _ => exact getElem_writeMap8_6 m a d
  | 7, _ => exact getElem_writeMap8_7 m a d

theorem bytesT8_writeMap8 (m : Mem) (a : Nat) (d : BitVec (8 * 8)) :
    bytesT8 (writeMap8 m a d) a = d := by
  rw [← bytesT_eight_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [getLsbD_bytesT _ 8 a k hk, getElem_writeMap8 m a d (k / 8) (by omega)]
  simp only [Option.getD_some, BitVec.getLsbD_extractLsb']
  have : k % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [this, decide_true, Bool.true_and]
  congr 1
  omega

theorem bytesT1_writeMap8_out (m : Mem) (a : Nat) (d : BitVec (8 * 8)) {x : Nat}
    (h : x < a ∨ a + 8 ≤ x) : bytesT1 (writeMap8 m a d) x = bytesT1 m x := by
  simp only [bytesT1, getElem?_writeMap8_out m a d x h]

/-- What an arm's stores leave in a slot: its store sequence and read-backs. -/
structure SlotStore (m m' : Mem) (a : Nat) (tag : BitVec 8) (val : BitVec 64) : Prop where
  val : bytesT8 m' a = val
  tag : bytesT1 m' (a + 8) = tag
  frame : ∀ x, (x < a ∨ a + 9 ≤ x) → m'[x]? = m[x]?

/-- `sd` then `sb` (`setobj`: the payload, then the tag). -/
theorem store_sd_sb (m : Mem) (A : Nat) (d : BitVec (8 * 8)) (b : BitVec 8) :
    SlotStore m ((writeMap8 m A d).insert (A + 8) b) A b d := by
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · refine (bytesT8_congr fun i hi => ?_).trans (bytesT8_writeMap8 m A d)
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]
  · simp [bytesT1]
  · rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega),
      getElem?_writeMap8_out m A d x (by omega)]

/-- `sb` then `sd` (`setivalue`: the tag, then the payload). -/
theorem store_sb_sd (m : Mem) (A : Nat) (d : BitVec (8 * 8)) (b : BitVec 8) :
    SlotStore m (writeMap8 (m.insert (A + 8) b) A d) A b d := by
  refine ⟨bytesT8_writeMap8 _ A d, ?_, fun x hx => ?_⟩
  · simp only [bytesT1]
    rw [getElem?_writeMap8_out _ A d (A + 8) (by omega)]
    simp
  · rw [getElem?_writeMap8_out _ A d x (by omega), Std.ExtHashMap.getElem?_insert,
      if_neg (by simp only [beq_iff_eq]; omega)]

/-! ## The dispatch table -/

/-- The exact `.rodata` of the Lua ELF is loaded. -/
abbrev RodataLoaded (m : Mem) : Prop :=
  Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte m

/-- Byte `i` of table entry `o`. -/
def jtByte (o i : Nat) : BitVec 8 := Image.rodataByte (Arms.jtBase - Image.rodataBase + 4 * o + i)

/-- Table entry `o`, as `lw` reads it. -/
def jtWord (o : Nat) : BitVec 32 :=
  (((jtByte o 3).append (jtByte o 2)).append (jtByte o 1)).append (jtByte o 0)

/-- **The arm of opcode `o`**: where the dispatch `jr` lands (the entry plus
the table base, bit 0 cleared). -/
def armTarget (o : Nat) : BitVec 64 :=
  BitVec.update ((BitVec.ofNat 64 Arms.jtBase + sign_extend (m := 64) (jtWord o))
    + sign_extend (m := 64) (0x000#12)) 0 0#1

theorem jtWord_eq {m : Mem} (h : RodataLoaded m) {o : Nat} (ho : o < Arms.jtEntries) :
    bytesT4 m (Arms.jtBase + 4 * o) = jtWord o := by
  have hb : ∀ i, i < 4 → m[Arms.jtBase + 4 * o + i]? = some (jtByte o i) := by
    intro i hi
    have := h (Arms.jtBase - Image.rodataBase + 4 * o + i)
      (by simp only [Arms.jtBase, Arms.jtEntries, Image.rodataBase, Image.rodataSize] at ho ⊢; omega)
    rw [show Image.rodataBase + (Arms.jtBase - Image.rodataBase + 4 * o + i)
      = Arms.jtBase + 4 * o + i by simp only [Arms.jtBase, Image.rodataBase]; omega] at this
    exact this
  have h0 := hb 0 (by omega)
  simp only [Nat.add_zero] at h0
  simp only [bytesT4, jtWord, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega),
    Option.getD_some]

/-- Every arm starts on an instruction boundary (the dispatch `jr`'s
alignment side condition). -/
theorem armTarget_aligned : ∀ o, o < Arms.jtEntries → (armTarget o).toNat % 4 = 0 := by
  decide +kernel

/-- No arm starts at the fetch head (so a dispatch takes steps). -/
theorem armTarget_ne_head : ∀ o, o < Arms.jtEntries → armTarget o ≠ Arms.headPc := by
  decide +kernel

/-- `.rodata` lies below the HTIF mailbox. -/
theorem rodata_below_tohost : Image.rodataBase + Image.rodataSize ≤ tohostAddr := by decide

end Lua.Vm.Sim

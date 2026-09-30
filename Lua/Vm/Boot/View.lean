import Lua.Vm.Repr

/-!
# Byte views and cheap kernel checks over them

A boot witness never reduces a memory (`Std.ExtHashMap`). It reduces a
*byte view* `v : Nat → Option (BitVec 8)`: a kernel-computable function
built from packed data (`Lua/Vm/Boot/Image.lean`). `PartialView m v` says
`m` agrees with `v` wherever `v` returns a byte, so every read fact decided
over `v` holds in `m` and in every memory extending `m` (its zero fill).

This is ship-your-interpreter's `ViewOf`/`PartialView`/`readLEv` layer
(`Vsa/Sim/Boot/{View,Store}.lean`), stated for this repository's reads
(`Lua.Vm.rdLE`, `BytesAt`). Each checker below is one `decide +kernel`
per fact over the view, never over a whole memory image.
-/

namespace Lua.Vm

/-- A byte view of memory. -/
abbrev View := Nat → Option (BitVec 8)

/-- `rdLE` over any byte function (`rdLE m = rdLEf (m[·]?)` by `rfl`). -/
def rdLEf (f : View) (a n : Nat) : Option Nat :=
  (List.range n).foldr (fun i acc => do
    let b ← f (a + i)
    let r ← acc
    pure (b.toNat + 256 * r)) (some 0)

theorem rdLE_eq_rdLEf (m : Mem) (a n : Nat) : rdLE m a n = rdLEf (fun k => m[k]?) a n := rfl

/-- `v` agrees with `m` wherever it returns a byte. -/
def PartialView (m : Mem) (v : View) : Prop := ∀ k b, v k = some b → m[k]? = some b

/-- `m` reads exactly as `v`. -/
def ViewOf (m : Mem) (v : View) : Prop := ∀ k, m[k]? = v k

theorem ViewOf.partial {m : Mem} {v : View} (h : ViewOf m v) : PartialView m v :=
  fun k b hk => (h k).trans hk

private theorem foldr_mono {f g : View} (hfg : ∀ k b, f k = some b → g k = some b) (a : Nat) :
    ∀ (l : List Nat) (x : Nat),
      l.foldr (fun i acc => do
        let b ← f (a + i)
        let r ← acc
        pure (b.toNat + 256 * r)) (some 0) = some x →
      l.foldr (fun i acc => do
        let b ← g (a + i)
        let r ← acc
        pure (b.toNat + 256 * r)) (some 0) = some x
  | [], _, h => h
  | i :: l, x, h => by
    simp only [List.foldr_cons] at h ⊢
    cases hb : f (a + i) with
    | none => rw [hb] at h; cases h
    | some b =>
      rw [hb] at h
      cases hr : l.foldr (fun i acc => do
          let b ← f (a + i)
          let r ← acc
          pure (b.toNat + 256 * r)) (some 0) with
      | none => rw [hr] at h; cases h
      | some r =>
        rw [hr] at h
        rw [hfg _ _ hb, foldr_mono hfg a l r hr]
        exact h

/-- A read decided over a partial view holds in the memory. -/
theorem PartialView.rdLE {m : Mem} {v : View} (h : PartialView m v) {a n x : Nat}
    (hr : rdLEf v a n = some x) : Lua.Vm.rdLE m a n = some x :=
  foldr_mono h a _ x hr

theorem PartialView.rd8 {m : Mem} {v : View} (h : PartialView m v) {a x : Nat}
    (hr : rdLEf v a 1 = some x) : Lua.Vm.rd8 m a = some x := h.rdLE hr
theorem PartialView.rd16 {m : Mem} {v : View} (h : PartialView m v) {a x : Nat}
    (hr : rdLEf v a 2 = some x) : Lua.Vm.rd16 m a = some x := h.rdLE hr
theorem PartialView.rd32 {m : Mem} {v : View} (h : PartialView m v) {a x : Nat}
    (hr : rdLEf v a 4 = some x) : Lua.Vm.rd32 m a = some x := h.rdLE hr
theorem PartialView.rd64 {m : Mem} {v : View} (h : PartialView m v) {a x : Nat}
    (hr : rdLEf v a 8 = some x) : Lua.Vm.rd64 m a = some x := h.rdLE hr

theorem PartialView.isSome {m : Mem} {v : View} (h : PartialView m v) {a n : Nat}
    (hr : (rdLEf v a n).isSome = true) : (Lua.Vm.rdLE m a n).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hr
  rw [h.rdLE hx]; rfl

/-! ## Byte ranges -/

/-- `n` zero bytes from `a`. -/
def ZeroAt (m : Mem) (a n : Nat) : Prop := ∀ i, i < n → m[a + i]? = some 0

/-- Byte segments `(base, bytes)`: each holds its bytes (`BytesAt`). -/
def SegsAt (m : Mem) (segs : List (Nat × List UInt8)) : Prop := ∀ s ∈ segs, BytesAt m s.1 s.2

def zeroOk (v : View) (a n : Nat) : Bool := (List.range n).all fun i => v (a + i) == some 0

theorem PartialView.zeroAt {m : Mem} {v : View} (h : PartialView m v) {a n : Nat}
    (hc : zeroOk v a n = true) : ZeroAt m a n := by
  intro i hi
  have := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  exact h _ _ (by simpa using this)

def bytesOk (v : View) (a : Nat) (bs : List UInt8) : Bool :=
  (List.range bs.length).all fun i => v (a + i) == some (BitVec.ofNat 8 (bs.getD i 0).toNat)

theorem PartialView.bytesAt {m : Mem} {v : View} (h : PartialView m v) {a : Nat} {bs : List UInt8}
    (hc : bytesOk v a bs = true) : BytesAt m a bs := by
  intro i hi
  have := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
  have hv : v (a + i) = some (BitVec.ofNat 8 (bs.getD i 0).toNat) := by simpa using this
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hv
  exact h _ _ hv

def segsOk (v : View) (segs : List (Nat × List UInt8)) : Bool :=
  segs.all fun s => bytesOk v s.1 s.2

theorem PartialView.segsAt {m : Mem} {v : View} (h : PartialView m v)
    {segs : List (Nat × List UInt8)} (hc : segsOk v segs = true) : SegsAt m segs :=
  fun s hs => h.bytesAt (List.all_eq_true.mp hc s hs)

/-- Reading a whole segment's word back: a read inside a pinned segment. -/
theorem BytesAt.rdLE {m : Mem} {a : Nat} {bs : List UInt8} (h : BytesAt m a bs) {o n x : Nat}
    (hc : rdLEf (fun k => if a ≤ k ∧ k < a + bs.length then
        some (BitVec.ofNat 8 (bs.getD (k - a) 0).toNat) else none) (a + o) n = some x) :
    Lua.Vm.rdLE m (a + o) n = some x := by
  refine PartialView.rdLE (v := fun k => if a ≤ k ∧ k < a + bs.length then
      some (BitVec.ofNat 8 (bs.getD (k - a) 0).toNat) else none) ?_ hc
  intro k b hk
  simp only at hk
  split at hk
  · rename_i hr
    have hi : k - a < bs.length := by omega
    have := h (k - a) hi
    rw [show a + (k - a) = k by omega] at this
    rw [this, ← hk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  · cases hk

end Lua.Vm

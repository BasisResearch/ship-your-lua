import Lua.Vm.DlHeap
import Lua.Vm.Boot.View

/-!
# The dlmalloc heap shape from a byte view

`heapCheck` decides every field of `DlHeap.HeapAt` over a partial byte view:
the chunk walk from `_end` to the top chunk and the bin lists (one list per
bin). `heapAt_of_check` turns a passing check into `HeapAt`. Ported from
ship-your-interpreter's `Vsa/Sim/Boot/Heap.lean` without the ledger fields.
-/

namespace Lua.Vm.Boot

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap

abbrev r64 (v : View) (a : Nat) : Option Nat := rdLEf v a 8

/-- The walk from `p` to `top` is `cs`. -/
def walkCheck (v : View) (top : Nat) : Nat → List Chunk → Bool
  | p, [] => p == top
  | p, c :: cs =>
    c.addr == p &&
    (match r64 v (p + 8), r64 v (p + c.size + 8) with
     | some h, some h' =>
       decide (h % 4 < 2) && chunkSize h == c.size && decide (32 ≤ c.size) &&
       c.size % 16 == 0 && prevInuse h' == c.inuse
     | _, _ => false) &&
    walkCheck v top (p + c.size) cs

theorem walkCheck_sound {m : Mem} {v : View} (h : PartialView m v)
    {top : Nat} : ∀ {cs p}, walkCheck v top p cs = true → ChunkWalk m p top cs := by
  intro cs
  induction cs with
  | nil =>
    intro p hc
    simp only [walkCheck, beq_iff_eq] at hc
    subst hc
    exact .top
  | cons c cs ih =>
    intro p hc
    obtain ⟨addr, size, inuse⟩ := c
    simp only [walkCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨rfl, hr⟩, hrest⟩ := hc
    cases h1 : r64 v (addr + 8) with
    | none => rw [h1] at hr; cases hr
    | some hd =>
      cases h2 : r64 v (addr + size + 8) with
      | none => rw [h1, h2] at hr; cases hr
      | some hd' =>
        rw [h1, h2] at hr
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hr
        obtain ⟨⟨⟨⟨hlow, hsz⟩, hmin⟩, hal⟩, hin⟩ := hr
        subst hsz hin
        exact .chunk (h.rd64 h1) hlow hmin (by omega) (h.rd64 h2) (ih hrest)

/-- Bin `b`'s circular list from `q` (predecessor `prev`) is `qs`. -/
def chainCheck (v : View) (b : Nat) : Nat → Nat → List Nat → Bool
  | q, prev, [] => q == b && r64 v (b + 24) == some prev
  | q, prev, q' :: qs =>
    q' == q && q != b && r64 v (q + 24) == some prev &&
    (match r64 v (q + 16) with
     | some nxt => chainCheck v b nxt q qs
     | none => false)

theorem chainCheck_sound {m : Mem} {v : View} (h : PartialView m v)
    {b : Nat} : ∀ {qs q prev}, chainCheck v b q prev qs = true → BinChain m b q prev qs := by
  intro qs
  induction qs with
  | nil =>
    intro q prev hc
    simp only [chainCheck, Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨rfl, hp⟩ := hc
    exact .close (h.rd64 hp)
  | cons q' qs ih =>
    intro q prev hc
    simp only [chainCheck, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨rfl, hne⟩, hp⟩, hn⟩ := hc
    cases hx : r64 v (q' + 16) with
    | none => rw [hx] at hn; cases hn
    | some nxt =>
      rw [hx] at hn
      exact .link hne (h.rd64 hp) (h.rd64 hx) (ih hn)

/-- Bin `i`'s list. -/
def binList (v : View) (i : Nat) (qs : List Nat) : Bool :=
  r64 v (binAt i + 16) == some (qs.headD (binAt i)) &&
  chainCheck v (binAt i) (qs.headD (binAt i)) (binAt i) qs

theorem binList_sound {m : Mem} {v : View} (h : PartialView m v)
    {i : Nat} {qs : List Nat} (hc : binList v i qs = true) : BinList m i qs := by
  simp only [binList, Bool.and_eq_true, beq_iff_eq] at hc
  exact ⟨h.rd64 hc.1, chainCheck_sound h hc.2⟩

/-- Bin lists, one per bin index (missing indices are empty). -/
def binsOf (L : List (List Nat)) (i : Nat) : List Nat := L.getD i []

/-- Consecutive chunks are never both free. -/
def coalescedCheck : List Chunk → Bool
  | c :: d :: cs => (c.inuse || d.inuse) && coalescedCheck (d :: cs)
  | _ => true

theorem coalescedCheck_sound : ∀ {cs : List Chunk}, coalescedCheck cs = true →
    ∀ i (hi : i + 1 < cs.length), cs[i].inuse = true ∨ cs[i + 1].inuse = true := by
  intro cs
  induction cs with
  | nil => intro _ i hi; simp at hi
  | cons c cs ih =>
    intro hc i hi
    cases cs with
    | nil => simp at hi
    | cons d cs =>
      simp only [coalescedCheck, Bool.and_eq_true, Bool.or_eq_true] at hc
      cases i with
      | zero => simpa using hc.1
      | succ i =>
        have := ih hc.2 i (by simp at hi ⊢; omega)
        simpa using this

/-- The bin indices `1 … 127`. -/
def binIdxs : List Nat := (List.range 127).map (· + 1)

theorem mem_binIdxs {i : Nat} (h0 : 0 < i) (h1 : i < numBins) : i ∈ binIdxs := by
  unfold binIdxs numBins at *
  simp only [List.mem_map, List.mem_range]
  exact ⟨i - 1, by omega, by omega⟩

/-- Every field of `HeapAt` over the view. -/
def heapCheck (v : View) (top brkv : Nat) (chunks : List Chunk) (L : List (List Nat)) : Bool :=
  r64 v symMallocSbrkBase == some heapStart &&
  r64 v symBrk == some brkv &&
  decide (brkv ≤ heapEnd) &&
  r64 v topAddr == some top &&
  decide (top ≤ brkv) &&
  (brkv - top) % 16 == 0 &&
  r64 v (top + 8) == some (brkv - top + 1) &&
  r64 v symMallocTopPad == some 0 &&
  (r64 v symMallocMaxSbrked).isSome &&
  (r64 v symMallocMallinfo).isSome &&
  (r64 v (heapStart + 8)).any (fun h => h % 2 == 1) &&
  walkCheck v top heapStart chunks &&
  coalescedCheck chunks &&
  chunks.all (fun c => c.inuse || r64 v (c.addr + c.size) == some c.size) &&
  binIdxs.all (fun i => binList v i (binsOf L i)) &&
  L.all (fun l => l.Nodup) &&
  binIdxs.all (fun i => (binsOf L i).all fun q =>
    (chunks.filter fun c => c.addr == q && !c.inuse && (i ≤ 1 || binIndex c.size == i)) != []) &&
  chunks.all (fun c => c.inuse ||
    (((List.range numBins).filter fun i => 0 < i && (binsOf L i).contains c.addr).length == 1)) &&
  decide ((binsOf L 1).length ≤ 1) &&
  (match r64 v binblocksAddr with
   | some bb => binIdxs.all fun i => i ≤ 1 || (binsOf L i).isEmpty || bb / 2 ^ (i / 4) % 2 == 1
   | none => false)

/-- A passing `heapCheck` is the heap shape. -/
theorem heapAt_of_check {m : Mem} {v : View} (h : PartialView m v)
    {top brkv : Nat} {chunks : List Chunk} {L : List (List Nat)}
    (hc : heapCheck v top brkv chunks L = true) :
    HeapAt m top brkv chunks (binsOf L) := by
  simp only [heapCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hsbrk, hbrk⟩, hbrkle⟩, htop⟩, htople⟩, htopsz⟩, htoph⟩,
    hpad⟩, hmax⟩, hmall⟩, hfirst⟩, hwalk⟩, hcoal⟩, hfoot⟩, hbins⟩, hnodup⟩,
    hfree⟩, hbinned⟩, hrem⟩, hbb⟩ := hc
  refine
    { sbrk_base := h.rd64 hsbrk
      brk := h.rd64 hbrk
      brk_le := hbrkle
      top_ptr := h.rd64 htop
      top_le := htople
      top_size := htopsz
      top_header := h.rd64 htoph
      top_pad := h.rd64 hpad
      max_sbrked := h.isSome hmax
      mallinfo := h.isSome hmall
      first_prev := ?_
      walk := walkCheck_sound h hwalk
      coalesced := coalescedCheck_sound hcoal
      footer := ?_
      bins_list := fun i h0 h1 =>
        binList_sound h (List.all_eq_true.mp hbins i (mem_binIdxs h0 h1))
      bins_nodup := ?_
      bin_free := ?_
      free_binned := ?_
      remainder := hrem
      binblocks_present := ?_
      binblocks := ?_ }
  · cases hx : r64 v (heapStart + 8) with
    | none => rw [hx] at hfirst; cases hfirst
    | some x => rw [hx] at hfirst; rw [h.rd64 hx]; exact hfirst
  · intro c hc hfree
    have := List.all_eq_true.mp hfoot c hc
    simp only [hfree, Bool.false_or, beq_iff_eq] at this
    exact h.rd64 this
  · intro i
    unfold binsOf
    rw [List.getD_eq_getElem?_getD]
    cases hi : L[i]? with
    | none => exact List.nodup_nil
    | some l =>
      have := List.all_eq_true.mp hnodup l (List.mem_of_getElem? hi)
      simpa using this
  · intro i q h0 h1 hq
    have := List.all_eq_true.mp (List.all_eq_true.mp hfree i (mem_binIdxs h0 h1)) q hq
    simpa using this
  · intro c hc hfree
    have := List.all_eq_true.mp hbinned c hc
    simp only [hfree, Bool.false_or, beq_iff_eq] at this
    exact this
  · cases hx : r64 v binblocksAddr with
    | none => rw [hx] at hbb; cases hbb
    | some x => rw [h.rd64 hx]; rfl
  · intro bb hbbr i h1 h2 hne
    cases hx : r64 v binblocksAddr with
    | none => rw [hx] at hbb; cases hbb
    | some x =>
      rw [hx] at hbb
      have hxb : x = bb := Option.some.inj ((h.rd64 hx).symm.trans hbbr)
      subst hxb
      have := List.all_eq_true.mp hbb i (mem_binIdxs (by omega) h2)
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.isEmpty_iff, beq_iff_eq] at this
      rcases this with (h' | h') | h'
      · omega
      · exact absurd h' hne
      · exact h'

end Lua.Vm.Boot

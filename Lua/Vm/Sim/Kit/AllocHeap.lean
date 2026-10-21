import Lua.Vm.Sim.Kit.Malloc
import VsaIris.Vsa.HeapRoom

/-!
# The Lua heap shape and the ported dlmalloc proof's (lane F1-A0-M)

`Lua.Vm.DlHeap.HeapAt` (the ledger-free shape the relation carries, decidable
for the boot witness) and the ported proof's `Vsa.Sim.DlHeap.HeapAt` with its
allocation ledger (`VsaIris/Vsa/{HeapShape,HeapRoom}.lean`) are the same
shape at the same addresses:

* `heapV`: a Lua heap is the ported proof's `PHeapAt` with the ledger of every
  chunk in use (`inuseBlocks`), the form `_malloc_r`'s and `_free_r`'s runs
  start from;
* `heapL`: the ported proof's heap is a Lua heap (the form the runs end in).

The chunk lists differ only in their structure's name (`toV`, `toL`).
-/

namespace Lua.Vm.Sim.Kit.AllocHeap

open Lua.Vm Lua.Vm.Layout
open VsaIris.VsaHeap

abbrev LC := Lua.Vm.DlHeap.Chunk
abbrev VC := Vsa.Sim.DlHeap.Chunk

/-! ## Addresses -/

theorem heapStart_eq : Vsa.Sim.DlHeap.heapStart = Lua.Vm.DlHeap.heapStart := rfl
theorem heapEnd_eq : Vsa.Sim.DlHeap.heapEnd = Lua.Vm.DlHeap.heapEnd := rfl
theorem avAddr_eq : Vsa.Sim.DlHeap.avAddr = Lua.Vm.DlHeap.avAddr := rfl
theorem binAt_eq (i : Nat) : Vsa.Sim.DlHeap.binAt i = Lua.Vm.DlHeap.binAt i := rfl
theorem topAddr_eq : Vsa.Sim.DlHeap.topAddr = Lua.Vm.DlHeap.topAddr := rfl
theorem binblocksAddr_eq : Vsa.Sim.DlHeap.binblocksAddr = Lua.Vm.DlHeap.binblocksAddr := rfl
theorem sbrkBase_eq : Vsa.Sim.DlHeap.sbrkBaseAddr = symMallocSbrkBase := rfl
theorem brkAddr_eq : Vsa.Sim.DlHeap.brkAddr = symBrk := rfl
theorem topPad_eq : Vsa.Sim.DlHeap.topPadAddr = symMallocTopPad := rfl
theorem maxSbrked_eq : Vsa.Sim.DlHeap.maxSbrkedAddr = symMallocMaxSbrked := rfl
theorem mallinfo_eq : Vsa.Sim.DlHeap.mallinfoAddr = symMallocMallinfo := rfl
theorem numBins_eq : Vsa.Sim.DlHeap.numBins = Lua.Vm.DlHeap.numBins := rfl
theorem chunkSize_eq (h : Nat) : Vsa.Sim.DlHeap.chunkSize h = Lua.Vm.DlHeap.chunkSize h := rfl
theorem prevInuse_eq (h : Nat) : Vsa.Sim.DlHeap.prevInuse h = Lua.Vm.DlHeap.prevInuse h := rfl
theorem binIndex_eq (s : Nat) : Vsa.Sim.DlHeap.binIndex s = Lua.Vm.DlHeap.binIndex s := rfl

/-- The ported proof's footprint is `MallocGlobal`. -/
theorem allocGlobal_iff (a : Nat) : allocGlobal a ↔ MallocGlobal a := by
  have e1 : symMallocAv = 0x8005c6d0 := rfl
  have e2 : symMallocSbrkBase = 0x8005d388 := rfl
  have e3 : symBrk = 0x8005d3b8 := rfl
  have e4 : errnoAddr = 0x8005d408 := rfl
  have e5 : symMallocMallinfo = 0x8005e560 := rfl
  unfold allocGlobal InRange MallocGlobal
  rw [e1, e2, e3, e4, e5]
  constructor <;> intro h <;> omega

/-- The reads agree. -/
theorem rd64_eq (m : Mem) (a : Nat) : rd64 m a = Vsa.MemRepr.read64 m a := by
  simp only [rd64, rdLE, Vsa.MemRepr.read64, Vsa.MemRepr.readLE, List.range_succ, List.range_zero,
    List.nil_append, List.cons_append, List.foldr_cons, List.foldr_nil, Nat.add_zero, Nat.add_assoc,
    Nat.reduceAdd]

/-! ## Chunks -/

def toV (c : LC) : VC := ⟨c.addr, c.size, c.inuse⟩
def toL (c : VC) : LC := ⟨c.addr, c.size, c.inuse⟩

@[simp] theorem toL_toV (c : LC) : toL (toV c) = c := rfl
@[simp] theorem toV_toL (c : VC) : toV (toL c) = c := rfl
@[simp] theorem map_toL_toV (cs : List LC) : (cs.map toV).map toL = cs := by
  simp [List.map_map, Function.comp_def]
@[simp] theorem map_toV_toL (cs : List VC) : (cs.map toL).map toV = cs := by
  simp [List.map_map, Function.comp_def]

theorem mem_map_toV {cs : List LC} {c : VC} : c ∈ cs.map toV ↔ toL c ∈ cs := by
  constructor
  · intro h; obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h; simpa using hd
  · intro h; exact List.mem_map.2 ⟨toL c, h, rfl⟩

theorem mem_map_toL {cs : List VC} {c : LC} : c ∈ cs.map toL ↔ toV c ∈ cs := by
  constructor
  · intro h; obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h; simpa using hd
  · intro h; exact List.mem_map.2 ⟨toV c, h, rfl⟩

/-! ## The walk and the bins -/

theorem walkV {m : Mem} : ∀ {p top : Nat} {cs : List LC},
    Lua.Vm.DlHeap.ChunkWalk m p top cs → Vsa.Sim.DlHeap.ChunkWalk m p top (cs.map toV)
  | _, _, _, .top => .top
  | _, _, _, .chunk h1 h2 h3 h4 h5 rest => .chunk h1 h2 h3 h4 h5 (walkV rest)

theorem walkL {m : Mem} : ∀ {p top : Nat} {cs : List VC},
    Vsa.Sim.DlHeap.ChunkWalk m p top cs → Lua.Vm.DlHeap.ChunkWalk m p top (cs.map toL)
  | _, _, _, .top => .top
  | _, _, _, .chunk h1 h2 h3 h4 h5 rest => .chunk h1 h2 h3 h4 h5 (walkL rest)

theorem chainV {m : Mem} {b : Nat} : ∀ {q prev : Nat} {qs : List Nat},
    Lua.Vm.DlHeap.BinChain m b q prev qs → Vsa.Sim.DlHeap.BinChain m b q prev qs
  | _, _, _, .close h => .close h
  | _, _, _, .link h1 h2 h3 rest => .link h1 h2 h3 (chainV rest)

theorem chainL {m : Mem} {b : Nat} : ∀ {q prev : Nat} {qs : List Nat},
    Vsa.Sim.DlHeap.BinChain m b q prev qs → Lua.Vm.DlHeap.BinChain m b q prev qs
  | _, _, _, .close h => .close h
  | _, _, _, .link h1 h2 h3 rest => .link h1 h2 h3 (chainL rest)

/-- A chain starts at its first element, or at the bin when empty. -/
theorem chain_head {m : Mem} {b : Nat} : ∀ {q prev : Nat} {qs : List Nat},
    Vsa.Sim.DlHeap.BinChain m b q prev qs → q = qs.headD b
  | _, _, _, .close _ => rfl
  | _, _, _, .link _ _ _ _ => rfl

/-! ## Counting the bins a chunk is on -/

/-- In a duplicate-free list, a filter of length one is a unique witness. -/
theorem filter_one_iff {l : List Nat} (hl : l.Nodup) (P : Nat → Bool) :
    (l.filter P).length = 1 ↔ ∃ i ∈ l, P i = true ∧ ∀ j ∈ l, P j = true → j = i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := List.length_eq_one_iff.1 h
    have hm : i ∈ l.filter P := by rw [hi]; exact List.mem_singleton_self i
    obtain ⟨hil, hip⟩ := List.mem_filter.1 hm
    refine ⟨i, hil, hip, fun j hj hpj => ?_⟩
    have : j ∈ l.filter P := List.mem_filter.2 ⟨hj, hpj⟩
    rw [hi] at this; simpa using this
  · rintro ⟨i, hil, hip, huniq⟩
    have hnd : (l.filter P).Nodup := hl.filter P
    have hall : ∀ x ∈ l.filter P, x = i := fun x hx => by
      obtain ⟨h1, h2⟩ := List.mem_filter.1 hx; exact huniq x h1 h2
    have hin : i ∈ l.filter P := List.mem_filter.2 ⟨hil, hip⟩
    generalize hL : l.filter P = L at hnd hall hin
    match L, hnd, hall, hin with
    | [], _, _, hin => cases hin
    | [_], _, _, _ => rfl
    | x :: y :: _, hnd, hall, _ =>
      have hx := hall x (by simp); have hy := hall y (by simp)
      exact absurd (hx.trans hy.symm) (by simp at hnd; exact hnd.1.1)

/-! ## A Lua heap is the ported proof's heap -/

/-- **`heapV`**: a Lua heap, with the ledger of the chunks in use. -/
theorem heapV {m : Mem} {top brk : Nat} {cs : List LC} {bins : Nat → List Nat}
    (h : Lua.Vm.DlHeap.HeapAt m top brk cs bins) :
    PHeapAt m (inuseBlocks (cs.map toV)) top brk (cs.map toV) bins := by
  have H : Vsa.Sim.DlHeap.HeapAt m [] (fun _ => False) top brk (cs.map toV) bins :=
    { sbrk_base := h.sbrk_base
      brk := h.brk
      brk_le := h.brk_le
      top_ptr := h.top_ptr
      top_le := h.top_le
      top_size := h.top_size
      top_header := h.top_header
      top_pad := h.top_pad
      max_sbrked := h.max_sbrked
      mallinfo := h.mallinfo
      first_prev := h.first_prev
      walk := walkV h.walk
      coalesced := fun i hi => by
        have hi' : i + 1 < cs.length := by simpa using hi
        simpa [toV] using h.coalesced i hi'
      footer := fun c hc hf => by
        have := h.footer (toL c) (mem_map_toV.1 hc) hf
        simpa [toL, rd64_eq] using this
      bins_list := fun i h0 h1 => ⟨_, (h.bins_list i h0 h1).fd, chainV (h.bins_list i h0 h1).chain⟩
      bins_nodup := h.bins_nodup
      bin_free := fun i q h0 h1 hq => by
        have hne := h.bin_free i q h0 h1 hq
        obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
        obtain ⟨hcm, hcp⟩ := List.mem_filter.1 hc
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
          decide_eq_true_eq] at hcp
        refine ⟨toV c, List.mem_map_of_mem hcm, hcp.1.1, hcp.1.2, fun hi => ?_⟩
        rcases hcp.2 with h' | h'
        · omega
        · exact h'
      free_binned := fun c hc hf => by
        have := h.free_binned (toL c) (mem_map_toV.1 hc) hf
        obtain ⟨i, hi, hip, huniq⟩ := (filter_one_iff List.nodup_range _).1 this
        simp only [List.mem_range, Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hi hip
        refine ⟨i, hip.1, hi, by simpa [toL] using hip.2, fun j hj0 hj1 hjm => huniq j
          (List.mem_range.2 hj1) ?_⟩
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
        exact ⟨hj0, by simpa [toL] using hjm⟩
      remainder := h.remainder
      binblocks_present := h.binblocks_present
      binblocks := h.binblocks
      live := fun e he => by cases he
      exact := fun e he => by cases he }
  exact ⟨(blockHeapAt_of_heapAt H h.top_room).1, h.brk_page, h.bb_lt⟩

/-! ## The ported proof's heap is a Lua heap -/

/-- **`heapL`**: the ported proof's heap (any ledger) is a Lua heap. -/
theorem heapL {m : Mem} {H : List (Nat × Nat)} {top brk : Nat} {cs : List VC}
    {bins : Nat → List Nat} (h : PHeapAt m H top brk cs bins) :
    Lua.Vm.DlHeap.HeapAt m top brk (cs.map toL) bins := by
  have HH := h.heap.heap
  exact
    { sbrk_base := HH.sbrk_base
      brk := HH.brk
      brk_le := HH.brk_le
      top_ptr := HH.top_ptr
      top_le := HH.top_le
      top_size := HH.top_size
      top_header := HH.top_header
      top_pad := HH.top_pad
      max_sbrked := HH.max_sbrked
      mallinfo := HH.mallinfo
      first_prev := HH.first_prev
      walk := walkL HH.walk
      coalesced := fun i hi => by
        have hi' : i + 1 < cs.length := by simpa using hi
        simpa [toL] using HH.coalesced i hi'
      footer := fun c hc hf => by
        have := HH.footer (toV c) (mem_map_toL.1 hc) hf
        simpa [toV, rd64_eq] using this
      bins_list := fun i h0 h1 => by
        obtain ⟨first, hf, hc⟩ := HH.bins_list i h0 h1
        have e := chain_head hc
        subst e
        exact ⟨hf, chainL hc⟩
      bins_nodup := HH.bins_nodup
      bin_free := fun i q h0 h1 hq => by
        obtain ⟨c, hc, hca, hcf, hci⟩ := HH.bin_free i q h0 h1 hq
        refine List.ne_nil_of_mem (a := toL c) (List.mem_filter.2 ⟨mem_map_toL.2 (by simpa using hc), ?_⟩)
        simp only [toL, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.or_eq_true,
          decide_eq_true_eq]
        refine ⟨⟨hca, hcf⟩, ?_⟩
        by_cases hi : i ≤ 1
        · exact .inl hi
        · exact .inr (hci (by omega))
      free_binned := fun c hc hf => by
        obtain ⟨i, hi0, hi1, him, huniq⟩ := HH.free_binned (toV c) (mem_map_toL.1 hc) hf
        refine (filter_one_iff List.nodup_range _).2 ⟨i, List.mem_range.2 hi1, ?_, fun j hj hjp => ?_⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem]
          exact ⟨hi0, by simpa [toV] using him⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq, List.contains_iff_mem] at hjp
          exact huniq j hjp.1 (List.mem_range.1 hj) (by simpa [toV] using hjp.2)
      remainder := HH.remainder
      binblocks_present := HH.binblocks_present
      binblocks := HH.binblocks
      brk_page := h.brk_page
      top_room := h.heap.top_room
      bb_lt := h.bb_lt }

/-! ## The ledger of the chunks in use -/

/-- A byte of a chunk in use is a byte of the ledger. -/
theorem inUse_iff {cs : List LC} {a : Nat} :
    InUse cs a ↔ ∃ e ∈ inuseBlocks (cs.map toV), VsaIris.InExt e a := by
  constructor
  · rintro ⟨c, hc, hu, h1, h2⟩
    refine ⟨(c.addr + 16, c.size - 8), mem_inuseBlocks.2 ⟨toV c, List.mem_map_of_mem hc, hu, rfl⟩, ?_⟩
    unfold VsaIris.InExt; simp only; omega
  · rintro ⟨e, he, hin⟩
    obtain ⟨c, hc, hu, rfl⟩ := mem_inuseBlocks.1 he
    refine ⟨toL c, mem_map_toV.1 hc, hu, ?_, ?_⟩ <;> unfold VsaIris.InExt at hin <;> simp only [toL] at * <;>
      omega

/-- The ledger used for free is exactly the entry's surviving live payloads. -/
theorem freeSurvivors_ledger (cs : List LC) (p : Nat) :
    inuseBlocks ((freeSurvivors cs p).map toV) =
      (inuseBlocks (cs.map toV)).filter (fun e => e.1 != p) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [freeSurvivors, inuseBlocks, List.filterMap_map] at ih
    by_cases hp : c.addr + 16 = p <;> cases hu : c.inuse <;>
      simp [freeSurvivors, inuseBlocks, toV, hp, hu, ih]

/-- A retained ledger entry still has its original base and capacity.
The resulting physical chunk may have greater capacity; callers retain the
entry allocation, without needing an equality of chunk lists. -/
theorem live_of_ledger {m : Mem} {cs : List LC} {H : List (Nat × Nat)}
    {cs' : List VC} {top' brk' : Nat} {bins' : Nat → List Nat}
    (hH : ∀ c ∈ cs, c.inuse = true → (c.addr + 16, c.size - 8) ∈ H)
    (hh' : PHeapAt m H top' brk' cs' bins') :
    ∀ c ∈ cs, c.inuse = true → ∃ sz, (⟨c.addr, sz, true⟩ : LC) ∈ cs'.map toL ∧ c.size ≤ sz := by
  intro c hc hu
  obtain ⟨d, hd, hdu, hda, hds⟩ := hh'.heap.heap.exact _ (hH c hc hu) (hH c hc hu)
  refine ⟨d.size, mem_map_toL.2 ?_, ?_⟩
  · have he : toV (⟨c.addr, d.size, true⟩ : LC) = d := by
      obtain ⟨a, sz, u⟩ := d
      simp only at hdu hda
      subst u
      simp only [toV]
      congr <;> omega
    rwa [he]
  · omega

end Lua.Vm.Sim.Kit.AllocHeap

import Lua.Vm.Sim.Kit.AtFn
import Lua.Vm.Sim.Kit.Malloc
import Lua.Vm.Sim.Kit.Str

/-!
# Memory agreement off a region, and the heap across it (lane F1-10)

A callee's summary says what it writes as a *region*: every byte off it
reads as before (`Agree R m m'`). Regions compose by union along a run
(`Agree.trans`), so a caller's summary is the union of its callees'
regions and its own stores, never a hand frame per call.

`HeapAt` reads only the arena and the allocator's globals (`HeapReads`), so
it survives every run whose region misses them (`HeapAt.congr`): the stdio
set-up, the frames, `errno`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap

/-! ## Agreement off a region -/

/-- `m'` reads as `m` off the region `R`. -/
def Agree (R : Nat → Prop) (m m' : Mem) : Prop := ∀ a, ¬ R a → m'[a]? = m[a]?

theorem Agree.refl (R : Nat → Prop) (m : Mem) : Agree R m m := fun _ _ => rfl

theorem Agree.trans {R S : Nat → Prop} {m m1 m2 : Mem} (h1 : Agree R m m1) (h2 : Agree S m1 m2) :
    Agree (fun a => R a ∨ S a) m m2 :=
  fun a ha => (h2 a fun h => ha (.inr h)).trans (h1 a fun h => ha (.inl h))

theorem Agree.mono {R S : Nat → Prop} {m m' : Mem} (h : Agree R m m') (hRS : ∀ a, R a → S a) :
    Agree S m m' := fun a ha => h a fun h => ha (hRS a h)

/-- An agreement read at one byte. -/
theorem Agree.get {R : Nat → Prop} {m m' : Mem} (h : Agree R m m') {a : Nat} (ha : ¬ R a) :
    m'[a]? = m[a]? := h a ha

/-- Reads off the region, unchanged. -/
theorem Agree.b8 {R : Nat → Prop} {m m' : Mem} (h : Agree R m m') {a : Nat} (hn : ∀ i, i < 8 → ¬ R (a + i)) :
    bytesT8 m' a = bytesT8 m a := Lua.Vm.Sim.AtF.bT8_congr fun i hi => h _ (hn i hi)
theorem Agree.b4 {R : Nat → Prop} {m m' : Mem} (h : Agree R m m') {a : Nat} (hn : ∀ i, i < 4 → ¬ R (a + i)) :
    bytesT4 m' a = bytesT4 m a := Lua.Vm.Sim.AtF.bT4_congr fun i hi => h _ (hn i hi)
theorem Agree.b2 {R : Nat → Prop} {m m' : Mem} (h : Agree R m m') {a : Nat} (hn : ∀ i, i < 2 → ¬ R (a + i)) :
    bytesT2 m' a = bytesT2 m a := Lua.Vm.Sim.AtF.bT2_congr fun i hi => h _ (hn i hi)

/-- The `d` bytes below `sp` (a callee's frames). -/
def Below (sp d a : Nat) : Prop := a < sp ∧ sp ≤ a + d

/-- The fields of `stdout` the set-up writes: `_p`, `_w`, `_flags`,
`_bf`, `_lbfsize` (not `_file`, the cookie or the hooks). -/
def StdoutW (a : Nat) : Prop :=
  Rng stdoutFile 8 a ∨ Rng (stdoutFile + 12) 6 a ∨ Rng (stdoutFile + 24) 12 a ∨ Rng (stdoutFile + 40) 4 a

/-- What `_malloc_r` writes besides its frames: its globals and the arena
off the chunks in use. -/
def MallocW (chunks : List Chunk) (a : Nat) : Prop :=
  MallocGlobal a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ¬ InUse chunks a)

/-- The arena `[_end, __heap_end)`. -/
def Arena (a : Nat) : Prop := heapStart ≤ a ∧ a < heapEnd

/-- `MallocW` without the chunks in use (for reads off the heap). -/
theorem MallocW.coarse {chunks : List Chunk} {a : Nat} (h : MallocW chunks a) : MallocGlobal a ∨ Arena a := by
  rcases h with h | ⟨h1, h2, _⟩
  · exact .inl h
  · exact .inr ⟨h1, h2⟩

theorem MallocPost.agree {m m' : Mem} {sp n p brk top' brk' : Nat} {chunks chunks' : List Chunk}
    {bins' : Nat → List Nat} (h : MallocPost m m' sp n p brk chunks top' brk' chunks' bins') :
    Agree (fun a => MallocW chunks a ∨ Below sp 1024 a) m m' := by
  intro a ha
  simp only [MallocW, Below, not_or, not_and] at ha
  obtain ⟨⟨hg, hh⟩, hb⟩ := ha
  refine h.keep a hg ?_ (by omega)
  by_cases h1 : heapStart ≤ a
  · by_cases h2 : a < heapEnd
    · exact .inr (.inr (Classical.byContradiction fun hn => hh h1 h2 hn))
    · exact .inr (.inl (by omega))
  · exact .inl (by omega)

/-- A presence-level agreement is one of the zero fills (`Vsa.Densify.fillZeroMem`):
the heap is stated of the fill (`MallocR_Statement`), as the machine reads totally. -/
theorem fill_congr {m m' : Mem} {a : Nat} (h : m'[a]? = m[a]?) :
    (Vsa.Densify.fillZeroMem m')[a]? = (Vsa.Densify.fillZeroMem m)[a]? := by
  simp only [Vsa.Densify.fillZeroMem_get, h]

/-- The fill reads totally as the memory (a complement for `Core.frame`). -/
theorem bytesT1_fill (m : Mem) (a : Nat) : bytesT1 (Vsa.Densify.fillZeroMem m) a = bytesT1 m a := by
  simp only [bytesT1, Vsa.Densify.fillZeroMem_get]
  split <;> simp

/-- Total reads of the fill are the memory's: a presence-level fact stated
of the fill (`StdioBoot`, `MemfsBoot`, `ZeroAt`) gives the machine's reads. -/
theorem bT8_of_fill {m : Mem} {a : Nat} {v : BitVec 64} (h : bytesT8 (Vsa.Densify.fillZeroMem m) a = v) :
    bytesT8 m a = v := (bytesT8_congrT fun i _ => (bytesT1_fill m _).symm).trans h
theorem bT4_of_fill {m : Mem} {a : Nat} {v : BitVec 32} (h : bytesT4 (Vsa.Densify.fillZeroMem m) a = v) :
    bytesT4 m a = v := (bytesT4_congrT fun i _ => (bytesT1_fill m _).symm).trans h

/-! ## What `HeapAt` reads -/

/-- The bytes `HeapAt` reads: the arena (and a header's width past its end),
`__malloc_av_`, `__malloc_sbrk_base`, `brk.0`, `__malloc_top_pad`,
`__malloc_max_sbrked_mem`, `__malloc_current_mallinfo`. -/
def HeapReads (a : Nat) : Prop :=
  (heapStart ≤ a ∧ a < heapEnd + 32) ∨ (symMallocAv ≤ a ∧ a < symMallocAv + 0x810) ∨
  (symMallocSbrkBase ≤ a ∧ a < symMallocSbrkBase + 8) ∨ (symBrk ≤ a ∧ a < symBrk + 8) ∨
  (symMallocTopPad ≤ a ∧ a < symMallocTopPad + 8) ∨
  (symMallocMaxSbrked ≤ a ∧ a < symMallocMaxSbrked + 8) ∨
  (symMallocMallinfo ≤ a ∧ a < symMallocMallinfo + 0x50)

theorem rd64_congr {m m' : Mem} {a : Nat} (h : ∀ i, i < 8 → m'[a + i]? = m[a + i]?) :
    rd64 m' a = rd64 m a := rdLE_congr h

theorem ChunkWalk.congr {m m' : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs →
      (∀ a, p ≤ a → a < top + 16 → m'[a]? = m[a]?) → ChunkWalk m' p top cs
  | _, _, _, .top, _ => .top
  | p, top, _, .chunk (h := hd) (h' := hd') e1 e2 e3 e4 e5 hw, hk => by
    have hle := ChunkWalk.le hw
    have hs := e3
    refine .chunk ((rd64_congr fun i _ => hk _ (by omega) (by omega)).trans e1) e2 e3 e4
      ((rd64_congr fun i _ => hk _ (by omega) (by omega)).trans e5)
      (ChunkWalk.congr hw fun a h1 h2 => hk a (by omega) h2)

theorem BinChain.congr {m m' : Mem} {b : Nat} :
    ∀ {q prev : Nat} {qs : List Nat}, BinChain m b q prev qs →
      (∀ a, b + 16 ≤ a → a < b + 32 → m'[a]? = m[a]?) →
      (∀ x ∈ qs, ∀ a, x + 16 ≤ a → a < x + 32 → m'[a]? = m[a]?) → BinChain m' b q prev qs
  | _, _, _, .close e, hb, _ => .close ((rd64_congr fun i _ => hb _ (by omega) (by omega)).trans e)
  | _, _, _, .link (q := q) ne e1 e2 hc, hb, hq =>
    .link ne ((rd64_congr fun i _ => hq q List.mem_cons_self _ (by omega) (by omega)).trans e1)
      ((rd64_congr fun i _ => hq q List.mem_cons_self _ (by omega) (by omega)).trans e2)
      (BinChain.congr hc hb fun x hx => hq x (List.mem_cons_of_mem _ hx))

/-- A binned chunk lies in the walk, so in the arena. -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.binned {m : Mem} {top brk : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m top brk chunks bins) {i q : Nat} (h0 : 0 < i) (h1 : i < numBins) (hq : q ∈ bins i) :
    heapStart ≤ q ∧ q ≤ top := by
  have hf := h.bin_free i q h0 h1 hq
  obtain ⟨c, hc, hp⟩ : ∃ c ∈ chunks, (c.addr == q && !c.inuse && (i ≤ 1 || binIndex c.size == i)) = true := by
    refine Classical.byContradiction fun hn => hf (List.filter_eq_nil_iff.mpr fun c hc hp => hn ⟨c, hc, hp⟩)
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  have := ChunkWalk.bound h.walk c hc
  have : heapStart = heapStart := rfl
  obtain ⟨⟨e, _⟩, _⟩ := hp
  subst e
  omega

/-- **The heap across a run that misses what it reads.** -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.congr {m m' : Mem} {top brk : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (h : HeapAt m top brk chunks bins) (hk : ∀ a, HeapReads a → m'[a]? = m[a]?) :
    HeapAt m' top brk chunks bins := by
  have e0 : heapStart = symEnd := rfl
  have e1 : heapEnd = symHeapEnd := rfl
  have e2 : symEnd = 0x8006ecd0 := rfl
  have e3 : symHeapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e10 : topAddr = avAddr + 16 := rfl
  have e11 : avAddr = symMallocAv := rfl
  have e12 : binblocksAddr = avAddr + 8 := rfl
  have htop := ChunkWalk.le h.walk
  have hbrk := h.brk_le
  have htb := h.top_le
  have arena : ∀ a, heapStart ≤ a → a < heapEnd + 32 → m'[a]? = m[a]? := fun a h1 h2 =>
    hk a (.inl ⟨h1, h2⟩)
  have av : ∀ a, symMallocAv ≤ a → a < symMallocAv + 0x810 → m'[a]? = m[a]? := fun a h1 h2 =>
    hk a (.inr (.inl ⟨h1, h2⟩))
  refine
    { sbrk_base := (rd64_congr fun i _ => hk _ (.inr (.inr (.inl ⟨by omega, by omega⟩)))).trans h.sbrk_base
      brk := (rd64_congr fun i _ => hk _ (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))).trans h.brk
      brk_le := h.brk_le
      top_ptr := (rd64_congr fun i _ => av _ (by omega) (by omega)).trans h.top_ptr
      top_le := h.top_le
      top_size := h.top_size
      top_header := (rd64_congr fun i _ => arena _ (by omega) (by omega)).trans h.top_header
      top_pad := (rd64_congr fun i _ =>
        hk _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))).trans h.top_pad
      max_sbrked := by
        rw [rd64_congr fun i _ => hk _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))))]
        exact h.max_sbrked
      mallinfo := by
        rw [rd64_congr fun i _ => hk _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩))))))]
        exact h.mallinfo
      first_prev := by
        rw [rd64_congr fun i _ => arena _ (by omega) (by omega)]
        exact h.first_prev
      walk := ChunkWalk.congr h.walk fun a h1 h2 => arena a h1 (by omega)
      coalesced := h.coalesced
      footer := fun c hc hf => by
        have := ChunkWalk.bound h.walk c hc
        rw [rd64_congr fun i _ => arena _ (by omega) (by omega)]
        exact h.footer c hc hf
      bins_list := fun i h0 h1 => by
        have hb : binAt i + 32 ≤ symMallocAv + 0x810 := by simp only [binAt, avAddr, numBins] at *; omega
        have hb' : symMallocAv ≤ binAt i := by simp only [binAt, avAddr]; omega
        have bl := h.bins_list i h0 h1
        exact ⟨(rd64_congr fun j _ => av _ (by omega) (by omega)).trans bl.fd,
          BinChain.congr bl.chain (fun a h2 h3 => av a (by omega) (by omega)) fun x hx a h2 h3 => by
            have := h.binned h0 h1 hx
            exact arena a (by omega) (by omega)⟩
      bins_nodup := h.bins_nodup
      bin_free := h.bin_free
      free_binned := h.free_binned
      remainder := h.remainder
      binblocks_present := by
        rw [rd64_congr fun i _ => av _ (by omega) (by omega)]
        exact h.binblocks_present
      binblocks := fun bb hb => by
        rw [rd64_congr fun i _ => av _ (by omega) (by omega)] at hb
        exact h.binblocks bb hb }

end Lua.Vm.Sim.Kit

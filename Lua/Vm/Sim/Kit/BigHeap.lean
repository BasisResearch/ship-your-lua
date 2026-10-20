import Lua.Vm.Sim.Kit.PrintSum
import Lua.Vm.EntryData

/-!
# The bignum allocator as a region (lane F1-25)

newlib's `mprec.c` keeps its bignums (`_Bigint`) in `_REENT`: `_Balloc(k)` pops
`_freelist[k]` or calls `_calloc_r` (the free lists' array itself on first use),
`_Bfree` pushes a block back by its `_k`, `_dtoa_r` frees `_result` on entry and
leaves its digits there, `__pow5mult` caches `5^(4·2^j)` on `_p5s`. Every
routine that computes with bignums (`_dtoa_r`, `_strtod_l`'s slow path, their
`__multiply`, `__pow5mult`, `__lshift`, `quorem`, …) therefore changes the heap
only through this one allocator. This file names that effect once:

* `ReentMp B` (`EntryData.lean`, lane F1-19): the bignums and the free lists in
  the region `B`, every block apart; `BigFoot B`: the bytes its facts read;
* `BigW H B F`: **what a bignum computation may write**: the allocator's
  (`MallocW H.chunks`: its globals and every byte of no chunk in use, so every
  block `_calloc_r` hands out), the bignums `B`, `_REENT`'s `_dtoa_r` words
  (`ReentWord`), and the caller's region `F` (the callees' frames, an output
  buffer);
* `BigRun F m m' H H' B B' c`: **a bignum computation's summary**: the heap
  `H'` (the chunks in use kept, the break grown by at most `c`), the bignums
  `B'` again (`ReentMp`, frozen on `BigFoot B'`), within `B` and the blocks
  fresh across `H → H'` (`Fresh`), every byte off `BigW H B F` kept.

`BigRun` composes along a run (`BigRun.trans`: the regions of the later step
lie in the earlier's) and is the identity on a run that allocates nothing
(`BigRun.refl`). A caller holding objects apart from `B` and in chunks in use
keeps them across any `BigRun` (`BigRun.keep_inUse`), and its facts on the
bignums move to `B'` (`BigRun.fresh_or`). Reuse surface: `_dtoa_r` (`%.14g`,
`FloatToStr_Statement`), `_strtod_l`'s bignum path and `__gethex`
(`FpStrFlt_Statement`, lane F9), and the `_Balloc`/`_Bfree` summaries.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- (lane F1-19) **The bytes `_dtoa_r`'s bignums' facts read**: the bignums
`B`, `_REENT`'s words. -/
def BigFoot (B : Nat → Prop) (a : Nat) : Prop := B a ∨ ReentWord a

/-- **A byte fresh across `H → H'`**: in a chunk in use at `H'`, in none at
`H`, in the arena. -/
def Fresh (H H' : HeapIx) (a : Nat) : Prop :=
  InUse H'.chunks a ∧ ¬ InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd

/-- **What a bignum computation may write**: the allocator's bytes
(`MallocW`: its globals and every byte of no chunk in use), the bignums `B`,
`_REENT`'s `_dtoa_r` words, and the caller's region `F`. -/
def BigW (H : HeapIx) (B F : Nat → Prop) (a : Nat) : Prop :=
  MallocW H.chunks a ∨ B a ∨ ReentWord a ∨ F a

/-- **A bignum computation's summary** (`_dtoa_r`, `_strtod_l`, `_Balloc`,
`_Bfree`, …): from `m` with the heap `H` and the bignums `B` to `m'` with
`H'` and `B'`: the heap's walk, the chunks in use kept, at most `c` more break,
the bignums frozen on their footprint, `B'` within `B` and the fresh blocks,
every byte off `BigW H B F` kept. -/
structure BigRun (F : Nat → Prop) (m m' : Mem) (H H' : HeapIx) (B B' : Nat → Prop) (c : Nat) : Prop where
  heap : HeapAt (fillZeroMem m') H'.top H'.brk H'.chunks H'.bins
  kept : ∀ ch ∈ H.chunks, ch.inuse = true → ch ∈ H'.chunks
  brk : H'.brk ≤ H.brk + c
  big : Frozen (BigFoot B') (fun M => ReentMp (fillZeroMem M) B') m'
  sub : ∀ a, B' a → B a ∨ Fresh H H' a
  keep : ∀ a, ¬ BigW H B F a → bytesT1 m' a = bytesT1 m a

/-- The allocator's globals lie below the heap. (Moved from `Kit/TolIntProof.lean`.) -/
theorem MallocGlobal.lt {a : Nat} (h : MallocGlobal a) : a < heapStart := by
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  have : heapStart = 0x8006ecd0 := rfl
  simp only [MallocGlobal] at h; omega

/-- A byte in use stays in use while the chunks in use are kept. -/
theorem InUse.mono {cs cs' : List Chunk} (hk : ∀ c ∈ cs, c.inuse = true → c ∈ cs') {a : Nat}
    (h : InUse cs a) : InUse cs' a := by
  obtain ⟨c, hc, hu, h1, h2⟩ := h
  exact ⟨c, hk c hc hu, hu, h1, h2⟩

/-- **No computation**: the bignums and the heap as they were. -/
theorem BigRun.refl {F : Nat → Prop} {m : Mem} {H : HeapIx} {B : Nat → Prop}
    (hh : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins)
    (hb : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m) : BigRun F m m H H B B 0 :=
  ⟨hh, fun _ h _ => h, by omega, hb, fun _ h => .inl h, fun _ _ => rfl⟩

/-- A byte fresh across a later step was in no chunk in use at the start. -/
theorem Fresh.not_inUse {H H' H'' : HeapIx} (hk : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) {a : Nat}
    (h : Fresh H' H'' a) : ¬ InUse H.chunks a := fun hu => h.2.1 (InUse.mono hk hu)

/-- A fresh byte is the allocator's at the start. -/
theorem Fresh.mallocW {H H' : HeapIx} {a : Nat} (h : Fresh H H' a) : MallocW H.chunks a :=
  .inr ⟨h.2.2.1, h.2.2.2, h.2.1⟩

/-- **`BigRun` along a run**: the later step's regions lie in the earlier's. -/
theorem BigRun.trans {F : Nat → Prop} {m m1 m2 : Mem} {H H1 H2 : HeapIx} {B B1 B2 : Nat → Prop} {c1 c2 : Nat}
    (h1 : BigRun F m m1 H H1 B B1 c1) (h2 : BigRun F m1 m2 H1 H2 B1 B2 c2) :
    BigRun F m m2 H H2 B B2 (c1 + c2) where
  heap := h2.heap
  kept := fun c hc hu => h2.kept c (h1.kept c hc hu) hu
  brk := by have := h1.brk; have := h2.brk; omega
  big := h2.big
  sub := fun a ha => (h2.sub a ha).elim (fun hb => (h1.sub a hb).imp id fun hf =>
      ⟨InUse.mono h2.kept hf.1, hf.2.1, hf.2.2⟩)
    fun hf => .inr ⟨hf.1, hf.not_inUse h1.kept, hf.2.2⟩
  keep := fun a ha => (h2.keep a fun hw => ha (by
      rcases hw with hw | hw | hw | hw
      · exact .inl (MallocW.anti h1.kept hw)
      · exact (h1.sub a hw).elim (fun hb => .inr (.inl hb)) fun hf => .inl hf.mallocW
      · exact .inr (.inr (.inl hw))
      · exact .inr (.inr (.inr hw)))).trans (h1.keep a ha)

/-- A wider caller's region. -/
theorem BigRun.mono {F F' : Nat → Prop} {m m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c c' : Nat}
    (h : BigRun F m m' H H' B B' c) (hF : ∀ a, F a → F' a) (hc : c ≤ c') : BigRun F' m m' H H' B B' c' :=
  ⟨h.heap, h.kept, by have := h.brk; omega, h.big, h.sub, fun a ha => h.keep a fun hw => ha (by
    rcases hw with hw | hw | hw | hw
    · exact .inl hw
    · exact .inr (.inl hw)
    · exact .inr (.inr (.inl hw))
    · exact .inr (.inr (.inr (hF a hw))))⟩

/-- **A byte of a chunk in use, apart from the bignums, `_REENT`'s words and
`F`, is kept.** -/
theorem BigRun.keep_inUse {F : Nat → Prop} {m m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (h : BigRun F m m' H H' B B' c) {a : Nat} (hu : InUse H.chunks a) (hlo : heapStart ≤ a) (hB : ¬ B a)
    (hF : ¬ F a) : bytesT1 m' a = bytesT1 m a := by
  refine h.keep a fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · rcases hw with hg | ⟨-, -, hn⟩
    · exact absurd hlo (Nat.not_le.mpr hg.lt)
    · exact hn hu
  · exact hB hw
  · have : heapStart = 0x8006ecd0 := rfl
    simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hw; omega
  · exact hF hw

/-- **A static byte off the allocator's globals, `_REENT`'s words and `F` is
kept.** -/
theorem BigRun.keep_static {F : Nat → Prop} {m m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (h : BigRun F m m' H H' B B' c) (hBh : ∀ a, B a → heapStart ≤ a) {a : Nat} (hlo : a < heapStart)
    (hm : ¬ MallocGlobal a) (hr : ¬ ReentWord a) (hF : ¬ F a) : bytesT1 m' a = bytesT1 m a := by
  refine h.keep a fun hw => ?_
  rcases hw with hw | hw | hw | hw
  · rcases hw with hg | ⟨h1, -, -⟩
    · exact hm hg
    · omega
  · have := hBh a hw; omega
  · exact hr hw
  · exact hF hw

/-- A new bignum byte was a bignum or fresh. -/
theorem BigRun.fresh_or {F : Nat → Prop} {m m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (h : BigRun F m m' H H' B B' c) {a : Nat} (ha : B' a) : B a ∨ Fresh H H' a := h.sub a ha

/-- **A new bignum byte apart from what the caller holds**: a byte the caller
holds in a chunk in use (or below the heap) and apart from `B` is no `B'` byte. -/
theorem BigRun.apart {F : Nat → Prop} {m m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (h : BigRun F m m' H H' B B' c) {a : Nat} (hx : InUse H.chunks a ∨ a < heapStart) (hB : ¬ B a) : ¬ B' a :=
  fun hb => (h.sub a hb).elim hB fun hf => hx.elim hf.2.1 fun hl => absurd hf.2.2.1 (Nat.not_le.mpr hl)

/-- What the heap's walk reads lies below the stack. -/
theorem HeapReads.lt {a : Nat} (h : HeapReads a) : a < heapEnd + 32 := by
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  simp only [HeapReads] at h
  omega

/-- **A run that stores only in the stack `F` is a bignum computation** that
allocates nothing. -/
theorem BigRun.ofFrame {F : Nat → Prop} {m m' : Mem} {H : HeapIx} {B : Nat → Prop}
    (hh : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins)
    (hb : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m) (hBh : ∀ a, B a → a < heapEnd)
    (hF : ∀ a, F a → heapEnd + 32 ≤ a) (hk : ∀ a, ¬ F a → bytesT1 m' a = bytesT1 m a) :
    BigRun F m m' H H B B 0 where
  heap := hh.ofTotal fun a hr _ => (hk a fun hf => absurd (hF a hf) (Nat.not_le.mpr hr.lt)).trans
    (bytesT1_fill m a).symm
  kept := fun _ h _ => h
  brk := by omega
  big := hb.trans fun a ha => hk a fun hf => by
    have := hF a hf
    rcases ha with hb' | hr
    · have := hBh a hb'; omega
    · have : heapEnd = 0x87800000 := rfl
      simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr; omega
  sub := fun _ h => .inl h
  keep := fun a ha => hk a fun hf => ha (.inr (.inr (.inr hf)))

/-- **Stack stores before a bignum computation.** -/
theorem BigRun.frame_before {F : Nat → Prop} {m m0 m' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (hh : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins)
    (hb : Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) m) (hBh : ∀ a, B a → a < heapEnd)
    (hF : ∀ a, F a → heapEnd + 32 ≤ a) (hk : ∀ a, ¬ F a → bytesT1 m0 a = bytesT1 m a)
    (h : BigRun F m0 m' H H' B B' c) : BigRun F m m' H H' B B' c := by
  have := (BigRun.ofFrame hh hb hBh hF hk).trans h
  rwa [Nat.zero_add] at this

/-- **Stack stores after a bignum computation.** -/
theorem BigRun.frame_after {F : Nat → Prop} {m m' m'' : Mem} {H H' : HeapIx} {B B' : Nat → Prop} {c : Nat}
    (h : BigRun F m m' H H' B B' c) (hBh : ∀ a, B a → a < heapEnd) (hF : ∀ a, F a → heapEnd + 32 ≤ a)
    (hk : ∀ a, ¬ F a → bytesT1 m'' a = bytesT1 m' a) : BigRun F m m'' H H' B B' c :=
  h.trans (BigRun.ofFrame h.heap h.big (fun a ha => (h.sub a ha).elim (hBh a) fun hf => hf.2.2.2) hF hk)

/-- `_REENT`'s `_dtoa_r` words are among the allocator words of the stdio
globals (`AllocWords`), so no stdio state reads them. -/
theorem ReentWord.alloc {a : Nat} (h : ReentWord a) : AllocWords a := by
  simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at h
  simp only [AllocWords]; omega

end Lua.Vm.Sim.Kit

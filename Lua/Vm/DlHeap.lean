import Lua.Vm.Repr
import Lua.Vm.LayoutRt

/-!
# The newlib dlmalloc heap at `luaV_execute`'s entry

A WHILE-free restatement of ship-your-interpreter's `DlHeap.HeapAt`
(`Vsa/Sim/DlHeap.lean`) at the Lua ELF's addresses (`Lua/Vm/LayoutRt.lean`),
over this repository's reads (`Lua.Vm.rd64`). The allocation ledger fields
(`live`, `exact`: the WHILE runtime's ownership of extents) are dropped; what
is left is the shape `_malloc_r`/`_realloc_r`/`_free_r` read.

`__malloc_av_` holds 128 bins; bin `i` is addressed as a chunk at
`symMallocAv + 16 * i`, so its `fd`/`bk` words sit at `+16`/`+24`. Bin 0's `fd`
word is the top chunk and its size word is the `binblocks` bitmap. htif.c's
`_sbrk` grows the heap from `_end` towards `__heap_end`, recording the break in
`brk.0`.

Every allocation F1 reaches goes through it: `print` → `luaL_tolstring` →
`lua_pushfstring`/`luaS_newlstr` (a new string per integer printed) →
`luaM_malloc_` → `l_alloc` (`c/src/main.c`) → `realloc`; `luaE_extendCI` for the
`CallInfo` of the call to `print`; `luaD_growstack` when the stack grows; and
newlib's `__smakebuf_r` for stdout's buffer at the first write.
-/

namespace Lua.Vm.DlHeap

open Lua.Vm Lua.Vm.Layout

def avAddr : Nat := symMallocAv
/-- Bin 0's size word: the `binblocks` bitmap. -/
def binblocksAddr : Nat := avAddr + 8
/-- Bin 0's `fd` word: the top chunk. -/
def topAddr : Nat := avAddr + 16
/-- `_end`: the first break `_sbrk` returns, and the first chunk. -/
def heapStart : Nat := symEnd
/-- `__heap_end`: `_sbrk` fails beyond it. -/
def heapEnd : Nat := symHeapEnd
def numBins : Nat := 128

/-- Bin `i`, viewed as a chunk. -/
def binAt (i : Nat) : Nat := avAddr + 16 * i

/-- Chunk size: the header without `PREV_INUSE` and `IS_MMAPPED`. -/
def chunkSize (h : Nat) : Nat := h / 4 * 4

def prevInuse (h : Nat) : Bool := h % 2 == 1

/-- newlib's `bin_index` for a chunk size. -/
def binIndex (sz : Nat) : Nat :=
  if sz / 512 = 0 then sz / 8
  else if sz / 512 ≤ 4 then 56 + sz / 64
  else if sz / 512 ≤ 20 then 91 + sz / 512
  else if sz / 512 ≤ 84 then 110 + sz / 4096
  else if sz / 512 ≤ 340 then 119 + sz / 32768
  else if sz / 512 ≤ 1364 then 124 + sz / 262144
  else 126

/-- One chunk of the walk; `inuse` is the next header's `PREV_INUSE` bit. -/
structure Chunk where
  addr : Nat
  size : Nat
  inuse : Bool
  deriving DecidableEq, Repr

/-- The contiguous chunks from `p` up to the top chunk `top`. -/
inductive ChunkWalk (m : Mem) : Nat → Nat → List Chunk → Prop where
  | top {p : Nat} : ChunkWalk m p p []
  | chunk {p top h h' : Nat} {cs : List Chunk} :
      rd64 m (p + 8) = some h → h % 4 < 2 →
      32 ≤ chunkSize h → chunkSize h % 16 = 0 →
      rd64 m (p + chunkSize h + 8) = some h' →
      ChunkWalk m (p + chunkSize h) top cs →
      ChunkWalk m p top (⟨p, chunkSize h, prevInuse h'⟩ :: cs)

/-- A bin's circular doubly-linked list, from `q` (predecessor `prev`) back to
the bin head `b`. -/
inductive BinChain (m : Mem) (b : Nat) : Nat → Nat → List Nat → Prop where
  | close {prev : Nat} : rd64 m (b + 24) = some prev → BinChain m b b prev []
  | link {q prev nxt : Nat} {qs : List Nat} :
      q ≠ b → rd64 m (q + 24) = some prev → rd64 m (q + 16) = some nxt →
      BinChain m b nxt q qs → BinChain m b q prev (q :: qs)

/-- Bin `i`'s list starts at its `fd` word (the bin itself when empty). -/
structure BinList (m : Mem) (i : Nat) (qs : List Nat) : Prop where
  fd : rd64 m (binAt i + 16) = some (qs.headD (binAt i))
  chain : BinChain m (binAt i) (qs.headD (binAt i)) (binAt i) qs

/-- The heap shape `_malloc_r` reads. `bins i` is bin `i`'s list in `fd`
order. -/
structure HeapAt (m : Mem) (top brkv : Nat) (chunks : List Chunk) (bins : Nat → List Nat) :
    Prop where
  sbrk_base : rd64 m symMallocSbrkBase = some heapStart
  brk : rd64 m symBrk = some brkv
  brk_le : brkv ≤ heapEnd
  top_ptr : rd64 m topAddr = some top
  top_le : top ≤ brkv
  top_size : (brkv - top) % 16 = 0
  /-- Top's size reaches the break; its predecessor is in use. -/
  top_header : rd64 m (top + 8) = some (brkv - top + 1)
  top_pad : rd64 m symMallocTopPad = some 0
  max_sbrked : (rd64 m symMallocMaxSbrked).isSome
  mallinfo : (rd64 m symMallocMallinfo).isSome
  /-- Nothing precedes the first chunk. -/
  first_prev : (rd64 m (heapStart + 8)).any (fun h => h % 2 == 1)
  walk : ChunkWalk m heapStart top chunks
  coalesced : ∀ i (hi : i + 1 < chunks.length),
    chunks[i].inuse = true ∨ chunks[i + 1].inuse = true
  footer : ∀ c ∈ chunks, c.inuse = false → rd64 m (c.addr + c.size) = some c.size
  bins_list : ∀ i, 0 < i → i < numBins → BinList m i (bins i)
  bins_nodup : ∀ i, (bins i).Nodup
  /-- Every binned chunk is a free chunk of the walk, in its size's bin. -/
  bin_free : ∀ i q, 0 < i → i < numBins → q ∈ bins i →
    (chunks.filter fun c => c.addr == q && !c.inuse && (i ≤ 1 || binIndex c.size == i)) ≠ []
  /-- Every free chunk is on exactly one bin. -/
  free_binned : ∀ c ∈ chunks, c.inuse = false →
    ((List.range numBins).filter fun i => 0 < i && (bins i).contains c.addr).length = 1
  /-- The last-remainder bin holds at most one chunk. -/
  remainder : (bins 1).length ≤ 1
  binblocks_present : (rd64 m binblocksAddr).isSome
  binblocks : ∀ bb, rd64 m binblocksAddr = some bb →
    ∀ i, 1 < i → i < numBins → bins i ≠ [] → bb / 2 ^ (i / 4) % 2 = 1

end Lua.Vm.DlHeap

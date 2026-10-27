# Fresh bignum allocation: the calloc seam

Source/ELF audit, 2026-10-27; this is a task map, not a proof.
Cached `_Balloc` and `_dtoa_r` result release are reviewed. First-use
freelist allocation and empty-class allocation still call `_calloc_r`.

The ELF `_calloc_r` at `0x8004a35c` calls `__muldi3` and `_malloc_r`.
At `0x8004a3a8` it reads the chunk header at `p-8`, masks its flag bits,
and subtracts 8. That physical payload capacity is what it zeroes,
not just the multiplication result. Capacities at most 72 take inline
stores; larger ones call `memset(p,0,capacity)` at `0x8004a410`.
Every allocator chunk has size divisible by 16 and size at least 32,
so capacity is at least 24 and congruent to 8 modulo 16.

`tasks/calloc-memset.md` targets the reusable large-capacity zeroing run.
`memset` starts at `0x8003b56c`; its aligned zero path loops over two
8-byte stores at `0x8003b590`, then uses the computed byte tail. The
calloc remainder selects eight tail bytes. The symbolic proof must
quantify over arbitrary length; a finite boot instance is insufficient.

`MallocPost` already carries the resulting `HeapAt`, the live physical
chunk at `p-16`, and preservation of every old in-use chunk. The calloc
composition must derive its actual header/capacity and separation of the
entire fresh capacity from old live payloads. `MallocPost.fresh` alone
only promises freshness for the requested length: do not use it unchanged
for all zeroed padding. Use resulting chunk disjointness plus the retained
old chunks and positive request to prove the larger region is fresh.

No general calloc, fresh Balloc, or FloatToStr obligation is discharged
by this audit. The small-capacity stores, multiplication/overflow bounds,
allocator composition, zeroed freelist installation, and bignum ownership
extension remain after the memset lemma.

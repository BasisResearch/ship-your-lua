# Fresh _Balloc composition

Source/ELF audit, 2026-10-27; a task map, not a proof.
The cached path is proved by `balloc_heap_sum`. Fresh paths share the
actual `_Balloc` entry at `0x8003d654` and its 32-byte stack frame.

If `_REENT->_freelist` is NULL, the call at `0x8003d6a4` is
`_calloc_r(_REENT, 8, 65)`. The returned array is stored at `_REENT+104`
before the non-NULL test. Its 520 requested bytes cover 65 pointers;
calloc zeroes the entire physical capacity. The next branch loads the
selected zero head, so a successful first use also allocates a bignum.
`ReentMpAt.fl_zero` supplies the empty previous ledger, not an assumed
post-allocation ledger.

With an initialized array and a zero head, `0x8003d6c4` computes
`1 << k` by **sllw**, then requests `28 + 4*(1 << k)` bytes from
`_calloc_r(_REENT, 1, ...)` at `0x8003d6e4`. This equals `bigSize k`
only after a class bound is proved: the machine sign-extends a 32-bit
shift. A positive mathematical allocation-room bound for `bigSize k`
inside this heap implies `k<31`; derive this, rather than pretending
that the existing ledger bound `k<=64` suffices. Reuse the generated
sllw rule from the dtoa-release lane and a shared pure bound lemma.

After successful allocation the body stores `_k` and `_maxwds` at
`b+8` and `b+12`, then clears `_sign`/`_wds` at `b+16` with one
8-byte store. `_next` and digits remain zero from calloc. The fresh
block is returned separately, not inserted into a freelist. Retain its
physical allocation base/capacity, semantic `bigSize k` region, and
separation from every old live block. Extend B by the fresh regions;
`ReentMpAt` keeps existing lists/cache/result, with the initialized
array added on first use. Supply `BigRun`, not a new heap-frame premise.

Budget both calls on first use. `MallocPost.brk_hi` charges request+20480;
a sufficient second-call room condition accounts for the first request520
and that allowance before adding `bigSize k+16384`. Keep the resulting
cost explicit; it is not zero-growth like cached Balloc. Account for
Balloc's 32-byte frame outside calloc's own frame and allocator stack.
The allocator's full-capacity freshness is needed for all calloc writes,
although B need only claim the logical requested object regions.

This seam does not prove dtoa arithmetic, decimal formatting or strtod.
Compose it with cached Balloc later under one ownership-aware interface.

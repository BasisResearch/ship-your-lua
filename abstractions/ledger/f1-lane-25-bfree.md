# F1-25 bignum primitive: newlib `_Bfree`

The exact machine stores are lifted to `ReentMp` ownership and `BigRun`
for a separately owned active block.

## Result

`Kit/Bfree.lean` proves `bfree_sum` at `0x8003d700` (nine instructions).
The input and post are named-field structures, `BfreeIn`/`BfreePushIn` and
`BfreePost`.

- NULL: the generated branch and return; no memory/pointer premise, memory
  unchanged.
- Non-NULL: read the signed class at `b + 8`, the freelist pointer at
  `reent + reentFreelistOff` (104), and the old head at `fl + 8*k`; write
  the old head at `b`, then `b` at the slot. `bfreeMem` exposes this exact
  memory, in instruction order. `bfreeMem_push` proves both links.
- Return: PC is the caller's aligned `ra`; `ra`, `sp`, `gp`, `s0`–`s11`
  and the console are preserved. `BfreePost.keep` is equality of optional
  bytes outside the two eight-byte writes, preserving presence as well as
  values. There is no allocator call and no claim that an allocating
  operation leaves the heap unchanged.
- `BigChain.congr` (beside its model in `EntryData.lean`),
  `bfree_rdLE_keep`, and `bfree_chain` prove the chain
  update for an apart owned block (`BfreeOwned`), preserving the class and
  capacity of every old node.

## Abstractions and generation

The proof uses the callee-context route: `gen_lua_at.py --fn _Bfree/null,_Bfree`, `FCx`,
`fat_seg`/`fat_close`, generated `runs`, and `fcx_ok`/`pins_of` for the
summary. The signed class load and scaled address are separate generated
segments so existing `AtNarrow` and `fat_shl` close them. No per-site proof,
pin normalizer, generated-file edit, or increased Lean budget is used.

`gen_lua_code.py` has a standalone pin list, and `gen_lua_arms.py` has
`STANDALONE_HELPERS` and a targeted `--helper` regeneration/check option.
Regeneration writes only changed content, preserving existing file timestamps.
The new pins, sites, segments, and AtF files are standalone imports.
`Lua/Vm/Code.lean`, `Lua/Vm/Arms.lean`, and `arms.tsv` are unchanged, as are
all pre-existing generated files and other generators.

Other reused names: `rdLE_congr`, `AllocHeap.rd64_eq`,
`read64_writeMap8`, `sdData_toNat`, `getElem?_writeMap8_out`,
`fw8_wm8`, `bytesT8_writeMap8`, and `sdData_id`.

## Exact premises and remaining work

`bfree_sum` has no whole-function premise. Its input requires `sp ≤ 2^32`
and aligned return PC. On the non-NULL branch it additionally requires:

- eight-aligned `reent`, `b`, and `fl`, in RAM above `tohost`;
  `reent + 112`, `b + 16`, and `fl + 520` bounded by `2^32`;
- `k ≤ 64`, and the block header apart from the 65-pointer array;
- the three actual loaded values (class, freelist pointer, old head).

`bfree_chain` additionally requires the block's present class/capacity
words and that every old chain block is apart from both the owned block
and the array (`BfreeOwned`), plus the old `BigChain`.

`Kit/BfreeHeap.lean` lifts the existing exact-store run, without another
machine proof. `bfree_heap_sum` supplies `BfreeHeapPost`: the original
`BfreePost` and `BigRun F m (bfreeMem m b fl k head) H H B B 0` for any
caller region `F`. The named `BfreeHeapIn` requires:

- `HeapAt` and `ReentMpAt` at the zero fill of the input memory;
- the existing non-NULL machine/load obligations `BfreePushIn`, plus
  present class/capacity words at the zero fill;
- an active block of class `k`, apart from every `bigBlocks` allocation
  (array, result, all free nodes and power-five cache nodes);
- the active allocation in old `B`, and every byte of `B` in a live heap
  payload within the arena (`HeapIn`).

These are input ownership and machine conditions; no desired postcondition
is assumed. `bfreeLists_perm`/`bfreeBlocks_perm` show the ownership list gains
exactly `(b, bigSize k)`. `reentMpAt_bfree` changes only head `k` and list `k`,
keeps the other chains via `BigChain.congr`, and preserves the result and
power-five cache. `bfree_keep_owned` gives optional-byte equality for each
old allocation except the array. `bfreeMem_frame` exposes the exact two
write ranges; `bfreeMem_total` and `bfreeMem_fill` bridge total bytes and
zero-filled presence. `bfree_frozen` re-establishes `ReentMp` frozen on
`BigFoot B` at the new memory. `bfree_bigRun` proves both writes lie in `B`,
hence in live payloads: `HeapAt.ofTotal` then preserves all allocator
metadata, the chunk list and break. The new bignum region is exactly old
`B`; no fresh allocation or heap growth is claimed.

Cache footprint audit: `BigChain` bounds `_k` and pins `_maxwds`, but does
not bound `_wds`, which `bigVal` follows. `ReentMpAt.p5cap` now explicitly
requires a present `_wds ≤ 2^_k` for each power-five node. This is true at
boot because the cache is empty (`ReentBoot.mp`); it is preserved by both
`reentMpAt_congr` and `reentMpAt_bfree`. `bigVal_congr` uses this bound to
put every value read inside the allocated capacity. Free-list nodes need
no value bound. Future cache-producing routines must prove the bound when
they insert or change a cache node.

`FloatToStr_Statement` and `FpStrFlt_Statement` remain open: this is their
first reusable bignum primitive.
`_Balloc`, the other `mprec.c` routines, `_dtoa_r`, the `%.14g` formatter,
and the value/length correctness proof remain.

## Validation

All Lean invocations use the main repo's `scripts/lean-capped.sh`, which
checks the worktree lock, at least 25 GB available RAM, inherited 12 GB
scope, and CPU affinity. Builds use this worktree's private `.lake/build`.
No shared dependency cache or unrelated untracked file is changed.

- `lake build Lua.Vm.Sim.Kit.BfreeHeap`: passes (1,337 jobs), including
  `EntryData`, `Bfree`, `BigHeap` and both generated runs.
- `gen_lua_code.py --check` and `gen_lua_at.py --fn _Bfree/null,_Bfree --check`:
  pass.
- `check_discipline.py` and `abstractions/gate.py`: pass.
- Targeted axiom audit: all 13 `BfreeHeap` theorems, `ReentBoot.mp`,
  `BigChain.congr`, `bfree_sum`, and `bfree_chain` (17 reports) pass;
  every report is exactly `[propext, Classical.choice, Quot.sound]`.
  `check.sh` builds `BfreeHeap` explicitly and includes these declarations
  in stage 6 alongside the existing machine/pin audits.
- `bash scripts/check.sh --static-only`: passes all generator drift checks,
  ELF/hash checks, forbidden-token scan, discipline, abstraction gate, and
  copied-layer checks (`WHILE` roots in the closure: none).
- Python generator syntax, `bash -n scripts/check.sh`, and
  `git diff --check`: pass.

The combined repository gate checks integration before publication.

The active-block contract does not cover `_dtoa_r`’s result release alone:
that call temporarily puts the result on a freelist before clearing
`_result`. Its future summary must cover the complete release prefix
using the exact-store primitive, as recorded in `abstractions/DEAD-ENDS.md`.

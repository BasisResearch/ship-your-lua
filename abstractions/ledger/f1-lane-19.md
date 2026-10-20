# Lane F1-19: the `CALL` invariant carries what an allocating `print` needs; `CallOpen` true as stated

Base: main `947567d` (lane F1-18). Route: the relation's region facts (`Frozen`, `StrtSafe.weaken`), the
boot witness's kernel checks (`gen_lua_boot_witness.py` + `Boot/Check.lean`, one `decide +kernel` per
`EntryChecks` field), `call_close`. Lines are added/removed lines (`git diff --numstat`). No heartbeat or
recursion limit was raised.

## Result

| target | status | where |
|---|---|---|
| 1. `g->allgc` in `CallDirty`/`EntryDirty` | **done**: both gain `[g + 112, g + 120)` (`gAllgcOff`); the boot footprint is checked off it (`entryDirtyRanges`) | `Rel.lean`, `EntryData.lean`, `Boot/Check.lean` |
| 2. the string table's safety in `CallInvAt` | **done**: `CallInvAt.alloc : CallAlloc` (`CallAllocAt` at a region `B` of bignums): `StrtSafe (fillZeroMem M) rt (Kept …) (CallX0 w F ∨ B) B` frozen with the literals on `FL`. `StrtSafe`/`StrChainK` moved to `EntryData.lean` and given `W` (chain nodes off the bignums); `X` is what the caller holds (`CallX0`: `F`, `L`, `g`, the `CallInfo`s, the stack above `ci->func`'s slot, below the heap). Boot: `VmEntryData.strt_safe` from `strtSafeCheck` on `e.litFoot` (which now records every chain node's `shrlen`), `EntryChecks.strt`; re-established by `call_close` (`CloseIn.safe`, `callX0_after`) | `EntryData.lean`, `Rel.lean`, `Boot/Check.lean`, `Entry.lean` (`strt_boot`), `CallClose.lean` |
| 3. `AllocIn`'s facts through `PrintIn` | **done**: `PrintIn.alloc : PrAlloc` (literals, `safe`, `big`, `bigIn`), `gc`, `stat` (`AllocStatic` from the frozen `LocaleWords` and `.rodata`, `fmtStatic_of`), `mt_fn`; built at the join (`call_alloc`, `call_gc`, `call_x`, `JoinIn.fl_w/keepK/nci_x/strt_w`); `PrintOut.st : PrintOutSt'` returns `PrAlloc`; `PrSt` threads it (`safe` unconditional, `big`, `bigIn`, `big_fl`) | `CallOpen.lean`, `CallPrint.lean`, `PrintRel.lean`, `TolStrProof.lean` |
| 4. `HeapBudget` from memory | **done**: a structure, `brk` (`callBudget args`, the stale `16 · w.rt.strtSize` term dropped) and `strt` (`strtNuse w.mo g + newStrs args ≤ strtSize w.mo g`); `PrintRelIf`'s budget is `PrBudget` (`call_strt` carries the table's room to the join). `luaS_resize` is thereby `HeapBudget_Statement`'s (A8) | `CallArm.lean`, `CallOpen.lean` |
| 5. floats: `_REENT`'s bignums apart | **done**: `ReentMp` (`ReentMpAt`: `_result`/`_result_k`/`_p5s`/`_freelist`, the 65 free lists' classes, the `_p5s` cache's values, every block pairwise apart, in `B`) frozen on `B ∪ ReentWord`; `reentP5sOff` generated; boot `ReentBoot` (all NULL, `ReentBoot.mp`) | `EntryData.lean`, `LayoutPrint.lean` |
| 6. functions: `mt[LUA_TFUNCTION]` pinned | **done**: `LuaStatic.mt_fn` (frozen on `F`, in `luaStaticWords`, value by `entryBaseCheck`), `PrintIn.mt_fn`. (In `LuaStatic`, the `CALL` invariant's frozen Lua state, rather than `LuaStateRel`: no arm needs it, and `LuaStateRel` is rebuilt by other lanes' arms) | `Rel.lean`, `EntryData.lean` |
| restate `PrintFlt`, `PrintFn`, `PrintAllocOff` | **done**: `PrintFlt_Statement`, `PrintFn_Statement` unchanged in form (`PrintRelOn`), true as stated over the stronger `PrintIn`/`PrBudget`; `PrintAllocOff_Statement` restated (an integer list whose new strings do not fit the table) and **proved** vacuous (`printAllocOff_proved`), dropped from `CallOpen` | `CallOpen.lean`, `PrintRel.lean` |
| `TolInt_Statement` | **not proved**: true as stated, now instantiable at every `CALL`; obstacle unchanged (`internshrstr` on arbitrary contents and its create path) | — |

`CallOpen` is now `tolInt : TolInt_Statement`, `printFlt : PrintFlt_Statement`, `printFn : PrintFn_Statement`,
each true as stated, all three open.

## Why the restated premises are true (against the ELF)

* What an allocating class writes besides fresh memory, the stack and `g`'s first words: `g->allgc`
  (`F` off it by `CallDirty`, the other kept objects apart from `g`: `call_gc`), a bucket's head (the array
  off `X`), a dead string's mark (off `X`), and for floats `_REENT`'s words and the bignums `B` (off `G`,
  the Lua objects, `FL`, the literals, the chain nodes: `PrBigIn`, `StrChainK`'s `W`). `G ⊆ Kept ∪ PrintStatic`
  keeps it off fresh chunks, the stdout buffer, the allocator's globals and `_REENT`.
* What it reads that the relation did not pin: `g->frealloc` (`LuaStatic.frealloc`), the locale words
  (`LocaleWords`), `G(L)->mt[LUA_TFUNCTION]` (`mt_fn`), `.rodata`, the bignums (`ReentMp`).
* Room: no `_malloc_r` fails within `argCost`, no `luaS_resize` within `HeapBudget.strt`.
* **Sail trace** (`experiments/print_alloc/probe.py fltprobe.lua`: 18 floats from `5e-324` to `1.8e308`,
  `±inf`, `nan`, `-0.0`, `print(print, 42, -7)`): per `luaL_tolstring` of a float at most four `_malloc_r`
  (the first `%.14g` of the run: the free lists' 520-byte array, two bignums, the string), one afterwards
  (the string), no `luaS_resize`; the static words loaded are `_impure_ptr`, `__global_locale + 0xe8/0x100/0x160`,
  `_impure_data + 0x50/0x58/0x68` (floats only) and the allocator's globals; an integer's and a function's
  touch none of `_REENT`'s `_dtoa_r` words. A static scan of every function reachable from `luaL_tolstring`
  finds no other `.data` word on these paths (`__sf`, `fds`, `files` only on stdout's set-up and error paths).
  The boot witnesses check the boot table safe (141 interned strings) and every `_REENT` word NULL.

## Numbers

| part | lines (+/−) | CPU (s) | peak (MB) |
|---|---|---|---|
| `Kit/CallPrint.lean` (`call_x`, `call_alloc`, `call_gc`, `call_strt`, `fmtStatic_of`, `JoinIn`'s 4 fields in both joins, `close_flKeep`, `close_bigKeep`, `closeX_sub`, `StaticW`) | 359/50 | see below | see below |
| `Boot/Check.lean` (`strSafeCheck`, `strtSafeCheck`, `localeRange`, `offX`, `strtAt_same`, `placedCheck_walk`) | 179/11 | | |
| `Kit/CallOpen.lean` (`PrX`, `StrtSafeIn`, `PrBigIn`, `PrAlloc`, `PrintOutSt`, `PrBudget`, statements) | 177/140 | | |
| `EntryData.lean` (`StrChainK`, `StrtSafe`, `ReentMp`, `ReentBoot`, `LocaleWords`, `EntryX`, fields) | 176/6 | | |
| `Kit/PrintRel.lean`, `Kit/TolStrProof.lean` (the threading) | 136/85, 27/14 | | |
| `Entry.lean`, `Rel.lean`, `CallClose.lean`, `Errno.lean`, `CallArm.lean` | 72/5, 43/3, 41/6, 30/5, 29/12 | | |
| generators (`gen_lua_boot_witness.py`, `gen_lua_layout.py`) | 46/3 | 17 (both traces) | — |
| boot witnesses (`decide +kernel`, `lake build`) | 0 hand | 204 (While), 248 (F1Ops) | ≈ 3.5 GB |

## Obstacles

1. **The table's growth.** With the table near full, a `print` runs `luaS_resize`: `_realloc_r` of the bucket
   array (its chunk changes size or is freed, so `PrintOut`'s "chunks in use kept" is false there) and every
   `u.hnext`. Kept inside `PrintCall_Statement` this would need the array's whole chunk off the caller's objects
   and a weaker `PrintOut`; it is beyond `HeapBudget.strt` instead, so it is `HeapBudget_Statement`'s (A8), whose
   truth there needs `_realloc_r` of a live block (unproved) and the invariant at the new array.
2. **`B` is threaded, not kept by `G`.** Folding the bignums into `G` (the kept bytes) fails: a float print
   writes them. So `PrSt` carries `big`/`bigIn` and every proved step shows them kept (`LitKeeps.big`,
   `prStrPost`'s `kB`, `reentWord_not_printW` for a write).
3. **Rel/EntryData edits rebuild every arm** (full `lake build Lua Vsa VsaIris`).
4. Other lanes' files touched: `Kit/Errno.lean` (the `errno` store keeps `CallInvAt.alloc`; `StatFacts`/`LuaStatic`
   constructors gained `mt_fn`, `locale`) — additive.

## Axioms

`scripts/check.sh` stage 6 lists `StrtSafe.weaken`, `ReentBoot.mp`, `strtSafeCheck_sound`, `strtAt_same`,
`placedCheck_walk`, `strt_boot`, `reent_boot`, `callX0_after`, `call_close`, `reentWord_not_printW`,
`printAllocOff_proved`, `fmtStatic_of`, `call_x`, `call_alloc`, `call_gc`, `call_strt`, `close_bigKeep`,
`closeX_sub` (and the earlier `printRel_of`, `printCall_of`, `callInv_boot`, `entryCheck_sound`,
`Complement.errno`): `[propext, Classical.choice, Quot.sound]`.

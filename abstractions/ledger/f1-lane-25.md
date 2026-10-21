# Lane F1-25: `CALL print` on a float down to `snprintf(…, "%.14g", …)`; the bignum region `BigRun`

Base: main `e473886` (lane F1-24). Route: CLAUDE.md's `CALL print` row (per-argument `TolArg`, one glue),
the callee-context rows (`gen_lua_at.py --fn`: `strspn`, `tostringbuff/f`, `lua_pushfstring/f`,
`luaL_tolstring/flt`), region facts frozen on footprints. Lines are non-blank, non-comment lines. CPU and peak
memory are one `lake env lean <file>` each (user time, maximum resident set) under `systemd-run --user --scope
-p MemoryMax=16G`, `LEAN_NUM_THREADS=4`. Heartbeats are per declaration, bracketed by rerunning the file with
`-DmaxHeartbeats` 50000 and 100000. No heartbeat or recursion limit was raised.

## Result

| target | status | where |
|---|---|---|
| per-class budget (task 1) | **done**: `PrSt` is `PrStR … (prCost args i)`; `ArgStr.cost` is `one allocation ≤ argCost v` (a float's sixteen); the glue `tolPost_of_runP` takes any state `PrStR … rm` with room for the string and the arguments after it (`hrm`); `tolPost_of_run` is its instance; no glue forked | `Kit/CallOpen.lean`, `Kit/TolIntProof.lean` |
| a run that computes with bignums before its string | **done**: `tolPost_of_split` (the run cut at the end of its bignum prefix; `PrStR.bigRun` carries `luaB_print`'s state across a `BigRun` to the memory, heap and bignums it leaves; `TolPost.pre`) | `Kit/TolSplit.lean` |
| the bignum allocator as a region (task 2) | **defined and used**: `BigRun F m m' H H' B B' c` over `ReentMp`/`BigFoot` (lane F1-19), `BigW`, `Fresh`; `BigRun.trans`, `mono`, `ofFrame`, `frame_before`, `frame_after`, `keep_inUse`, `keep_static`, `apart`; `AllocWords` now holds `_REENT`'s `_dtoa_r` words (no stdio fact reads them), so `stdout`'s state crosses a `BigRun`. **`_Balloc`/`_Bfree` summaries not proved** (below) | `Kit/BigHeap.lean`, `Sim/StdioState.lean` |
| floats per argument | **done**: `TolFlt_Statement := TolArg IsFlt`; `printRel_of` takes it (no list-level float premise); `show_ascii`/`prLine_chars` for every value | `Kit/CallOpen.lean`, `Kit/PrintRel.lean` |
| `strspn(s, "-0123456789")` | **proved**: `strspn_sum` (the set a `.rodata` literal: the inner scan unrolled into one fork per character, the outer loop by `seg_loop`; `spanLen`) | `Kit/Strspn.lean`, `AtF/Strspn.lean` |
| `tostringbuff` on a float | **proved from `FloatToStr_Statement`**: `tsb_sum` (`snprintf` a call node, `strspn_sum`, the `".0"` suffix; the model's `tostringbuff`, `tsbBytes_eq`) | `Kit/TsbF.lean`, `AtF/TsbF.lean` |
| `lua_pushfstring(L, "%f", n)` | **proved**, two halves: `pushfF_pre` (to `tostringbuff`'s return, a `BigRun`), `pushfF_post` (`pf_newlstr`, `pf_tail` shared with `"%I"`, `"%s: %p"`) | `Kit/PushfF.lean`, `AtF/PushfF.lean` |
| `luaL_tolstring` on a float | **proved**, two halves: `tolflt_pre`, `tolflt_post` | `Kit/TolFlt.lean`, `AtF/TolFlt.lean` |
| `TolFlt_Statement` | **proved from `FloatToStr_Statement`**: `tolFlt_of` (class facts `argStr_flt`: no literal is a float's string, `G14Byte`, `Lua/Num/Fmt14gFacts.lean`) | `Kit/TolFltProof.lean` |
| `PrintFlt_Statement` | **discharged to `FloatToStr_Statement`**: `printFlt_of`; `CallOpen = {floatToStr}` | `Kit/TolFltProof.lean`, `Kit/CallOpen.lean` |
| `FloatToStr_Statement` (task 3) | **open, the one premise**: `snprintf(buf, 44, "%.14g", x)` to `G14Post` (the model's `fmt14gBits`, one to twenty-one bytes, a `BigRun` within `dtoaRoom`) | `Kit/FltFmt.lean`, PHASES row |

## Why the premise is at `snprintf`, not at `_dtoa_r`'s value

The task's target was a single value premise (lifted `_dtoa_r` = a `Nat` reference). Not reached in this lane:

* **Machine side of `_dtoa_r`**: 1,400 instructions, 129 calls (17 `__muldf3`, 10 `__subdf3`, 10 `__floatsidf`,
  8 `__ledf2`, 7 `__adddf3`, 6 `__fixdfsi`, 5 `__divdf3`, 8 `__multadd`, 6 `__lshift`, 6 `__mcmp`, 6 `__i2b`,
  4 `__pow5mult`, 2 `quorem`, 11 `_Bfree`, 3 `_Balloc`, `__d2b`, `__mdiff`, `__multiply`, `memcpy`), three digit
  paths (quick floating, small integer, bignum). Each `mprec.c` routine is a loop over a heap array (a `memcpy`-sized
  lane each), `_svfprintf_r`'s float conversion is a second `snprintf` specialisation (lane FMT's size). Estimated at
  several lanes.
* **Value side**: the reference exists (`Lua.Num.dec14`, `decExp`, `keepsZeros`); the quick path's correctness is a
  floating-point error-bound argument (it bails out to the bignum path when unsure), and `dec14`'s own length bound
  needs `decExp`'s exactness (`10^k ≤ v < 10^(k+1)`), not proved. So `FloatToStr_Statement` carries the machine's
  count bound (one to twenty-one bytes) as part of the run (`G14Post.len_lo`/`len_hi`).
* What the lane did instead: everything around `snprintf` is proved, and the premise's post is stated over the
  bignum region abstraction, so the remaining work is exactly `snprintf`'s run (`_svfprintf_r` + `_dtoa_r` +
  `mprec.c`) against `fmt14gBits`.

Evidence the premise is true: `c/tests/float/run.sh` (lane float-s0b: the Lean model `fmt14g`/`tostringbuff`
equals the ELF on Sail on every vector, subnormals, powers of ten and halfway cases included); lane F1-19's `print`
traces (at most four `_malloc_r` per float, far within `dtoaRoom`; `_REENT`'s words the only static words written).

## Numbers

| file | hand lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|
| `Kit/BigHeap.lean (new; `MallocGlobal.lt` moved here)` | 126 | 1.5 | 1,996 | < 50k |
| `Kit/TolSplit.lean (new)` | 214 | 3.7 | 3,601 | < 50k |
| `Kit/FltFmt.lean (new: `FloatToStr_Statement`)` | 31 | 0.9 | 1,970 | < 50k |
| `Lua/Num/Fmt14gFacts.lean (new)` | 112 | 3.4 | 801 | < 50k |
| `Kit/Strspn.lean (new; `bytesAt_get` moved here)` | 241 | 27.4 | 2,212 | 100k–200k |
| `Kit/TsbF.lean (new)` | 287 | 7.7 | 3,419 | 50k–100k |
| `Kit/PushfF.lean (new)` | 301 | 17.7 | 3,611 | 50k–100k |
| `Kit/TolFlt.lean (new)` | 170 | 9.4 | 3,432 | < 50k |
| `Kit/TolFltProof.lean (new)` | 158 | 2.4 | 3,824 | < 50k |
| `Kit/TolIntProof.lean` (`PrStR` glue, `tolPost_of_runP`, `ArgStr.cost ≥`, `tolV_in` on the slot's bits) | +29 net (+113/−84 raw) | 19.6 | 4,115 | 50k–100k (as before) |
| `Kit/CallOpen.lean`, `Kit/PrintRel.lean`, `Kit/TolFnProof.lean`, `Kit/PushfI.lean`, `Sim/StdioState.lean`, `Kit/CallPrint.lean` | +22, +1, +6, −5, +2, 0 net | — | — | — |
| `scripts/gen_lua_at.py` (`strspn`, `tostringbuff/f`, `lua_pushfstring/f`, `luaL_tolstring/flt`), `gen_lua_arms.py` (helpers `lua_tonumberx`, `tostringbuff.part`, `strspn`; edits), `gen_lua_code.py`, `check.sh` | +96, +17, +3, +28 raw | — | — | — |
| **hand total (new files)** | **1640** | | | |

| generated file | lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|
| `Lua/Vm/AtF/Strspn.lean` | 1360 | 165.6 | 2,346 | < 50k |
| `Lua/Vm/AtF/TsbF.lean` | 309 | 15.8 | 1,969 | < 50k |
| `Lua/Vm/AtF/PushfF.lean` | 1894 | 365.3 | 4,409 | 100k–200k |
| `Lua/Vm/AtF/TolFlt.lean` | 1214 | 292.0 | 4,033 | 100k–200k |
| segments, sites, code pins (`Haddnum2buff`, `HluaL_tolstring`, `HluaO_pushvfstring`, new `Hlua_tonumberx`, `Htostringbuff_part_0_isra_0`, `Hstrspn`) | +7,700 (approx.) | — | — | — |

## Obstacles

1. **Segment liveness**: unstopping `addnum2buff`'s float branch made `x16`/`x17` live in its `_n` segment (the
   `snprintf` varargs spill); no existing at-lemma used that segment, so nothing else changed.
2. **A narrow sum in an address** (`addiw` of the count, then `add`: the `".0"` suffix): `fat_side` has no rule for
   `sext (extractLsb (ofNat n) 31 0)`; the spec states the sum's `Nat` as a root fact (`TSB_P`'s `ad1`, proved by
   `tsb_ad1`) rather than a hook in `AtFn.lean` (which every at-module imports).
3. **Heartbeats per declaration**: `strspn`'s outer loop with eleven unrolled character forks on both successor
   kinds exceeded 200k in one declaration; split into `spn_in_loop`, `spn_in_end`, `spn_out` over one setup macro.
4. **Name clashes** with earlier lanes (`tsX`, `tf_pre`, `MallocW.anti`, `bytesAt_get`): renamed or moved.
5. **A NaN's payload** is not determined by its `Value`: `tolV_in` now takes the representation of the slot's own
   bits (`hrep` on the instance), so a float's bits are read from the memory.
6. Builds: changing `StdioState.lean` (`AllocWords`) and the code-pin index rebuilds most of `Lua`.

## Axioms

`scripts/check.sh` stage 6 adds `BigRun.{trans,ofFrame,frame_before,frame_after,keep_inUse,apart}`,
`PrStR.bigRun`, `TolPost.pre`, `tolPost_of_runP`, `tolPost_of_split`, `strspn_sum`, `spanLen_of`, `tsbBytes_eq`,
`tsb_sum`, `pff_tsb`, `pushfF_pre`, `pushfF_post`, `tolflt_pre`, `tolflt_post`, `argStr_flt`, `lits_nomatch_flt`,
`tolFlt_of`, `printRel_tol`, `CallOpen.print`, `printFlt_of`, `printFn_of`, `Lua.Num.fmt14g_byte` (and
`printFn_of_tol`, `printFlt_of_tol` for the retired `printFn_of_flt`): every one `[propext, Classical.choice, Quot.sound]`. `scripts/check.sh` passes (all stages, the full `lake build Lua Vsa VsaIris` included); `python3 abstractions/gate.py` ok.

# Lane F1-17: `TolStr_Statement` proved (`luaL_tolstring` on a string)

Base: main `5b168a5`. Route: CLAUDE.md's callee-context rows (`gen_lua_at.py --fn`, `fat_run`), `seg_loop`
for `luaH_get`'s chain walk, call nodes for `lua_pushstring` (`pushLit_proved`) and `luaH_get`.
Lines are non-blank, non-comment lines (doc comments excluded). CPU and peak memory are one
`lake env lean <file>` each (user time, maximum resident set). Heartbeats are per declaration, bracketed
by rerunning the file with `-DmaxHeartbeats` 50000 and 100000. No limit was raised.

## Result

| target | status | theorem / file |
|---|---|---|
| `TolStr_Statement` | **proved** | `tolStr_proved` (`Kit/TolStrProof.lean`) |
| `CallOpen` | **`printAlloc` alone** | `CallOpen.print O := printRel_of mallocR_proved pushLit_proved tolStr_proved O.printAlloc` (moved to `Kit/TolStrProof.lean`; `CallPrint.lean` imports it) |

Axioms of `tolStr_proved`, `CallOpen.print`, `hget_miss_sum`, `gmf_miss_sum`, `toltopl_sum`,
`tol_{s,l}_pre`, `tol_tail_{s,l}`, `prStrPost`, `call_args_heap`: `[propext, Classical.choice, Quot.sound]`
(`scripts/check.sh` stage 6).

## The proofs (per part)

| part | hand lines | generated lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|---|
| `luaH_get`'s miss: `HMissAt`, `NodeMiss.toAt`, `hg_mp`, `hget_loop`, `hget_miss_sum` (`Kit/Getmetafield.lean`) | 188 | `AtF/LuaHGetMiss` 381 | 25.3 (file) | 3,010 (file) | < 50k |
| `luaL_getmetafield.part.0`: `StrMtMiss.hgetIn`, `rod_absent`, `gmf_miss_sum`, `gmf_rest`, `gmf_tail` (same file) | 257 | `AtF/GmfMiss` 556 | (above) | (above) | 50k–100k (`gmf_miss_sum`, `gmf_tail`) |
| `luaL_tolstring` on strings: `toltopl_sum`, `gmfIn_of`, `tolSMid_of`, `tolS_m2`, `tol_{s,l}_pre` (one tactic `tol_pre_run`), `tol_{s,l}_mid` (`tol_mid_run`), `tolStrPost_of`, `tol_tail_{s,l}` (`Kit/TolStr.lean`) | 434 (macros 2 × ~40, used twice each) | `AtF/TolStrS`, `TolStrL` 2 × 1,020, `TolTopL` 333 | 34.1 | 3,023 | < 50k |
| `TolStr_Statement`: `Frozen.mem_of_det`, `str_foot`, `tolS_in`, `notTolSW_of`, `notW_of_keep`, `str_kept`, `prStrPost`, `str_repr_at`, `tolStr_proved`, `CallOpen.print` (`Kit/TolStrProof.lean`) | 366 | — | 17.1 | 3,966 | 100k–200k (`prStrPost`, as `prLitPost`) |
| `PrintIn.args_heap`, `ChunkWalk.addr_lo`, `call_args_heap` (`Kit/{CallOpen,CallPrint}.lean`) | 40 | — | — | — | — |
| helper segments (`gen_lua_arms.py` `HELPERS`: `luaL_getmetafield.part.0`, `lua_rawget`, `index2value`, `luaH_get`, `lua_pushvalue`; stops lifted in `luaL_tolstring`, `luaL_callmeta`, `lua_tolstring`) | — | 8,214 (`Arms/{Segs,Sites}/H…`) | — | — | — |

Generator setup (`gen_lua_at.py`): `luaH_get/miss`, `luaL_getmetafield/miss`, `tol_str` (two tag modules),
`tol_top` (two tag modules); the regenerated `TolTop` gained the long-string path (unused by `toltop_sum`).

`python3 abstractions/gate.py` passes (`a1-kit-arm` 69 cases, first 1.9, last 4.1).

## Obstacles and what fixed them

1. **`TolStr_Statement` was not provable as stated.** `PrintIn` let an argument's string object lie in the
   static image (`keep_in`: `Kept ∨ PrintStatic`, and `ι` is arbitrary), and there `TolPost.src_lo`
   (`SrcLo`: below `tohost` only when shorter than 1024 bytes) fails for a long string. Fix: the field
   `PrintIn.args_heap` (the string's pointer at or above `__heap_start`), proved at the producer from the
   relation's ownership (`Complement.own` → `ChunkOwns`, the chunk walk from `__heap_start`:
   `ChunkWalk.addr_lo`, `call_args_heap`).
2. **Where the argument's string lies** is not a `PrintIn` field. It follows from the freeze: every byte a
   frozen fact pins is in the footprint (`Frozen.mem_of_det`: change the byte, the fact must fail), so the
   contents, terminator and header are among `G` and the slots (`str_foot`), hence kept by the run
   (`notW_of_keep`) and in chunks in use (`str_kept`). The length is read off the representation at the
   tail's memory (`str_repr_at`), never threaded through the run.
3. **Heartbeats.** One `luaL_getmetafield` summary ran out of the default budget. Splitting at the call
   roots (`gmf_rest`, `gmf_tail`) did not suffice: the cost was `omega` case-splitting nine disjunctive
   separations kept in context. Fix: the separations enter only the goals that need them (`gmf_ap`, the
   per-region `kS`/`kL`/`kR`); every declaration is now below 100k but `prStrPost`.
4. **`omega` and `heapEnd`** hit the recursion limit on goals stating `heapEnd + … ≤ sp` (as lane F1-15
   saw); `homega`/`generalize heapEnd` fixes them.
5. **The generator** needed: the string metatable's `Ok` facts (`t_al`, the slot/`L` separation `tL`), the
   dead `nilvalue` path of `lua_pushvalue` as a stop (`0x80001fcc`), `absentkey`'s `.rodata` words as `cells`.

## Open

* `PrintAlloc_Statement` (`CallOpen.printAlloc`, lane FMT in parallel).
* `prLitPost` (lane F1-15) and `prStrPost` share their keep/`TolPost` assembly; folding `prLitPost` into a
  width-generic form was left to avoid editing `PrintRel.lean` under the parallel lanes.

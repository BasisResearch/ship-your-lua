# Lane F1-15: `PrintRel_Statement` per value class, `PushLit_Statement` proved

Route: CLAUDE.md's A1 rows. Callee-context at-lemmas (`gen_lua_at.py --fn`, `fat_run`), `seg_loop` for the
hash loop and the chain walk, `kit_run` for helper segments without at-lemmas (the bucket, `luaS_newlstr`'s
tail jump, `__umoddi3`, `luaE_setdebt`). Lines are non-blank, non-comment lines. CPU and peak memory are
one `lake env lean <file>` each (user time, maximum resident set). Heartbeats are per declaration,
bracketed by rerunning the file with `-DmaxHeartbeats` 50000 and 100000. The limit was never raised, so
the default of 200000 holds.

## Result

| target | status | theorem / file |
|---|---|---|
| 1a. decompose `PrintRel_Statement` per class | **done** (earlier commit `e10dc40`) | `printRel_of : MallocR_Statement → PushLit_Statement → TolStr_Statement → PrintAlloc_Statement → PrintRel_Statement` (`Kit/PrintRel.lean:594`) |
| 1b. `luaL_tolstring` on nil, `true`, `false` | **proved over `PushLit_Statement`** | `tolLit_proved` (`Kit/PrintRel.lean`) |
| 1c. `PushLit_Statement` | **proved** | `pushLit_proved` (`Kit/PushLitProof.lean:241`) |
| 1d. `luaL_tolstring` on strings | open, named premise `TolStr_Statement` | `CallOpen.tolStr` |
| 2. integers and floats | kept as premises (`IntegerToStr_Statement`, `G14From`), under `PrintAlloc_Statement` | `CallOpen.printAlloc` |
| 3. `CallOpen.print` narrowed | **done** | `CallOpen.print O := printRel_of O.mallocR pushLit_proved O.tolStr O.printAlloc` (`Kit/PrintRel.lean:628`); `CallOpen` is now `printAlloc`, `tolStr`, `mallocR`, `freeR` |

## The proofs (per arm)

| part | hand lines | generated lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|---|
| `umoddi3_sum`, `luaC_step_sum` (`Kit/PushLit.lean`) | 115 | `AtF/LuaCStep` 102 | 5.8 | 2,320 | 50k–100k heartbeats |
| `internshrstr_sum`, `newlstr_sum`, `int_hash`, `int_chain`, `ChainFirst.toAt`, `hstep_mach`, `bucket_addr` (`Kit/Intern.lean`) | 575 | `AtF/Internshrstr` 456 | 16.3 | 2,454 | 50k–100k |
| `snew_nil`/`_true`/`_false`/`_tos` by one tactic `snew_run`, `cand_of_zero`, `LitCache.shift` (`Kit/SNew.lean`) | 435 (the macro: 216 lines, used 4 times) | `AtF/LuaSNew{Nil,True,False,Tos}` 4 × 476 | 93.8 | 3,393 | 100k–200k (the `snew_run` expansions) |
| `pushstring_sum`, `pushLit_proved` (`Kit/PushLitProof.lean`) | 237 | `AtF/Pushstring` 278 | 17.6 | 3,393 | 100k–200k (`pushstring_sum`) |
| helper segments and code pins (`gen_lua_arms.py` `HELPERS`, `gen_lua_code.py` `EXTRA`) | — | 13,032 (`Arms/{Segs,Sites}/H{internshrstr,luaS_new,luaS_newlstr,lua_pushstring,luaC_step,luaE_setdebt}`) | — | — | — |

`python3 abstractions/gate.py` passes after each part. For `a1-kit-arm` it reports 67 cases (first 1.9, last 4.1).

## Obstacles and what fixed them

1. **The old `PushLit_Statement` was false.** Each of these breaks its post: a cache entry with equal
   contents, an earlier chain node with equal contents, and a running collector.
   * Fix: boot facts `ChainFirst` (the walk meets the interned string first) and `LitCache`/`CandOk` (the
     cache's words are candidates of their row: the literal's own string, or `strcmp`-different).
   * `gcstp` is a hypothesis.
   * All of these are kernel-checked by `Boot/Check` on the witness.
2. **The callees' memory differs from the caller's.**
   * `luaS_new` shifts the cache row before `internshrstr` reads the string table. So the literals'
     facts are stated `Frozen` on a footprint `FL` below the heap's end and off the string cache.
   * The statement now takes `Frozen FL (LitsHold …)`. The caller supplies `FL ∩ cache = ∅` from
     `PrintIn.dirty`/`LitsFoot.apart`.
3. **The string scans were stated with the wrong frames and ranges.**
   * `strcmp`/`strlen`/`memcmp` were stated for heap ranges above `tohost`. The literal lies in
     `.rodata`, below `tohost`.
   * Fix: `McCtx`/`ScCtx`/`SlCtx` take `0x80000000 ≤ P` and `p_th` (below or above `tohost`), and the
     earlier lane-15 commit added `ScanFrame` (`s6`/`s10` carried, `PASS_THROUGH_S`).
4. **`internshrstr`'s loop rows pinned `ra`.** The segments do not carry `ra`. The generator's `int_row`
   now omits it: `ra` is saved and dead until the return.
5. **Bounds the boot facts lacked**, now added:
   * the bucket array in RAM (`LitsIn.hash_hi ≤ symHeapEnd`);
   * chain nodes, interned strings and candidates below the heap's end;
   * every literal's string a candidate of its row (`lit_cands`);
   * `PrintIn.f_al` (`func % 8 = 0`), which `lua_pushstring`'s stores need;
   * `PushCx` with room for the callees' frames, and `L`/`g`/`top` apart;
   * `LitApart`: the literal's string apart from the push's stores.
6. **`luaHash` in 32 bits.** `srliw`/`slliw`/`addw` on the sign-extended hash equals `UInt32` `hstep`
   (`hstep_mach`). This is proved by `extract_sext` and `sext_xor32`, not by `bv_decide`. The bucket
   mask uses `Nat.and_sub_one_eq_zero_iff_isPowerOfTwo` (`bucket_addr`).
7. **Termination of the chain walk.** `ChainFirst` gives no measure. `ChainAt` adds the walk's length,
   proved from `ChainFirst` by `ChainFirst.toAt` (an induction on the boot fact, not on the machine run),
   and `seg_loop` uses that length as its measure.

## Open

* `TolStr_Statement`: `luaL_getmetafield` → `lua_rawget` → `luaH_get`'s miss on the string metatable (the
  boot fact `StrMtMiss` is in place), `lua_pushvalue`, `lua_tolstring` of a long string.
* `PrintAlloc_Statement`: integers (`IntegerToStr_Statement`), floats (`G14From`), functions. `print_sum`'s
  invariant carries no per-argument break budget.
* `MallocR_Statement`, `FreeR_Statement` (A0).

## Axioms

All of `pushLit_proved`, `pushstring_sum`, `snew_{nil,true,false,tos}`, `internshrstr_sum`, `newlstr_sum`,
`int_hash`, `int_chain`, `umoddi3_sum`, `luaC_step_sum`, `LitCache.shift`, `CallOpen.print`:
`[propext, Classical.choice, Quot.sound]` (`scripts/check.sh` stage 6).

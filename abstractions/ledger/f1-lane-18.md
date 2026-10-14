# Lane F1-18: `CallOpen.printAlloc` split by value class over a per-argument budget; run lemmas generated

Base: main `705a5e2`. Route: CLAUDE.md's callee-context rows (`gen_lua_at.py --fn`), `print_sum`'s loop
(`seg_loop`), the region lemmas (`Frozen.trans`, `Kept.mono`). Lines are non-blank, non-comment lines
(diff stat). CPU and peak memory are one `lake env lean <file>` each (user time, maximum resident set).
No heartbeat or recursion limit was raised; every declaration elaborates at the default 200k.

## Result

| target | status | where |
|---|---|---|
| 1. FMT's run lemmas from the generator | **done**: `gen_lua_at.py` `runs` (a root path by its root pc, context, end, guard texts; `row`, `when`, `unless`, `extra`, `derive`), emitted in `SnprintfLld/Runs.lean`, each applying the path's at-lemmas by name; the 16 hand run lemmas of `Kit/IntFmt.lean` replaced (signatures identical, `export`ed) | `scripts/gen_lua_at.py`, `Lua/Vm/AtF/SnprintfLld/Runs.lean` |
| 2a. a per-argument budget in `print_sum`'s invariant | **done**: the state is `S i k` (before argument `i`); `PrSt.room` (`PrRoom (prCost args i)`: `argCost` per class, `stdoutNeed` before `stdout`'s buffer), `PrSt.strt` (room in `g->strt`), `PrSt.safe` (`StrtSafe`, frozen with the literals), `PrSt.gc` (`g->allgc` off `PrKeep`), `PrSt.stat` (`AllocStatic`: `g->frealloc`, `snprintf`'s static words); `PrintPost.room` (a write keeps it: `HeapGrant.brk_hi` from `MallocPost.brk_hi`); `PrSt'` lets the literals' footprint change; `PrSt.next0` for the classes that allocate nothing; `callBudget` sums `argCost` | `Kit/{PrintSum,PrintIO,CallOpen,PrintRel,CallArm}.lean` |
| 2b. `PrintAlloc_Statement` split | **done**: `CallOpen` = `tolInt : TolInt_Statement` (per argument, `TolArg IsInt`), `printFlt : PrintFlt_Statement`, `printFn : PrintFn_Statement`, `allocOff : PrintAllocOff_Statement`; `printRel_of` assembles them with `tolLit_proved`, `tolStr_proved` (the line now for integers too: `show_ascii`, `int_ascii`) | `Kit/{CallOpen,PrintRel,TolStrProof}.lean` |
| 2c. the integer class proved | **not done**: `TolInt_Statement` open (obstacles 2, 3) | — |
| 3. `G14From` | **not started**: obstacle 4 | PHASES row S0b |
| 4. functions | **named premise** `PrintFn_Statement`: obstacle 5 | — |

## Numbers

| part | hand lines (non-blank, non-comment, before → after) | generated lines | CPU (s) | peak (MB) | largest declaration |
|---|---|---|---|---|---|
| generator `runs` (`gen_lua_at.py`, Python) | +167 | `SnprintfLld/Runs.lean` 1,008 | 6.3 (`Runs`; the hand `IntFmt.lean` it replaces ran `fat_run`'s search) | 2,295 | < 50k |
| `Kit/IntFmt.lean` (run lemmas → `export`) | 411 → 40 | — | — | — | — |
| `print_sum` indexed (`Kit/PrintSum.lean`), `PrintPost.room` (`Kit/PrintIO.lean`), `HeapGrant.brk_hi` (`Kit/{Swsetup,Smakebuf,SfvFirst}.lean`), `Kit/PrintS.lean` | 834 → 839, 143 → 159, +2, 0 | — | — | — | `fwrite_print`, `pr_mid` < 200k |
| budget, classes, `StrtSafe`, `AllocStatic`, `AllocIn`, premises (`Kit/{CallOpen,CallArm}.lean`) | 193 → 258, 253 → 258 | `Lua/Vm/LayoutPrint.lean` 20 (`gen_lua_layout.py` +32) | — | — | — |
| `printLua_st`, `PrSt.next0`, budget lemmas, `AllocStatic.congr`, `allocStatic_not_printW`, `litKeeps` (split off `prLitPost`: one declaration's budget), `TolLitPost.strt`, `int_ascii`, `show_ascii`, `printRel_of` (`Kit/PrintRel.lean`) | 526 → 781 | — | — | — | `litKeeps`, `prLitPost` 100k–200k |
| `prStrPost`, `TolStrPost.strt`, `tolStr_proved` (`Kit/TolStrProof.lean`) | 366 → 386 | — | — | — | `prStrPost` 100k–200k |

`python3 abstractions/gate.py`: ok (`a1-kit-arm` 69 cases, first 1.9, last 4.1).

## Obstacles (with evidence)

1. **`print_sum`'s state had no argument index** (lane F1-15's obstacle). Fixed by indexing it (`S i k`);
   the budget is the state's, consumed by an allocating `luaL_tolstring` and kept by a write
   (`PrintPost.room`). A write that sets `stdout` up grows the break by at most `1024 + 16384 + 4096`
   (`HeapGrant.brk_hi`, threaded from `MallocPost.brk_hi` through `__smakebuf_r` and `__swsetup_r`).
2. **`PrintIn` keeps `G` off none of what an allocating `luaL_tolstring` writes, so lane F1-15's
   `PrintAlloc_Statement` was false, and with it `CallOpen`.** `luaC_newobj` links the new string at
   `g->allgc`: `0x8000e930: sd a0,112(s0)` with `s0 = G(L)` (`gAllgcOff = 112`, generated). `PrintIn.keep_apart`
   keeps `G` off `[g + 16, g + 64)` and the string cache only; `G` contains `CallInv`'s footprint `F`, which
   is only off `CallDirty` (the same two ranges of `g`), and enlarging a valid `F` by `g->allgc` gives another
   (`Frozen` is monotone in the footprint). On such an entry, `print(n)` for an `n` whose decimal string is
   not interned writes `g->allgc`, so `PrintOut.keep` fails and `PrintRel_Statement` is false there. The same
   holds for the bucket head `internshrstr` writes on a miss, the mark `changewhite` writes on a dead string
   found, and every `u.hnext` `luaS_resize` rewrites. The split makes the per-argument statement
   `TolInt_Statement` true by stating what it writes off `PrKeep` in `PrSt` (`gc`, `safe`) and the static words
   it reads that `PrintIn` does not pin (`stat`: `g->frealloc`, which `luaM_malloc_` calls through a `jalr`; the
   C locale's `.data` words `FmtStatic` reads), and isolates the
   gap in `PrintAllocOff_Statement` (`printRel_of`'s case split on `AllocIn`), documented as false. The fix is
   a relation lane: `CallDirty`/`EntryDirty` gain `g->allgc`; `CallInvAt` gains the table's safety
   (`StrtSafe` over the caller's ranges, frozen with the literals), checked on the boot table (a
   `strChainCheck` with bounds, marks and `u.hnext` off the footprint) and kept by `call_close` from
   `PrintOut`; `PrintIn` passes `AllocIn` on; `HeapBudget` reads the table's size from memory (`callBudget`
   takes `w.rt.strtSize`, the boot's, stale after a resize).
3. **`newlstr_sum` interns only a boot literal** (`LitInterned`: the walk meets it first, no allocation). The
   integer's string is any short contents: `internshrstr`'s walk over any chain (now `StrtSafe`: readable,
   `shrlen ≤ 40`, in chunks in use) and its create path (`luaC_newobj` → `luaM_malloc_` → `l_alloc` →
   `_malloc_r`, within `argCost`; `memcpy`; the bucket's head; `nuse`), then the literals' facts re-frozen on
   a new footprint (the head word is in the old one). The path above it is mapped: `luaL_tolstring`
   (`lua_isinteger` at `0x80021c14`, `lua_tointegerx`, `lua_pushfstring(L, "%I")` at `0x80021c3c`, the tail
   `j lua_tolstring`), `lua_pushfstring` (`luaO_pushvfstring`, then `luaC_step` when `GCdebt > 0`),
   `luaO_pushvfstring` on `"%I"` (`strchr` on the 8-aligned `.rodata` word, ground; `addstr2buff(…, 0)`;
   the jump table at `0x80052c1c`; `addnum2buff` → `snprintf(buf, 44, "%lld")` = `integerToStr_proved`;
   `strlen("")`; `luaS_newlstr(L, sp + 56, blen)`; the tag `| 64`; `L->top += 16`).
4. **`G14From`**: `_dtoa_r` frees `_REENT->_result` on entry (`ld a1,80(a0)`, `_Bfree`) and `_Balloc` pops
   `_REENT->_freelist[k]` (`ld a5,104(a0)`; the lists' array by `_calloc_r(_REENT, 8, 65)` the first
   time), so a true `%.14g` statement needs an invariant of those bignums (in chunks in use, apart from what
   the caller keeps, `k`/`maxwds` consistent), which neither `PrintIn` nor `CallInv` carries; the float class
   stays the whole-call `PrintFlt_Statement`. Zero prints `"0"` before any `_Balloc` (`__eqdf2` at
   `0x8004a814`).
5. **Functions**: `luaL_tolstring`'s default case calls `lua_getmetatable` (`G(L)->mt[LUA_TFUNCTION]`,
   `luaTfunction = 6`, generated), which `LuaStateRel` does not pin (nil, booleans, numbers only), then
   `lua_typename`, `lua_topointer`, `lua_pushfstring(L, "%s: %p")`.
6. Heartbeats: `prLitPost` was at 100k–200k (lane F1-15); the budget's facts pushed it over, so its keeps are
   a declaration of their own (`litKeeps`, a named structure `LitKeeps`).
7. Discipline R7 (`>8 ∃` in `CallOpen.lean`): the footprint-carrying wrappers are inductives (`PrSt'`,
   `LitsSafe`), the class test one definition (`HasClass`).

## Open

* `TolInt_Statement` (obstacle 3), `PrintFlt_Statement` (obstacle 4), `PrintFn_Statement` (obstacle 5),
  `PrintAllocOff_Statement` (false as stated: obstacle 2, the relation lane).

## Axioms

`#print axioms` of `run_E`, `run_Qn1`, `run_Pn`, `run_Rn2`, `PrSt.next0`, `prCost_succ`, `prAllocs_succ`,
`anyAlloc_of_cost`, `StrtSafeIn.mono`, `litKeeps`, `TolLitPost.strt`, `TolStrPost.strt`, `show_ascii`,
`prLine_chars`, `fwrite_print`, `prStrPost`, `printLua_st`, `printRel_of`, `CallOpen.print`,
`tolStr_proved`, `integerToStr_proved`: `[propext, Classical.choice, Quot.sound]` (`scripts/check.sh`
stage 6).

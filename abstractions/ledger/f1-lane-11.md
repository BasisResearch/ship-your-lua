# Lane F1-11: toward `SimArm .CALL`: presence-level keeps, every phase of `stdout`, `luaB_print`

Base: main `eb982c0`. Route: CLAUDE.md's callee-context rows (lanes F1-8..10).
Lines are non-blank, non-comment lines (`--` lines and `/- … -/` blocks
dropped). CPU and peak memory are one `lake env lean <file>` each
(`/usr/bin/time`: user time, maximum resident set). Heartbeats are per
declaration, bracketed by rerunning the file with `-DmaxHeartbeats` 25k, 50k,
100k (never raised; default 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1. presence-level keeps | **done** (one generic route, no summary restated) | `Agree.ofTotal`, `fill_total`, `HeapAt.ext`, `HeapAt.congrU`, `HeapAt.ofTotal`, `HeapAt.ofStdioKeep`, `SetupPost.heapAfter` (`Kit/HeapFill.lean`) |
| 1b. the heap of the set-up stated of the zero fill | **done** (statement change) | `MallocR_Statement`, `HeapGrant`, `SmakebufPost`, `StdoutSetup_Statement` (`HeapAt (fillZeroMem m)`, `StdioBoot (fillZeroMem m)`); lane F1-10's proofs adapted (`fill_congr`, `bT8_of_fill`) |
| 2a. `print("")`: empty writes, the stream between `__sinit` and its buffer | **proved** | `sfv_empty`, `fwrite_boot0`, `fwrite_fresh0`, `stdoutSetup_fresh` (`Kit/StdoutEmpty.lean`, `Lua/Vm/AtF/FwriteFresh.lean`) |
| 2b. one write from any phase of `stdout` | **proved from `MallocR_Statement`** | `fwrite_print` (`StdoutPh`, `StdoutIn`, `PrintPost`, `Kit/PrintIO.lean`) |
| 2c. `luaB_print` | **proved over named premises** | `print_sum : MallocR_Statement → PrintLua L sp0 n S bs → …` (`Kit/PrintSum.lean`, `Lua/Vm/AtF/Print.lean`); `pr_tail`, `pr_mid`, `pr_step`, `pr_loop` (`seg_loop`) |
| 2d. `luaL_tolstring` per value class | open | the premise `PrintLua.tolstring` (`TolPost`) |
| 3a. `lua_gettop`, `lua_settop(L, -2)` | **proved** | `gettop_sum`, `settop_pop_sum` on `ApiAt` (`Kit/LuaApi.lean`) |
| 3b. `luaD_precall` (C path), `luaD_poscall`, relation facts, `ExitOk` | open | — |
| 4. `SimArm .CALL` | open | `OpenArms.CALL` stays; obstacle 2 below |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists `HeapAt.ext/congrU/ofTotal/ofStdioKeep`,
`Agree.ofTotal`, `SetupPost.heapAfter`, `sfv_empty`, `fwrite_boot0`,
`fwrite_fresh0`, `stdoutSetup_fresh`, `SetupPost.print`, `fwrite_print`,
`gettop_sum`, `settop_pop_sum`, `PrintSt.keep`, `pr_tail`, `pr_mid`,
`pr_step`, `pr_loop`, `print_sum`).

## 1. Presence-level keeps: one lemma, no summary restated

A total-read keep (`bytesT1 m' a = bytesT1 m a`) says nothing about
presence, so it never gives `Agree` of the machine memories. It does give
`Agree` of their **zero fills** (`Vsa.Densify.fillZeroMem`): in RAM every
byte of a fill is present and holds the total read (`fill_total`,
`Agree.ofTotal`). The fill reads totally as the memory (`bytesT1_fill`), so
it is as good a complement for `Core.frame` as the memory itself, and every
presence fact of a memory holds of its fill (`Ext`, `HeapAt.ext`). So
`RuntimeMem.heap` after a print is `HeapAt (fillZeroMem m')`
(`HeapAt.ofTotal`), from any summary's total keep off what `HeapAt` reads but
the chunks in use (`HeapAt.congrU`: the walk reads headers, free chunks'
footers and links, never an in-use payload, so the `stdout` buffer may
change under it).

The same observation forced a statement change (law 4, evidence):
`MallocR_Statement` and the set-up took `HeapAt m` and `StdioBoot m` of the
**machine** memory, which `VmRel` never provides (`Core.frame` is total;
only `.text` is held present). Restated of the fill (the machine reads
totally, so the premise is no stronger), with lane F1-10's proofs adapted by
`fill_congr`/`bT8_of_fill` (24 lines changed).

## 2. Every phase of `stdout`

`print("")` writes 0 bytes first: `_fwrite_r` still runs `CHECK_INIT`
(`__sinit`) and `ORIENT`, but `__sfvwrite_r` returns at once for
`uio_resid = 0` (`0x80033b54`), so `stdout` has a third state between boot
and set up (`StdoutFresh`). `fwrite_print` covers the five cases (boot/fresh
× empty/not, set up); the writes from the fresh stream run `fwrite`'s
at-lemmas at `_flags = 0x2009` (`gen_lua_at.py --fn fwrite/fresh`). The post
`PrintPost` states the new phase, the heap of the fill, `out ++ pend' = pend
++ bytes`, the chunks in use kept, where a new buffer lies (`buf_new`: a
fresh block of the arena) and a total keep off `PrintW` (what a write may
change).

`luaB_print`'s `"\t"` and `"\n"` lie in `.rodata`, below `errno`, which the
stdio statements excluded (`errnoAddr + 4 ≤ src`). Generalized to `SrcLo`:
below `tohost` when shorter than the buffer (never written by `__swrite`
straight from where it lies, whose console loop reads above `tohost`); lane
F1-9's loop proof went through unchanged but for the case split (2 lines).

## 3. `luaB_print`

On the callee-context route with `luaL_tolstring` a call node
(`gen_lua_arms.py` `CALLEE_READS` keeps its argument registers live), the
loop head `0x80022f68` a root, the first argument's string write run on the
loop's rows with `i = 1`. The Lua side is abstract: an invariant `S k ph H m`
and the bytes `bs i`; `PrintLua` holds the callees' contracts and `S`'s
stability under a write and under `luaB_print`'s own frame. `print_sum`'s
post `PrEnd`: the console gains `pend ++ prLine bs n ++ "\n"`, `stdout` set up
and flushed, `S` again, the chunks in use kept, the caller's frames kept.
The I/O state's own footprint (`PrintFoot`) gives `PrintSt.keep` (with
congruences of `StdioBoot`, `MemfsBoot`, `StdoutFresh`, `StdoutAtW`,
`StdioUp`).

## Per piece

| piece | hand lines | generated lines | CPU / peak (hand file) | largest declaration |
|---|---|---|---|---|
| presence keeps (`Kit/HeapFill.lean`) | 261 | — | 2.6 s / 2.1 GB | ≤ 25k |
| empty writes, fresh stream (`Kit/StdoutEmpty.lean`) | 212 | at-lemmas 557 (`FwriteFresh`, 19) | 8.9 s / 2.2 GB; at-lemmas 52.2 s / 2.4 GB | ≤ 25k |
| every phase (`Kit/PrintIO.lean`) | 162 | — | 2.1 s / 2.1 GB | ≤ 25k |
| `lua_gettop`, `lua_settop` (`Kit/LuaApi.lean`) | 92 | at-lemmas 72 + 187; segments, sites, code pins 5,545 | 3.1 s / 1.9 GB; at-lemmas 2.6 s, 6.4 s | ≤ 25k |
| `luaB_print` (`Kit/PrintSum.lean`) | 850 | at-lemmas 676 (21, 16 roots); segments, sites 3,927 | 19.8 s / 2.4 GB; at-lemmas 41.1 s / 2.2 GB | `print_sum` (50k, 100k]; `pr_mid`, `pr_step`, `pr_tail` (25k, 50k] |

Setup (generators, statements): `gen_lua_at.py` +76 (`fwrite/fresh`,
`lua_gettop`, `lua_settop/pop`, `luaB_print`; `LUA_OK`, `PRINT_*`),
`gen_lua_arms.py` +16 (three helpers, `CALLEE_READS`), `gen_lua_code.py` +4;
statement changes in lane F1-10's/F1-9's files 58 lines.

## Obstacles (with evidence)

1. **Presence of the machine memory.** (Solved, above.) `VmRel` holds the
   machine memory only by total reads; any premise stated of the machine
   memory's presence (`MallocR_Statement`'s `HeapAt m`, `StdoutSetup`'s
   `StdioBoot m`) could not be met from the relation. The fill is the
   uniform answer.
2. **Heap room for allocating value classes.** `print(i)` for an integer (or
   float) allocates a string per new value (`luaL_tolstring` →
   `lua_pushfstring` → `luaS_newlstr` → `luaC_newobj` → `_malloc_r`), and the
   harness stops the collector (`c/src/main.c:38`, `lua_gc(L, LUA_GCSTOP)`).
   No room invariant on `VmRel` (`brk + k ≤ __heap_end`, what
   `MallocR_Statement` asks) survives every reachable state: a loop printing
   distinct integers exhausts the 120 MB arena. Then `luaM_malloc_` runs the
   emergency `luaC_fullgc` (`cantryagain` is not blocked by
   `LUA_GCSTOP`'s `gcstp`). So `SimArm .CALL` on integers/floats needs either
   that path (the GC, PHASES A8) or a named budget premise; strings, nil and
   booleans allocate only once (the `stdout` buffer, the `CallInfo` of
   `luaE_extendCI`, possibly `"__tostring"` if not interned at boot), so a
   one-shot room fact in the relation suffices for them.
3. **`luaL_tolstring` is the per-class work.** Every class goes through
   `luaL_callmeta` → `luaL_getmetafield` → `lua_getmetatable` (`G(L)->mt`:
   `LuaStateAt.mt_*` gives nil/booleans/numbers no metatable; strings have
   the string library's, so `lua_pushstring("__tostring")` → `luaS_new`
   (`strcache`, `StrCacheAt`) → `lua_rawget` → `luaH_getshortstr`), then a push
   (`lua_pushvalue`, `lua_pushstring` of an interned literal, or
   `lua_pushfstring`) and `lua_tolstring`. `TolPost` is the contract
   `print_sum` needs.
4. **`fwrite`'s flags as a literal cell.** The generator decides
   `_fwrite_r`'s `ORIENT` and unlock tests from a literal `_flags` cell, so
   the fresh stream (`0x2009`) needs its own at-lemma module (`FwriteFresh`,
   identical to `Fwrite` but the literal) and `fwf_post`/`fwu_post` are
   one-module instances of one proof. A cell given by known bits (the tests
   read bits 9 and 13 only) would merge them.

## What is left (the remainder)

* `luaL_tolstring` per value class (`PrintLua.tolstring`, `TolPost`) and the
  concrete Lua invariant `S` (`ApiAt`, the arguments, the complement's
  facts), with its stability (`PrintLua.stable`).
* `luaD_precall`'s C path (`checkstackGCp`, `next_ci`/`luaE_extendCI`, the C
  `CallInfo`), `luaD_poscall` (`moveresults`, `L->ci`), the relation facts
  (stdio state in the complement as `PrintSt`, `LuaStateAt.next`, `ι`/`own`,
  `ci->top`, `ExitOk` after a print: `stdio_exit_handler` → `_fclose_r`,
  `_free_r` (a `FreeR_Statement` beside `MallocR_Statement`)).
* `SimArm .CALL`: obstacle 2 first.
* `MallocR_Statement` (A0), `IntegerToStr_Statement`.

## Gate

`abstractions/gate.py`: `a1-kit-arm` ok (58 cases, first 2.1, last 2.9).
`a1-float-arm` fails (12 cases, first-quarter 2.7, last 13.3): its files
(`Kit/AtFlt*.lean`, the float lanes' cluster) are unchanged by this lane, so
the failure is the base's. `scripts/check.sh`: stages 1–3b, 4, 5 (the full
`lake build Lua Vsa VsaIris`, 1 min 57 s wall, 3.7 GB peak), 5b and 6 (429
axiom reports, all within `propext`, `Classical.choice`, `Quot.sound`) pass;
3c is the float cluster above.

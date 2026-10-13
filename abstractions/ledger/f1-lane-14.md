# Lane F1-14: `CallOpen`'s fields (`exit` after a `print`, `luaE_extendCI`, `luaD_poscall` with results, the stack growth)

Base: `fdee414` (merge of lane F1-13). Route: CLAUDE.md's A1 rows: the
callee-context at-lemmas (`gen_lua_at.py --fn`, `fat_run`), the kit route
(`kit_run`) for `exit` and `luaD_poscall`, `seg_loop` over `compMem` for the
nil-fill loop. Lines are non-blank, non-comment lines. CPU and peak memory are
one `lake env lean <file>` each (`/usr/bin/time -v`: user time, maximum
resident set). Heartbeats are per declaration, bracketed by rerunning the
file with `-DmaxHeartbeats` 50k and 100k (never raised; default 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1. `exitUp : ExitUp_Statement` | **proved from `FreeR_Statement`** | `exitUp_of_free` (`Kit/ExitUp.lean`); `CallOpen.exitUp` is the theorem, `CallOpen.freeR : FreeR_Statement` the remaining premise (`Kit/Malloc.lean`, A0 like `MallocR_Statement`) |
| 2. `extendCI : ExtendCI_Statement` | **proved from `MallocR_Statement`** | `extendCI_of_malloc` (`Kit/ExtendCI.lean`); `CallOpen.extendCI` is the theorem, `CallOpen.mallocR : MallocR_Statement` the premise (A0) |
| 3. `poscall : PoscallN_Statement` | **proved** | `Ret.poscallN` (`Kit/PoscallN.lean`); `CallOpen.poscall` is the theorem |
| 4. `grow : PrintGrow_Statement CallInv` | **proved vacuous** | `printGrow_none` (`Kit/CallOpen.lean`), from the invariant's `growFree` and `call_bounds`; `CallOpen.grow` is the theorem |
| 5. `print : PrintRel_Statement` | open | see obstacle 3 |

`CallOpen` is now `print`, `mallocR`, `freeR`: besides `PrintRel_Statement`, only the two A0 allocator premises.

## 1. `exit(0)` once `stdout` is set up

**True or false.** The Sail run of `while.lua` (the committed ELF), traced
from `exit` (`--trace-pcs` over `exit`, `stdio_exit_handler`,
`_fwalk_sglue`, `_fclose_r`, `__sclose`, `_close_r`, `_close`, the locks,
`_free_r`), takes: `__call_exitprocs`, the `jalr` to `stdio_exit_handler`,
`_fwalk_sglue` over `__sf`'s three streams; `stdin`: `_fclose_r` takes the
lock, `__sflush_r`'s read path (`_r = _ur = 0`: nothing to seek), `__sclose`
→ `_close_r` → `_close(0)` (`fds[0]` freed), no buffer, `_flags = 0`;
`stdout`: `__sflush_r` (nothing pending), `_close(1)`, `_free_r` of the
buffer (`__SMBF`); `stderr` as `stdin`; then `_exit(0)`. So the exit is
correct on the machine, but `ExitUp_Statement` as lane F1-13 stated it (over
`StdoutIn w.mo _ (.up buf [])`, the heap and `__atexit`) was **not
provable**: nothing constrained `stdin`'s and `stderr`'s `FILE`s (their
`_close` hooks, flags, `_ub`/`_lb`), `__sglue` or `__stdio_exit_handler`, and
`exit` jumps through them.

**The invariant fixed.** `StdoutIn.fresh`/`.up` carry `StdioRest` (the
handler, `__sglue`, `stdin` and `stderr` as `StdQuiet`: read-only or
unbuffered, nothing read ahead, no `ungetc`/line buffer, `_close =
__sclose`), and `StdioUp` carries `StdoutTail` (`stdout`'s `_close`, `_ub`,
`_lb`) and `FdsStd` (`fds[0]`, `fds[2]` after `fs_init`). They are
established where `stdout` leaves boot: `__sinit` (`SinitPost.tail`: `std()`
leaves `_ub` … `_lock`, still the `.bss` zeros of `StdioBoot.files`;
`StdQuiet.of_std`, `StdoutTail.of_std`) and `fs_init` (`FstatPost.fds`,
threaded through `__smakebuf_r`, `__swsetup_r`, `sfvwrite_first`), and kept by
every write (`StdioRest.congrT` over `RestFoot`, `StdioRest.of_first`,
`StdoutAtW`/`StdioUp` congruences, `PrintSt.keep`). `ExitUp_Statement` now
takes the `CALL` invariant at `.up buf []` (the statement's shape kept; its
hypothesis is the invariant, which also places `ExitFree` in the C stack or
chunks in use apart from the buffer: `exitFree_kept`). `call_close` builds the
invariant at the new pointers before the complement and hands it to `exit`.

**The proof.**

* generated: `gen_lua_arms.py` helpers `stdio_exit_handler`, `_fwalk_sglue`
  (root `0x800340b4`), `_fclose_r` (root `0x800325e8`, stop `0x800326a8`),
  `__sclose`, `_close_r`, `_close`, the `__sfp` locks,
  `__retarget_lock_close_recursive`; `exit` without its stop `0x8002f87c`;
  `__sflush_r`'s read path (stop `0x80032734` instead of `0x8003271c`);
  `INDIRECT` for the three `jalr`s; `_free_r` a call node (`CALLEE_READS`).
  The existing `Hexit`, `Hsflush_r` segments only gained additions.
  `gen_lua_at.py --fn`: `stdio_exit_handler` (`AtF/ExitHandler`, four roots),
  `_fclose_r/stdin`, `_fclose_r/stderr` (`fclose_std`: one root each),
  `_fclose_r/stdout` (three roots: after `__sflush_r`, after `_free_r`).
* hand: `fclose_in`, `fclose_err` (one macro `quiet_run`), `fclose_out`
  (`sflush_sum`, `FreeR_Statement`), `exit_handler_sum`, `exit_run_up`
  (`kit_run` through `exit` and `__call_exitprocs` to the handler, then to
  `_exit`'s store, `Ret.exit_halt`), `exitUp_of_free`.

## 2. `luaE_extendCI` with `ci->next` NULL

**True or false.** As lane F1-13 stated it, false: `luaM_malloc_` adds the
block's size to `g->GCdebt` (`sd a5,24(s0)`, `s0 = G(L)`) before it returns,
and `ExtPost.keep` claimed every byte off the allocator's region, the block,
`ci->next`, `L->nci` and the stack kept. And `luaM_malloc_` calls
`g->frealloc` through a `jalr`, which nothing constrained.

**The statement and the invariant fixed.** `ExtPost.keep` is also off
`g->GCdebt`; `g->frealloc` (main.c's `l_alloc`, `0x8000172c`) is frozen in
`LuaStatic` (`luaStaticWords` gains `(g, 8)`, boot-checked by
`entryBaseCheck`), so `EntryDirty`/`CallDirty`'s `[g, g + 64)` is narrowed to
`[g + 16, g + 64)` (a `print` never writes `frealloc`/`ud`) and the keeps
that stated `¬ Rng g 64` with it (`PrintIn.keep_apart`, `PushPost`,
`TolLitPost`, `TolLitAt`, `call_keep`); `g->GCdebt` joins `CallLitDirty`;
`ExtCx` places the `lua_State`, the `CallInfo` and `g` (aligned: the entry
contract's and the invariant's `g_al`; `L` apart from `g->GCdebt` and from the
`CallInfo`; all three in chunks in use); `ExtPost.stdio` takes `stdout`'s
buffer apart from the links (at the call site from `Kept.nbuf`).
`MallocPost.brk_hi` bounds the break's growth (a strengthening of the A0
premise; dlmalloc's `malloc_extend_top` makes one page-rounded `_sbrk` and at
most one correction), which `ExtPost.brk` needs.

**The proof.**

* generated: `gen_lua_arms.py` helpers `luaE_extendCI`, `luaM_malloc_` (root
  `0x800110c0`, stops `size == 0` and the allocation failing), `l_alloc`
  (main.c's: `gen_lua_code.py`'s `DUP_FIRST` pins the first of the two static
  `l_alloc`s), `realloc`, `_realloc_r` (stop: a non-NULL `ptr`); `INDIRECT`
  `0x800110bc → 0x8000172c`; `_malloc_r` a call node reading `ra` too
  (`CALLEE_READS`: `_realloc_r` tail-jumps to it). `gen_lua_at.py --fn
  luaE_extendCI` (`AtF/ExtendCI`: two roots, the call node `0x8000172c`).
* hand: `lalloc_sum` (`kit_run` to `_malloc_r`, `MallocR_Statement`),
  `ext_ret` (root 3 to the return), `ext_post` (the post-memory facts),
  `extendCI_of_malloc` (root 0, the call, the slots read back); the stdio
  congruences generalised to `StdioFoot` (the stdio globals but the
  allocator's words, `AllocWords`): `StdioBoot.congrF`, `MemfsBoot.congrF`,
  `StdoutFresh.congrA`, `StdoutAtW.congrA`, `StdioUp.congrA`,
  `StdoutIn.congrA` (the old `congr`/`congrT` are one-line instances;
  `PrintSt.keep` goes through `StdoutIn.congrA`).
* One elaboration trap, recorded: `omega` and `assumption` recurse past
  `maxRecDepth` on `sp - 96 - 64` against literals when defeq unfolds
  `Nat.sub`; the proof keeps such terms out of the context (numeric facts
  normalised to literals first, `sp - 96 - 64` only in goals).

## 3. `luaD_poscall` with `C ≥ 2`

`HluaD_poscall` regenerated past `0x8000a4d8` (stops: the result copies
`0x8000a44c` and the close path `0x8000a5e4`; root: the loop `0x8000a4a4`).
Lane F1-12's worry, that regeneration changes `seg_8000a4b8_8000a4d0`: the
diff only adds segments and pins; `poscall_sum` rebuilt unchanged. The
statement needed two corrections: `n` (the C function's result count) is
`luaB_print`'s `0` (with `n > 0`, `moveresults` copies results instead of
filling nils, so `∀ n` was false), and `PcCxW` places the result slots
(`res_lo`, `res_hi`, `res_ci`, `res_L`: below the frame, apart from the
`CallInfo` and `L`), supplied from `CallNums` in `call_pos_run`. The proof is
four declarations: `pos_one` (`w = 1`), `posN_head`, `pn_loop` (`seg_loop`
over `compMem`, `OP_LOADNIL`'s shape), `posN_tail`; `pcw_post` the post. The
guards over `w` go through one normaliser `pn_guard` (Nat comparisons of
`ofNat` words: `fbeq`, `fbne`, `sge_nat`, `sge_neg`, `slt_nat`, then `omega`).

## 4. The stack growth

Growth cannot happen for the F1 entry programs: the entry contract gains
`VmEntryData.call_room` (`func + 16 (2 + maxstacksize) + 320 < stack_last`,
kernel-checked by `entryBaseCheck`; `gen_lua_boot_witness.py` checks it
natively), the `CALL` invariant `growFree` (`func + 16 (1 + maxstacksize) +
320 < stack_last`, from `call_room` at the entry and after `VARARGPREP`'s
one-slot move, kept by `call_close`), and with `call_bounds`'s `a + b ≤
maxstacksize` the growth states' `¬ (slot a + 16 b + 320 < stack_last)` is
refuted (`printGrow_none`). Room above the frame: 480 bytes (`while.lua`),
368 (`f1_ops.lua`); after `VARARGPREP` 464 and 352, against the 320 needed.
A program whose main frame leaves fewer than `LUA_MINSTACK` slots fails the
entry contract.

## Numbers

| file | hand lines | generated lines | CPU (user) | peak RSS | largest declarations |
|---|---|---|---|---|---|
| `Kit/ExitUp.lean` | 456 | at-lemmas 1,046 + 1,046 + 979 + 551 (`AtF/{FcloseIn,FcloseErr,FcloseOut,ExitHandler}`); segments 6,738 (nine helpers) + 481 (`Hexit`, `Hsflush_r` additions) | 46.8 s | 3.0 GB | `fclose_out`, `exit_handler_sum`, `exit_run_up` (100k, 200k]; `fclose_in`/`fclose_err` (50k, 100k] |
| `Kit/PoscallN.lean` | 235 | segments +1,734 (`HluaD_poscall`) | 29.7 s | 2.4 GB | `pos_one`, `posN_head` (100k, 200k]; `posN_tail` (50k, 100k] |
| the invariant (`StdioState`, `Stdio`, `Sinit`, `Setup`, `Smakebuf`, `Swsetup`, `SfvFirst`, `StdoutSetup`, `StdoutEmpty`, `Sfvwrite`, `Fflush`, `PrintIO`, `PrintSum`, `CallClose`, `HeapKeep`) | +≈330 | — | — | — | < 50k |
| `printGrow_none`, `call_room`/`growFree` (`CallOpen`, `EntryData`, `Boot/Check`, `Entry`, `Vararg`, `Rel`) | +≈35 | — | — | — | < 50k |
| `Kit/ExtendCI.lean` | 369 (with doc comments) | at-lemmas 259 (`AtF/ExtendCI`); segments and sites 4,101 (five helpers) | 25.0 s | 2.8 GB | `ext_post`, `extendCI_of_malloc` (50k, 100k]; `ext_ret`, `lalloc_sum` < 50k |
| the `ExtendCI` statement and invariant (`CallOpen`, `Rel`, `EntryData`, `Boot/Check`, `Entry`, `CallPrint`, `Tolstring`, `StdioState`, `PrintSum`, `Malloc`, generators) | +≈190 | boot witnesses regenerated | — | — | < 50k |

Full `lake build Lua`: 1,263 jobs, successful, the boot witnesses re-checked
in the kernel after `entryBaseCheck`'s new conjunct.

## Obstacles

1. **`ExitUp_Statement` and `PoscallN_Statement` were false as stated**
   (section 1, section 3): fixed by carrying the missing facts in the
   invariant and by stating `luaD_poscall` at `print`'s zero results with the
   result slots placed, never by weakening the conclusion.
2. **`ExtendCI_Statement` was false as stated** (section 2): fixed by
   freezing `g->frealloc`, narrowing the dirty region of `g`, adding
   `g->GCdebt` to the keep's exceptions and placing the objects (`ExtCx`);
   proved from `MallocR_Statement`, whose post gained `brk_hi`.
3. **`PrintRel_Statement`** (target 5) is lane F1-13's obstacle 1 unchanged:
   not attempted.

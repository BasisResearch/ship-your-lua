# Lane F1-9: toward `SimArm .CALL`: `__sfvwrite_r`'s loop, `fwrite`, groundwork for the first write

Base: main `34e183a`. Route: CLAUDE.md's callee-context rows (lane F1-8),
`seg_loop` for the loop. Lines are non-blank, non-comment lines (`--` lines
and `/- … -/` blocks dropped). CPU and peak memory are one `lake env lean
<file>` each (`/usr/bin/time -v`: user time, maximum resident set). Heartbeats
are per declaration, `Elab.async false`, bracketed by rerunning the file
under `maxHeartbeats` 25k, 50k, 100k, 150k (default budget 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1. `SfvwriteLbf_Statement` | **proved** | `Kit.sfvwrite_lbf` (`Lua/Vm/Sim/Kit/Sfvwrite.lean`) |
| — `FwriteStdout_Statement` | **proved** | `Kit.fwrite_stdout := fwrite_stdout_of_sfv sfvwrite_lbf` |
| 2. `StdoutSetup_Statement` | open; groundwork | `__sinit`'s at-lemmas build (`Lua/Vm/AtF/Sinit.lean`); obstacles below |
| 3. `luaB_print` per value class | open | not started |
| 4. `luaD_precall` (C path), `luaD_poscall`, the relation facts | open | not started |
| 5. `SimArm .CALL` | open | `OpenArms.CALL` stays |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists `sfvwrite_lbf`, `fwrite_stdout`, `sfv_turn`,
`sfv_flush`, `sfv_move`, `sfv_swrite`, `sfv_mc`, `sfv_store`).

## 1. `__sfvwrite_r`'s line-buffered loop

The loop is `seg_loop` over the head `0x80033dac` on `2·len + [buffer full]`
(a fill of a full buffer consumes nothing but empties it; every other turn
consumes at least one byte). The invariant `SfvSt` (named fields): `stdout`
holding `pend` (`StdoutAtW`, its `_w` a parameter), `StdioUp`, the console
`o = pushes o₀ out` with `out ++ pend = pend₀ ++ (the q bytes consumed)`,
the saved frame `[sp - 88, sp)`, and `SfvKeep` of the caller's bytes.

The generator does the case analysis; the hand proof is one lemma per root:

* **roots** (`gen_lua_at.py`, `FNS["__sfvwrite_r"]`): the entry; the head
  `L`; the body `D` (`0x80033db0`, newline distance known: reached from the
  head and both `memchr` returns); the step size `S` (`0x80033dbc`, `s =
  min(len, nldist)`, so the copy/write/fill paths are generated once for both
  minima); the newline distance `N` (`0x80033e00`, after a copy or a write);
  the tail `T` (`0x80033e0c`, `uio_resid -= w`, the cursor); the call
  returns. 155 → 51 at-lemmas. Every root shares one atom layout
  (`fresh_at`: `s2`…`s9` at `X.n 20 … 25`), so a root's context is the
  previous one re-bound (`FCx.set`, evaluated by `sfv_set`).
* **splices** (one per callee, each with ≥ 2 users but `sfv_swrite`):
  `sfv_mc` (`memchr_nl`, both return values; head and entry), `sfv_move`
  (`memmove_sum`; copy and fill), `sfv_swrite` (`swrite_sum`; the direct
  write), `sfv_flush` (`fflush_r_stdout`; after a newline and after a fill);
  `stdout`'s own stores by `sfv_store` (`_p`, `_w`: `sfv_push` for a copy,
  `sfv_fill` for a fill).

| piece | hand lines | generated lines | CPU / peak | heaviest declarations |
|---|---|---|---|---|
| library (invariant, values, memory facts, splices, stores) | 512 | — | (in the file below) | `sfv_entry` 100k–150k |
| roots: `sfv_tail` 32, `sfv_nld` 47, `sfv_copy` 36, `sfv_write` 32, `sfv_fillp` 50, `sfv_size` 46, `sfv_body` 23, `sfv_mcret0/1` 36, `sfv_mc` 33, `sfv_turn` 23, `sfvwrite_lbf` 46 + `sfv_entry` 18 | 422 | at-lemmas 1,248 (51); segments + sites of `__sfvwrite_r` 9,393 | `Kit/Sfvwrite.lean`: 43.2 s / 2.8 GB; at-lemmas 101.8 s / 2.8 GB | `sfv_fillp`, `sfv_size` 50k–100k; `sfvwrite_lbf` ≤ 100k; the rest ≤ 50k |
| `fwrite` (`fwrite_stdout`) | 1 | — | — | — |

Setup (generators): `gen_lua_at.py` +52 (the roots, `fresh_at`, `jr` to a
literal target, `__sinit`'s spec), `gen_lua_arms.py` +25 (`INDIRECT`: an
indirect call through a known `FILE` hook carries the callee's reads, so the
`jalr` to `__swrite` keeps `a3`; `__sinit`'s helpers; sanitized module and
pin names), `syi/{disasm_to_sites,gen_sites,disasm_to_segment}.py` +8 (`jr
off(rs1)`). Statement changes (no proved statement weakened):
`StdoutAt` became `StdoutAtW` with `room ≤ 1024` (`StdoutAt` its
abbreviation), `SfvwriteLbf`/`FwriteStdout` carry the callees' stack depth
(3 KiB / 4 KiB below `sp`, `StdoutKeepD`) and `errno` below `src`.

## 2. The first write: groundwork

`__sinit`'s at-lemmas are generated and build (48, one path: `std()` of the
three `FILE`s walked through `global_stdio_init`, `memset`'s short path — a
computed jump into its `sb` chain, now followed by the walker — and the no-op
locks): 985 generated lines, 77.4 s / 2.5 GB. `global_stdio_init`'s epilogue
is a root whose loads read the saved slots of the root memory (`rcells`).

## Obstacles (with evidence)

1. **The callee specs did not compose as stated.** `SfvwriteLbf_Statement`
   asked `buf + 2048 ≤ sp` and kept everything below `sp - 1024`, but
   `_fflush_r` (at `sp - 96`) needs `buf + 3072 ≤ sp - 96` and clobbers down
   to `sp - 96 - 2048`; `FwriteStdout_Statement` likewise. Restated with the
   depths; `fwrite_stdout_of_sfv` follows.
2. **`StdoutAt` was not an invariant of the real buffer.** A copy of exactly
   the room fills the buffer (`|pend| = 1024`, `room : < 1024` false), and the
   fill path stores `_p` without `_w` before `_fflush_r` (the flush resets
   `_w` unread). `StdoutAtW` (the word a parameter, a full buffer allowed);
   the flush summaries take it.
3. **A `jalr` through a `FILE` hook dropped the callee's argument.** The
   liveness fixpoint stopped at the indirect call, so `seg_80033de0_80033df4`
   did not carry `a3` (= 1024) and `swrite_sum`'s `swPre` could not be met.
   `gen_lua_arms.py` `INDIRECT`.
4. **Definitional unfolding of the console.** Re-rooting after `__swrite`
   with the console `pushes o (bytesAt m p 1024)` in the context ran past the
   recursion limit (`isDefEq` unfolds `pushes` over 1024 bytes); the console
   is generalised to a variable first.
5. **`__sinit`'s summary.** Forwarding the epilogue's eight saved slots
   through the 65 stores of the three `std()` (`fat_rd` on `m32`) reaches
   the recursion limit (`maximum recursion depth`, not a heartbeat bound).
   The next cut: the three `__retarget_lock_init_recursive` calls as abstract
   calls, each a root carrying the stack slots (`carried`), so no chain is
   longer than one `std()`. Also, `StdioBoot` lacks `_REENT->__cleanup = 0`,
   which `_fwrite_r`'s `CHECK_INIT` and `__sinit` read (`stdioCheck` would
   check it on the traced entry).
6. **`_malloc_r` has no summary at Lua addresses.** The `SWP` step tables are
   regenerated, but syi's dlmalloc spec sits on its WHILE ledger (`DlHeap`,
   `AllocLedger`: PHASES A0, not ported). `__smakebuf_r`'s buffer (and every
   allocation `print` makes: `luaS_newlstr` for an integer, `luaE_extendCI`)
   needs it; a `MallocR_Statement` over `DlHeap.HeapAt` (the footprint: the
   free chunks, the top chunk, `__malloc_av_`, the `_sbrk` state) is the named
   premise to state next.

## What is left (the remainder)

* `StdoutSetup_Statement`: `__sinit` (obstacle 5), `_fwrite_r`'s
  `CHECK_INIT` path and `__sfvwrite_r`'s `cantwrite` path (a second spec
  without the `_flags` cell: after `__swsetup_r` it reads `0x2889`, before it
  `0x2009`), `__swsetup_r` → `__smakebuf_r` → `__swhatbuf_r` → `_fstat_r` →
  `_fstat` (`getfd` → `fs_init`, `memset` of the `stat`: `memset`'s block loop),
  `_isatty_r` → `_isatty`, `_malloc_r` (obstacle 6).
* `IntegerToStr_Statement`, `luaB_print`, `luaD_precall`'s C path,
  `luaD_poscall`, the relation facts and `SimArm .CALL`: as in lane F1-8's
  remainder.

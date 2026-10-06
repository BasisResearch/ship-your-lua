# Lane F1-8: toward `SimArm .CALL`: callee-context rows, and `print`'s stdio callees on them

Base: main `6f31b36`. Route: CLAUDE.md's A1 row (round 4: segment-local
at-lemmas), extended to C callees. Lines are non-blank, non-comment lines
(`--` lines and `/- … -/` blocks dropped). CPU and peak memory are one
`lake env lean <file>` each (`/usr/bin/time -v`). Heartbeats are per
declaration, elaborated synchronously (`Elab.async false`), in
`maxHeartbeats` units (default budget 200k).

## Result

| target | status | theorem / file |
|---|---|---|
| 1. callee-context rows (`At`/`Loc`/`Cx` and `gen_lua_at.py` for a callee, keyed by entry pc) | **landed** | `Lua/Vm/Sim/Kit/AtFn.lean` (`FCx`, `fat_seg`, `fat_close`, `fat_mem`, `fat_rd`, `fat_run`, `fat_call`, `fat_cmp`, `fcx_ok`), `scripts/gen_lua_at.py --fn` (`FNS`), `Lua/Vm/AtF/{Fflush,Fflush_r,Memmove,Memchr,Sfvwrite}.lean` |
| 2a. `FflushStdout_Statement` | **proved** | `Kit.fflush_stdout` (`Kit/Fflush.lean`) |
| 2b. `FwriteStdout_Statement` | open; callees proved | `Kit.memmove_sum` (`Kit/Memmove.lean`), `Kit.memchr_nl` (`Kit/Memchr.lean`), `Kit.fflush_r_stdout` (`Kit/Fflush.lean`); `__sfvwrite_r`'s 155 at-lemmas build (`Lua/Vm/AtF/Sfvwrite.lean`) |
| 2c. `StdoutSetup_Statement` | open | not started (below) |
| 2d. `IntegerToStr_Statement` | open | not started (below) |
| 3. `luaB_print` per F1 value class | open | not started |
| 4. `luaD_precall` (C path), `luaD_poscall`, the relation facts | open | not started |
| 5. `SimArm .CALL` | open | `OpenArms.CALL` stays |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists `fflush_stdout`, `fflush_r_stdout`, `sfl_mid32`,
`flush_fin`, `memmove_sum`, `memchr_nl`, `mc_hz`).

## 1. The callee-context rows

Lane F1-6 wrote one context macro and one pin normaliser per helper
(`wr_ctx`, `sfl_ctx`, `sfl_norm`, …) because the at-lemma rows existed only
over an arm context. The callee version:

* **Context** `FCx`: Nat atoms `X.n i` (`sp`, pointers, counts: addresses are
  affine in them), words `X.b i` (`ra`, the caller's `s0`–`s11`, data), the
  root memory `X.m` and console `X.o`. A *root* is a fresh context: the
  callee's entry, a loop head (`loops`, with its own facts `Ok_<loop>`), or
  the return from a call whose effect is abstract (`calls`: the summary
  proof splices the callee there; the callee-saved registers survive, the
  loop registers it re-binds are fresh atoms of the return's root, the
  stack stores the callee keeps are carried as facts).
* **Rows and memories** are `@[at_row]` abbreviations over `X`, printed in a
  canonical form (`BitVec.ofNat 64 (Nat term)`, `bytesT<w> X.m a`; a Nat
  subtraction where the atoms' lower bounds make it exact, `2^64 - x` where
  `x` is bounded, `BitVec` subtraction otherwise). A value the walk cannot
  put in canonical form is the segment's own post-pin term with its
  parameters replaced by the row's values, so it meets the segment
  syntactically; a store of such a value takes its data from the segment's
  post-memory term.
* **What a path reads** is a hypothesis of the at-lemma: a `FILE` field
  (`cells`), a structure the caller passes or a frame slot (`rcells`), a
  stack slot kept across a call; and a branch outcome over Nat atoms is a
  hypothesis (`hf*`) of the path's later at-lemmas (the guard of one segment
  is the side condition of the next).
* **Proofs**: `fat_seg` (the segment, side conditions by `kit_disch`, the
  return target by `fat_ret`, guards by `fat_guard`/`fat_gnd`), `fat_close`
  (the post-state normalised once by `fat_rd`, the pins by `at_pins`, the
  memory by `fat_mem`, structural: never a `rfl` across a store chain);
  `fat_run` chains them by pc and row name (guards closed by `fat_hyp`:
  `with_reducible assumption`, `omega`, `fat_cmp` over Nat atoms).
* **Calls**: a callee with segments is walked through (`ret` to the literal
  `ra`); a summary that keeps the memory is a generated call at-lemma
  (`pure`, `fat_call`); an abstract call ends the root.

## Per summary

| summary | hand lines | generated lines (at-lemmas; segments + sites) | CPU / peak (hand file) | largest declarations (heartbeats) |
|---|---|---|---|---|
| library `Kit/AtFn.lean`, `Kit/Stdio.lean` | 327 + 61 | — | 3.0 s / 2.0 GB; 1.4 s / 2.0 GB | ≤ 3.3k |
| `fflush`, `_fflush_r` (`fflush_stdout`, `fflush_r_stdout`, the shared `sfl_mid32`, `flush_fin`) | 117 | 434 + 404 (16 + 14 at-lemmas); 3,344 + 3,303 | 5.6 s / 2.1 GB; generated 21.8 s + 19.1 s / 2.1 GB | `fflush_stdout` 30.2k, `fflush_r_stdout` 26.4k; generated ≤ 32.4k |
| `memmove` (`memmove_sum`: `mm_bytes`, `mm_words`, `mm_blocks`, the entry; `MoveOut`) | 330 | 1,152 (50 at-lemmas); 4,787 | 23.0 s / 2.3 GB; generated 65.6 s / 2.6 GB | `memmove_sum` 126.4k, `mm_blocks` 98.3k; generated `at_8003b4e8_8003b4f4_t` 166.3k |
| `memchr` (`memchr_nl`: `mc_bytes`, `mc_words`, `mc_align`, the entry; the word test `mc_hz`) | 321 | 993 (39 at-lemmas); 3,642 | 13.2 s / 2.2 GB; generated 30.0 s / 2.2 GB | `mc_align` 73.6k; generated ≤ 23.2k |
| `__sfvwrite_r` (line-buffered) | — (open) | 2,959 (155 at-lemmas, 9 roots); 9,393 | generated 159.4 s / 2.9 GB | generated `at_80033c00_80033c2c_1` 106.2k |

Setup (generators): `gen_lua_at.py` +895 lines (the callee walker, `FNS`),
`gen_lua_arms.py` +33 (`HELPERS` for `fflush`, `memmove`, `_fflush_r`,
`memchr`, `__sfvwrite_r`; a helper whose code pins are split into parts
fetches through the part's pin), `gen_lua_code.py` +2 (`EXTRA`). Generated
in all: 5,942 at-lemma lines, 26,469 segment and site lines, 10,230 code-pin
lines.

## Obstacles (with evidence)

1. **A `rfl`/`decide`/default-transparency `assumption` on a machine term
   escapes `first`.** `fat_side`'s `rfl` on an address goal and
   `fat_hyp`'s `assumption` against an unrelated `Bool` guard unfolded
   `BitVec.ofNat` past the recursion limit (`maximum recursion depth`,
   a runtime exception `first` does not catch; memchr's word-loop exit and
   `__sfvwrite_r`'s flush path). The closers now decide only ground goals
   (`ground_decide`), compare with reducible transparency, and run
   `fat_ret` only on goals about `Sail.BitVec.update`.
2. **A segment with several stores states its data exponentially.** Each
   load after a store reads through the segment's own store chain, so a
   4-store segment's post-state is a tree of nested copies; `fat_mem`'s
   `rfl` and per-store `at_eq` calls timed out (`memmove`'s 32-byte block).
   Fixed twice: `fat_close` normalises the post-state with one `simp` (one
   cache), and the block body is cut after each store (`HELPERS` roots
   `0x8003b4d8`, …). The cut segment is still the heaviest generated
   declaration (166.3k).
3. **A finite `decide` over a goal `simp` produced blew 22 GB.** The `w8end`
   lane lemma first proved by `revert r; decide` after `simp only
   [BitVec.toNat_and, …]` took 150 s and 22 GB (killed under the 12 GB cap);
   stated on the ground BitVec form (`w8end_lane`, 24 lanes) it takes under a
   second. The same happened to `congrArg (Nat.testBit · k)` on a
   `simp`-produced `toNat` equation in `mc_hz`; the `getLsbD` form at the
   `BitVec` level is instant.
4. **Roots multiply unless a call's return re-binds the loop registers.**
   `__sfvwrite_r` with the callee-saved registers kept as they were gave 39
   roots and 366 at-lemmas (each predecessor's row a new root); with the loop
   registers re-bound as fresh atoms at each return (`fresh`), 9 roots and
   155 at-lemmas. The remaining hand cost of `FwriteStdout_Statement` is one
   splice per call return and the loop invariant: the next step.

## What is left (the remainder, exactly)

* `FwriteStdout_Statement`: the line-buffered loop of `__sfvwrite_r` over
  its 9 roots (`seg_loop` on the bytes left; invariant: `StdoutAt M buf pend`
  with `out ++ pend = pend₀ ++ bytesAt m src c`, `resid = n - c`; one splice
  per return: `memchr_nl` (×2 return values), `memmove_sum` (copy and
  partial fill), `fflush_r_stdout` (after a newline and after a partial
  fill), `swrite_sum` (a chunk of ≥ 1024 bytes into an empty buffer)), then
  `fwrite` → `_fwrite_r` (generate with `__muldi3` as a `pure` call, the
  locks inline, `__sfvwrite_r` abstract).
* `StdoutSetup_Statement`: `__sinit` (`global_stdio_init`, its `memset`),
  `__swsetup_r`, `__smakebuf_r` (`_fstat` → `fs_init`, `_malloc_r` on the
  `SWP` allocator route, `_isatty`), each a callee on the route.
* `IntegerToStr_Statement`: `snprintf` → `_svfprintf_r` (3,212
  instructions; the `%lld` path with `__udivdi3`/`__umoddi3`, `__ssprint_r`
  → `__ssputs_r` → `memmove`).
* `luaB_print` (integer, string, boolean, nil; floats under the named
  premise `G14From`), `luaD_precall`'s C path and `luaD_poscall`, the
  relation facts (stdio state, `LuaStateAt.next`, heap growth with `ι` and
  `Complement.own`, `ci->top`, `Complement.exit` after a print) and
  `SimArm .CALL`: not started.

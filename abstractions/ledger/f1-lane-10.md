# Lane F1-10: toward `SimArm .CALL`: the first write's set-up

Base: main `ad9b9a8`. Route: CLAUDE.md's callee-context rows (lanes F1-8/9).
Lines are non-blank, non-comment lines (`--` lines and `/- … -/` blocks
dropped). CPU and peak memory are one `lake env lean <file>` each
(`/usr/bin/time -v`: user time, maximum resident set). Every new declaration
elaborates within the default 200k heartbeats (no option raised); the
summaries were split into one lemma per root run and per root memory where a
single declaration ran out (below).

## Result

| target | status | theorem / file |
|---|---|---|
| 1a. `__sinit` (lane F1-9's obstacle 5) | **proved** | `Kit.sinit_boot` (`Kit/Sinit.lean`): the two lock-init calls are roots carrying the stack slots (`gen_lua_at.py` `calls`), so no store chain is longer than one `std()`; the epilogue reads the saved slots as root 2's carried facts |
| 1b. `_REENT->__cleanup = 0` in `StdioBoot`, `stdioCheck` | **done** | `StdioBoot.cleanup`, `stdioCheck`, `gen_lua_boot_witness.py`; both boot witnesses re-checked (`Witness.While`, `Witness.F1Ops`, 258 s each, 3.3 GB) |
| 1c. `MallocR_Statement` | **stated** (named premise) | `Kit/Malloc.lean`; not cheap via `AllocSteps` (below) |
| 1d. `StdoutSetup_Statement` | **proved from `MallocR_Statement`** | `Kit.stdoutSetup_of_malloc` (`Kit/StdoutSetup.lean`) over `sinit_boot`, `sfvwrite_first` (`Kit/SfvFirst.lean`), `swsetup_sum` (`Kit/Swsetup.lean`), `smakebuf_sum` (`Kit/Smakebuf.lean`), `fstat_sum`, `isatty_sum` (`Kit/Setup.lean`) |
| 2. `luaB_print` per value class | open | not started |
| 3. `luaD_precall` (C path), `luaD_poscall`, the relation facts | open | not started; obstacle 3 below |
| 4. `SimArm .CALL` | open | `OpenArms.CALL` stays |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists `sinit_boot`, `fstat_sum`, `isatty_sum`,
`smakebuf_sum`, `swsetup_sum`, `sfvwrite_first`, `stdoutSetup_of_malloc`,
`DlHeap.HeapAt.congr`).

## `MallocR_Statement`: why a premise

`VsaIris/MallocRun.lean` (copied) keeps `MallocLocalRun` — the
instruction-level `_malloc_r` — as an assumption; ship-your-interpreter proves
it (`VsaIris/Vsa/MallocRunAll.lean`, `mallocLocalRun_proved`) at its WHILE
addresses over ~9,700 lines of `VsaIris/Vsa/Malloc*.lean` on its allocation
ledger. Here only the step tables are at Lua addresses
(`VsaIris.Vsa.AllocSteps`). A summary at Lua addresses is the A0 port, not
cheap. The premise: with room for one `_sbrk` (`brk + n + 16384 ≤
__heap_end`), `_malloc_r(_REENT, n)` returns a 16-aligned block of a chunk
now in use, fresh, below the new break; `HeapAt` holds again; every chunk in
use stays in use; it writes only its globals (`nm -S`), the arena off the
chunks in use (payload to the next `prev_size`) and 1 KiB of stack.

## Per piece

| piece | hand lines | generated lines | CPU / peak (hand file) |
|---|---|---|---|
| `__sinit` (`Kit/Sinit.lean`: `FileStd`, `SinitPost`, 3 root keeps, 3 `std()` field lemmas, the frame, `sinit_boot`) | 174 | at-lemmas 934 (46, 3 roots) | 53.3 s / 2.0 GB |
| `_malloc_r` premise (`Kit/Malloc.lean`) | 36 | — | — |
| regions (`Kit/HeapKeep.lean`: `Agree`, `Below`/`Rng`/`StdoutW`/`MallocW`, `HeapReads`, `ChunkWalk`/`BinChain`/`HeapAt.congr`) | 151 | — | 1.8 s / 1.8 GB |
| `_fstat_r`, `_isatty_r` (`Kit/Setup.lean`) | 87 | 856 + 241 (33 + 8 at-lemmas; `memset`'s misaligned head and unrolled block loop inside `_fstat`) | 15.8 s / 2.1 GB |
| `__smakebuf_r` (`Kit/Smakebuf.lean`: 4 root runs, 4 root memories, `smb_pre`, `smakebuf_sum`) | 249 | 386 (11 at-lemmas, 4 roots) | 11.7 s / 2.2 GB |
| `__swsetup_r` (`Kit/Swsetup.lean`) | 135 | 295 (9, 2 roots) | 5.2 s / 2.0 GB |
| `__sfvwrite_r` first write (`Kit/SfvFirst.lean`: width lemmas, `StdoutFresh`, `sfs_pre`, `sfvwrite_first` handing over to lane F1-9's loop at the first `memchr`) | 308 | 375 (13, 2 roots) | 23.1 s / 2.6 GB |
| `fwrite` first write (`Kit/StdoutSetup.lean`: `fws_pre`, `stdoutSetup_of_malloc`) | 247 | 657 (23, 3 roots) | 18.4 s / 2.3 GB |

Setup (generators, libraries): `gen_lua_at.py` +150/−24 (`root_cells`
with `None`, `rcellsw`, `ends`, `jalr off(rs1)`, atom residues `res` for
`andi` masks, same-atom comparisons decided, the six `FNS` entries),
`gen_lua_arms.py` +37 (six helpers; `memset`'s block loop and internal
`jalr`, `RET_TO` liveness for its `sb` chain's `ret`; `_fwrite_r`'s and
`__sfvwrite_r`'s set-up paths no longer stops), `gen_lua_code.py` +4,
`AtFn.lean` +105 (`ground_bv` for ground shifts and masks, `and_lowmask`,
`fat_gnd` by `fat_cmp`, an `at_eq_ext` rule for residues). Generated:
segments, sites and code pins +25,172 lines.

## Obstacles (with evidence)

1. **`ground_bv` must not fold immediates or fields at top level.** Folding
   `sign_extend k#12` and `extractLsb k 5 0` everywhere broke lane F1-8's
   `memmove` at-lemmas (`at_8003b4f4_8003b518_t`: the guard hypothesis keeps
   `sign_extend 0x018#12`, and `shl_ofNat` stops matching `5#6`). It folds
   only shifts, masks and xors of ground terms; immediates and sums stay.
2. **Keeps stated per access width are too coarse.** `SinitPost.keep` first
   excluded `a + 8 ≤ __cleanup` (an 8-byte condition on a 1-byte address),
   which failed for the bytes just below the word (`StdoutSetup.lean`, omega
   counterexample `0x8005d1f9 ≤ a ≤ 0x8005d1ff`); byte-precise now. Likewise
   the set-up regions are exact fields (`StdoutW`), so `_file`, the cookie
   and the hooks survive.
3. **`HeapAt` after a `print` needs presence-level keeps.** `HeapAt` reads
   with `rd64` (bytes present), but the line-buffered loop's keep (`SfvKeep`,
   lanes F1-6..9, through `StdoutKeep`) is byte-total (`bytesT1`, `getD 0`).
   So `StdoutSetup_Statement` grants the heap at the set-up's memory `M`
   (`SetupPost.grant`) and keeps `M → m'` only by `SfvKeep`. Re-establishing
   `RuntimeMem.heap` after `CALL print` needs the stdio summaries' keeps
   restated as `Agree` (`getElem?`), or presence of the arena carried as an
   invariant.
4. **Single declarations ran out of heartbeats.** `__smakebuf_r`'s summary
   as one proof (four roots, three splices) reached the whnf timeout at the
   declaration; split into one lemma per root run (`smb_run0..3`), per root
   memory (`smb_m1..5`) and the prefix (`smb_pre`). `omega` with `heapEnd`
   in context hit the recursion limit twice; a generalised `heapEnd` fixes it.
5. **A first write of 0 bytes is not covered.** `__sfvwrite_r` returns at
   once for `uio_resid = 0` without the set-up; `print("")` sets `stdout` up
   at its newline. `StdoutSetup_Statement` assumes `n ≥ 1`.

## What is left (the remainder)

* `MallocR_Statement` (A0: port ship-your-interpreter's dlmalloc proof to
  the Lua addresses' step tables).
* `IntegerToStr_Statement`, `luaB_print` per value class, `luaD_precall`'s C
  path, `luaD_poscall`, the relation facts (stdio state, `LuaStateAt.next`,
  heap growth with `ι`/`Complement.own`, `ci->top`, `ExitOk` after a print)
  and `SimArm .CALL`: not started; obstacle 3 first.

## Gate

`abstractions/gate.py`: ok (`a1-kit-arm` 58 cases, first 2.1, last 2.9).
`scripts/check.sh` (all stages, including the full `lake build Lua Vsa VsaIris`, 4 min 29 s wall, 3.5 GB peak, and stage-6 axioms): OK.

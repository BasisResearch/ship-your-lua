# Lane F1-6: toward `SimArm .CALL` (`print`): the console end of the stdio chain

Base: main `b90a992`. Route: the `SegSt` helper summaries the arms compose
with (`gen_lua_arms.py` `HELPERS`, `kit_run`, `seg_loop`, `SegSt.call`).
Lines are non-blank, non-comment lines (`--` lines and `/- … -/` blocks,
docstrings included, dropped). CPU and peak memory are one `lake env lean
<file>` each (`/usr/bin/time -v`); heartbeats are per declaration,
elaborated synchronously (`Elab.async false`), in `maxHeartbeats` units
(default budget 200k).

## Result

| target | status | theorem |
|---|---|---|
| the `tohost` console store as a segment step | **proved** | `Lua.Vm.Sim.Kit.segSt_putc` (`Kit/Console.lean`), instance `write_putc` |
| htif.c `_write(1, buf, n)` on the console | **proved** | `Kit.write_sum` (`Kit/Write.lean`; the loop `write_loop` by `seg_loop`) |
| newlib `_write_r`, `__swrite` | **proved** | `Kit.write_r_sum`, `Kit.swrite_sum` (`Kit/Swrite.lean`) |
| `__sflush_r(ptr, stdout)` on the line-buffered `stdout` | **proved** | `Kit.sflush_sum` (`Kit/Sflush.lean`): the pending bytes to the console through the `FILE`'s `_write` hook, `0` returned, `StdoutAt m' buf []`, `SflOut` (what it keeps) |
| `fwrite(src, 1, n, stdout)`, `fflush(stdout)`, the first write's set-up, `lua_integer2str` | **stated** | `FwriteStdout_Statement`, `FflushStdout_Statement`, `StdoutSetup_Statement`, `IntegerToStr_Statement` (`Kit/CallSpec.lean`) |
| `luaB_print`'s formatting, `luaD_precall`/`luaD_poscall`, `SimArm .CALL` | **open** | the traced path and the relation facts `VmRel` lacks: PHASES.md A1 (`CALL`) |

Axioms of every new theorem: `[propext, Classical.choice, Quot.sound]`
(check.sh stage 6 lists them). `scripts/check.sh` passes (all stages);
`abstractions/gate.py`: `a1-kit-arm` 52 cases, ok.

## Setup (generators and library)

| piece | file | lines |
|---|---|---|
| `sh` stores: `writeMap2`, `exec_sh` (over the copied `exec_sh_bm`), `getElem?_writeMap2_out` | `Vsa/Sim/StoreHalf.lean` | 31 |
| `TextLoaded.writeMap2` (imported by `sh` segments only, so `Text.lean` and its 1,400 dependants do not move) | `Lua/Vm/Arms/TextHalf.lean` | 8 |
| a linking `jalr` (indirect call): `RegsOk.jalr` | `Lua/Vm/Arms/RegsOkJalr.lean` | 17 |
| generators: `sh` and `jalr` site/segment classes (`gen_sites.py` `emit_sh`/`emit_jalr`, `disasm_to_segment.py`, `gen_segment.py`), `HELPERS` for `_write`, `_write_r`, `__swrite`, `__sflush_r`, `TOHOST_SEAMS` (the console store a stop; liveness through it), conditional imports; code pins (`EXTRA`); layout fields (`FILE` `_p` … `_lock`, `_flags2`, `_reent.__cleanup`, `__swrite`) | `scripts/{gen_lua_arms,gen_lua_code,gen_lua_layout}.py`, `scripts/syi/{gen_sites,gen_segment,disasm_to_segment}.py` | 143 py (+), 19 (−) |

## Per summary

| summary | hand lines | generated lines (segments, sites, code pins) | CPU (user) / peak | largest declarations (heartbeats) |
|---|---|---|---|---|
| console seam `segSt_putc`, `pushes`, `output_pushes` | 103 (`Kit/Console.lean`) | — | 1.2 s / 1.84 GB | `gprGet_putcFrame` 4.0k, `segSt_putc` 0.8k |
| `_write` | 211 (`Kit/Write.lean`, incl. `AbiFrame`, `bytesAt`, the guard lemmas) | 2,922 (`Segs/Hwrite`, `Sites/Hwrite`) + code pins | 9.4 s / 2.00 GB; segments 9.7 s / 1.95 GB | `write_sum` 82.1k, `write_loop` 45.7k |
| `_write_r`, `__swrite` | 204 (`Kit/Swrite.lean`) | segments 4.0 s + 5.7 s | 7.0 s / 1.97 GB | `write_r_sum` 45.9k, `swrite_sum` 34.8k |
| `__sflush_r`, `StdoutAt` | 421 (`Kit/Sflush.lean`: 9 summaries/lemmas, the forwarding `simp` `sfl_fwd`, the read-through lemmas for `writeMap2`/`writeMap4`) | segments 11.7 s / 2.06 GB, sites 4.6 s | 31.2 s / 2.24 GB | `sfl_pro2` 120.9k, `sfl_outW` 34.8k, `sfl_head` 33.3k, `sfl_pro1` 31.4k |
| statements | 60 (`Kit/CallSpec.lean`) | — | 0.9 s | — |

Generated in all: 16,174 lines (8 segment/site modules, 8 code-pin modules).

## What the emulator shows `print` runs (`c/tests/while.lua`, `--trace-all`)

* `stdout` after the first `print`: `_flags = 0x2889` (`__SWR | __SLBF |
  __SMBF | __SNPT | __SORD`), `_file = 1`, `_bf._base = _p = 0x80072f50` (a
  1024-byte `_malloc_r` chunk), `_bf._size = 0x400`, `_lbfsize = -1024`, `_w`
  counting down from `0` with the pending bytes, `_cookie = stdout`,
  `_write = __swrite` (`StdoutAt`'s fields).
* `print(i)` for an integer: `luaL_tolstring` → `lua_pushfstring` →
  `luaO_pushvfstring` → `snprintf` → `_svfprintf_r` (with `__udivdi3`,
  `__umoddi3`, `__ssprint_r` → `__ssputs_r` → `memmove`) → `luaS_newlstr` →
  `internshrstr` → `luaC_newobj` → `_malloc_r`; `fwrite` → `_fwrite_r` →
  `__sfvwrite_r` (`memchr`, `memmove`); the `"\n"` `fwrite` reaches
  `_fflush_r` → `__sflush_r` → `__swrite` → `_write_r` → `_write`; `fflush`
  → `__sflush_r` with nothing pending. The first `print` also runs
  `__sinit` (`global_stdio_init`, the Duff's-device `memset`),
  `__swsetup_r`, `__smakebuf_r` (`_fstat` → `fs_init`, `_malloc_r` →
  `_sbrk`, `_isatty`). `luaE_extendCI` does not appear on the second `print`
  (`ci->next` was allocated by the first).

## Obstacles (with evidence)

1. **`omega` and a literal-valued `def` atom.** `example (h : fileSize + 1536
   ≤ sp) : fileSize + 20 ≤ sp := by omega` (with `Lua.Vm.LayoutRt` imported)
   fails with `maximum recursion depth`, and so does the same with
   `tohostAddr`; a plain variable or a literal works. The summaries rewrite
   such atoms to literals before `omega` (`sflush_sum`'s `h4`, `h5`), and
   `errnoAddr` is a `def`, not an `abbrev` (as an `abbrev` `omega` recursed on
   it inside `have … := by omega`).
2. **Runtime exceptions escape `first`.** A `kit_guard_ext` closer `exact
   wr_fd` tried on the wrong guard unified two `Bool` computations through
   `bytesT4` of a free memory and raised `maximum recursion depth`, which
   `first` and `kit_run`'s `try … catch` do not catch (a runtime exception):
   the whole `kit_run` failed. Every guard is now stated before `kit_run` and
   closed by `guard_assumption` (syntactic), or by a normalising `simp`
   followed by `decide`/`exact`.
3. **Store chains and the budget.** One declaration that runs five segments
   and normalises after each one costs 160–190k (`sfl_head`, inlined, 189.4k);
   split at segment boundaries into rows with normalised pins and memory
   (`sfl_pro1`, `sfl_pro2`, `sfl_pro`, `sfl_head`, `sfl_mid`, `sfl_ret`), every
   declaration is at most 121k.
4. **Forwarding by `simp` works here.** B-SEGLOCAL reported that `simp` would
   not forward loads through stores; here one `simp (disch := omega) only
   [bytesT8_wm8_out, bytesT8_wm4_out, b8_wm2_out, …, bytesT8_wm8_same, …]`
   (`sfl_fwd`, `sfl_rd`) forwards every read of `__sflush_r`'s 13-store
   memory (the out-lemmas' side conditions are `Nat` separations).
5. **A missing abstraction (duplication signal).** Each helper summary has
   its own context macro (`wr_ctx`, `wrr_ctx`, `sw_ctx`, `sfl_ctx`) and pin
   normaliser (`sfl_norm`/`sfl_tnorm`): the at-lemma rows (`At`/`Loc`) exist
   only over an arm context `Cx`. A callee-context version of the rows
   (entry pins as atoms, the callee's frame and the callers' stores as a
   log) would make these per-function macros generated, as `gen_lua_at.py`
   does for arms; `__sfvwrite_r` (311 instructions, 8 loops) and
   `_svfprintf_r` (1,523) should wait for it.
6. **`VmRel` cannot carry a `print`.** Its complement (`RuntimeMem`) holds
   neither the stdio state (`StdioBoot`/`MemfsBoot` before the first
   `print`, `StdoutAt … [] ∧ StdioUp` after), nor the heap's growth (the
   `stdout` buffer, the interned strings, the C `CallInfo`) with the intern
   map, and `LuaStateAt.next = 0` holds only until the first `CALL`. These
   are relation changes (lane F1-4 owns `Core`); PHASES.md A1 lists them.

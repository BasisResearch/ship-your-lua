# Phase 1: validation experiments

Outcome: **Lua 5.4.7 runs on the executable Sail RISC-V model.** The
bare-metal ELF prints `55\n2500\n36\n` for `while.lua` and exits 0 in
215,723 Sail steps. It agrees with native `lua` on all 18 difftest programs
across F1–F4, floats, coroutines, and the `io`/`os` libraries over the
in-image file system. The F1 bytecode semantics reproduces
the ELF's output on three programs by kernel-checked derivation. No blockers.

Measured 2026-09-30 on aws-dev. The ELF is `c/lua-riscv-htif.elf`, sha256
`c3224616601284958ff81ffd0e3b86758c9dc5232bb7aa3cab414e2e1229eec8`.
`make -C c riscv-htif` reproduces it bit for bit from a fresh clone.

## 1. Toolchain

* **Toolchain.** xPack `riscv-none-elf-gcc` **15.2.0-1**, linux-x64 tarball
  (sha256 `aaaa8060…a33758`, matching the release's `.sha`), installed
  under `~/toolchains/`. It bundles newlib 4.5.0.20241231. This is the
  release that built ship-your-interpreter's proof ELF (its `.comment` reads
  `xPack GNU RISC-V Embedded GCC arm64 15.2.0`, and its dtoa path is under
  `newlib-4.5.0.20241231`).
* **Flags.** `c/Makefile` uses the WHILE HTIF build's flags: `-march=rv64i
  -mabi=lp64 -mcmodel=medany -O2 -std=gnu11`.
  * The ISA is plain rv64i because the Lean emulator's model has no M/F/D.
  * Multiplication, division and all `double` arithmetic go through libgcc's
    soft routines.
  * Startup and linker script are WHILE's `crt0.S` and `link.ld`; the only
    change is a separate `.lua_chunk` region (below). The HTIF back end
    `htif.c` started as WHILE's and now has an in-image file system (§6).
* **Reproducibility check.** I rebuilt the WHILE ELF from ship-your-interpreter's
  `c/` with this Linux toolchain.
  * Every one of its 258 functions has the same size as in the committed
    proof ELF.
  * The images still differ, because newlib archive members are linked in a
    different order (a Linux vs macOS-arm64 toolchain build). The code is the
    same modulo relocations.
  * So the library proofs carry over as templates to regenerate at new
    addresses, not byte for byte. The census below measures the overlap.

## 2. The bare-metal Lua build (`c/`)

* **Source.** Lua **5.4.7**, vendored unmodified in `vendor/lua-5.4.7`
  (tarball sha256 `9fbf5e28…1e30`). Configuration is done by force-including
  `c/src/baremetal.h`:
  * a constant hash seed (`luai_makeseed`);
  * no `table.sort` pivot randomisation;
  * `'.'` as the decimal point;
  * `-DLUA_USE_JUMPTABLE=0`, so `luaV_execute` dispatches through one C
    `switch`;
  * on the ELF, `os.execute` has no shell (`system` is not linked);
  * on the host `lua` only, a clock frozen at 0, matching the ELF's (§6).
* **Libraries.** base, string, table, coroutine, io and os. There is no
  package, debug, math or utf8.
* **Collector.** `main.c` calls `lua_gc(L, LUA_GCSTOP)` right after
  `lua_newstate`, before any library is opened. In every traced run
  `luaC_step` is entered but returns at `!gcrunning`; no mark, sweep,
  atomic or free function ever executes. There is no `lua_close`.
* **Chunk.** `luac -s` (the host `luac` built from the same source) compiles
  it, and `c/src/chunk.S` embeds it in its own 64 KiB `.lua_chunk` section
  after `.bss`. Its length is stored in front as data.
  * As a result, `.text`, `.rodata`, `.data` and `_end` are **byte-identical
    for every program**.
  * This was checked on all 18 difftest ELFs and the 5 validation programs'
    ELFs: the md5s of `.text`, `.rodata`, `.data` and `.init_array` match.
  * One image pin (`Lua/Vm/Image.lean`) therefore serves every program.
* **Output and exit.** Output goes through HTIF (`htif.c`); `stderr` shares
  the console. Exit codes are 0 for ok, 1 for a load error, 2 for a runtime
  error and 3 for out of memory.
* **ELF.** 515,824 bytes on disk (323 KB of `.text`, the 64 KiB chunk region, symbols).
  It contains no `ecall` (`scripts/check.sh` stage 2).
  * `.text` is 322,760 bytes at `0x80000000`; `.rodata` is 55,776 bytes at
    `0x8004ecc8`.
  * `tohost` is at `0x8005c6c0`; `luaV_execute` at `0x8001bf68`; `luaB_print`
    at `0x80022f18`.
  * The chunk region is at `0x8005ecd0`; `_end` is `0x8006ecd0`.

## 3. Runs on the Sail model

The emulator is ship-your-interpreter's `lean_riscv_emulator`
(`riscv-lean/lean_emulator`, executable Sail RV64D model) — the one used for
its corpus cross-check (REVIEW2.md §4). Its speed is about 47k steps/s.

| `while.lua` (`c/tests/while.lua`, port of `while.wl`) | step |
|---|---|
| `main` entered (crt0 done) | 3,223 |
| `luaL_loadbufferx` entered (state + 6 libraries opened) | 177,029 |
| `lua_pcallk` entered (chunk undumped) | 181,019 |
| **`luaV_execute` entered** (the Layer A cut point) | **181,166** |
| exit store to `tohost` (exit 0, output `55\n2500\n36\n`) | 215,722 (215,723 steps total) |

Running the chunk takes 34,557 steps from VM entry. `luaV_execute`
dispatches 671 instructions, 15 distinct opcodes. The rest is `print`
through `luaL_tolstring`, `snprintf` and newlib stdio.

**Difftest** (`c/tests/difftest.sh`, 18 programs, `c/tests/difftest/`). The
comparison:
* Both sides run the same stripped `luac` chunk.
* The host side is `lua` built from the same source with the same
  `baremetal.h` (so `pairs` order agrees, and the clock is frozen at 0),
  with the collector stopped, in an empty environment with `TZ=UTC0`, in a
  scratch directory.
* The target side is the bare-metal ELF on the Sail emulator.
* Stdout and exit status (zero vs nonzero) are compared.

| program | covers | result | Sail steps |
|---|---|---|---|
| f1_arith | integer arithmetic, `//` `%` edge cases, wraparound, bitwise | PASS | 317,386 |
| f1_cond | if/elseif, and/or/not, repeat, nested loops | PASS | 401,320 |
| f1_for | numeric for edge cases, zero step error (pcall) | PASS | 210,874 |
| f1_while | = `while.lua` | PASS | 215,723 |
| f2_array | array part, `#`, SETLIST, nested tables | PASS | 267,005 |
| f2_next | **real `next` order** over string/int/float/bool keys | PASS | 319,539 |
| f2_tablelib | sort (with/without comparator), insert/remove/concat/unpack/pack/move | PASS | 256,973 |
| f3_closures | closures, shared upvalues, recursion (fib 15), varargs composition | PASS | 675,646 |
| f3_pcall | error objects, pcall/xpcall, error in deep recursion (`longjmp`) | PASS | 515,643 |
| f3_uncaught | uncaught error → exit 1 (host) / 2 (ELF) | PASS | 189,822 |
| f3_varargs | select, multret, 10,000-deep tail calls | PASS | 2,647,749 |
| f4_metatables | `__index/__add/__eq/__lt/__le/__len/__concat/__call/__tostring/__newindex` | PASS | 275,221 |
| f4_objects | inheritance chains, gmatch word count | PASS | 288,472 |
| f4_strings | string library, `format` (`%d %x %q …`), find/match/gsub/gmatch, coercions | PASS | 282,828 |
| f5_floats | `%.14g`, inf, −0.0, NaN, float `//` `%`, float for-loop (soft-float) | PASS | 491,495 |
| f6_coroutines | create/resume/yield/status/wrap, error inside a coroutine | PASS | 236,676 |
| f7_io | `io.open` in every mode, `read` formats, `seek`, `io.lines`, `io.input`/`io.output`, `io.open` errors (message and errno), `os.remove`/`os.rename`, a removed file read through its handle | PASS | 607,172 |
| f7_os | `os.time`/`os.clock` (frozen at 0), `os.date` (`!` and local, `*t`), `os.time{…}`, `os.getenv`, `os.exit(3)` after buffered output | PASS | 345,557 |

The result is 18/18. The step counts are 53k-57k higher than without
`io`/`os`, all of it before VM entry (opening the two libraries, and crt0
clearing a larger `.bss`). Printing a function value gives `function: 0x80022f18`,
the address of `luaB_print` (`c/tests/print_print.lua`). The semantics takes
this rendering as a parameter (`Host`); `Lua/Vm/Host.lean` instantiates it.

**Semantics check.** `Lua/Programs/Validation.lean` proves, by kernel
evaluation of a stepper that is proved sound for the inductive `Step`
(`run_sound`), that F1's `BcSem` produces exactly the ELF's output for:

* `while.lua`;
* `f1_ops.lua`, which uses every F1 rule family: `FORPREP`/`FORLOOP`, the
  `//`/`%` `-1` cases, `mininteger // -1`, `TESTSET`, `NOT`, `EQK`/`EQI`/`LTI`/`LEI`/`GTI`, and more;
* `print_print.lua`.

A wrong output string is rejected. `Supported` holds for all three
(`Lua/Programs/Supported.lean`).

## 4. Census of the ELF (`experiments/census/CENSUS.md`)

The census reran ship-your-interpreter's `disasm_census.py` and
`disasm_reachable.py` (patched copies) and its `disasm_to_sites.py` and
`disasm_to_segment.py`. New tools cover reachability through indirect
calls and jump tables, trace-based dynamic sets, template matching, and
per-arm sizes. `experiments/census/tools/run_all.sh` reruns everything in
about 2 minutes.

**Whole image.**

| | Lua ELF | WHILE ELF |
|---|---|---|
| functions | 980 | 258 |
| instructions | 80,690 | 25,336 |
| unique instruction words | 26,784 | 10,399 |
| mnemonics | 69 (new: `lb`, `sra`, `ebreak`) | 66 |

**Reachable image.**
* **Static, from `_start`.** 848 functions and 76,355 instructions.
  * Indirect calls were resolved by address flow: the `luaL_Reg` tables, the
    `lua_Alloc` pointer, the protected-call bodies and the stdio hooks.
  * All 57 jump tables were resolved and their sizes cross-checked.
  * About 9.4k of those instructions are the text parser, lexer and code
    generator. They are reachable only via `load`, and no run executes them.
* **Dynamic.**

| run | PCs | functions |
|---|---|---|
| `while.lua` | 6,560 | 173 |
| `while.lua`, boot/undump | 4,413 | 118 |
| `while.lua`, after VM entry | 2,793 | 89 |
| union of the 18 difftests | 25,148 | 502 |

**Template match** (by name, modulo relocations and branch/call targets).
* **Whole image.** 64 functions are byte-identical to the WHILE ELF, and 139
  more are identical modulo relocations: about 20.2k instructions. These are
  newlib, libgcc soft-int/soft-float, dlmalloc, stdio, `memcpy`/`memset`/`strlen`,
  and `setjmp`/`longjmp`.
* **Difftest union.** 101 reused functions (13,716 instructions), 12,951
  instructions of them inside ship-your-interpreter's proven `interp_run`
  scope, among them
  `_malloc_r`/`_free_r`/`_realloc_r`, `__muldi3`/`__udivdi3`/`__moddi3`,
  `__adddf3`/`__muldf3`/`__divdf3`, the `vfprintf` core and `_dtoa_r`.
* **New code.** 390 functions (32,547 instructions), about 74% of executed
  PCs; the per-file split is `experiments/census/per_origin.md`.
* **Site classes.** `disasm_to_sites.py` classifies 87.2–88.0% of
  instructions and fully classifies 68–74% of basic blocks. The WHILE ELF's
  own baseline is 87.9% and 73.1%. The rejects are `slli`/`andi`/`srli`
  masks, `auipc`/`lui`, `addw`, `lh`/`sh` and `jalr`.
* **Decode table.** ship-your-interpreter's decode lemmas cover 37.0% of the
  union's 10,615 unique words and 47.6% of `while.lua`'s.
* **`gen_fn.py` budget.** 742 of the 848 statically reachable functions fit it.
* **A `disasm_to_segment.py` flaw.** It silently drops unsupported rows. On
  the `OP_MOVE` arm it drafted 2 steps for 5 instructions. Fixed in A0.7
  (PHASES.md): it now fails on unsupported rows and drafts all F1 arms.

**`luaV_execute`.**
* **Size.** 4,020 instructions (16 KB) at `0x8001bf68–0x8001fe38`.
* **Dispatch.** **One dispatch site**: a 10-instruction fetch at `0x8001bfe4`,
  one `jr` at `0x8001c008`, and 145 jumps back to it.
* **Jump table.** At `0x8005336c`: 82 entries of 4 bytes each, relative to
  the table base. `OP_EXTRAARG` is out of range and goes to the default arm.
* **F1.** F1's 43 opcodes add up to 2,239 instructions of per-arm reach
  (arms overlap). Their integer fast paths total 613 instructions.
  * Largest arms: `FORPREP` 205 (float path and `__udivdi3`), `LE` 166,
    `LT` 160 (float and string compares), `MOD`/`MODK` 99/98, and
    `IDIV`/`IDIVK` 79/80.
  * Smallest arms: `JMP` 9, `LOADI` 12, `MOVE` 15.
  * The per-opcode table with callees is in `CENSUS.md` §4 and
    `luaV_execute_arms.tsv`.

**New C constructs vs WHILE** (static reach; WHILE ELF in parentheses).
* **TValue tag dispatch.** 439 `lbu` of `tt_` (+8 mod 16) (3), 118 of them in
  `luaV_execute`.
* **Jump tables.** 57 (17), including the 82-way VM table.
* **Indirect calls.** 75 `jalr` (29). 16 sites are executed: `l_alloc`,
  `luaD_precall` → C function, `luaD_rawrunprotected`, `luaZ_fill`.
* **Soft-float call sites.** 578 (115), 170 of them in `luaV_execute`.
* **Soft-int mul/div call sites.** 216 (70); the new ones are mostly the
  date arithmetic of `os.date`/`os.time` in newlib.
* **`setjmp`/`longjmp`.** One site each (`luaD_rawrunprotected`/`luaD_throw`),
  byte-identical to WHILE's. `longjmp` is executed by f1_for, f3_pcall,
  f3_uncaught and f6_coroutines.
* **Other.**
  * 7 `ebreak` null-dereference traps, never executed.
  * Varargs C functions: 15 (5).
  * Tail jumps into other functions: 316 (56).

## 5. What this means for the plan

* **Layer A's cut point.** `luaV_execute(L, ci)` is a single-dispatch loop
  over one jump table, so the WHILE `interp_run` pattern applies arm by arm.
  The F1 arms are small except where the float and string slow paths share
  an arm (`LT`/`LE`/`FORPREP`/`MOD`). Those arms need the `Supported`
  invariant (integers only) to prune the slow paths.
* **Reuse.**
  * The allocator, soft-int, soft-float, stdio/`vfprintf` and `setjmp`/`longjmp`
    proofs are reusable as generator inputs, but not byte for byte: addresses
    and the `tohost` location differ (PHASES A0).
  * The generator layer's Lean backing (segment bridges, frame
    metatheorems, allocator ledger, newlib Iris proofs) imports WHILE
    representation modules through 40 edges
    (`experiments/port/CUTS.txt`). Cutting them is the first porting task.
* **Genuinely new work.**
  * TValue tag dispatch, a representation of tables with `next` order,
    and `lua_longjmp` error recovery.
  * The 23k-instruction Lua core.
  * Soft-float, needed as soon as the Float fragment starts.

## 6. The `io` and `os` libraries

* **File system.** `c/src/htif.c` implements newlib's system calls with an
  in-image file system that follows the shared OS spec (`tcb/`,
  `TCB.Os.next`).
  * It starts empty, as `OsState.init` does. There are files and
    directories, the spec's path resolution, and one descriptor table
    (0-2 the console, `open` takes the smallest free number, `EBADF` for
    any descriptor it did not issue).
  * It provides `_open`/`_close`/`_read`/`_write`/`_lseek`/`_fstat`/`_stat`/
    `_unlink`/`rename`/`mkdir`/`rmdir`.
  * Its state is in `.bss`, and file contents are in the heap (`malloc`),
    so the allocator's proofs cover that memory; a static pool would need
    an allocator of its own.
  * Limits: 64 files and directories, 32 descriptors.
  * The same code is ship-your-ocaml's `htif.c` (its OCaml-only parts
    are marked `OCAML` there).
* **Conformance** (`experiments/os/RESULTS.md`, `experiments/os/run.sh`):
  * 0 of 6,490 generated traces are rejected: 5,275 accepted, 79 at
    calls the spec leaves unconstrained, and 1,136 stop at `opendir`,
    which the ELF lacks.
  * All 26 console scripts are accepted.
* **Clock.** `_gettimeofday` and `_times` return 0 (`TCB.Os.Clock.frozen`).
  So `os.time()` is 0, `os.clock()` is 0.0, and `os.date()` is
  `1970-01-01 00:00:00`; newlib has no `TZ`, so local time is UTC.
  newlib's own versions execute `ecall`, and the ELF has none.
* **Process.**
  * `os.exit(n)` runs newlib's `exit` (stdio flushed), then `_exit`, the
    HTIF exit.
  * `os.getenv` is `nil`: newlib's environment is empty, as is the
    spec's.
  * `os.execute()` is `false`, and `os.execute(cmd)` fails with `ENOSYS`
    (`baremetal.h`, so `system` is not linked).
  * `io.popen` raises `'popen' not supported` (`LUA_USE_POSIX` is unset).
* **Temporary files.** `os.tmpname` is newlib's `tmpnam`, which probes
  names with `open` (no `mkstemp`) and returns `/tmp/t1.0`.
  * `/tmp` does not exist in the empty file system, so `io.open` of that
    name fails with `ENOENT`, as does `io.tmpfile`.
  * A program that wants temporary files names them itself.
* **Error messages.** `io.open` of a missing file gives
  `f: No such file or directory` and errno 2 on both sides; newlib's
  `strerror` agrees with glibc's on the errors the spec has. The errno
  numbers are newlib's (`Lua/Vm/Layout.lean`).

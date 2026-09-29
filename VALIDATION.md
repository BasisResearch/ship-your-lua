# Phase 1: validation experiments

Outcome: **Lua 5.4.7 runs on the executable Sail RISC-V model.** The
bare-metal ELF prints `55\n2500\n36\n` for `while.lua` and exits 0 in
159,140 Sail steps. It agrees with native `lua` on all 16 difftest programs
across F1–F4, floats and coroutines. The F1 bytecode semantics reproduces
the ELF's output on three programs by kernel-checked derivation. No blockers.

Measured 2026-09-29 on aws-dev. The ELF is `c/lua-riscv-htif.elf`, sha256
`c019b0b7547131c7f211df75f3e33a06bf6928caf7c2644a1fb305239a309323`.
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
  * Startup, linker script and HTIF back end are WHILE's `crt0.S`, `link.ld`
    and `htif.c`. The only change is a separate `.lua_chunk` region (below).
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
    `switch`.
* **Libraries.** base, string, table and coroutine. There is no io, os,
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
  * This was checked on all 16 difftest ELFs: the section md5s match.
  * One image pin (`Lua/Vm/Image.lean`) therefore serves every program.
* **Output and exit.** Output goes through HTIF (`htif.c`); `stderr` shares
  the console. Exit codes are 0 for ok, 1 for a load error, 2 for a runtime
  error and 3 for out of memory.
* **ELF.** 418,872 bytes on disk (272 KB of `.text`, the 64 KiB chunk region, symbols).
  * `.text` is 272,288 bytes at `0x80000000`; `.rodata` is 23,616 bytes at
    `0x800427a0`.
  * `tohost` is at `0x80048400`; `luaV_execute` at `0x8001aa00`; `luaB_print`
    at `0x800219b0`.
  * The chunk is at `0x80049868`; `_end` is `0x80059870`.

## 3. Runs on the Sail model

The emulator is ship-your-interpreter's `lean_riscv_emulator`
(`riscv-lean/lean_emulator`, executable Sail RV64D model) — the one used for
its corpus cross-check (REVIEW2.md §4). Its speed is about 47k steps/s.

| `while.lua` (`c/tests/while.lua`, port of `while.wl`) | step |
|---|---|
| `main` entered (crt0 done) | 1,015 |
| `luaL_loadbufferx` entered (state + 4 libraries opened) | 120,671 |
| `lua_pcallk` entered (chunk undumped) | 124,661 |
| **`luaV_execute` entered** (the Layer A cut point) | **124,808** |
| exit store to `tohost` (exit 0, output `55\n2500\n36\n`) | 159,139 (159,140 steps total) |

Running the chunk takes 34,332 steps from VM entry. `luaV_execute`
dispatches 671 instructions, 15 distinct opcodes. The rest is `print`
through `luaL_tolstring`, `snprintf` and newlib stdio.

**Difftest** (`c/tests/difftest.sh`, 16 programs, `c/tests/difftest/`). The
comparison:
* Both sides run the same stripped `luac` chunk.
* The host side is `lua` built from the same source with the same
  `baremetal.h` (so `pairs` order agrees), with the collector stopped.
* The target side is the bare-metal ELF on the Sail emulator.
* Stdout and exit status (zero vs nonzero) are compared.

| program | covers | result | Sail steps |
|---|---|---|---|
| f1_arith | integer arithmetic, `//` `%` edge cases, wraparound, bitwise | PASS | 261,038 |
| f1_cond | if/elseif, and/or/not, repeat, nested loops | PASS | 344,831 |
| f1_for | numeric for edge cases, zero step error (pcall) | PASS | 154,507 |
| f1_while | = `while.lua` | PASS | 159,140 |
| f2_array | array part, `#`, SETLIST, nested tables | PASS | 210,290 |
| f2_next | **real `next` order** over string/int/float/bool keys | PASS | 266,758 |
| f2_tablelib | sort (with/without comparator), insert/remove/concat/unpack/pack/move | PASS | 200,640 |
| f3_closures | closures, shared upvalues, recursion (fib 15), varargs composition | PASS | 619,147 |
| f3_pcall | error objects, pcall/xpcall, error in deep recursion (`longjmp`) | PASS | 459,225 |
| f3_uncaught | uncaught error → exit 1 (host) / 2 (ELF) | PASS | 133,641 |
| f3_varargs | select, multret, 10,000-deep tail calls | PASS | 2,591,307 |
| f4_metatables | `__index/__add/__eq/__lt/__le/__len/__concat/__call/__tostring/__newindex` | PASS | 222,048 |
| f4_objects | inheritance chains, gmatch word count | PASS | 235,669 |
| f4_strings | string library, `format` (`%d %x %q …`), find/match/gsub/gmatch, coercions | PASS | 229,942 |
| f5_floats | `%.14g`, inf, −0.0, NaN, float `//` `%`, float for-loop (soft-float) | PASS | 438,430 |
| f6_coroutines | create/resume/yield/status/wrap, error inside a coroutine | PASS | 180,349 |

The result is 16/16. Printing a function value gives `function: 0x800219b0`,
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
| functions | 837 | 258 |
| instructions | 68,072 | 25,336 |
| unique instruction words | 23,140 | 10,399 |
| mnemonics | 69 (new: `lb`, `sra`, `ebreak`) | 66 |

**Reachable image.**
* **Static, from `_start`.** 693 functions and 61,912 instructions.
  * Indirect calls were resolved by address flow: the `luaL_Reg` tables, the
    `lua_Alloc` pointer, the protected-call bodies and the stdio hooks.
  * All 52 jump tables were resolved and their sizes cross-checked.
  * About 9.4k of those instructions are the text parser, lexer and code
    generator. They are reachable only via `load`, and no run executes them.
* **Dynamic.**

| run | PCs | functions |
|---|---|---|
| `while.lua` | 5,917 | 163 |
| `while.lua`, boot/undump | 3,793 | 106 |
| `while.lua`, after VM entry | 2,655 | 89 |
| union of the 16 difftests | 19,018 | 379 |

**Template match** (by name, modulo relocations and branch/call targets).
* **Whole image.** 77 functions are byte-identical to the WHILE ELF, and 131
  more are identical modulo relocations: about 20.4k instructions. These are
  newlib, libgcc soft-int/soft-float, dlmalloc, stdio, `memcpy`/`memset`/`strlen`,
  and `setjmp`/`longjmp`.
* **Difftest union.** 91 reused functions (13,976 instructions). 74 of them
  are inside ship-your-interpreter's proven `interp_run` scope, among them
  `_malloc_r`/`_free_r`/`_realloc_r`, `__muldi3`/`__udivdi3`/`__moddi3`,
  `__adddf3`/`__muldf3`/`__divdf3`, the `vfprintf` core and `_dtoa_r`.
* **New code.** 286 functions (23,199 instructions), about 71% of executed
  PCs: lvm.c 5,214, lstrlib 2,479, lapi 2,143, ldo 1,731, ltable 1,456, and
  libc `_strtod_l` 1,601.
* **Site classes.** `disasm_to_sites.py` classifies 87.4–87.8% of
  instructions and fully classifies 69–74% of basic blocks. The WHILE ELF's
  own baseline is 87.9% and 73.1%. The rejects are `slli`/`andi`/`srli`
  masks, `auipc`/`lui`, `addw`, `lh`/`sh` and `jalr`.
* **Decode table.** ship-your-interpreter's decode lemmas cover 43.3% of the
  union's 8,346 unique words and 51.1% of `while.lua`'s.
* **`gen_fn.py` budget.** 614 of the 693 statically reachable functions fit it.
* **A `disasm_to_segment.py` flaw.** It silently drops unsupported rows. On
  the `OP_MOVE` arm it drafted 2 steps for 5 instructions. Fixed in A0.7
  (PHASES.md): it now fails on unsupported rows and drafts all F1 arms.

**`luaV_execute`.**
* **Size.** 4,020 instructions (16 KB) at `0x8001aa00–0x8001e8d0`.
* **Dispatch.** **One dispatch site**: a 10-instruction fetch at `0x8001aa7c`,
  one `jr` at `0x8001aaa0`, and 145 jumps back to it.
* **Jump table.** At `0x800466dc`: 82 entries of 4 bytes each, relative to
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
* **TValue tag dispatch.** 438 `lbu` of `tt_` (+8 mod 16) (3), 118 of them in
  `luaV_execute`.
* **Jump tables.** 49 (17), including the 82-way VM table.
* **Indirect calls.** 66 `jalr` (29). 16 sites are executed: `l_alloc`,
  `luaD_precall` → C function, `luaD_rawrunprotected`, `luaZ_fill`.
* **Soft-float call sites.** 575 (115), 170 of them in `luaV_execute`.
* **Soft-int mul/div call sites.** 106 (70).
* **`setjmp`/`longjmp`.** One site each (`luaD_rawrunprotected`/`luaD_throw`),
  byte-identical to WHILE's. `longjmp` is executed by f1_for, f3_pcall,
  f3_uncaught and f6_coroutines.
* **Other.**
  * 7 `ebreak` null-dereference traps, never executed.
  * Varargs C functions: 10 (5).
  * Tail jumps into other functions: 255 (56).

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

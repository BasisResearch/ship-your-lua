# Disassembly census: `c/lua-riscv-htif.elf` vs syi `c/while-riscv-htif.elf`

All numbers come from Python and objdump in this directory. No Lean or `lake` was run.
The scripts are in `tools/`. `disasm_census.py`, `disasm_reachable.py`,
`disasm_to_sites.py` and `disasm_to_segment.py` are copies from syi. The census
copy was patched only to take its output path from argv. The other scripts were
written for this census: `lib.py`, `origin.py`, `reach.py`, `dyn.py`, `match.py`,
`arms.py`, `constructs.py`, `tables.py`, `trace_pcs.sh` and `run_all.sh`.

**Rerun:** `cd <census dir> && tools/run_all.sh`. It needs only python3,
objdump and the emulator, and takes about 2 minutes with 9 parallel traces.
It regenerates every JSON/TSV file here, including `numbers.json`, which holds
the headline numbers for diffing. It does not rewrite this file.

Environment overrides:

* `LUA_ELF` (default `~/Documents/code/ship-your-lua/c/lua-riscv-htif.elf`);
* `DIFFTEST_DIR` (default `$(dirname LUA_ELF)/build/difftest`);
* `SYI`, a read-only syi checkout (default `~/Documents/code/syi`);
* `LUA_SRC`, `OBJDUMP`/`TC`, `EMU` and `JOBS`.

The trace file for the main ELF must be named after the ELF's basename
(`lua-riscv-htif`), because `dyn.py`, `match.py` and `arms.py` look for
`traces/lua-riscv-htif.pcs.tsv`.

## Current build: `io` and `os` libraries (ELF `c3224616…`)

The ELF now opens `io` and `os`, and `htif.c` has an in-image file system
(VALIDATION.md §2). `tools/run_all.sh` was rerun on it with the 18 difftest
ELFs (the 16 below plus `f7_io`, `f7_os`). The JSON and TSV files in this
directory are current. The detailed tables in sections 0-5 below are the
previous build's (ELF `c019b0b7`, 16 difftests), unless a number is given
here. Old → new:

* **Whole image.**
  * 837 → 980 function symbols (835 → 978 unique names) and 68,072 → 80,690
    instructions.
  * 23,140 → 26,784 unique words; still 69 mnemonics.
  * By origin: `liolib.c` (1,919 instructions) and `loslib.c` (679) are new, and
    `htif.c` has 1,468 instructions in 23 functions (the whole boot origin,
    crt0 + htif + main, was 206).
    libc grew to 303 functions and 31,923 instructions: stdio `fopen`/
    `fseek`/`tmpnam`, `strftime`/`mktime`/`gmtime`, `setlocale`.
* **Sections.**
  * `.text`: 0x4ecc8 bytes at 0x80000000.
  * `.rodata`: 0xd9e0 bytes at 0x8004ecc8.
  * `.data`: 0xce0 bytes at 0x8005c6d0.
  * `.init_array`: 8 bytes, newlib's `register_fini`, a no-op that crt0
    never calls.
  * `.bss`: 0x1918 bytes at 0x8005d3b8.
  * `.lua_chunk`: 0x8005ecd0.
  * The 18 difftest ELFs still agree with the main ELF outside
    `.lua_chunk`.
* **`luaV_execute`.**
  * 4,020 instructions, as before, at 0x8001bf68..0x8001fe38.
  * The fetch head is at 0x8001bfe4, the dispatch `jr` at 0x8001c008, the
    default arm at 0x8001c1e4 and the jump table at 0x8005336c.
  * The per-arm sizes and callees are unchanged; only the addresses moved.
* **Static reach.**
  * 693 → 848 functions and 61,912 → 76,355 instructions (25,922 unique
    words).
  * Jump tables: 52 → 57, with 1,890 → 2,239 entries. Indirect sites: 83
    `jalr`, 17 tail jumps.
  * `dynamic_not_static` is still empty.
* **Traces.**
  * `while.lua` runs 159,140 → **215,723** steps, and `luaV_execute` is
    first entered at step 124,808 → **181,166**.
  * The whole difference is before VM entry, in opening `io`/`os` and in
    crt0 clearing a larger `.bss`. The VM part is 34,332 → 34,557 steps:
    newlib's `_write` now looks up the descriptor table.
  * Every difftest's total grew by 53k-57k steps. `f7_io` takes 607,172
    steps and `f7_os` 345,557.
* **Dynamic sets.**
  * `while.lua`: 6,560 PCs, 173 functions; after entry, 2,793 PCs and 89
    functions.
  * Union of 18: 25,148 PCs, 10,615 unique words, 502 functions.
* **Template match (whole image).**
  * 64 functions identical and 139 identical modulo relocations (20,153
    instructions). 14 have the same name but differ, and 760 are new.
  * Difftest union: 33 identical + 68 modulo relocations; 390 new
    functions (32,547 instructions).
* **Site classes.** 87.9% of instructions and 73.5% of blocks (static
  reach); the union is 88.0% / 72.6%.
* **Decode index.** syi's decode lemmas cover 37.0% of the union's unique
  words and 47.6% of `while.lua`'s.
* **`gen_fn.py` budget.** 742 of the 848 statically reachable functions fit
  it.

## 0. Inputs and how the disassembly was produced

* `experiments/disasm.txt` in syi is plain `objdump -d c/while-riscv-htif.elf`,
  with default aliases (`li`/`mv`/`j`/`ret`) and `.text` only.
  `riscv-none-elf-objdump -d` from xPack 15.2.0-1 reproduces it exactly: the
  diff after the header line is empty and both files have 25,857 lines.
* The same command on the Lua ELF gives `lua_disasm.txt` (69,752 lines). The
  WHILE output is `while_disasm.txt`.
* Lua ELF sections (relinked build):
  * `.text`: 0x427a0 bytes at 0x80000000;
  * `.rodata`: 0x5c40 bytes at 0x800427a0;
  * `.data`: 0xc78 bytes at 0x80048410;
  * `.bss`: 0x7d8 bytes at 0x80049090;
  * `.lua_chunk`: a fixed 64 KiB section at 0x80049868. It holds
    `_chunk_size` (read by main as data) and then `_chunk_start`.
* The 16 difftest ELFs in `c/build/difftest/` are byte-identical to the main
  ELF in `.text`, `.rodata` and `.data`. I checked this with an md5 of each
  section extracted by `objcopy -O binary -j`, and all 17 ELFs agree. Only
  `.lua_chunk` differs, so trace PCs map one-to-one onto `lua_disasm.txt`.
* Traces: `lean_riscv_emulator <elf> --trace-all --max-steps 20000000`, streamed
  through awk (`tools/trace_pcs.sh`). The awk keeps one row per PC with its
  execution count before and after the first step at `pc == luaV_execute`.
  The entry PC is read with `nm`; it is now 0x8001aa00. Total disk use is
  2.1 MB.
* **Trace step counts.** The relinked `lua-riscv-htif.elf` runs **159,140
  steps**, and luaV_execute (0x8001aa00) is first entered at **step 124,808**.
  The previous link ran 159,311 steps with entry at step 124,979; neither
  matches the brief's ~149k / 114,289. `f1_while.elf` gives exactly the same
  PC set and step counts, so it is the same `while.lua` program.
* The other difftests take 133,641 to 619,147 steps, except `f3_varargs`, which
  takes 2,591,307. All of them halted normally.

## 1. Whole image (`disasm_census.py`)

| | WHILE ELF | Lua ELF | ratio |
|---|---|---|---|
| function symbols (objdump headers) | 258 (257 unique names) | 837 (835 unique names) | 3.2x |
| instructions | 25,336 | 68,072 | 2.7x |
| unique instruction words | 10,399 | 23,140 | 2.2x |
| unique mnemonics | 66 | 69 | |

* `disasm_census.py` counts functions by name. It reports 257 and 835 because
  `__sbprintf` (both ELFs) and `l_alloc` (Lua: main.c and lauxlib.c) appear twice.
* Mnemonics only in Lua: `lb` (10 sites), `ebreak` (7) and `sra` (2). There is
  no mnemonic that appears only in WHILE.
* 8,418 of the Lua unique words also occur in the WHILE ELF, and 14,722 are new.
* Top mnemonics in Lua: ld 9,603; mv 8,000; sd 6,687; li 5,666; addi 5,360;
  jal 4,017; j 3,362; beqz 1,826; lbu 1,723 (WHILE: 342); add 1,685.
* Outputs: `lua_census.json`/`.out` and `while_census.json`/`.out`.

Split by origin, using STT_FILE context for local symbols, `nm -A` on the
rv64i/lp64 multilib `libc.a`/`libgcc.a`/`libm.a` for globals, and a grep of the
Lua sources:

| origin | functions | instructions |
|---|---|---|
| Lua core and libs (26 .c files) | 558 | 39,947 |
| libc (newlib) | 221 | 23,344 |
| libgcc (soft-float and soft-int) | 28 | 2,286 |
| libm (fmod, pow, floor, frexp, …) | 16 | 1,777 |
| boot (crt0, htif, main.c) | 14 | 206 |

Per-file detail is in `per_origin.tsv` / `per_origin.md`.

## 2. Reachable image

### 2a. Static reachability from `_start` (`tools/reach.py`, adapted from `disasm_reachable.py`)

Edges and how each kind is resolved:

* **Direct edges** are `jal`/`j`/branch targets that land in another function.
  This is what `disasm_reachable.py` does.
* **Switch jump tables** are recognised by shape:
  `auipc/addi base (# addr)`, `slli`, `add`, `lw`, `add base`, `jr`. Entries
  are int32 offsets from the table base, so `target = base + sext(entry)`.
  * The table size comes from the preceding `bltu K,idx`/`bgeu idx,K` against a
    `li K`. It is cross-checked by requiring every target to fall inside the same
    function.
  * All 52 tables in the Lua ELF and all 17 in the WHILE ELF resolved, and every
    bound matched.
  * Tables only add intra-function edges, so they do not change the function set.
* **Indirect calls** are 72 `jalr` sites plus 15 non-table `jr` sites. They are
  resolved by an **address-flow closure**. A function is added when either:
  * reachable code materialises its address with `auipc`+`addi # <fn>`; or
  * its address is stored as an 8-byte pointer inside a data object that
    reachable code (or a reachable data object) references.
  * Data objects are bounded by sized symbols. Anonymous regions run to the next
    symbol.
* In this ELF, the closure resolves:
  * `lua_CFunction`s through the `luaL_Reg` arrays: `base_funcs` (23),
    `strlib` (17), `co_funcs` (8), `tab_funcs` (7) and `stringmetamethods` (8).
  * `luaopen_string/table/coroutine` through main's `libs[]`, and
    `luaopen_base` through an lla in `main`.
  * `lua_Alloc` = main.c `l_alloc` (lla in `main`). The lauxlib `l_alloc`,
    reached only from `luaL_newstate`, stays unreachable.
  * Protected-call bodies: `f_luaopen`, `f_call`, `f_parser`, `resume`,
    `unroll`, `closepaux`, `dothecall`.
  * Continuations and readers: `pairscont`, `finishpcall`, `dofilecont`,
    `getS`, `getF`, `generic_reader`, `writer`, `ipairsaux`, `gmatch_aux`,
    `luaB_auxwrap`, `boxgc`.
  * newlib stdio hooks (`__sread/__swrite/__sseek/__sclose`) and the locale
    `mbtowc`/`wctomb` pointers.

| variant | functions | instructions | unique words |
|---|---|---|---|
| Lua, direct edges only | 305 | 36,632 | 14,635 |
| **Lua, address-flow closure (used below)** | **693 / 837** | **61,912 / 68,072** | **21,565** |
| Lua, every address-taken function (114) as root (upper bound) | 718 | 63,254 | 21,942 |
| WHILE, direct only from `_start` | 145 | 20,371 | 8,894 |
| WHILE, address-flow from `_start` | 175 / 258 | 21,844 / 25,336 | 9,287 |
| (syi `disasm_reachable.json`, root `interp_run`) | 124 | | |

* The closure is sound for the dynamic runs: every function touched by any of
  the 17 traces is in the 693 set (`dynamic_not_static = []`).
* 144 functions stay unreachable (6,160 instructions): 89 libc, 45 Lua, 5 libm
  and 5 libgcc. The Lua ones are `lua_close`, the hook and debug API,
  `luaL_ref`, `luaL_traceback`, `luaL_newstate`, `panic`, and similar.
* The static set is loose. It includes the whole text front end: lparser
  (4,346), lcode (3,345) and llex (1,673), about 9.4k instructions reachable
  through `load`/`loadstring`/`dofile` → `f_parser`. None of the traces execute
  them because the embedded chunk is loaded in mode `"b"`. It also includes
  `string.dump` (ldump) and the file stdio path (`fopen`, `fread`, `freopen`,
  `fseek`).

### 2b. Dynamically reached (`tools/dyn.py`, `dynamic.json`)

"PCs" means distinct instructions executed. "Functions" means functions with at
least one executed PC.

| set | PCs | functions | unique words | functions by family |
|---|---|---|---|---|
| while.lua, whole run | 5,917 | 163 | 3,315 | lua 98, libc 51, boot 9, libgcc 5 |
| while.lua, before luaV_execute entry (boot + state + undump) | 3,793 | 106 | 2,230 | lua 82, libc 17, boot 4, libgcc 3 |
| while.lua, at/after luaV_execute entry | 2,655 | 89 | 1,758 | libc 46, lua 31, boot 8, libgcc 4 |
| while.lua, after-only (not executed before entry) | 2,124 | 65 | 1,443 | |
| difftest union (16 ELFs, including f1_while = while.lua) | 19,018 | 379 | 8,346 | lua 277, libc 73, libgcc 19, boot 9, libm 1 |
| difftest union, after luaV_execute entry | 17,256 | 342 | 7,722 | lua 240, libc 73, libgcc 19, boot 9, libm 1 |
| difftest union, before entry | 4,115 | 110 | 2,409 | |

* luaV_execute itself: while.lua touches 413 of its 4,020 instructions, and the
  difftest union touches 2,069.
* Before entry, while.lua runs `lundump.c` (479 PCs, 5 functions) and
  `lzio.c`, plus `lua_newstate`/`f_luaopen`, `luaS_init`, `luaT_init`,
  `luaX_init` (38), the four `luaopen_*`, `luaL_requiref`, `luaL_setfuncs` and
  `luaH_*` table construction.
* After entry, while.lua runs:
  * Lua: `luaV_execute`, `luaD_precall`/`poscall`/`pcall`/`rawrunprotected`,
    `luaB_print`, `luaL_tolstring`, `lua_tolstring`, `luaO_pushvfstring`,
    `luaH_getshortstr`, `luaS_newlstr`/`internshrstr`, `luaC_step`/`newobj`,
    `luaT_adjustvarargs`.
  * libc: `snprintf` → `_svfprintf_r` (for number formatting), and
    `fwrite` → `__sfvwrite_r` → `_write` (print).
  * Allocator: `malloc`/`realloc`/`free`.
  * libgcc: `__muldi3`, `__moddi3`, `__umoddi3`, `__udivdi3`.
* Per-run numbers are in `dynamic.json` under `per_run`. The PC count ranges
  from 5,917 (while) to 10,054 (f5_floats).

## 3. Template match against the WHILE ELF and the syi generators

### 3a. Function bodies shared with the WHILE ELF (`tools/match.py`, `function_match.tsv`)

Method: compare function by function, by name.

* **identical_words**: the same 32-bit words.
* **identical_mod_reloc**: the same after normalising address-dependent fields:
  * `jal`/`j`/branch targets become symbol names;
  * the `auipc` hi20 is wildcarded;
  * the lo12 of an instruction whose base came from `auipc` becomes the
    referenced function name, or `DATA`;
  * `gp`-relative immediates are wildcarded (relaxed `_impure_ptr` and similar).
* A body-hash lookup catches renamed copies.

| set | identical words | identical modulo relocs | other name | same name, different | new |
|---|---|---|---|---|---|
| whole image (fns / insts) | 77 / 2,216 | 131 / 18,226 | 1 / 2 | 4 / 1,512 | 624 / 46,116 |
| static reach (693 / 61,912) | 47 / 1,431 | 84 / 15,705 | 1 / 2 | 4 / 1,512 | 557 / 43,262 |
| while.lua dynamic (163 / 17,161) | 23 / 620 | 39 / 5,979 | 0 | 2 / 169 | 99 / 10,393 |
| difftest union dynamic (379 / 37,344) | 33 / 912 | 58 / 13,064 | 0 | 2 / 169 | 286 / 23,199 |
| executed PCs, while.lua (5,917) | 375 | 1,523 | 0 | 137 | 3,882 (66%) |
| executed PCs, union (19,018) | 769 | 4,604 | 0 | 152 | 13,493 (71%) |

* Of the "same name, different" functions, 3 are name collisions
  (`main`, `statement`, `block`).
* The fourth is `global_stdio_init.part.0`. Its only difference is one
  `addi s2,s2,%lo(__sseek)` that became `mv s2,s2` because lo12 = 0, so it is
  effectively reused.
* **Reused and inside syi's proof scope** means the function is in syi
  `disasm_reachable.json`, the `interp_run` closure. This covers 74 of the 91
  reused functions in the union, which is 13,470 of their 13,976 instructions,
  and 46 of 62 for while.lua. The large ones are:
  * soft-float: `__adddf3` (418), `__subdf3` (440), `__muldf3` (307),
    `__divdf3` (328), `__eqdf2`/`__gedf2`/`__ledf2`, `__floatsidf`,
    `__fixdfsi`, `__unorddf2`;
  * soft-int: `__muldi3`, `__moddi3`, `__umoddi3`, `__hidden___udivdi3`,
    `__divdi3`, `__clzdi2`;
  * printf: `_svfprintf_r` (3,212), `_vfprintf_r` (3,395), `_vfiprintf_r`,
    `_dtoa_r` (1,407), and mprec (`__multiply`, `__lshift`, `__pow5mult`,
    `quorem`, `__d2b`, …);
  * allocator (dlmalloc): `_malloc_r` (560), `_realloc_r` (396),
    `_free_r` (193), `_calloc_r`, `_malloc_trim_r`;
  * stdio: `__sfvwrite_r` (311), `__sflush_r`, `_fwrite_r`, `__swsetup_r`,
    `__smakebuf_r`, `__swbuf_r`, `__ssputs_r`, `__ssprint_r`;
  * string and memory: `memcpy`, `memmove`, `memset`, `memchr`, `strlen`,
    `strcmp`, `strcpy`, `strncpy`;
  * `setjmp`, `longjmp`, `snprintf`, `fprintf`, `exit`, `__call_exitprocs`,
    `_sbrk`, `_fstat`, `_isatty`, `_exit`.
* Reused but outside syi's scope (17 functions): `_close`, `_write`,
  `_write_r`, `_close_r`, `__swrite`, `__sclose`, `_fclose_r`, `fflush`,
  `stdio_exit_handler`, `_fwalk_sglue`, `__sfp_lock_*`, `strchr`, `strncmp`,
  `memcmp`, `__ascii_mbtowc`, `_start`.
* **New function families.** Dynamic union, instructions per family:
  * lvm.c: 5,214. This is mostly luaV_execute (4,020), plus `luaV_concat` 222,
    `luaV_equalobj` 212, `luaV_finishset`/`luaV_lessthan` 143 each, and
    `luaV_finishget` 93.
  * lstrlib: 2,479 (`str_format` 521, `str_gsub` 334, `match` 330).
  * lapi: 2,143 (53 functions).
  * libc `_strtod_l`: 1,601. It is new; the WHILE ELF never parsed floats.
  * ldo: 1,731 (`luaD_precall` 226, `luaD_pretailcall` 222, `luaD_poscall`
    147, `lua_resume`).
  * ltable: 1,456 (`luaH_newkey` 364, `luaH_resize` 249, `luaH_getn`,
    `mainpositionTV`).
  * ldebug: 1,060. lobject: 1,057. lauxlib: 1,019. ltablib: 841.
  * lundump: 764 (boot only). lbaselib: 716. ltm: 596. lgc: 507 (`luaC_step`).
  * lstring: 407. lfunc: 389. lstate: 368. lcorolib: 326.
  * libgcc: `__floatdidf` and `__fixdfdi` (116 together; 64-bit int ↔ double is
    new).
  * libm: `floor` (114).
* The while.lua dynamic "new" set is 99 functions and 10,393 instructions. Of
  that, lvm.c is 4,256, lapi 1,380, ltable 1,032, lundump 764 and ldo 675.

### 3b. `disasm_to_sites.py` / `disasm_to_segment.py` (site-battery classes)

I ran `classify()` from syi's `disasm_to_sites.py` on every instruction. A block
counts as classified when every instruction in it gets a site row, which is when
the `disasm_to_segment.py` draft would be complete. Basic blocks are split at
branch and jump targets, after terminators and calls, and at jump-table targets.

| set | instructions site-classified | basic blocks fully classified |
|---|---|---|
| WHILE ELF, whole (baseline) | 22,278 / 25,336 = 87.9% | 4,740 / 6,485 = 73.1% |
| Lua static reach | 54,359 / 61,912 = 87.8% | 11,621 / 15,797 = 73.6% |
| Lua while.lua executed PCs | 5,173 / 5,917 = 87.4% | 886 / 1,286 = 68.9% |
| Lua union executed PCs | 16,620 / 19,018 = 87.4% | 3,178 / 4,401 = 72.2% |

* Rejects in the static reach, by reason:
  * OP-IMM other than ADDI: 3,731 (`slli` 1,426, `andi` 1,114, `srli` 490,
    `zext.b` 224, `ori` 215, …);
  * `auipc`: 1,022;
  * R-type other than ADD/SUB: 868 (`or`, `and`, `xor`, `sll`, `slt`, `snez`, …);
  * OP-IMM-32 other than ADDIW: 674 (`srliw`, `slliw`, `sraiw`);
  * `lui`: 416;
  * RTYPEW other than SUBW: 401 (`addw` 299, …);
  * `lh`/`lhu`/`lb`/`lwu`: 236; `sh`: 124;
  * `jalr` shape: 67; `ebreak`: 7; x0-base loads and stores: 7.
* The rejection profile matches the WHILE ELF's. These classes are simply not
  in the gen_sites battery. The WHILE proofs cover them through the
  genseg/gen_fn decode-table route.
* `disasm_to_segment.py` **silently drops `#UNSUPPORTED` comment rows**. On the
  OP_MOVE arm (0x8001be84..0x8001be98) it produced a 2-step draft for a
  5-instruction range, missing `srliw`, `zext.b` and `slli`. See
  `demo/op_move_seg.json`. A draft is only faithful for fully classified blocks.
* Demo outputs in `demo/`:
  * `fetch_sites.tsv`, the dispatch head 0x8001aa7c..0x8001aaa4: 10 rows,
    2 unsupported (`andi a4,s4,127`, `slli`);
  * `op_addi_sites.tsv`: 7 rows, 7 unsupported.

### 3c. Decode table and whole-function generator

* **syi `scripts/decode_index.tsv`** (8,303 words with decode lemmas) covers:
  * 7,165 / 23,140 of Lua's whole-image unique words (31.0%);
  * 7,080 / 21,565 in the static reach (32.8%);
  * 1,693 / 3,315 of while.lua's executed words (51.1%);
  * 3,616 / 8,346 of the union's executed words (43.3%).
* The rest need new lemmas from `gen_decode_table.py`, which is mechanical. The
  step-3 AST dump needs Lean, so I did not run it.
* New mnemonics against the 65 in the decode table: `lb`, `sra`, `sraw` and
  `ebreak` in the static reach; only `lb` (4 PCs) and `sraw` (1 PC) are executed.
* **`gen_fn.py` budget** (≤150 instructions, ≤20 branches), static reach:
  * 614 / 693 functions fit;
  * 569 of those also have no `jalr` or non-`ret` `jr`, which gen_fn has no
    terminator for;
  * 462 of those are not reused from WHILE.
* Same budget for the union: 338 of 379 fit, 319 have no indirect jumps, 248
  are new. For while.lua: 146 of 163, 133, and 84.
* Over budget in the union: 41 functions. These include `luaV_execute`,
  `luaD_precall`, `luaD_pretailcall`, `luaH_newkey`, `luaH_resize`,
  `lua_getinfo`, `str_format`, `_strtod_l`, and the printf and malloc cores
  (which already have syi proofs).
* **`gen_code_lemmas.py` chunking** (16 instructions per chunk): 4,212 chunks
  for the static reach (3,067 in new functions) and 2,526 for the union
  (1,602 new). luaV_execute alone is 252 chunks.

## 4. luaV_execute (`tools/arms.py`, `luaV_execute_arms.json` / `.tsv`)

* **Size:** 0x8001aa00..0x8001e8d0, 4,020 instructions (16,080 bytes). That is
  5.9% of the image, and 1.18x the largest function in the WHILE ELF
  (`_vfprintf_r`, 3,395 instructions).
* **One dispatch site.** The fetch head is at `luaV_execute+0x7c` = 0x8001aa7c,
  with 145 in-function jumps back to it (`vmbreak`). The sequence is:

  ```
  bnez s5,trap
  lw s4,0(s11)                        # i = *pc
  addi s3,s11,4
  andi a4,s4,127                      # GET_OPCODE
  bltu s1(=81),a4,default
  slli a5,a4,2
  add a5,s8,a5
  lw a5,0(a5)
  add a5,s8,a5
  jr a5
  ```

  It is 10 instructions, and luaV_execute has exactly **1** `jr` and 1 `ret`.
  `s8` holds the table base for the whole function (set once in the prologue).
* **Jump table:** 0x800466dc in `.rodata` (it sits right after
  `udatatypename`), **82 entries** of int32 base-relative offsets.
  * Ops 0..81 each go to a distinct target.
  * **OP_EXTRAARG (82) is not in the table.** Indices > 81 go through the
    `bltu` to the default at 0x8001ac7c, which is `mv s11,s3; j fetch`. So the
    83rd opcode is the 2-instruction default arm.
* **How arms are measured:**
  * **reach** is the number of luaV_execute instructions reachable from the
    arm's jump-table target over the intra-function CFG. It follows branches,
    in-function `j`, and fall-through after `jal`. It stops at the fetch head,
    at `ret`, at `j` out of the function, and after `jal` to a noreturn error
    function (`luaG_runerror`, `luaG_typeerror`, `luaG_forerror`,
    `luaG_opinterror`, `luaG_tointerror`, `luaG_ordererror`,
    `luaG_concaterror`, `luaD_throw`, …).
  * **excl** is the subset of reach that no other arm reaches.
  * **linear** is the straight-line run from the target to the first `j`, `ret`
    or noreturn call, which is roughly the fast path.
  * **tgt-hits** is how many times the target PC executed. It is an upper bound
    on dispatches, because a few targets are also jumped to internally; the
    default target is a shared `vmbreak` stub, for example.
  * Callees are `jal`s inside the reach set. `xN` means N call sites.
* **Totals.** All arms together cover 4,001 of the 4,020 instructions. The
  other 19 are the prologue and the trap path.
* while.lua executes 15 distinct opcodes: MOVE, LOADI, GETTABUP, ADDI, MODK,
  ADD, MUL, JMP, EQI, LTI, LEI, GTI, CALL, RETURN and VARARGPREP. That is 671
  dispatches (the `jr` executes 671 times).
* The union executes 61 of the 82 table arms: all except LOADKX, SUBK, POWK,
  BANDK, BORK, BXORK, SHRI, SHLI, POW, DIV, BAND, BOR, BXOR, SHL, SHR, MMBINK,
  BNOT, NOT, TBC, TESTSET and TFORLOOP. It also executes the default target.

**F1 opcodes.** The 33 ops are MOVE, LOADI, LOADF, LOADK, ADD, ADDI, ADDK, SUB,
SUBK, MUL, MULK, MOD, MODK, IDIV, IDIVK, EQ, LT, LE, EQK, EQI, LTI, LEI, GTI,
GEI, JMP, TEST, FORPREP, FORLOOP, RETURN0, RETURN1, RETURN, CALL and GETTABUP.

| F1 size measure | instructions |
|---|---|
| union of reach sets | 1,901 (47% of luaV_execute) |
| sum of reach sets | 2,028 |
| sum of exclusive | 1,812 |
| sum of linear fast paths | 463 |

* The big F1 arms are the comparisons, because they carry int/float mixed
  paths. FORPREP is 205 instructions (25 branches; `__hidden___udivdi3` x2 for
  the loop count, plus `luaV_tonumber_`, `luaV_tointeger` and
  `luaG_forerror`). LE is 166 and LT is 160 (`l_strcmp`, `luaT_callorderTM`,
  and 9 soft-float compares).
* MOD/MODK are 98–99 instructions (`__moddi3`, `fmod`, float fix-up) and
  IDIV/IDIVK are about 80 (`__divdi3`, `__moddi3`, `floor`).
* The simple ones: MOVE is 15 (5 exclusive, since it shares the `setobj` tail
  with LOADK and others), LOADI 12, JMP 9, LOADK 14, TEST 26, EQI 41,
  LTI/LEI/GTI/GEI 51–53, ADDI 33, ADD 52, FORLOOP 55, CALL 42, RETURN0/1
  72/84, RETURN 87, GETTABUP 48.

Per-opcode table. `reach`, `excl` and `linear` are in instructions; `br` is the
number of branches in the reach set.

| # | opcode | F1 | target | reach | excl | linear | br | tgt-hits while | tgt-hits union | callees (jal; xN = N sites) |
|---|---|---|---|---|---|---|---|---|---|---|
| 0 | MOVE | F1 | 8001be84 | 15 | 5 | 5 | 0 | 3 | 145 |  |
| 1 | LOADI | F1 | 8001be54 | 12 | 12 | 12 | 0 | 9 | 411 |  |
| 2 | LOADF | F1 | 8001be98 | 14 | 14 | 14 | 0 | 0 | 10 | __floatsidf |
| 3 | LOADK | F1 | 8001ba94 | 14 | 4 | 14 | 0 | 0 | 111 |  |
| 4 | LOADKX |  | 8001bef0 | 15 | 15 | 15 | 0 | 0 | 0 |  |
| 5 | LOADFALSE |  | 8001bd54 | 8 | 8 | 8 | 0 | 0 | 155 |  |
| 6 | LFALSESKIP |  | 8001bed0 | 8 | 8 | 8 | 0 | 0 | 14 |  |
| 7 | LOADTRUE |  | 8001b5d0 | 8 | 8 | 8 | 0 | 0 | 222 |  |
| 8 | LOADNIL |  | 8001bd1c | 14 | 14 | 14 | 1 | 0 | 7 |  |
| 9 | GETUPVAL |  | 8001bb40 | 17 | 17 | 17 | 0 | 0 | 13493 |  |
| 10 | SETUPVAL |  | 8001bca8 | 33 | 29 | 29 | 3 | 0 | 503 | luaC_barrier_ |
| 11 | GETTABUP | F1 | 8001ba1c | 48 | 43 | 20 | 2 | 3 | 240 | luaH_getshortstr, luaV_finishget |
| 12 | GETTABLE |  | 8001bacc | 71 | 71 | 16 | 5 | 0 | 145 | luaH_get, luaH_getint, luaV_finishget |
| 13 | GETI |  | 8001b6e8 | 50 | 45 | 13 | 3 | 0 | 15 | luaH_getint, luaV_finishget |
| 14 | GETFIELD |  | 8001b67c | 45 | 40 | 17 | 2 | 0 | 70 | luaH_getshortstr, luaV_finishget |
| 15 | SETTABUP |  | 8001b5f0 | 68 | 48 | 25 | 6 | 0 | 18 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 16 | SETTABLE |  | 8001b994 | 93 | 73 | 21 | 10 | 0 | 179 | luaC_barrierback_, luaH_get, luaH_getint, luaV_finishset |
| 17 | SETI |  | 8001b8cc | 74 | 54 | 18 | 7 | 0 | 3 | luaC_barrierback_, luaH_getint, luaV_finishset |
| 18 | SETFIELD |  | 8001b84c | 65 | 45 | 22 | 6 | 0 | 32 | luaC_barrierback_, luaH_getshortstr, luaV_finishset |
| 19 | NEWTABLE |  | 8001b7a0 | 48 | 48 | 33 | 4 | 0 | 36 | luaC_step, luaH_new, luaH_resize |
| 20 | SELF |  | 8001b540 | 52 | 52 | 26 | 3 | 0 | 11 | luaH_getstr, luaV_finishget |
| 21 | ADDI | F1 | 8001b4dc | 33 | 31 | 13 | 2 | 123 | 13318 | __adddf3, __floatsidf |
| 22 | ADDK | F1 | 8001b46c | 55 | 51 | 15 | 6 | 0 | 10 | __adddf3, __floatdidf x2 |
| 23 | SUBK | F1 | 8001b41c | 55 | 51 | 15 | 6 | 0 | 0 | __floatdidf x2, __subdf3 |
| 24 | MULK | F1 | 8001c5d4 | 54 | 50 | 17 | 6 | 0 | 16 | __floatdidf x2, __muldf3, __muldi3 |
| 25 | MODK | F1 | 8001c568 | 98 | 88 | 27 | 14 | 100 | 201 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 26 | POWK |  | 8001c29c | 61 | 57 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 27 | DIVK |  | 8001c270 | 48 | 46 | 9 | 5 | 0 | 5 | __divdf3, __floatdidf x2 |
| 28 | IDIVK | F1 | 8001c200 | 80 | 72 | 24 | 9 | 0 | 4 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 29 | BANDK |  | 8001c1a8 | 54 | 52 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 30 | BORK |  | 8001c150 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 31 | BXORK |  | 8001c0f8 | 54 | 54 | 7 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 32 | SHRI |  | 8001c824 | 63 | 63 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 33 | SHLI |  | 8001c7c8 | 62 | 60 | 7 | 8 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor |
| 34 | ADD | F1 | 8001c460 | 52 | 50 | 16 | 6 | 69 | 11354 | __adddf3, __floatdidf x2 |
| 35 | SUB | F1 | 8001c3fc | 53 | 49 | 16 | 6 | 0 | 1 | __floatdidf x2, __subdf3 |
| 36 | MUL | F1 | 8001c760 | 53 | 49 | 16 | 6 | 9 | 921 | __floatdidf x2, __muldf3, __muldi3 |
| 37 | MOD | F1 | 8001c6f0 | 99 | 89 | 19 | 14 | 0 | 629 | __adddf3, __floatdidf x2, __gedf2 x2, __ledf2 x2, __moddi3, fmod, luaG_runerror |
| 38 | POW |  | 8001bf88 | 57 | 55 | 8 | 6 | 0 | 0 | __eqdf2, __floatdidf x2, __muldf3, pow |
| 39 | DIV |  | 8001bf2c | 49 | 45 | 8 | 5 | 0 | 0 | __divdf3, __floatdidf x2 |
| 40 | IDIV | F1 | 8001c944 | 79 | 69 | 19 | 9 | 0 | 1 | __divdf3, __divdi3, __floatdidf x2, __moddi3, floor, luaG_runerror |
| 41 | BAND |  | 8001c8e4 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 42 | BOR |  | 8001c508 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 43 | BXOR |  | 8001c4a8 | 83 | 81 | 7 | 10 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 44 | SHL |  | 8001c088 | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 45 | SHR |  | 8001c014 | 93 | 91 | 7 | 13 | 0 | 0 | __eqdf2 x2, __fixdfdi x2, __gedf2 x2, __ledf2 x2, floor x2 |
| 46 | MMBIN |  | 8001c888 | 23 | 23 | 23 | 0 | 0 | 2 | luaT_trybinTM |
| 47 | MMBINI |  | 8001bfb4 | 24 | 24 | 24 | 0 | 0 | 1 | luaT_trybiniTM |
| 48 | MMBINK |  | 8001c394 | 26 | 26 | 26 | 0 | 0 | 0 | luaT_trybinassocTM |
| 49 | UNM |  | 8001c33c | 39 | 37 | 11 | 2 | 0 | 4 | luaT_trybinTM |
| 50 | BNOT |  | 8001c9b0 | 54 | 54 | 11 | 5 | 0 | 0 | __eqdf2, __fixdfdi, __gedf2, __ledf2, floor, luaT_trybinTM |
| 51 | NOT |  | 8001c2fc | 20 | 20 | 16 | 2 | 0 | 0 |  |
| 52 | LEN |  | 8001c6ac | 17 | 17 | 17 | 0 | 0 | 47 | luaV_objlen |
| 53 | CONCAT |  | 8001c640 | 27 | 27 | 21 | 2 | 0 | 12 | luaC_step, luaV_concat.part.0 |
| 54 | CLOSE |  | 8001c9f4 | 15 | 15 | 15 | 0 | 0 | 12 | luaF_close |
| 55 | TBC |  | 8001b3f0 | 11 | 11 | 11 | 0 | 0 | 0 | luaF_newtbcupval |
| 56 | JMP | F1 | 8001b17c | 9 | 9 | 9 | 0 | 122 | 872 |  |
| 57 | EQ | F1 | 8001b128 | 31 | 31 | 19 | 1 | 0 | 5 | luaV_equalobj |
| 58 | LT | F1 | 8001b32c | 160 | 160 | 11 | 16 | 0 | 17 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 59 | LE | F1 | 8001b0a4 | 166 | 166 | 11 | 16 | 0 | 676 | __adddf3, __eqdf2, __fixdfdi x2, __floatdidf x2, __gedf2 x4, __ledf2 x5, floor x2, l_strcmp, luaT_callorderTM |
| 60 | EQK | F1 | 8001b2e8 | 27 | 27 | 15 | 1 | 0 | 502 | luaV_equalobj |
| 61 | EQI | F1 | 8001b288 | 41 | 41 | 10 | 4 | 100 | 10835 | __eqdf2, __floatsidf |
| 62 | LTI | F1 | 8001af04 | 53 | 53 | 10 | 4 | 11 | 2000 | __floatsidf, __ledf2, luaT_callorderiTM |
| 63 | LEI | F1 | 8001aea4 | 51 | 51 | 10 | 3 | 16 | 33 | __floatsidf, __ledf2, luaT_callorderiTM |
| 64 | GTI | F1 | 8001b044 | 53 | 53 | 10 | 4 | 101 | 203 | __floatsidf, __gedf2, luaT_callorderiTM |
| 65 | GEI | F1 | 8001afe0 | 52 | 52 | 10 | 3 | 0 | 10 | __floatsidf, __gedf2, luaT_callorderiTM |
| 66 | TEST | F1 | 8001b3b0 | 26 | 26 | 14 | 2 | 0 | 211 |  |
| 67 | TESTSET |  | 8001af64 | 33 | 33 | 14 | 2 | 0 | 0 |  |
| 68 | CALL | F1 | 8001b234 | 42 | 23 | 17 | 3 | 3 | 2738 | luaD_precall, luaG_tracecall |
| 69 | TAILCALL |  | 8001b1a0 | 100 | 48 | 13 | 8 | 0 | 10008 | luaD_poscall, luaD_pretailcall, luaF_closeupval, luaG_tracecall |
| 70 | RETURN | F1 | 8001adf8 | 87 | 47 | 31 | 7 | 1 | 27 | luaD_poscall, luaF_close, luaG_tracecall |
| 71 | RETURN0 | F1 | 8001ad54 | 72 | 38 | 3 | 6 | 0 | 2 | luaD_poscall, luaG_tracecall |
| 72 | RETURN1 | F1 | 8001ace4 | 84 | 50 | 3 | 6 | 0 | 2013 | luaD_poscall, luaG_tracecall |
| 73 | FORLOOP | F1 | 8001ac84 | 55 | 55 | 7 | 4 | 0 | 577 | __adddf3, __gedf2 x2, __ledf2 |
| 74 | FORPREP | F1 | 8001ab90 | 205 | 203 | 11 | 25 | 0 | 21 | __eqdf2, __gedf2 x5, __hidden___udivdi3 x2, __ledf2, luaG_forerror x3, luaG_runerror, luaV_tointeger x2, luaV_tonumber_ x4 |
| 75 | TFORPREP |  | 8001aaa4 | 71 | 15 | 34 | 4 | 0 | 9 | luaD_call, luaF_newtbcupval, luaG_traceexec, memcpy |
| 76 | TFORCALL |  | 8001aae0 | 56 | 0 | 19 | 4 | 0 | 95 | luaD_call, luaG_traceexec, memcpy |
| 77 | TFORLOOP |  | 8001ab88 | 34 | 2 | 2 | 3 | 0 | 0 | luaG_traceexec |
| 78 | SETLIST |  | 8001bd74 | 75 | 75 | 32 | 8 | 0 | 8 | luaC_barrierback_, luaH_realasize, luaH_resizearray |
| 79 | CLOSURE |  | 8001bbc4 | 79 | 77 | 34 | 7 | 0 | 43 | luaC_barrier_, luaC_step, luaF_findupval, luaF_newLclosure |
| 80 | VARARG |  | 8001bb84 | 16 | 16 | 16 | 0 | 0 | 6 | luaT_getvarargs |
| 81 | VARARGPREP |  | 8001b760 | 22 | 22 | 12 | 1 | 1 | 21 | luaD_hookcall, luaT_adjustvarargs |
| 82 | EXTRAARG (default, not in table) |  | 8001ac7c | 2 | 0 | 2 | 0 | 0 | 2 |  |

Notes on the table:

* **Arithmetic arms.** Integer `+`/`-` are inline `add`/`sub` on the
  `tt_ == LUA_VNUMINT` fast path. Integer `*` calls `__muldi3`; `%` and `//`
  call `__moddi3` and `__divdi3`, because rv64i has no M extension. Every
  arithmetic arm also has a float path through `__floatdidf` (int→double) and
  soft-float `__*df3`.
* **Arms with no direct jal** (MOVE, LOADI, JMP, TEST, …) call nothing. OP_CALL
  calls `luaD_precall`, which for Lua closures returns a new CallInfo and loops
  back to `startfunc` inside luaV_execute (`luaD_precall` is not re-entered
  recursively). For C functions it reaches `jalr` in `luaD_precall`
  (`precallC`).
* **GETTABUP** (used to fetch `print`) has a fast path through
  `luaH_getshortstr` and a slow path through `luaV_finishget`.

## 5. New C constructs against WHILE (`tools/constructs.py`, `constructs.json`/`.tsv`)

| construct (how counted) | Lua whole | Lua, Lua-origin code | Lua static reach | Lua union dynamic fns | luaV_execute | WHILE whole | WHILE static reach |
|---|---|---|---|---|---|---|---|
| TValue tag loads: `lbu rd, off(rs)` with off ≡ 8 (mod 16), the `tt_` byte of a 16-byte TValue | 472 | 470 | 438 | 334 | 118 | 3 | 2 |
|   … followed within 4 instrs by andi/addi/branch on rd (tag test chain) | 191 | 191 | 175 | 117 | 23 | 0 | 0 |
| all `lbu` | 1,723 | 1,314 | 1,506 | 845 | 127 | 342 | 236 |
| switch jump tables (distinct) / total entries | 52 / 1,890 | 41 / 1,284 | 49 / 1,783 | 17 / 582 | 1 / 82 | 17 / 654 | 14 / 547 |
| `jalr` (indirect call) sites | 72 | 39 | 66 | 26 | 0 | 29 | 23 |
| non-`ret` `jr` sites (jump tables plus indirect tail jumps) | 67 (52 tables + 15) | 46 | 59 | 23 | 1 | 27 | 19 |
| setjmp / longjmp call sites | 1 / 1 | 1 / 1 | 1 / 1 | 1 / 1 | 0 | 2 / 2 | 2 / 2 |
| soft-float call sites (`jal`/`j` to `__*df*`, `__float*`, `__fix*`, `__extend*`, `__trunc*`) | 595 | 267 | 575 | 376 | 170 | 115 | 113 |
| soft-int mul/div call sites (`__muldi3`, `__divdi3`, `__moddi3`, `__udivdi3`, `__umoddi3`, si variants) | 116 (+1 tail) | 53 | 106 | 82 | 10 | 70 (+1) | 59 (+1) |
| 128-bit long double (`__trunctfdf2` sites) | 4 | 0 | 4 | 3 | 0 | 4 | 4 |
| varargs functions (prologue spills a1..a7 incl. a5–a7) | 10 | 5 | 8 | 6 | 0 | 5 | 3 |
| 16-bit `lh`/`lhu`/`sh` | 364 | 147 | 336 | 176 | 4 | 170 | 161 |
| `lb` (signed byte) | 10 | 10 | 10 | 8 | 0 | 0 | 0 |
| `ebreak` (GCC isolated null-deref trap: `ld/sd x,0(zero); ebreak`) | 7 | 7 | 7 | 0 | 0 | 0 | 0 |
| variable shifts `sll/srl/sra(w)` | 192 | 57 | 187 | 98 | 9 | 72 | 57 |
| `memcpy` / `memmove` / `memset` call sites | 37 / 10 / 32 | 28 / 1 / 7 | 31 / 10 / 31 | 26 / 9 / 21 | 1 / 0 / 0 | 12 / 9 / 22 | 12 / 9 / 20 |
| tail-call `j` into another function | 255 | 181 | 210 | 111 | 0 | 56 | 35 |
| direct `jal` call sites | 4,017 | 2,892 | 3,691 | 2,067 | 285 | 1,106 | 955 |

Details on specific constructs:

* **Soft-float breakdown** (whole Lua image):
  * `__muldf3` 98, `__ledf2` 79, `__eqdf2` 71, `__gedf2` 66, `__adddf3` 63,
    `__subdf3` 57, `__floatdidf` 43, `__fixdfdi` 31, `__divdf3` 26,
    `__floatsidf` 23, `__unorddf2` 13, `__fixdfsi` 8, …
  * luaV_execute accounts for 170 of the soft-float sites: `__gedf2` 37,
    `__ledf2` 34, `__floatdidf` 32, `__eqdf2` 22, `__fixdfdi` 20, `__adddf3` 8,
    `__floatsidf` 7, `__divdf3` 4, `__muldf3` 4, `__subdf3` 2.
  * `__floatdidf`/`__fixdfdi` (int64 ↔ double) do not appear in the WHILE ELF.
    All the other soft-float routines are shared.
* **Jump tables.** 41 of the 52 are in Lua code:
  * lcode ×9, lgc ×9, lparser ×4, llex ×2, ldebug ×3;
  * `luaV_execute`, `luaV_equalobj`, `mainpositionTV`, `getgeneric`,
    `loadFunction`, `intarith`, `numarith`, `luaO_pushvfstring`, `lua_gc`,
    `luaB_collectgarbage`;
  * lstrlib: `match_class`, `getoption`, `str_pack`, `str_unpack`.
  * The remaining 11 are libc and libgcc (`_svfprintf_r`, `_vfprintf_r`,
    `_vfiprintf_r`, `__divdf3` ×2, `_strtod_l` ×2, `_strerror_r`,
    `__loadlocale`, `__jis_mbtowc` ×2). Eight of those also exist in WHILE; the
    two `_strtod_l` tables and `_strerror_r` do not.
  * The WHILE ELF has its own 9 tables in `lexer_next`, `statement`, `unary`,
    `value_equal`, `value_print`, `eval_expr` and `exec_stmt`. So jump tables
    are not a new idiom; the 82-way table is.
  * Executed jump tables: while.lua runs `luaV_execute`, `mainpositionTV`,
    `loadFunction`, `luaO_pushvfstring`, `lua_gc` and `_svfprintf_r`. The union
    adds `luaV_equalobj`, `getgeneric`, `intarith`, `lua_getinfo`,
    `match_class`, `__divdf3` and `_vfprintf_r`.
* **Indirect calls (`jalr`).** 39 are in Lua code:
  * `dumpFunction`/`luaU_dump` 10 each (lua_Writer);
  * `luaE_warnerror` 4 (warnf);
  * `luaD_rawrunprotected` (Pfunc), `luaD_precall`/`luaD_pretailcall`
    (lua_CFunction);
  * `luaM_malloc_`/`realloc_`/`free_` (`g->frealloc` = `l_alloc`);
  * `lua_newstate`, `luaZ_fill` (lua_Reader), `luaD_throw` (panic),
    `luaD_hook`, `resume`, `unroll`, `resizebox`.
  * Executed sites: 13 for while.lua and 16 for the union, in `luaM_*` ×3,
    `luaD_precall`, `luaD_pretailcall`, `luaD_rawrunprotected`,
    `lua_newstate`, `luaZ_fill`, plus libc `exit`, `_fwalk_sglue`,
    `__sflush_r`, `_fclose_r`, `__sfvwrite_r`, `_svfprintf_r`/`_vfprintf_r`,
    and `memset`'s computed `jalr -104(a3)`.
* **The 15 non-table indirect `jr`s:**
  * libgcc `__udivsi3`/`__umodsi3`/`__umoddi3`/`__moddi3` return through
    `jr t0` (6 sites; a millicode-style internal call);
  * `memset` `jr 12(a3)` (a computed jump into its store ladder);
  * pointer tail calls in `tryagain`, `close_state`, `luaE_warning`,
    `luaE_warnerror`, `str_format`, `_reclaim_reent`, `_mbtowc_r`,
    `_wctomb_r`.
* **setjmp/longjmp.** There is 1 `setjmp` call (in `luaD_rawrunprotected`) and
  1 `longjmp` call (in `luaD_throw`). WHILE has 2 of each. Both routines are
  byte-identical to the WHILE ELF's, which already proves them.
  * while.lua executes `setjmp` only.
  * The union also executes `longjmp` (f1_for, f3_pcall, f3_uncaught and
    f6_coroutines).
* **Varargs.**
  * Lua: `lua_pushfstring`, `luaO_pushfstring`, `luaG_runerror`,
    `luaL_error`, `lua_gc`.
  * libc (same as WHILE): `fprintf`, `snprintf`, `fiprintf`, `_fprintf_r`,
    `_fiprintf_r`.
  * `luaO_pushvfstring` walks the `va_list` (282 instructions, executed by
    while.lua).
* **128-bit.** The only 128-bit code is `__trunctfdf2` (long double in printf),
  which is shared with WHILE. There are no `__multi3`/TI-mode sites.
* **Other new items:**
  * `lb` sign-extending byte loads (10 sites, all in Lua code: `lua_getinfo`
    ×2, `luaG_getfuncline`, `luaG_traceexec`, `basicgetobjname`,
    `luaK_fixline`, `jumponcond`, `luaH_getint`, `luaH_getn`,
    `luaH_realasize`; `ls_byte` fields such as `lineinfo`);
  * 7 `ebreak` null-deref traps in lgc/lparser, never executed;
  * `sra`/`sraw` (13 sites: libm `__ieee754_pow` ×4, `__ieee754_fmod` ×2,
    `floor` ×2, `__ulp`, plus `llex` ×2 and `luaC_runtilstate` ×2). Lua's own
    `>>` is logical (`luaV_shiftl` uses `srl`);
  * 16-bit `lh`/`lhu`/`sh`: 147 sites in Lua code (for example the
    `CallInfo.callstatus` and `nresults` fields), against 170 in the whole
    WHILE ELF, all of which are in libc.

## Files

* `tools/`: self-contained scripts; `tools/run_all.sh` reruns everything.
* `numbers.json` (headline numbers) and `old/numbers.json` (the previous link, for diffing).
* `arms_table.md`: the per-opcode table used in section 4.

* `lua_disasm.txt` and `while_disasm.txt`: `objdump -d` output.
* `lua_census.{json,out}` and `while_census.{json,out}`: section 1.
* `lua_reach.json` and `while_reach.json`: reachable and unreachable lists,
  jump tables with every target, indirect sites, and the reason each
  indirectly reached function was added.
* `dynamic.json` and `per_origin.{tsv,md}`, plus `traces/*.pcs.tsv`
  (`pc count before after`) and `traces/*.meta`: section 2.
* `template_match.json` and `function_match.tsv` (per function: origin, size,
  category, WHILE counterpart, whether it is in syi scope, static and dynamic
  flags), plus `demo/`: section 3.
* `luaV_execute_arms.{json,tsv}`: section 4.
* `constructs.{json,tsv}`: section 5.

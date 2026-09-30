# Round 3: callee census and L-C3 (callee frame law), results

Input for ROUND-3.md §1(b) and §2. Checked on the ELF (objdump) and on Sail
traces of the Lean emulator, never against the Lean model.

Rerun (about 6 min in all; `LC3_WORK` holds the patched ELFs, default `/tmp/lc3_work`):

```
cd abstractions/checks/round3
M=~/Documents/code/ship-your-lua/c/tests
for f in progs/*.lua $M/difftest/f1_*.lua; do python3 -c "import lc3_trace as T; T.compile_lua('$f')"; done
W=/tmp/lc3_work; F1="$M/while.luac $M/f1_ops.luac $M/f1b_bits.luac $M/print_print.luac $M/f1_src.luac $W/f1_while.luac $W/lc3_arith.luac $W/lc3_grow.luac $W/lc3_strcmp.luac $W/lc3_div0.luac $W/lc3_forerr.luac $W/lc3_opint.luac"
python3 callee_census.py --dyn $F1 --json $W/census_f1.json   # static + dynamic census
python3 callee_groups.py $W/census_f1.json                      # dynamic, grouped
python3 lc3_footprint.py $F1                                    # L-C3 on F1 programs
python3 lc3_footprint.py $M/f4_strlite.luac $W/f1_arith.luac $W/f1_cond.luac $W/f1_for.luac  # beyond F1
```

Files: `lc3_trace.py` (patched ELFs via `gen_lua_boot_witness.patched_elf`,
streamed `--trace-all` rows), `callee_census.py`, `callee_groups.py`,
`lc3_footprint.py`, `progs/lc3_*.lua`. The `progs` programs are:

- `lc3_arith`: MUL/MOD/IDIV (+K), and FORPREP with step 7, −9 and 999999999;
- `lc3_strcmp`: EQ/EQK/LT/LE on strings;
- `lc3_grow`: 20 locals, then `print`, which grows the Lua stack;
- `lc3_div0`, `lc3_forerr`, `lc3_opint`: the three error chains (`//0`, a zero
  `for` step, `nil + 1`).

`f1_arith`/`f1_cond`/`f1_for` are not F1: they use `type`, `pcall`, closures
and string arithmetic. They are run separately.

## 1. How many distinct callees A1 needs contracts for

The F1 opcode set is `Lua/Fragment.lean`'s: 54 opcodes, which includes
MMBIN/MMBINI/MMBINK. PHASES' "52 F1 arms" is the same set without two of them.

**Static (objdump call graph).**
- Edges: `jal`, a `j` into another function's start, and resolved `jalr`. The
  resolved `jalr` are the precall C function = `luaB_print`,
  `g->frealloc` = `l_alloc`, and `fp->_write` = `__swrite`.
- Each arm is walked from its jump-table target to the head.

| group | roots | transitive closure | cut at GC step / `luaV_execute` re-entry / TM calls |
|---|---|---|---|
| (a) arms' direct callees (all paths, float and TM included) | 27 | 315 | 196 |
| (b) error paths (`luaG_*error` → `luaD_throw` → `longjmp` → `main` → `fprintf`, `exit`) | 6 | 320 | 155 |
| (c) CALL `print`, RETURN*, and the frames `luaV_execute` returns through | 12 | 343 | 304 |
| (d) stack growth, CI allocation, VARARGPREP | 5 | 315 | 154 |
| **all** | | **343** | **320 functions, 32,087 instructions** |

21 indirect sites in the cut closure stay unresolved, among them
`luaD_throw`'s panic, `exit`'s atexit handlers, `_svfprintf_r` and `luaD_hook`.

Under `Supported` (integers only: `ValRepr` never has tag 19, and trap = 0),
**37 of the 54 arms call nothing on a live path**: every call they contain is
on a float branch, an MMBIN metamethod branch or an error branch. The other
17 arms need 16 distinct direct callees:

| arm(s) | live direct callees |
|---|---|
| MUL, MULK | `__muldi3` |
| MOD, MODK | `__moddi3` |
| IDIV, IDIVK | `__divdi3`, `__moddi3` (floor fix-up) |
| FORPREP | `__hidden___udivdi3` (the iteration count, when step ≠ 1), `luaV_tointeger`, `luaV_tonumber_` |
| EQ, EQK | `luaV_equalobj` |
| LT, LE | `l_strcmp` (→ `strcoll` → `strcmp`, `strlen`) |
| GETTABUP | `luaH_getshortstr` (`luaV_finishget` on a miss) |
| CALL | `luaD_precall` (`luaG_tracecall` only with hooks) |
| RETURN, RETURN0, RETURN1 | `luaD_poscall` (`luaF_close` with k) |
| VARARGPREP | `luaT_adjustvarargs` (`luaD_hookcall` only with hooks) |

**Dynamic.** These are the functions entered at or below `luaV_execute` in 12
F1 runs:

- the 5 validation chunks;
- `f1_while`;
- the 6 `lc3_*` programs.

| group | functions | instructions | exclusive to the group |
|---|---|---|---|
| (a) arm helpers, normal paths | 11 | 557 | 7 |
| (b) error chains (3 kinds exercised) | 81 | 11,608 | 30 |
| (c) CALL `print` (with the first-call stdio init) | 81 | 9,155 | 31 |
| (c) RETURN and exit (entered; `ccall` … `main` are returned *into*, not entered, and add about 7 frames) | 19 | 837 | 0 |
| (d) stack growth (inside CALL at 20 locals) | 7 | 754 | 0 |
| (d) VARARGPREP | 1 | 64 | 1 |
| **total distinct** | **131** | **14,583** | |

**The contract problem is dominated by `print` and the error chains, not by
the arms.** The 17 arms with live calls need 11 functions (557 instructions).
CALL, the error paths and the exit path need about 120 more, most of them
newlib stdio, `_svfprintf_r` (3,212 instructions) and dlmalloc.

**Contracts that already exist, and at which addresses:**

| callee (Lua ELF size, instructions) | needed by | contract here? |
|---|---|---|
| `__muldi3` (9) | MUL, MULK; `_fwrite_r` | `muldi3_spec` (Vsa/Sim/Muldi3Spec), **at WHILE addresses**; Lua code pin in `Lua/Vm/Code` |
| `__hidden___udivdi3` (18) | FORPREP; `_fwrite_r` | `udivdi3_spec` (Vsa/Sim/DivLoops), **at WHILE addresses**; Lua code pin |
| `__divdi3` (2), `__moddi3` (15), `__umoddi3` (13) | IDIV/MOD (+K); `__sfvwrite_r` | sites only (DivSites2/3, WHILE); no spec; Lua code pins for divdi3/moddi3 |
| `luaV_equalobj` (212), `l_strcmp` (55) + `strcoll`/`strcmp`/`strlen` | EQ/EQK, LT/LE | Lua code pins only; `strcmp`/`strlen` code pins at WHILE addresses (`Vsa/Sim/Code/Strcmp`, `Strlen`) |
| `luaH_getshortstr` (27), `luaV_finishget` (93) | GETTABUP | Lua code pins only |
| `luaV_tointeger` (90), `luaV_tonumber_` (48) | FORPREP | Lua code pins only |
| `luaT_adjustvarargs` (64) | VARARGPREP | Lua code pin only |
| `luaD_precall` (226) → `luaB_print` (62) → `luaL_tolstring` (153) → `lua_pushfstring`/`luaO_pushvfstring` (282)/`snprintf`/`_svfprintf_r` (3,212) → `luaS_newlstr`/`internshrstr` → `fwrite` → `_fwrite_r` (122) → `__sfvwrite_r` (311) → `__swrite` → `_write_r` → `_write` (166, HTIF) | CALL | stdio specs (`Stdout.*`, `Fprintf.*`) **at WHILE addresses, not ported** (PHASES A0.2); `_write` `TohostSite` not instantiated for Lua (A0.5); Lua code pins for precall/print/tolstring/fwrite only |
| `_malloc_r` (562), `_realloc_r` (396), `_free_r` (193) | CALL (CI, strings, stdio buffer), stack growth, errors | **SWP step tables at Lua addresses** (`VsaIris.Vsa.AllocSteps`): the one callee family ready at Lua addresses |
| `memcpy`/`memmove`/`memset` (74/74/55) | print, realloc, errors | `MemcpySpec` at WHILE addresses |
| `luaD_growstack` (57), `luaD_reallocstack` (99), `correctstack` (30), `luaC_step` (338), `luaG_traceexec` | CALL at ≥ 15 locals | none |
| `luaD_poscall` (147), `exit`/`__call_exitprocs`/`_fclose_r`/`__sflush_r`/`_exit` | RETURN*, the exit path | Lua code pin for `luaD_poscall`; `exit_haltFact`/`Console` generic (ported), not instantiated |
| `luaG_runerror` (51), `luaG_opinterror`, `luaG_forerror` → `luaO_pushvfstring` … `luaD_throw` (33) → `longjmp` (17) → `fprintf` → `_vfprintf_r` → `exit` | error paths (`stuck_sim`) | Lua code pins for the three `luaG_*`; nothing else |

## 2. L-C3 on the traces

**Method.**
- **Shadow memory.** The PT_LOAD image, then every traced store. All loads were
  checked against it: **0 mismatches**.
- **Activations.** An activation is a linking `jal` from `luaV_execute`'s code
  (its successor has `ra = pc+4`), until pc+4 is reached with the same `sp`.
  If `sp` rises above the call's `sp` first, it is a non-return (`longjmp`).
- **Stores.** Every store during an activation, nested callees included, is
  classified against a snapshot taken at the call:
  - the callee's frame (below the call's `sp`);
  - `luaV_execute`'s frame, or frames above it;
  - `L->field`, `ci->field`, `ci->next->field`, `G->field`;
  - Lua stack slots: below `base`, `R[<A]`, `R[≥A]`, or above `maxstacksize`;
  - `.data`/`.bss` by symbol, the heap, and `tohost`.
- **The arms' own code.** The same classification was applied to the stores
  `luaV_execute`'s arm code makes itself, snapshotted at the head.

**Results (F1 programs; activation counts are summed over the 12 runs).**

| helper | activations | stores outside its own frame | purity against a Python oracle |
|---|---|---|---|
| `__muldi3` | 43 | none | a0 = a0·a1 mod 2⁶⁴: 43/43 |
| `__moddi3` | 238 | none | C truncating remainder: 238/238 |
| `__divdi3` | 7 | none | C truncating quotient: 7/7 |
| `__hidden___udivdi3` | 15 | none | unsigned quotient: 15/15 |
| `luaV_equalobj` | 7 | none | raw equality of the two TValues (short strings by pointer, long by bytes): 7/7 |
| `l_strcmp` | 6 | none | sign = byte-wise comparison of the contents: 6/6 |
| `luaH_getshortstr` | 48 | none | (read-only) |
| `luaV_tointeger` | 16 | **`luaV_execute`'s frame** (`sp+40`: the out-parameter `&init`/`&limit`) | — |
| `luaT_adjustvarargs` | 12 | `ci->func`, `ci->top`, `ci->nextraargs`, `L->top`, slots `R[≥0]` (it copies the function and fixed parameters up) | — |
| `luaD_poscall` | 9 | `L->ci`, `L->top` | — |
| `luaD_precall` (CALL `print`) | 45 | see below | — |
| `luaG_runerror`, `luaT_trybiniTM` (error) | 2 + 1, **all non-returning** | heap, `G->{GCdebt,allgc,strt.nuse}`, `L->top`, slots above `maxstacksize`, and `errorJmp->status` **in `luaD_rawrunprotected`'s frame** (above `luaV_execute`'s) | — |

The `luaD_precall` (CALL `print`) footprint over 45 calls:

- **Memory:**
  - heap: 2,033 stores (interned strings, the new `CallInfo`, the stdio
    buffer, malloc chunk headers);
  - `__sf` stdout `FILE`: 1,468;
  - `__malloc_av_`: 118, plus the mallinfo and sbrk globals;
  - the `.data` globals `errno`, `fds`, `files`, `fs_ready`,
    `_impure_data` and `__stdio_exit_handler`;
  - the HTIF mailbox (`tohost`/`fromhost`): 657 stores, one pair per character.
- **Lua state:**
  - `L->top`, `L->ci` and `L->nci`;
  - `ci->next->{func,top,nresults,callstatus}`;
  - `G->{GCdebt, allgc, strt.nuse, totalbytes, strcache}`.
- **Lua stack:** slots `R[≥A]` (150) and slots above `maxstacksize` (80).
- **Only at 20 locals (stack growth):**
  - `L->stack`, `L->stack_last`, `ci->func`, `ci->top`,
    `L->base_ci.{func,top}` (`correctstack`);
  - `R[<A]` (36) and below `base` (19). These are **allocator metadata and a
    reused `CallInfo` written into the freed old stack block** (`_free_r`,
    `_malloc_r`, `luaE_extendCI`);
  - `ci->trap`, set by `luaG_traceexec` at the next head.

**Arms' own stores** (not helpers), per opcode:

- **Most arms** write only `R[A]`.
- **FORLOOP** writes `R[A]`, `R[A+1]` and `R[A+3]`; **FORPREP** writes
  `R[A+1]` and `R[A+3]`, plus its frame out-parameters.
- **LOADNIL** writes `R[A..A+B]`.
- **GETTABUP** writes `R[A]` plus a spill in `luaV_execute`'s frame.
- **`ci->savedpc` and `L->top`** (`savepc`/`Protect`) are written by:
  - CALL, and MOD/MODK/IDIV/IDIVK on every execution (230/230 for MODK);
  - EQ, LT and LE on strings;
  - FORPREP and MMBIN*.

  They are *outside* `VmRel`'s window (`Ranges.ci_out`; `L` is in the
  complement).
- **RETURN** writes `ci->savedpc`, `ci->func` and `L->top`.
- **VARARGPREP** writes `ci->savedpc`.

Beyond F1 (`f4_strlite`, `f1_arith`/`cond`/`for`):

- `luaT_trybinTM` on string arithmetic *returns*, after a metamethod call
  that re-enters `luaV_execute` (it writes `ci->next->…`).
- `luaV_concat` writes the heap and `R[≥A]`.
- CLOSURE writes the heap.

**Verdict: L-C3 as stated is FALSE, and holds in a refined form.**

1. **Pure leaves (holds exactly):** the soft-int helpers, `luaV_equalobj`,
   `l_strcmp` and `luaH_getshortstr`.
   - They write only below the call's `sp`, and their result is the oracle's
     function of the inputs: **0 counterexamples in 316 soft-int and 13
     compare activations**.
   - For EQ/LT the inputs include the *memory* behind the pointers (TString
     bytes, TValues). So the law is "a0 = f(⟦args⟧_mem)", with the pointed-to
     representation read through the complement.
2. **Out-parameters in the caller's frame (refinement).** `luaV_tointeger`
   writes into `luaV_execute`'s frame at an address the caller passes.
   - The footprint must include "declared out-pointers", not only "below
     `sp`".
   - The address is within `Win`'s C-frame part, so `VmRel` survives it.
3. **Runtime-state helpers (refinement).** CALL, RETURN and VARARGPREP have a
   *named runtime footprint*: {`L->top`, `L->ci`, `L->nci`, `ci->func`,
   `ci->top`, `ci->nextraargs`, `ci->next->*`, `R[≥A]` and the slots above
   `maxstacksize`}, relative to `base`/`A`.
   - `print` adds the heap (allocator, interned strings, `CallInfo`), `G`'s
     GC and string-table counters, the stdout `FILE` and the fd table, and
     the console (HTIF).
   - This is the kill-port shape (every register ≥ A is clobbered) plus an
     allocator/heap ownership footprint. It is **not** "own frame +
     outputs".
4. **The arms themselves break `Core.frame` at `ci->savedpc`/`L->top`.**
   - The arms named above (MOD, CALL, …) write both fields directly (`savepc`,
     `Protect`). The frame law for arms must let exactly {`ci->savedpc`,
     `L->top`} vary, not the whole complement.
   - This is already the pilot's open item for MOD/IDIV; the trace confirms
     the set is those two fields and nothing else.
5. **Stack growth breaks "relative to base" unless the law re-bases.**
   - After `luaD_reallocstack`, the old register block is freed memory that
     the allocator and `luaE_extendCI` overwrite. So no law can keep "old
     slots unchanged".
   - The refined law: the helper returns with `ci->func` moved (`correctstack`)
     and trap set. That the new slots `R[<A]` equal the old ones is not checked
     here.
   - This is the `VmRel`-with-new-`func` route already planned.
6. **Errors never return.** Every activation of `luaG_runerror` or
   `luaT_trybin*TM` (on a non-number) ended by `longjmp` (3/3). Their only
   write outside the heap/`G`/`L->top` is `errorJmp->status` in
   `luaD_rawrunprotected`'s frame. For `stuck_sim` the law needed is "no
   return to the head, and the program exits nonzero", not a frame.

The refined L-C3 splits into three shapes, each a single law:

- **(pure)** `wp(call f) = λQ. Q[a0 := f(⟦a0..a3⟧)]`, with memory below `sp`
  havocked;
- **(runtime)** a footprint of named `L`/`ci`/`G` fields, slots ≥ A, and heap
  ownership, relative to `base`;
- **(noreturn)** `wp(call f) = exit ≠ 0`.

Only the pure shape is small. It covers 10 of the 11 functions the arms
entered on normal paths: all of them except `luaV_tointeger`, which writes
an out-parameter (shape 2).

#!/usr/bin/env python3
"""Emit the site batteries and SegSt segment theorems of every F1 arm of
luaV_execute.

The arms and their segments are scripts/draft_f1_arms.py's (reach from the
jump-table target up to the fetch head, cut at branch targets and after
every control transfer), with one more cut: after every `jal`, so that a
segment ends at a call and the callee is composed at the arm level. A
segment that ends in a conditional branch is emitted once per polarity
(`_t` taken, `_n` not taken).

For each segment scripts/syi/disasm_to_segment.py's `complete` builds a
gen_segment.py spec with `"boundary": "segst"` and no hole: the pre/post
states are `SegSt` over the read-before-written registers and the memory
`m0`, and the address side conditions, branch guards and `jr` alignments
are named hypotheses `h*_<step>` of the theorem. The instructions are
proved by gen_sites.py site lemmas (loads through the TOTAL classes),
decoded by `Vsa.Sim.decodeW`, fetched from `.text` through the generated
code pins (`Lua.Vm.Code.luaV_execute_at_<addr>`), with `.text` carried
across stores by `Lua.Vm.Arms.TextLoaded.{writeMap8,writeMap4,insert}`.

Output (GENERATED, check.sh stage 1 checks drift):
    Lua/Vm/Arms/Sites/S<nn>.lean   site batteries (unique addresses)
    Lua/Vm/Arms/Segs/G<nn>.lean    segment theorems `seg_<lo>_<hi>[_t|_n]`
    Lua/Vm/Arms.lean               index
    Lua/Vm/Arms/arms.tsv           arm -> its segment theorems

    python3 scripts/gen_lua_arms.py [--check] [--only OP_MOVE,OP_JMP]
"""
import argparse
import csv
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts/syi"))
import draft_f1_arms as dfa          # noqa: E402
import disasm_to_sites as d2s        # noqa: E402
import disasm_to_segment as d2seg    # noqa: E402
import gen_sites                     # noqa: E402
import gen_segment                   # noqa: E402

OUT = ROOT / "Lua/Vm/Arms"
NS = "Lua.Vm.Arms"
PRED = "Lua.Vm.Arms.TextLoaded"
TEMPLATE = ("Lua.Vm.Code.luaV_execute_at_{addr} "
            "(Lua.Vm.Code.textLoaded_LuaV_execute_p{part}Loaded hmem)")
CODE_IMPORTS = ["Lua.Vm.Code.FixedImage_LuaV_execute", "Lua.Vm.Arms.Text"]
SURVIVAL = {"sd": "Lua.Vm.Arms.TextLoaded.writeMap8 $prev _ {hwin}",
            "sw": "Lua.Vm.Arms.TextLoaded.writeMap4 $prev _ {hwin}",
            "sh": "Lua.Vm.Arms.TextLoaded.writeMap2 $prev _ {hwin}",
            "sb": "Lua.Vm.Arms.TextLoaded.insert $prev _ {hwin}"}
JT = json.load(open(dfa.ARMS_JSON))["summary"]["jump_table"]
# The arms with an A1 simulation proof (Lua/Vm/Sim/Arms, scripts/gen_lua_arm.py).
# Their segments carry the registers `luaV_execute` holds at the fetch head
# (`KEEP`: sp, gp, s0 = L, s1 = 81, s2 = 3, s3 = pc + 1, s4 = the instruction,
# s5 = trap, s7 = ci, s8 = the jump table, s9 = base, s11 = pc) and the console
# output, the frame `Lua.Vm.Sim.VmRel` needs; the other arms' segments do not
# pay for it until their simulation lands.
SIM_OPS = {"OP_MOVE", "OP_LOADI", "OP_JMP", "OP_ADD", "OP_EQI", "OP_FORLOOP", "OP_SUB",
           "OP_ADDI", "OP_ADDK", "OP_SUBK",
           "OP_BAND", "OP_BOR", "OP_BXOR", "OP_LTI", "OP_GTI", "OP_LEI", "OP_GEI",
           "OP_LOADTRUE", "OP_LOADFALSE", "OP_LFALSESKIP", "OP_LOADK", "OP_BNOT",
           "OP_NOT", "OP_TEST", "OP_TESTSET",
           # round-3 bake-off (KIT): the held-out arms
           "OP_MUL", "OP_MOD", "OP_EQ",
           # kit lane 1: the arithmetic and bitwise family
           "OP_MULK", "OP_MODK", "OP_IDIV", "OP_IDIVK", "OP_UNM", "OP_SHL", "OP_SHR",
           "OP_SHLI", "OP_SHRI", "OP_BANDK", "OP_BORK", "OP_BXORK"}
# lane KIT-2: the control and compare family
SIM_OPS |= {"OP_FORPREP", "OP_LOADNIL", "OP_EQK", "OP_LT", "OP_LE"}
# lane F1-3: `OP_VARARGPREP` at the entry (`luaT_adjustvarargs` a summarised call)
SIM_OPS |= {"OP_VARARGPREP"}
# Arms with a kernel outside the census summary's F1 list (the strings slice
# of `Lua/Fragment.lean`: `LEN` on a string). Their segments and sites are
# emitted in modules of their own (`Segs/X<op>`, `Sites/SX<op>`), so the
# address-chunked modules of the F1 arms stay as they are.
EXTRA_ARMS = ["OP_LEN"]
# lane F1-F6: `OP_DIV`, `OP_DIVK` (`op_arithf(K)`, always float: no integer kernel
# case, so outside the census summary's F1 list)
EXTRA_ARMS += ["OP_DIV", "OP_DIVK"]
# lane F1-21: `OP_POW`, `OP_POWK` (`op_arithf(K)`'s `luai_numpow`, always float)
EXTRA_ARMS += ["OP_POW", "OP_POWK"]
# extra arms whose segment modules the index `Lua/Vm/Arms.lean` does not import
# (their at-files do, `gen_lua_at.py` `IMPORTS`), so a new arm leaves the index,
# and every at-file importing it, as they are
STANDALONE = {"OP_POW", "OP_POWK"}
SIM_OPS |= set(EXTRA_ARMS)
KEEP = [2, 3, 8, 9, 18, 19, 20, 21, 23, 24, 25, 27]
# The register invariant a `sim` segment threads (every GPR present, the HTIF
# mailbox idle: `VmRel`'s `Core.ok`), one step lemma per step class.
OK = {"pred": "Lua.Vm.RegsOk", "ns": "Lua.Vm.RegsOk"}
OK_IMPORT = "Lua.Vm.Arms.RegsOk"
SITES_PER_MODULE = 40
SEGS_PER_MODULE = 12
HEADER = "GENERATED by scripts/gen_lua_arms.py -- do not edit."


# The helpers the held-out arms call (M5 call nodes), as `[lo, hi)` code
# ranges: their segments are cut like an arm's (branch targets, after every
# control transfer and `jal`) and carry the caller's fetch-head registers
# (`KEEP`), the caller's temporaries live across the call (`s6` = `R[A]`,
# `s10`; `t0`, `__moddi3`'s return address across `__udivdi3`) and, by a
# liveness fixpoint over all helper segments, every register a later segment
# reads, so a helper summary composes with the arm's segments by pin lookup.
# (name, code-pin name, lo, hi, caller temporaries, extra roots, stops): the
# extra roots are computed-jump targets (`luaV_equalobj`'s `ttypetag` jump
# table: nil/booleans, then integer, short string and light C function); the
# stops are where a path leaves the F1 values (number variants that differ,
# a long string's `luaS_eqlngstr`).
SUMMARISED = {"__muldi3", "__moddi3", "luaV_equalobj", "__divdi3"}
# lane KIT-2: FORPREP's `forlimit` (`luaV_tointeger` on an integer limit) and
# its count division
SUMMARISED |= {"luaV_tointeger", "__hidden___udivdi3"}
# lane float-sf3: `__muldf3` keeps a4-a7, t1, t3, t4 live across its four
# `__muldi3` calls (gcc's -fipa-ra: `__muldi3` writes only a0-a3), so
# `__muldi3`'s segments carry them too (`PASS_THROUGH`)
HELPERS = [("__muldi3", "__muldi3", 0x8002f6c8, 0x8002f6ec, [22, 26, 6, 14, 15, 16, 17, 28, 29], [], []),
           ("__hidden___udivdi3", "__hidden___udivdi3", 0x8002f734, 0x8002f77c, [5, 22, 26],
            [], []),
           ("__moddi3", "__moddi3", 0x8002f7b0, 0x8002f7e0, [22, 26], [], []),
           # lane F1-F4: the float paths are followed (the same-variant float arm
           # `0x8001b90c`, `__eqdf2`, a root of the jump table; the mixed
           # integer/float paths from `0x8001b810`, `luaV_tointegerns(F2Ieq)`
           # inlined: `floor`, `__eqdf2`, the range, `__fixdfdi`)
           ("luaV_equalobj", "LuaV_equalobj", 0x8001b780, 0x8001bad0, [],
            [0x8001b84c, 0x8001b7f4, 0x8001b8f8, 0x8001b90c], []),
           # `__divdi3` (`0x8002f72c`): its sign tests, then either falls through
           # into `__hidden___udivdi3` (`0x8002f734`, its own helper) or branches
           # into the sign fix-ups that objdump labels `__umoddi3+0x10`/`+0x20`
           # (a second range, pinned as `__umoddi3`)
           ("__divdi3", "__divdi3", 0x8002f72c, 0x8002f734, [22, 26], [], []),
           # lane float-sf4: from `__umoddi3`'s own entry `0x8002f77c` (`mv t0,ra; jal
           # __udivdi3; mv a0,a1; jr t0`: `__divdf3`'s `udiv_qrnnd` remainders);
           # `__divdi3`'s sign fix-ups `0x8002f78c`, `0x8002f79c` are roots
           # lane F1-15: from its own entry `0x8002f77c` too (`luaS_new`'s `point2uint(s) % 53`)
           ("__umoddi3", "__umoddi3", 0x8002f77c, 0x8002f7b0, [22, 26], [0x8002f78c, 0x8002f79c], [])]
# lane KIT-2: `luaV_tointeger` on a non-string, non-float value (the string
# and float paths `0x8001ae4c`, `0x8001ae98` are stops: F1's limits are
# integers, `forprepK`)
HELPERS += [("luaV_tointeger", "LuaV_tointeger", 0x8001ade8, 0x8001af50, [22, 26], [],
             [])]
# lane F1-F8: FORPREP's coerced classes. `luaV_tointeger`'s float path
# (`0x8001ae98`: `floor`, `__eqdf2`, `__adddf3` for `F2Iceil`, the range,
# `__fixdfdi`) is followed; `luaV_tonumber_` on a non-string (`cvt2num`: an
# integer by `__floatdidf`; the string path `0x8001abac` a stop)
SUMMARISED |= {"luaV_tonumber_"}
# lane F1-F8: `luaO_str2num` on an integer numeral (`l_str2int` inlined: the
# leading spaces, the sign, the decimal digits with the overflow test, the hex
# digits, the trailing spaces); the `l_str2d` fallback `0x80011b5c` a stop
HELPERS += [("luaO_str2num", "LuaO_str2num", 0x80011998, 0x80011c94, [22, 26], [], [0x80011b5c])]
HELPERS += [("luaV_tonumber_", "LuaV_tonumber_", 0x8001ab58, 0x8001ac18, [22, 26], [],
             [])]
# axis S (S-SCAN): the string callees. `luaV_equalobj`'s long-string arm
# (`0x8001b8f8`, now a root of its jump table) tail-calls `luaS_eqlngstr` ->
# `memcmp`; `OP_LT`/`OP_LE` on two strings call `l_strcmp` -> `strcoll`
# (`j strcmp`) and `strlen`.
SUMMARISED |= {"l_strcmp"}
HELPERS += [("luaS_eqlngstr", "LuaS_eqlngstr", 0x80017184, 0x800171d4, [], [], []),
            ("memcmp", "Memcmp", 0x80036198, 0x80036204, [22, 26], [], []),
            ("l_strcmp", "L_strcmp", 0x8001a704, 0x8001a7e0, [], [], []),
            ("strcoll", "Strcoll", 0x80036374, 0x80036378, [22, 26], [], []),
            ("strcmp", "Strcmp", 0x8003b920, 0x8003ba4c, [22, 26], [], []),
            ("strlen", "Strlen", 0x8003b770, 0x8003b844, [22, 26], [], [])]
# lane F1-15: the string scans keep the caller's `s6`, `s10` (`luaS_new`,
# `internshrstr` call them from C frames that must return them); their callers
# on the arm route carry them only where they are live (`PASS_THROUGH`)
PASS_THROUGH_S = {0x80036198: {"x22", "x26"}, 0x80036374: {"x22", "x26"}, 0x8003b920: {"x22", "x26"},
                  0x8003b770: {"x22", "x26"}}
# lane F1-3: `luaT_adjustvarargs(L, 0, ci, p)` at the entry: no fixed
# parameters (the copy loop `0x80019858` is a stop: `A = 0`, `blez` taken) and
# room on the stack (the `luaD_growstack` call `0x800198bc` is a stop)
SUMMARISED |= {"luaT_adjustvarargs"}
HELPERS += [("luaT_adjustvarargs", "LuaT_adjustvarargs", 0x800197f0, 0x800198f0, [], [],
             [0x80019858, 0x800198bc])]
# lane F1-2: `OP_LEN`'s `luaV_objlen` on a string (variants 4 and 20); the table
# path (`luaH_getn`, `0x8001bb78`) and the metamethod path (`0x8001bb14`) are
# stops: `δ .len` has no other F1 value
HELPERS += [("luaV_objlen", "LuaV_objlen", 0x8001bae0, 0x8001bc28, [], [], [0x8001bb14, 0x8001bb78])]
SUMMARISED |= {"luaV_objlen"}
# lane F1-4: the `OP_RETURN*` family (`FinalSim`: the return out of
# `luaV_execute`, `CIST_FRESH`), its callees with nothing open
# (`luaF_close`: `L->openupval = NULL`, the `bnez` to `0x8000c11c` a stop;
# `L->tbclist < base`, the `bltu` not taken at `0x8000c264` a stop) and
# `luaD_poscall` with no hooks and `wanted = 0` (`0x8000a3bc`, `0x8000a4d8`
# stops), and the C return chain after `luaV_execute`'s `ret`: `ccall`'s tail,
# `luaD_rawrunprotected`'s, `luaD_pcall`'s and `lua_pcallk`'s (status 0),
# `main`'s, `_start`'s `j exit`, `exit` (`__call_exitprocs` with `__atexit =
# NULL`, the `0x8003bb3c` loop a stop; no `__stdio_exit_handler`, its `jalr` a
# stop), and `_exit` up to its `tohost` store
SIM_OPS |= {"OP_RETURN", "OP_RETURN0", "OP_RETURN1"}
SUMMARISED |= {"luaF_close", "luaF_closeupval", "luaD_poscall"}
HELPERS += [("luaF_close", "LuaF_close", 0x8000c224, 0x8000c380, [22, 26], [], [0x8000c264]),
            ("luaF_closeupval", "LuaF_closeupval", 0x8000c114, 0x8000c224, [22, 26], [],
             [0x8000c11c]),
            # lane F1-14: `wanted ≥ 1` (`C ≥ 2`) with no results: `wanted = 1`'s nil
            # (`0x8000a548`) and the nil-fill loop (`0x8000a4a4`, a root); the
            # result copies (`0x8000a44c`, `nres > 0`) and the close path
            # (`0x8000a5e4`, `wanted < -1`) are stops
            ("luaD_poscall", "LuaD_poscall", 0x8000a39c, 0x8000a5e8, [22, 26], [0x8000a4a4],
             [0x8000a3bc, 0x8000a44c, 0x8000a5e4]),
            ("luaD_callnoyield", "LuaD_callnoyield", 0x8000b0bc, 0x8000b0e0, [22, 26], [], []),
            # lane F1-16: from `setjmp`'s return (`0x80009c24`), where `longjmp`
            # lands with `a0 = 1`; the `a0 = 0` path (the protected call) a stop
            ("luaD_rawrunprotected", "LuaD_rawrunprotected", 0x80009c24, 0x80009c60, [22, 26],
             [], [0x80009c28]),
            ("luaD_pcall", "LuaD_pcall", 0x8000b4c0, 0x8000b4f0, [22, 26], [], []),
            ("lua_pcallk", "Lua_pcallk", 0x8000413c, 0x80004154, [22, 26], [], []),
            ("main", "Main", 0x80001808, 0x80001820, [22, 26], [], []),
            ("_start", "_start", 0x80000038, 0x8000003c, [22, 26], [], []),
            ("exit", "Exit", 0x8002f85c, 0x8002f888, [22, 26], [], []),
            ("__call_exitprocs", "__call_exitprocs", 0x8003bb00, 0x8003bc70, [22, 26], [],
             [0x8003bb3c]),
            ("__retarget_lock_acquire_recursive", "__retarget_lock_acquire_recursive",
             0x8003b428, 0x8003b42c, [22, 26], [], []),
            ("__retarget_lock_release_recursive", "__retarget_lock_release_recursive",
             0x8003b440, 0x8003b444, [22, 26], [], []),
            ("_exit", "_exit", 0x8000063c, 0x8000064c, [22, 26], [], [])]
# lane F1-16: the throw: `luaG_errormsg` with no error handler (`L->errfunc =
# 0`; the handler call `0x80009280` a stop), `luaD_throw` with an error jump
# (`L->errorJmp` set; the `0x80009a60` path, no handler, a stop), newlib's
# `longjmp` (its `ret` into the `jmp_buf`'s `ra`)
HELPERS += [("luaG_errormsg", "LuaG_errormsg", 0x80009260, 0x800092cc, [22, 26], [], [0x80009280]),
            ("luaD_throw", "LuaD_throw", 0x80009a40, 0x80009ac4, [22, 26], [], [0x80009a60]),
            ("longjmp", "Longjmp", 0x8003ba8c, 0x8003bad0, [22, 26], [], [])]
# helper modules whose `H<name>` would collide (`exit`, `_exit`)
HMOD = {"_exit": "HUexit"}
# lane F1-6: htif.c's `_write` on a console descriptor (`getfd`, the
# `htif_putc` loop). The `tohost` store `0x80000d3c` is MMIO, not a memory
# store: it is a stop, and the loop resumes at the root `0x80000d40` after the
# console step (`Kit/Console.lean`). The lazy `fs_init` (`0x80000b04`: on
# `print`'s path `__smakebuf_r`'s `_fstat` ran it first), the file path
# (`0x80000b5c`, `kind == FD_FILE`) and the `EBADF` exit (`0x80000d58`) are
# stops: a console descriptor of an initialised table reaches none of them.
HELPERS += [("_write", "_write", 0x80000ae8, 0x80000d80, [22, 26], [0x80000d40],
             [0x80000b04, 0x80000d3c, 0x80000b5c, 0x80000d58])]
# lane F1-6: newlib's write path above it: `__swrite` (the `FILE`'s write
# hook: clear `__SOFF`, tail-call `_write_r`; the `__SAPP` seek `0x80034f68` is a
# stop: stdout is not opened for append) and `_write_r` (`errno = 0`, `_write`;
# the `-1` path `0x8003b3f0` is a stop: the console write returns `n`).
HELPERS += [("__swrite", "__swrite", 0x80034f18, 0x80034fa0, [22, 26], [], [0x80034f68]),
            ("_write_r", "_write_r", 0x8003b3b0, 0x8003b40c, [22, 26], [], [0x8003b3f0])]
# lane F1-6: `__sflush_r` on a write stream (`__SWR`): `_p := _bf._base`,
# `_w := 0` (line-buffered) and the write loop through the `FILE`'s hook (`jalr
# a5`, `0x80032890`; its return `0x80032894` is a root). The read path
# (`0x8003271c`) and the short-write error exit (`0x8003289c`) are stops: the
# console hook writes everything (`swrite_sum`).
HELPERS += [("__sflush_r", "__sflush_r", 0x800326f8, 0x80032954, [22, 26], [0x80032894],
             [0x80032734, 0x8003289c])]
# lane F1-7: `OP_GETTABUP _ENV "print"`'s `luaH_getshortstr` (the chain walk;
# the `absentkey` return `0x800180ec` is a stop: the walk finds `print`,
# `EnvMem.found`), and the arm itself on the route (its segments in their
# chunked modules, with the fetch-head registers)
HELPERS += [("luaH_getshortstr", "LuaH_getshortstr", 0x8001808c, 0x800180f8, [22, 26], [],
             [0x800180ec])]
SUMMARISED |= {"luaH_getshortstr"}
SIM_OPS |= {"OP_GETTABUP"}
# lane F1-8: `print`'s stdio calls on the callee-context route
# (`scripts/gen_lua_at.py --fn`): `fflush(stdout)` (the `__sinit` call
# `0x80032a98` and the `fflush(NULL)` walk `0x80032ae4` are stops: `stdout` is
# set up, `StdioUp`)
HELPERS += [("fflush", "Fflush", 0x80032a1c, 0x80032af8, [22, 26], [],
             [0x80032a98, 0x80032ae4])]
# lane F1-8: `memmove` (`__sfvwrite_r` copying into the `stdout` buffer): every
# path but the backward copy (`0x8003b450`, a stop: the buffer and the source
# are disjoint, so `dst < src + n` with `src < dst` is infeasible); the
# 32-byte block body is cut after each of its stores (roots `0x8003b4d8`, …):
# a segment's post-state holds every load through the segment's earlier
# stores, so four stores in one segment state their data exponentially
HELPERS += [("memmove", "Memmove", 0x8003b444, 0x8003b56c, [22, 26],
             [0x8003b4d8, 0x8003b4e0, 0x8003b4e8], [0x8003b450])]
# lane F1-8: `_fflush_r(ptr, stdout)` (`__sfvwrite_r`'s flushes; the `__sinit`
# call `0x80032a04` is a stop: `StdioUp`)
HELPERS += [("_fflush_r", "_fflush_r", 0x80032954, 0x80032a1c, [22, 26], [], [0x80032a04])]
# lane F1-8: `memchr` (`__sfvwrite_r`'s search for the newline)
HELPERS += [("memchr", "Memchr", 0x800360d8, 0x80036198, [22, 26], [], [])]
# lane F1-8: `__sfvwrite_r` on the set-up line-buffered `stdout`: its
# line-buffered loop (the return from the `FILE`'s write hook `0x80033df4` a
# root). Stops: `__swsetup_r` (`0x80033c2c`: `stdout` is set up), the
# unbuffered and fully buffered loops (`0x80033ba8`, `0x80033c70`: `__SLBF`),
# the error exits (`0x80033ea8`, `0x80034008`: the console takes every byte)
HELPERS += [("__sfvwrite_r", "__sfvwrite_r", 0x80033b50, 0x8003402c, [22, 26], [0x80033df4],
             [0x80033ba8, 0x80033c70, 0x80033ea8, 0x80034008, 0x80033ed0])]
# lane F1-8: `fwrite` (`j _fwrite_r`) and `_fwrite_r` on the set-up `stdout`
# (`__sinit`, `0x800342c0`, a stop: `StdioUp`; the wide-orientation and
# short-write paths are decided by `_flags2 = 0` and `__sfvwrite_r`'s `0`)
HELPERS += [("fwrite", "Fwrite", 0x800342e4, 0x80034300, [22, 26], [], []),
            ("_fwrite_r", "_fwrite_r", 0x800340fc, 0x800342e4, [22, 26], [], [])]
# lane F1-9: `__sinit` at the first write (`global_stdio_init`: `std()` of the
# three `FILE`s, each `memset(&_mbstate, 0, 8)` and a no-op lock init); only
# `memset`'s short path (`n <= 15`: a computed jump into its `sb` chain, whose
# targets are roots; the block loop `0x8003b578` a stop)
HELPERS += [("__sinit", "__sinit", 0x80032ed0, 0x80032f30, [22, 26], [], []),
            ("global_stdio_init.part.0", "Global_stdio_init_part_0", 0x80032bfc, 0x80032d7c, [22, 26],
             [0x80032d4c, 0x80032d54], []),
            ("memset", "Memset", 0x8003b56c, 0x8003b648, [22, 26],
             [0x8003b5bc + 4 * i for i in range(15)] + [0x8003b630], []),
            ("__retarget_lock_init_recursive", "__retarget_lock_init_recursive",
             0x8003b418, 0x8003b41c, [22, 26], [], [])]
# lane F1-10: the first write's set-up. `_fwrite_r`'s `CHECK_INIT` (`__sinit`)
# and `__sfvwrite_r`'s `cantwrite` (`__swsetup_r`, its error exit `0x80033ed0` a
# stop) are no longer stops; `memset`'s block loop is followed (`_fstat`'s
# `memset(st, 0, 104)`: the misaligned head through the internal `jalr` into
# the `sb` chain, which returns to `0x8003b630`: `RET_TO`). `__swsetup_r` on a
# write stream without a buffer (stops: the `__sinit` call `0x800359ac`, a
# stream not open for writing `0x800358e0`, no buffer after `__smakebuf_r`
# `0x80035950`, not line-buffered `0x80035934`); `__smakebuf_r` on a character
# device (stops: unbuffered `0x80049a38`, `_fstat` failing `0x80049b00`/`0x80049b04`,
# `_malloc_r` failing `0x80049b64`, not a tty `0x80049b94`); `_fstat_r` →
# `_fstat` on the console (`fs_init` inlined; stops: `_fstat`'s `-1`
# `0x8003b124`, a file `0x80000f34`, `EBADF` `0x80000f44`); `_isatty_r` →
# `_isatty` (stops: `-1` `0x8004a1a4`, a file `0x800015f8`, `EBADF` `0x80001624`)
HELPERS += [("__swsetup_r", "__swsetup_r", 0x8003587c, 0x800359e0, [22, 26], [],
             [0x800359ac, 0x800358e0, 0x80035950, 0x80035934]),
            ("__smakebuf_r", "__smakebuf_r", 0x80049a2c, 0x80049ba4, [22, 26], [],
             [0x80049a38, 0x80049b00, 0x80049b04, 0x80049b64, 0x80049b94]),
            ("_fstat_r", "_fstat_r", 0x8003b0e8, 0x8003b140, [22, 26], [], [0x8003b124]),
            ("_fstat", "_fstat", 0x80000e9c, 0x80000f58, [22, 26], [], [0x80000f34, 0x80000f44]),
            ("_isatty_r", "_isatty_r", 0x8004a170, 0x8004a1c0, [22, 26], [], [0x8004a1a4]),
            ("_isatty", "_isatty", 0x80001598, 0x80001630, [22, 26], [], [0x800015f8, 0x80001624])]
# lane F1-11: `luaB_print` (its callees `luaL_tolstring`, `fwrite`, `fflush`
# abstract: call nodes), `lua_gettop`, `lua_settop` (its `luaF_close` of a
# to-be-closed slot above the new top, `0x80001c8c`, a stop: `luaB_print`'s
# pops never reach `L->tbclist`)
HELPERS += [("luaB_print", "LuaB_print", 0x80022f18, 0x80023010, [22, 26], [], []),
            ("lua_gettop", "Lua_gettop", 0x80001bb4, 0x80001bd4, [22, 26], [], []),
            ("lua_settop", "Lua_settop", 0x80001bd4, 0x80001cbc, [22, 26], [], [0x80001c8c])]
# lane F1-12: `OP_CALL` (its `jal luaD_precall` a call node) and
# `luaD_precall`'s light-C-function path (`precallC`): the `LUA_VLCF` case, no
# stack growth (`checkstackGCp`'s `luaD_growstack`, `0x8000abe4`, a stop),
# `next_ci` (`ci->next` reused, or `luaE_extendCI`: a call node), no call hook
# (`0x8000ace0` a stop), the C function through `jalr a7` (`luaB_print`), then
# `luaD_poscall`; the Lua-function and `__call` paths (`0x8000aae0`) are stops
SIM_OPS |= {"OP_CALL"}
SUMMARISED |= {"luaD_precall"}
# the argument registers an arm's summarised call reads (live into its `jal`,
# beside the registers live at the return address)
CALL_ARGS = {"luaD_precall": {"x10", "x11", "x12"}}
HELPERS += [("luaD_precall", "LuaD_precall", 0x8000aab4, 0x8000ae3c, [22, 26], [0x8000ac8c],
             [0x8000aae0, 0x8000abe4, 0x8000ace0])]
# lane F1-12: `luaL_tolstring` on its nil and boolean paths (no metatable:
# `luaL_callmeta` → `lua_getmetatable` → 0; `lua_type`; `lua_toboolean`; the
# literal through `lua_pushstring`, a call node; the tail `j lua_tolstring`),
# its callees on a positive index into the C frame, and `lua_tolstring` of the
# top's short string (index -1). The stops: a metamethod (`0x80021b68`,
# `0x80021a70`), the number, string, other and error paths of
# `luaL_tolstring`; pseudo-indices, absent slots, tables and full userdata;
# a non-string or long string at the top
HELPERS += [("luaL_tolstring", "LuaL_tolstring", 0x80021b2c, 0x80021d90, [22, 26], [],
             [0x80021b68, 0x80021bec, 0x80021cb0, 0x80021c5c]),
            ("lua_absindex", "Lua_absindex", 0x80001b7c, 0x80001bb4, [22, 26], [], []),
            ("luaL_callmeta", "LuaL_callmeta", 0x80021a24, 0x80021ac0, [22, 26], [], [0x80021a80]),
            ("lua_getmetatable", "Lua_getmetatable", 0x80003788, 0x8000388c, [22, 26], [],
             [0x80003804, 0x8000382c, 0x80003844, 0x800037c0]),
            ("lua_type", "Lua_type", 0x80002068, 0x8000211c, [22, 26], [], [0x800020c8, 0x80002084]),
            ("lua_toboolean", "Lua_toboolean", 0x800028ec, 0x80002994, [22, 26], [],
             [0x80002924, 0x8000294c]),
            ("lua_tolstring", "Lua_tolstring", 0x80002994, 0x80002b00, [22, 26], [],
             [0x800029a0, 0x80002a60, 0x800029c4, 0x80002a7c])]
# lane F1-17: `luaL_tolstring` on a string argument (the `LUA_TSTRING` case
# `0x80021c44`, `lua_pushvalue`; `0x80002abc` the tail's long string): its
# `luaL_callmeta` finds the string metatable (`0x80021a70`), then
# `luaL_getmetafield.part.0`: `lua_pushstring("__tostring")` (a call node),
# `lua_rawget(L, -2)` → `index2value` (a negative index; pseudo-indices
# `0x800018d8` a stop), `luaH_get` on the short-string key (the main position,
# the chain walk `0x80018278` a root; other key types `0x800181b0` a stop), the
# miss (`absentkey`), `lua_settop(L, -3)`. A metafield found (`0x8002057c`,
# `0x800035dc`, `0x80021a80`) and a pseudo-index (`0x80001ff0`) are stops
HELPERS += [("luaL_getmetafield.part.0", "LuaL_getmetafield_part_0", 0x8002052c, 0x800205b0, [22, 26], [],
             [0x8002057c]),
            ("lua_rawget", "Lua_rawget", 0x80003584, 0x800035fc, [22, 26], [], [0x800035dc]),
            ("index2value", "Index2value", 0x800018a0, 0x80001934, [22, 26], [], [0x800018d8]),
            ("luaH_get", "LuaH_get", 0x800181a0, 0x800182b4, [22, 26], [0x80018278], [0x800181b0]),
            ("lua_pushvalue", "Lua_pushvalue", 0x80001fb0, 0x80002068, [22, 26], [], [0x80001ff0])]
# lane F1-14: `exit(0)` once `print` installed `__stdio_exit_handler`: its
# `jalr a5` (no longer a stop) into `stdio_exit_handler` → `_fwalk_sglue(_REENT,
# _fclose_r, &__sglue)` (its `jalr s5` into `_fclose_r`) over `__sf`'s three
# streams. `_fclose_r`: the `__sinit` call `0x800326a8` a stop (`StdioUp.init`);
# `__sflush_r`'s read path (`stdin`, `stderr`; the above: its seek `0x80032734`
# a stop, nothing read ahead); the `_close` hook `__sclose` → `_close_r` →
# htif.c's `_close` (stops: the lazy `fs_init` `0x800008b8`, a bad descriptor
# `0x80000970`, a file `0x8000092c`; `_close_r`'s `errno` path `0x8003afe8`); the
# no-op locks; `_free_r` of `stdout`'s buffer a call node (`FreeR_Statement`)
HELPERS += [("stdio_exit_handler", "Stdio_exit_handler", 0x80032af8, 0x80032b0c, [22, 26], [], []),
            ("_fwalk_sglue", "_fwalk_sglue", 0x8003402c, 0x800340fc, [22, 26], [0x800340b4], []),
            ("_fclose_r", "_fclose_r", 0x80032580, 0x800326ec, [22, 26], [0x800325e8], [0x800326a8]),
            ("__sclose", "__sclose", 0x80035004, 0x8003500c, [22, 26], [], []),
            ("_close_r", "_close_r", 0x8003afb4, 0x8003b004, [22, 26], [], [0x8003afe8]),
            ("_close", "_close", 0x800008a4, 0x80000984, [22, 26], [],
             [0x800008b8, 0x80000970, 0x8000092c]),
            ("__sfp_lock_acquire", "__sfp_lock_acquire", 0x80032f30, 0x80032f38, [22, 26], [], []),
            ("__sfp_lock_release", "__sfp_lock_release", 0x80032f38, 0x80032f40, [22, 26], [], []),
            ("__retarget_lock_close_recursive", "__retarget_lock_close_recursive",
             0x8003b420, 0x8003b424, [22, 26], [], [])]
# lane F1-14: `luaE_extendCI(L)` (`luaD_precall`'s `next_ci` with `ci->next`
# NULL): `luaM_malloc_(L, 64, 0)` (its `jalr a5` through `g->frealloc` a call
# node, the return `0x800110c0` a root; stops: `size == 0` `0x800110ec`, the
# allocation failing `0x800110f4`), then the links; main.c's `l_alloc` →
# `realloc` → `_realloc_r` with `ptr` NULL (stops: `free` `0x8000173c`,
# `_realloc_r` of a block `0x80030324`), its tail `j _malloc_r` a call node
HELPERS += [("luaE_extendCI", "LuaE_extendCI", 0x80016a5c, 0x80016aa8, [22, 26], [], []),
            ("luaM_malloc_", "LuaM_malloc_", 0x80011084, 0x80011118, [22, 26], [0x800110c0],
             [0x800110ec, 0x800110f4]),
            ("l_alloc", "L_alloc", 0x8000172c, 0x80001758, [22, 26], [], [0x8000173c]),
            ("realloc", "Realloc", 0x8003030c, 0x80030320, [22, 26], [], []),
            ("_realloc_r", "_realloc_r", 0x80030320, 0x80030518, [22, 26], [], [0x80030324])]
# lane F1-15: `lua_pushstring(L, s)` of a C literal: `luaS_new` (`__umoddi3`,
# `strcmp` on the cache's row, on a miss `strlen` and `luaS_newlstr` → `j
# internshrstr`: the hash loop `0x800173a4`, the chain walk `0x800173f0` with
# `memcmp`; the creation path `0x8001742c` a stop: the literal is interned),
# `luaC_step` with the collector stopped (`j luaE_setdebt`; the running path
# `0x8000ec98` a stop); `lua_pushstring(L, NULL)` (`0x8000304c`) and a long
# string (`0x8001769c`) stops
HELPERS += [("lua_pushstring", "Lua_pushstring", 0x80002fe4, 0x8000305c, [22, 26], [], [0x8000304c]),
            ("luaS_new", "LuaS_new", 0x8001772c, 0x800177f0, [22, 26], [], []),
            ("luaS_newlstr", "LuaS_newlstr", 0x80017694, 0x8001772c, [22, 26], [], [0x8001769c]),
            ("internshrstr", "Internshrstr", 0x80017350, 0x8001751c, [22, 26], [0x800173a4, 0x800173f0],
             [0x800174b4]),
            ("luaC_step", "LuaC_step", 0x8000ec80, 0x8000f1c8, [22, 26], [], [0x8000ec98]),
            ("luaE_setdebt", "LuaE_setdebt", 0x80016a20, 0x80016a54, [22, 26], [], [])]

# the argument registers of a callee with no segments of its own (a call node
# whose summary is a named premise): live into the `jal` (`luaL_tolstring(L,
# idx, &len)`; lane F1-12: `luaE_extendCI(L)`)
CALLEE_READS = {0x80021b2c: {"x10", "x11", "x12"}, 0x80016a5c: {"x10"},
                # lane F1-F4: libm `floor(x)` (no segments: `FloorSpec`), from
                # `luaV_equalobj`'s mixed integer/float paths
                0x8002bb14: {"x10"},
                # lane F1-F4: the soft-float routines `luaV_equalobj` calls read only
                # their arguments (their summaries pin the caller's `HFrame`, `s6` and
                # `s10` included, which the summary proof pins at the call)
                0x8002e350: {"x10", "x11"}, 0x8002e3c0: {"x10", "x11"},
                0x8002e460: {"x10", "x11"}, 0x8002f188: {"x10"},
                # lane F1-12: `lua_pushstring(L, s)`
                0x80002fe4: {"x10", "x11"},
                # lane F1-14: `_free_r(ptr, p)`, `_malloc_r(ptr, n)` (with `ra`: `_realloc_r` tail-jumps to it)
                0x8003be24: {"x10", "x11"}, 0x8002fa34: {"x1", "x10", "x11"}}
# a `ret` (by its address) that also returns into its own helper's code (an
# internal `jalr`: `memset`'s `sb` chain): its live-out includes the code
# after that call
RET_TO = {0x8003b5f8: [0x8003b630]}
# indirect calls whose target the callee rows know (`jalr` through a `FILE`
# hook): the callee's entry reads flow back into the caller's segments, as a
# `jal`'s do (`__sfvwrite_r`'s `fp->_write`, `__swrite`, reads `a3`)
INDIRECT = {0x80033df0: 0x80034f18, 0x8000ac88: 0x80022f18,
            # lane F1-14: `exit`'s `__stdio_exit_handler`, `_fwalk_sglue`'s
            # `_fclose_r`, `_fclose_r`'s `_close` hook `__sclose`
            0x8002f87c: 0x80032af8, 0x800340b0: 0x80032580, 0x800325e4: 0x80035004,
            # `luaM_malloc_`'s `g->frealloc` (main.c's `l_alloc`)
            0x800110bc: 0x8000172c}
# lane float-m0: libgcc's soft-float routines of the T1/T2 float paths
# (FLOAT-DESIGN.md §3, M0), all loop-free but `__clzdi2` (a counted byte scan,
# unrolled by `scripts/gen_lua_fn.py`); their whole-function summaries are
# `scripts/gen_lua_fn.py`'s (`Lua/Vm/Fn/*`)
FLOAT_HELPERS = [("__clzdi2", 0x8002f7ec, 0x8002f844), ("__floatsidf", 0x8002f0f8, 0x8002f188),
                 ("__floatdidf", 0x8002f200, 0x8002f358), ("__fixdfdi", 0x8002f188, 0x8002f200),
                 ("__eqdf2", 0x8002e350, 0x8002e3c0), ("__gedf2", 0x8002e3c0, 0x8002e460),
                 ("__ledf2", 0x8002e460, 0x8002e504), ("__adddf3", 0x8002d7a8, 0x8002de30),
                 ("__subdf3", 0x8002e9d0, 0x8002f0b0)]
HELPERS += [(fn, fn, lo, hi, [22, 26], [], []) for fn, lo, hi in FLOAT_HELPERS]
# lane float-sf3: the routines whose callees are soft-float or soft-int
# routines, lifted by `scripts/gen_lua_fn.py` with call nodes to the callees'
# proved summaries: libm `floor` (`s_floor.c`: `__adddf3`, `__gedf2`). They
# are not call nodes of the arms (`FLOAT_CALLS`), so no arm segment changes.
FN_HELPERS = [("floor", "Floor", 0x8002bb14, 0x8002bcdc),
              # `__muldf3` (`_FP_MUL`: four `__muldi3` partial products, two `__clzdi2`)
              ("__muldf3", "__muldf3", 0x8002e504, 0x8002e9d0),
              # lane float-sf4: `__divdf3` (`_FP_DIV`: `udiv_qrnnd` by two `__udivdi3`,
              # two `__umoddi3`, two `__muldi3`; `__clzdi2`; two class-switch jump
              # tables, whose entries are roots: `FN_ROOTS`)
              ("__divdf3", "__divdf3", 0x8002de30, 0x8002e350),
              # lane float-sf5: libm `fmod` (`w_fmod.c`: `__ieee754_fmod`, `__eqdf2`,
              # `__unorddf2`, `__errno`, `__divdf3`) and `__ieee754_fmod`
              # (`e_fmod.c`: six loops; `__muldf3`, `__divdf3` on its NaN path)
              ("fmod", "Fmod", 0x8002b964, 0x8002b9fc),
              ("__ieee754_fmod", "__ieee754_fmod", 0x8002bdb4, 0x8002c2a8),
              # `__unorddf2` (a leaf) and `__errno` (`_impure_ptr`'s load)
              ("__unorddf2", "__unorddf2", 0x8002f0b0, 0x8002f0f8),
              ("__errno", "__errno", 0x8003b40c, 0x8003b414),
              # lane float-sf6: libm `__ieee754_sqrt` (`e_sqrt.c`: bit by bit, four
              # loops; `__muldf3`, `__adddf3`, `__subdf3`, `__divdf3`, `__ledf2` call
              # nodes on its class paths and its rounding-direction test)
              ("__ieee754_sqrt", "__ieee754_sqrt", 0x8002d448, 0x8002d78c),
              # lane float-sf6: libm `pow` (`w_pow.c`: `__ieee754_pow`, `__unorddf2`,
              # `__eqdf2`, `__ledf2`, `finite`, `__errno`), `__ieee754_pow`
              # (`e_pow.c`: soft-float call nodes, `fabs`, `scalbn`; tail jumps to
              # `__ieee754_sqrt`, `__math_oflow`, `__math_uflow`), `scalbn`
              # (`s_scalbn.c`), the error exits (`math_err.c`: `__math_*` -> `xflow`
              # -> `with_errno`, the `errno` store), `fabs`, `finite`
              ("pow", "Pow", 0x8002b9fc, 0x8002bb14),
              ("finite", "Finite", 0x8002bd9c, 0x8002bdb4),
              ("__ieee754_pow", "__ieee754_pow", 0x8002c2a8, 0x8002d09c),
              ("scalbn", "Scalbn", 0x8002d09c, 0x8002d244),
              ("with_errno", "With_errno", 0x8002d244, 0x8002d278),
              ("xflow", "Xflow", 0x8002d278, 0x8002d2b8),
              ("__math_uflow", "__math_uflow", 0x8002d2b8, 0x8002d2c4),
              ("__math_oflow", "__math_oflow", 0x8002d2d0, 0x8002d2dc),
              ("fabs", "Fabs", 0x8002d78c, 0x8002d7a8)]
# a lifted routine's computed-jump targets (its jump tables' entries), and
# cuts between a spill and a reload of another slot (`0x8002e1f0`: the reload
# then reads the node's memory, a forwarded slot, `gen_lua_fn.py` `FORWARD`)
FN_ROOTS = {"__divdf3": [0x8002e114, 0x8002df68, 0x8002df8c, 0x8002df34, 0x8002df3c,
                         0x8002e08c, 0x8002e2cc, 0x8002e1f0]}
# a callee's registers carried through its segments without being its
# inputs: a call to it carries them only where they are live after the
# return (`helper_live`), so its other callers' segments do not change
PASS_THROUGH = {0x8002f6c8: {"x6", "x14", "x15", "x16", "x17", "x28", "x29"},
                # lane float-sf4: `__udivdi3` keeps `t0` (`__moddi3`'s, `__umoddi3`'s
                # return address); a caller that does not read it after the call
                # (`__divdf3`) does not carry it
                0x8002f734: {"x5"}}
# the callers a callee's pass-through applies to (default: every caller), so
# that no other helper's segments change
PASS_THROUGH_FOR = {0x8002f734: {"__divdf3"}}
PASS_THROUGH.update(PASS_THROUGH_S)
HELPERS += [(fn, cap, lo, hi, [22, 26], FN_ROOTS.get(fn, []), []) for fn, cap, lo, hi in FN_HELPERS]
# the arms whose float paths run through the soft-float call nodes (lane
# float-m0, M1): only there is a call to a soft-float routine a call node (its
# return address continues the arm), so the other arms' segments stay as they are
FLOAT_CALLS = {fn for fn, _, _ in FLOAT_HELPERS} | {"floor"}   # libm `floor`: a named premise (`FloorSpec`; lane F2, from A-INC)
FLOAT_UNARY = {"__floatsidf", "__floatdidf", "__fixdfdi", "__clzdi2", "floor"}
FLOAT_ARMS = {"OP_LOADF", "OP_EQI", "OP_LTI", "OP_GEI", "OP_ADDI", "OP_FORLOOP",
              "OP_SUB", "OP_FORPREP", "OP_LT",  # round 5 (A-JOIN): SUB's, FORPREP's, LT's float paths
              # lane F2: LEI's, GTI's, ADD's, ADDK's, SUBK's, LE's float paths
              "OP_LEI", "OP_GTI", "OP_ADD", "OP_ADDK", "OP_SUBK", "OP_LE",
              # lane F2: the bitwise arms' `tointegerns` (`floor`, F2Ieq)
              "OP_BNOT", "OP_BAND", "OP_BOR", "OP_BXOR",
              # lane F3: the shifts' `tointegerns` (a converted operand live across
              # the calls: `s10`)
              "OP_SHL", "OP_SHR", "OP_SHLI", "OP_SHRI"}
# lane F1-F5: `luai_nummul` by `__muldf3` (proved: `Muldf3.spec_proved`), a
# call node of MUL's and MULK's float paths
FLOAT_CALLS |= {"__muldf3"}
FLOAT_ARMS |= {"OP_MUL", "OP_MULK"}
# lane F1-F6: `luai_numdiv` by `__divdf3` (proved: `Divdf3.spec_proved`), a call
# node of DIV's and DIVK's paths (always float) and, with libm `floor`
# (`luai_numidiv`), of IDIV's and IDIVK's float paths
FLOAT_CALLS |= {"__divdf3"}
FLOAT_ARMS |= {"OP_DIV", "OP_DIVK", "OP_IDIV", "OP_IDIVK"}
# lane F1-F7: `luai_nummod` by libm `fmod` (`Lua.Vm.Fn.FmodR`: its `errno`
# store outside the frame), then the sign correction (`__gedf2`, `__ledf2`,
# `__adddf3`): a call node of MOD's and MODK's float paths. `fmod`'s frame
# stores the caller's callee-saved registers, so every one is live into its
# call (`FLOAT_CALL_KEEP`: the summary's frame is the row's)
FLOAT_CALLS |= {"fmod"}
FLOAT_ARMS |= {"OP_MOD", "OP_MODK"}
FLOAT_CALL_KEEP = {"fmod": {"x22", "x26"}}
# lane F1-21: `luai_numpow` by libm `pow` (`b == 2`: `__muldf3`; else `pow`,
# `Lua.Vm.Fn.PowQ`: its `errno` stores outside the frame), a call node of
# POW's and POWK's paths; its frame stores the caller's callee-saved
# registers, so every one is live into its call, as for `fmod`
FLOAT_CALLS |= {"pow"}
FLOAT_ARMS |= {"OP_POW", "OP_POWK"}
FLOAT_CALL_KEEP["pow"] = {"x22", "x26"}
SIM_OPS |= {"OP_LOADF"}
# `tohost` seams: a stop that is a console store (`sd rs2, imm(rs1)` to
# `tohost`, run by `Kit/Console.lean`'s step) and the registers it reads; the
# liveness flows through it to the root after it.
TOHOST_SEAMS = {0x80000d3c: {"x12", "x15"}}
# the registers a helper returns (live at its `ret`)
RESULTS = {"luaS_eqlngstr": {"x10"}, "memcmp": {"x10"}, "l_strcmp": {"x10"},
           "strcoll": {"x10"}, "strcmp": {"x10"}, "strlen": {"x10"},"__muldi3": {"x10"}, "__hidden___udivdi3": {"x10", "x11"}, "__moddi3": {"x10"},
           "__divdi3": {"x10"}, "__umoddi3": {"x10"},
           "luaV_equalobj": {"x10"}, "luaV_tointeger": {"x10"}, "luaV_tonumber_": {"x10"}, "luaO_str2num": {"x10"}, "luaT_adjustvarargs": set(), "luaV_objlen": set(),
           "luaF_close": set(), "luaF_closeupval": set(), "luaD_poscall": set(),
           "luaD_callnoyield": set(), "luaD_rawrunprotected": {"x10"}, "luaD_pcall": {"x10"},
           "lua_pcallk": {"x10"}, "main": {"x10"}, "_start": set(), "exit": set(),
           "__call_exitprocs": set(), "__retarget_lock_acquire_recursive": set(),
           "__retarget_lock_release_recursive": set(), "_exit": set(),
           "_write": {"x10"}, "__swrite": {"x10"}, "_write_r": {"x10"},
           "__sflush_r": {"x10"}, "luaH_getshortstr": {"x10"}, "fflush": {"x10"}, "memmove": {"x10"}, "_fflush_r": {"x10"}, "memchr": {"x10"}, "__sfvwrite_r": {"x10"}, "fwrite": {"x10"}, "_fwrite_r": {"x10"},
           "__sinit": set(), "global_stdio_init.part.0": set(), "memset": {"x10"},
           "__retarget_lock_init_recursive": set(),
           "__clzdi2": {"x10"}, "__floatsidf": {"x10"}, "__floatdidf": {"x10"},
           "__fixdfdi": {"x10"}, "__eqdf2": {"x10"}, "__gedf2": {"x10"}, "__ledf2": {"x10"},
           "__adddf3": {"x10"}, "__subdf3": {"x10"}, "floor": {"x10"}, "__muldf3": {"x10"}, "__divdf3": {"x10"},
           "fmod": {"x10"}, "__ieee754_fmod": {"x10"}, "__unorddf2": {"x10"}, "__errno": {"x10"},
           "__ieee754_sqrt": {"x10"},
           "pow": {"x10"}, "finite": {"x10"}, "__ieee754_pow": {"x10"}, "scalbn": {"x10"},
           "with_errno": {"x10"}, "xflow": {"x10"}, "__math_uflow": {"x10"}, "__math_oflow": {"x10"},
           "fabs": {"x10"},
           "__swsetup_r": {"x10"}, "__smakebuf_r": set(),
           "_fstat_r": {"x10"}, "_fstat": {"x10"}, "_isatty_r": {"x10"}, "_isatty": {"x10"},
           "luaB_print": {"x10"}, "lua_gettop": {"x10"}, "lua_settop": set(),
           "luaD_precall": {"x10"}, "luaL_tolstring": {"x10"}, "lua_absindex": {"x10"},
           "luaL_callmeta": {"x10"}, "lua_getmetatable": {"x10"}, "lua_type": {"x10"},
           "lua_toboolean": {"x10"}, "lua_tolstring": {"x10"},
           "stdio_exit_handler": {"x10"}, "_fwalk_sglue": {"x10"}, "_fclose_r": {"x10"},
           "__sclose": {"x10"}, "_close_r": {"x10"}, "_close": {"x10"},
           "__sfp_lock_acquire": set(), "__sfp_lock_release": set(),
           "__retarget_lock_close_recursive": set(),
           "luaE_extendCI": {"x10"}, "luaM_malloc_": {"x10"}, "l_alloc": {"x10"}, "realloc": {"x10"},
           "_realloc_r": {"x10"}}
# lane F1-16: `longjmp` "returns" into the `jmp_buf`'s `ra` with the status in
# `a0` and the `jmp_buf`'s `sp` and `s0`-`s11`
RESULTS["longjmp"] = {"x10", "x2", "x8", "x9"} | {f"x{r}" for r in range(18, 28)}
RESULTS["luaG_errormsg"] = set()
RESULTS["luaD_throw"] = set()
RESULTS.update({"luaL_getmetafield.part.0": {"x10"}, "lua_rawget": {"x10"}, "index2value": {"x10"},
                "luaH_get": {"x10"}, "lua_pushvalue": set()})
RESULTS.update({"lua_pushstring": {"x10"}, "luaS_new": {"x10"}, "luaS_newlstr": {"x10"},
                "internshrstr": {"x10"}, "luaC_step": set(), "luaE_setdebt": set()})
# lane F1-20: `luaL_tolstring` on an integer (`0x80021c0c`; the float path
# `0x80021cb0` a stop): `lua_isinteger`, `lua_tointegerx` on a positive index
# below the top (stops: pseudo-indices, an index past the top, a non-integer),
# `lua_pushfstring(L, "%I", i)` -> `luaO_pushvfstring` on `"%I"` (the jump
# table's `'I'` target `0x80011fc0` a root; stops: `"%%"`, an unknown
# conversion, the concatenation of a second piece), `strchr` (the NUL search
# `0x800362e8` a stop; its word test split at `0x80036250`, `0x80036274`), `addstr2buff` and `addnum2buff` with room in the
# buffer (stops: their flushes, a float), `memcpy` (stops: the 64-byte
# blocks, a misaligned destination), `internshrstr`'s creation path (the table's
# growth `0x800174b4` a stop), `luaC_newobj` (over `luaM_malloc_`)
HELPERS += [("lua_isinteger", "Lua_isinteger", 0x800021f4, 0x80002298, [22, 26], [], [0x80002228]),
            ("lua_tointegerx", "Lua_tointegerx", 0x800027fc, 0x800028ec, [22, 26], [],
             [0x80002850, 0x80002878, 0x8000288c]),
            ("lua_pushfstring", "Lua_pushfstring", 0x800030a4, 0x80003110, [22, 26], [], []),
            ("luaO_pushvfstring", "LuaO_pushvfstring", 0x80011d98, 0x80012200, [22, 26], [0x80011fc0],
             [0x80012020, 0x800121f0, 0x800121e0]),
            ("addstr2buff", "Addstr2buff", 0x800114b0, 0x80011584, [22, 26], [], [0x80011520, 0x80011554]),
            ("addnum2buff", "Addnum2buff", 0x80011584, 0x80011630, [22, 26], [], [0x80011610, 0x800115b8]),
            ("strchr", "Strchr", 0x80036204, 0x80036374, [22, 26], [0x80036250, 0x80036274], [0x800362e8]),
            ("memcpy", "Memcpy", 0x8003b648, 0x8003b770, [22, 26], [], [0x8003b6e0, 0x8003b73c]),
            ("luaC_newobj", "LuaC_newobj", 0x8000e8ec, 0x8000e940, [22, 26], [], [])]
RESULTS.update({"lua_isinteger": {"x10"}, "lua_tointegerx": {"x10"}, "lua_pushfstring": {"x10"},
                "luaO_pushvfstring": {"x10"}, "addstr2buff": set(), "addnum2buff": set(), "strchr": {"x10"},
                "memcpy": {"x10"}, "luaC_newobj": {"x10"}})
# lane F1-FMT: `lua_integer2str` = `snprintf(buf, 44, "%lld", i)`: `snprintf`
# (stops: `size > INT_MAX` `0x80034ea4`, `size == 0` `0x80034e64`, an error
# return `0x80034e94`), `_svfprintf_r` on the paths `"%lld"` takes (its
# conversion switch's `'l'` and `'d'` targets and the return from the
# locale's `mbtowc` hook, `jalr s4`, are roots; every successor `"%lld"` never
# takes is a stop: read off the emulator trace of `print(12345, -7, 0,
# math.mininteger)`), the locale callees (`_localeconv_r`, `strlen` of the
# decimal point, `memset` of the `mbstate`, `__locale_mb_cur_max`, the hook
# `__ascii_mbtowc`), the digit loop's `__umoddi3`/`__udivdi3` (call nodes),
# and the output `__ssprint_r` -> `__ssputs_r` -> `memmove` on a string
# `FILE` with room (stops: an empty iov `0x80049724`, the error exit
# `0x800497a8`, the growth path `0x8004e518`)
HELPERS += [("snprintf", "Snprintf", 0x80034de0, 0x80034eb4, [22, 26], [],
             [0x80034e64, 0x80034e94, 0x80034ea4]),
            ("_svfprintf_r", "_svfprintf_r", 0x80042e70, 0x800460a0, [22, 26],
             [0x80042f60, 0x80043824, 0x80043d50, 0x80043b88, 0x800431f0],
             [0x80042ecc, 0x80042f70, 0x80043014, 0x80043058, 0x80043098, 0x80043110, 0x80043140,
              0x80043160, 0x8004318c, 0x800431d4, 0x8004320c, 0x8004331c, 0x80043410, 0x80043508,
              0x8004361c, 0x8004383c, 0x80043870, 0x800438ac, 0x80043918, 0x80043934, 0x80043b58,
              0x80043d5c, 0x80043d64, 0x80043ea8, 0x80044454]),
            ("_localeconv_r", "_localeconv_r", 0x8004a160, 0x8004a168, [22, 26], [], []),
            ("__locale_mb_cur_max", "__locale_mb_cur_max", 0x8003af90, 0x8003af98, [22, 26], [], []),
            ("__ascii_mbtowc", "__ascii_mbtowc", 0x8003cd58, 0x8003cdc0, [22, 26], [],
             [0x8003cd78, 0x8003cda0, 0x8003cdb0]),
            ("__ssprint_r", "__ssprint_r", 0x800496e4, 0x800497d4, [22, 26], [],
             [0x80049724, 0x800497a8]),
            ("__ssputs_r", "__ssputs_r", 0x8004e4b0, 0x8004e644, [22, 26], [], [0x8004e518])]
RESULTS.update({"snprintf": {"x10"}, "_svfprintf_r": {"x10"}, "_localeconv_r": {"x10"},
                "__locale_mb_cur_max": {"x10"}, "__ascii_mbtowc": {"x10"},
                "__ssprint_r": {"x10"}, "__ssputs_r": {"x10"}})
# the locale's `mbtowc` hook (`__global_locale.mbtowc`, `__ascii_mbtowc`)
INDIRECT[0x80042f5c] = 0x8003cd58
# `__udivdi3`'s `t0` is dead after `_svfprintf_r`'s digit-loop call
PASS_THROUGH_FOR[0x8002f734] = PASS_THROUGH_FOR[0x8002f734] | {"_svfprintf_r"}


def helper_edit(fn, roots=(), stops=(), unstop=()):
    """A helper's roots and stops widened by a later lane (in place)."""
    for k, h in enumerate(HELPERS):
        if h[0] == fn:
            HELPERS[k] = (*h[:5], [*h[5], *roots], [s for s in h[6] if s not in unstop] + list(stops))
            return
    raise KeyError(fn)


# lane F1-24: `luaL_tolstring` on a function (the `default` case `0x80021c5c`):
# `lua_getmetatable` finds no metatable (`G(L)->mt[LUA_TFUNCTION]` NULL; a
# metatable found, `0x80021cd0`, a stop), `lua_type`, `lua_typename`,
# `lua_topointer` of a light C function (stops: pseudo-indices `0x80002e64`, an
# index past the top `0x80002e8c`, a closure or userdata `0x80002ea4`, other
# values `0x80002e48`), `lua_pushfstring(L, "%s: %p", kind, p)`:
# `luaO_pushvfstring`'s `'s'` and `'p'` targets roots (stops: a NULL string
# `0x8001219c`, a flush before `%p` `0x80012148`), `strlen` of the type name,
# `snprintf(buf, 32, "%p", p)`: `_svfprintf_r`'s `'p'` target a root, the
# hex digit loop and the `0x` prefix (`0x800438ac` no longer a stop; stops: a
# precision `0x80043c70`, padding `0x800438c8`, `0x8004434c`, a sign `0x80043ed8`)
helper_edit("luaL_tolstring", stops=[0x80021cd0], unstop=[0x80021c5c])
HELPERS += [("lua_typename", "Lua_typename", 0x8000211c, 0x80002138, [22, 26], [], []),
            ("lua_topointer", "Lua_topointer", 0x80002e14, 0x80002f1c, [22, 26], [],
             [0x80002e64, 0x80002e8c, 0x80002ea4, 0x80002e48])]
RESULTS.update({"lua_typename": {"x10"}, "lua_topointer": {"x10"}})
helper_edit("luaO_pushvfstring", roots=[0x80011e54, 0x80011f2c], stops=[0x8001219c, 0x80012148])
helper_edit("_svfprintf_r", roots=[0x80043c48], stops=[0x80043c70, 0x800438c8, 0x8004434c, 0x80043ed8],
            unstop=[0x800438ac])


def helper_span(fn, lo=None, hi=None):
    """A helper's range widened by a later lane (in place)."""
    for k, h in enumerate(HELPERS):
        if h[0] == fn:
            HELPERS[k] = (h[0], h[1], h[2] if lo is None else lo, h[3] if hi is None else hi, *h[4:])
            return
    raise KeyError(fn)


# lane F1-26: the unwind after a Lua error. `main`'s error branch after
# `lua_pcallk` returns 2 (`lua_tolstring(L, -1, NULL)`, `fprintf(stderr, …)`
# a call node, `return 2`)
helper_span("main", hi=0x800018a0)


def helper_cfg(lo, hi):
    """{addr: (row, successors, ends_segment)} over one helper's range."""
    out = {}
    for addr, word, raw in d2s.disassemble(d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF, lo, hi):
        row = d2s.classify(addr, word, raw, {addr: "taken"})[-1]
        c, o, nxt = row.cls, row.ops, addr + 4
        if c is None:
            raise SystemExit(f"unsupported instruction at 0x{addr:x}: {raw}")
        if c.startswith("branch_"):
            tgt = (addr + d2s.sext(int(o[3], 16), 13)) % 2**64
            succ, end = [x for x in (tgt, nxt) if lo <= x < hi], True
        elif c == "j":
            tgt = (addr + d2s.sext(int(o[0], 16), 21)) % 2**64
            succ, end = ([tgt] if lo <= tgt < hi else []), True
        elif c in ("jr", "jalr"):
            succ, end = [], True
        else:
            succ, end = [nxt], False
        out[addr] = (raw, succ, end)
    return out


def helper_segments(lo, hi, roots=(), stops=()):
    """The helper's code reachable from `lo` and the `roots` (not through the
    `stops`), cut into segments (each root a leader)."""
    g = helper_cfg(lo, hi)
    reach, work = set(), [lo, *roots]
    while work:
        a = work.pop()
        if a in reach or a not in g or a in stops:
            continue
        reach.add(a)
        work.extend(g[a][1])
    segs = []
    for a, b in dfa.segments(g, reach, lo):
        cuts = [x for x in roots if a < x < b]
        for x in cuts:
            segs.append((a, x))
            a = x
        segs.append((a, b))
    return g, split_at_calls(g, segs)


def d2s_last_is_ret(hi):
    """Whether the instruction before `hi` is a `ret` (or `jr t0`, the soft-int
helpers' return through the saved `ra`)."""
    raw = next(iter(d2s.disassemble(d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF, hi - 4, hi)))[2]
    return raw.split()[0] == "ret" or raw.split()[:2] == ["jr", "t0"]


def helper_live(cuts, owner):
    """Per helper segment, the registers a later helper segment reads that
    it neither reads nor writes (liveness fixpoint over the pool of helper
    segments; a `jal`'s successor is its callee's entry)."""
    info = {}
    for n, (lo, hi, path, keep) in cuts.items():
        spec, _ = seg_spec(lo, hi, path, n, True, keep=keep)
        em = gen_segment.SegmentEmitter(spec)
        em.emit()
        m = re.match(r"\(?(0x[0-9a-f]+)#64", em.end_pc)
        end = int(m.group(1), 16) if m else None     # a return: no static successor
        info[n] = ({p["reg"] for p in spec["pins"]}, {r for r, _ in em.pins}, end)
    live = {n: set(info[n][0]) for n in cuts}

    roots = {fn: rs for fn, _, _, _, _, rs, _ in HELPERS}

    def live_out(n):
        if info[n][2] is None:
            hi = cuts[n][1]
            if hi - 4 in INDIRECT:
                return set().union(*[live[m] for m in cuts if cuts[m][0] == INDIRECT[hi - 4]])
            if d2s_last_is_ret(hi):     # a return: the helper's results
                return RESULTS[owner[n]].union(*[live[m] for m in cuts if owner[m] == owner[n]
                                                 and cuts[m][0] in RET_TO.get(hi - 4, [])])
            # a computed jump (a jump table): its targets are the helper's roots
            return set().union(*[live[m] for m in cuts
                                 if owner[m] == owner[n] and cuts[m][0] in roots[owner[n]]])
        end = info[n][2]
        if end in PASS_THROUGH and owner[n] in PASS_THROUGH_FOR.get(end, {owner[n]}):
            # a call: the callee's inputs, and what lives across it
            pt = PASS_THROUGH[end]
            after = set().union(*[live[m] for m in cuts if cuts[m][0] == cuts[n][1]])
            return (set().union(*[live[m] for m in cuts if cuts[m][0] == end]) - pt) | (pt & after)
        if end in CALLEE_READS:
            return set(CALLEE_READS[end])
        if end in TOHOST_SEAMS:     # the console store, then the code after it
            return TOHOST_SEAMS[end] | set().union(*[live[m] for m in cuts if cuts[m][0] == end + 4])
        return set().union(*[live[m] for m in cuts if cuts[m][0] == end])
    changed = True
    while changed:
        changed = False
        for n in cuts:
            new = info[n][0] | (live_out(n) - info[n][1])
            if not new <= live[n]:
                live[n] |= new
                changed = True
    return {n: live_out(n) - info[n][1] for n in cuts}


def helper_cuts():
    """Every helper segment: name -> (lo, hi, path, keep), its owner, and the
    registers it carries for later segments (`helper_live`)."""
    cuts, owner = {}, {}
    for fn, cap, lo, hi, temps, roots, stops in HELPERS:
        g, segs = helper_segments(lo, hi, roots, stops)
        for a, b in segs:
            for suf, path in variants(g, a, b):
                name = f"seg_{a:08x}_{b:08x}{suf}"
                cuts[name] = (a, b, path, KEEP + temps)
                owner[name] = fn
    return cuts, owner, helper_live(cuts, owner)


def helper_specs(fn):
    """[(name, lo, hi, spec)] of helper `fn`'s segments, as emitted
    (`scripts/gen_lua_fn.py` folds them)."""
    cuts, owner, extra = helper_cuts()
    out = []
    for name, (a, b, path, keep) in cuts.items():
        if owner[name] != fn:
            continue
        keep = sorted(set(keep) | {int(r[1:]) for r in extra[name]})
        spec, _ = seg_spec(a, b, path, name, True, keep=keep)
        out.append((name, a, b, spec))
    return out


def helper_all():
    """[(module, battery, segment module)] for every helper."""
    cuts, owner, extra = helper_cuts()
    out = []
    for fn, cap, lo, hi, temps, roots, stops in HELPERS:
        specs, sites = [], {}
        for name, (a, b, path, keep) in cuts.items():
            if owner[name] != fn:
                continue
            keep = sorted(set(keep) | {int(r[1:]) for r in extra[name]})
            spec, rows = seg_spec(a, b, path, name, True, keep=keep)
            specs.append((name, spec))
            for row in rows:
                p = row.split("\t")
                sites.setdefault((int(p[0], 16), p[2]), row)
        out.append(helper_emit(fn, cap, lo, hi, specs, sites))
    return out


def helper_emit(fn, cap, lo, hi, specs, sites):
    """The site battery and segment module of one helper."""
    objs = []
    for n, key in enumerate(sorted(sites), 1):
        p = sites[key].split("\t")
        objs.append(gen_sites.Site(int(p[0], 16), int(p[1], 16), p[2], p[3:], n))
    mod = HMOD.get(fn, "H" + re.sub(r"[^A-Za-z0-9_]", "_", fn.lstrip("_")))
    # a helper whose code pins are split into parts (`gen_lua_code.py`, more
    # than 256 instructions: `__sfvwrite_r`, `__adddf3`, `__subdf3`) fetches
    # through its part's pin; `FixedImage_<cap>` imports every part
    part_dir = ROOT / f"Lua/Vm/Code/{cap}"
    if part_dir.is_dir():
        template = f"Lua.Vm.Code.{re.sub(r"[^A-Za-z0-9_]", "_", fn)}_at_{{addr}} (Lua.Vm.Code.textLoaded_{cap}_p{{part}}Loaded hmem)"
        parts = gen_sites.load_parts(part_dir)
    else:
        template = f"Lua.Vm.Code.{re.sub(r"[^A-Za-z0-9_]", "_", fn)}_at_{{addr}} (Lua.Vm.Code.textLoaded_{cap}Loaded hmem)"
        parts = {a: 0 for a in range(lo, hi, 4)}
    battery = gen_sites.emit_battery(
        objs, PRED, "", [f"Lua.Vm.Code.FixedImage_{cap}", "Lua.Vm.Arms.Text"], "", NS,
        template, parts, f"the helper {fn} (driver: scripts/gen_lua_arms.py)")
    bodies = []
    for name, spec in specs:
        em = gen_segment.SegmentEmitter(spec)
        em.emit()
        bodies.append(em.body_text)
    jalr = any(st["class"] == "jalr" for _, spec in specs for st in spec["steps"])
    half = any(st["class"] == "sh" for _, spec in specs for st in spec["steps"])
    ok_imports = OK_IMPORT + ("\nimport Lua.Vm.Arms.RegsOkJalr" if jalr else "") + \
        ("\nimport Lua.Vm.Arms.TextHalf" if half else "")
    text = f"""import {NS}.Sites.{mod}
import {ok_imports}
import Lua.Vm.Arms.Text
import Vsa.Sim.SegState

/-! {HEADER}

Segment theorems of the helper `{fn}` (`[0x{lo:08x}, 0x{hi:08x})`), `SegSt` to
`SegSt`, carrying the caller's fetch-head registers (scripts/syi/gen_segment.py,
`"boundary": "segst"`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim

namespace {NS}

""" + "\n\n".join(bodies) + f"\n\nend {NS}\n"
    return mod, battery, text


def split_at_calls(g, segs):
    out = []
    for lo, hi in segs:
        start = lo
        for a in range(lo, hi, 4):
            if g[a][0].split()[0] == "jal" and a + 4 < hi:
                out.append((start, a + 4))
                start = a + 4
        out.append((start, hi))
    return out


def variants(g, lo, hi):
    """[(suffix, path)] for the segment: one per polarity of a final branch."""
    last = hi - 4
    base = {a: "nottaken" for a in range(lo, hi, 4)}
    word = next(iter(d2s.disassemble(d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF,
                                     last, hi)))[1]
    if (word & 0x7f) == 0b1100011:
        return [("_t", {**base, last: "taken"}), ("_n", base)]
    return [("", base)]


def seg_spec(lo, hi, path, name, sim, keep=KEEP):
    """The segst spec of [lo, hi) along `path`; a `sim` segment carries the
    fetch-head registers (`keep`) and the console output."""
    lines = []
    for addr, word, raw in d2s.disassemble(d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF,
                                           lo, hi):
        lines += [x.tsv() for x in d2s.classify(addr, word, raw, path)]
    spec, rows = d2seg.complete(lo, hi, lines, "<elf>", name, PRED, NS, [], SURVIVAL,
                                keep=keep if sim else None, output=sim)
    if sim:
        spec["ok"] = OK
    return spec, rows


def collect(only):
    g = dfa.cfg()
    f1 = set(json.load(open(dfa.ARMS_JSON))["summary"]["F1_ops"]) | dfa.F1_EXTRA_OPS | set(EXTRA_ARMS)
    arms, cuts = [], {}
    for r in csv.DictReader(open(dfa.ARMS_TSV), delimiter="\t"):
        if r["op"] not in f1 or (only and r["op"] not in only):
            continue
        t = int(r["target"], 16)
        reach = dfa.arm(g, t)
        segs = split_at_calls(g, dfa.segments(g, reach, t))
        names = []
        for lo, hi in segs:
            for suf, path in variants(g, lo, hi):
                name = f"seg_{lo:08x}_{hi:08x}{suf}"
                names.append(name)
                cuts[name] = (lo, hi, path)
        arms.append((r["op"], names))
    sim = {n for op, ns in arms if op in SIM_OPS for n in ns}
    specs, sites = {}, {}
    for name, (lo, hi, path) in cuts.items():
        spec, rows = seg_spec(lo, hi, path, name, name in sim)
        specs[name] = (lo, spec, rows)
    # calls to a summarised helper continue at the return address (call nodes)
    float_segs = {n for op, ns in arms if op in FLOAT_ARMS for n in ns}
    jal_end = {n for n, (lo, hi, path) in cuts.items()
               if g[hi - 4][0].split()[0] == "jal"
               and (re.search(r"<([^>+]+)>", g[hi - 4][0]).group(1) in SUMMARISED
                    or (n in float_segs
                        and re.search(r"<([^>+]+)>", g[hi - 4][0]).group(1) in FLOAT_CALLS))}
    jal_args = {n: CALL_ARGS[re.search(r"<([^>+]+)>", g[cuts[n][1] - 4][0]).group(1)]
                for n in jal_end
                if re.search(r"<([^>+]+)>", g[cuts[n][1] - 4][0]).group(1) in CALL_ARGS}
    # round 5 (A-JOIN): a soft-float call node reads its arguments (`a0`, and
    # `a1` for a binary routine), set before the `jal` or carried into it
    for n in jal_end & float_segs:
        lo, hi, path = cuts[n]
        callee = re.search(r"<([^>+]+)>", g[hi - 4][0]).group(1)
        if callee in FLOAT_CALLS:
            jal_args[n] = (({"x10"} if callee in FLOAT_UNARY else {"x10", "x11"})
                           | FLOAT_CALL_KEEP.get(callee, set()))
    for name, regs in live_keep(arms, specs, sim, jal_end, jal_args).items():
        if regs:
            lo, hi, path = cuts[name]
            spec, rows = seg_spec(lo, hi, path, name, True,
                                  keep=KEEP + sorted(int(r[1:]) for r in regs))
            specs[name] = (lo, spec, rows)
    for name, (lo, spec, rows) in specs.items():
        for row in rows:
            parts = row.split("\t")
            key = (int(parts[0], 16), parts[2])
            sites.setdefault(key, row)
    return arms, specs, sites


def live_keep(arms, specs, sim, jal_end=frozenset(), jal_args=None):
    """Per SIM segment, the registers a later segment of its arm reads that
    the segment neither reads nor writes (a temporary such as `ADD`'s slot
    of `R[A]`, computed before a branch and stored after it): they are
    carried through (`keep`), by a liveness fixpoint over the arm's
    segments. A segment ending in a `jal` continues at the return address
    (the callee is a summarised call node)."""
    info = {}
    for n in sim:
        em = gen_segment.SegmentEmitter(specs[n][1])
        em.emit()
        m = re.match(r"\(?(0x[0-9a-f]+)#64", em.end_pc)
        end = int(m.group(1), 16) if m else None    # a return (`OP_RETURN*`'s `ret`)
        if n in jal_end:
            end = int(n.split("_")[2], 16)
        info[n] = ({p["reg"] for p in specs[n][1]["pins"]}, {r for r, _ in em.pins}, end)
    extra = {n: set() for n in sim}
    for op, names in arms:
        if op not in SIM_OPS:
            continue
        live = {n: set(info[n][0]) for n in names}

        def live_out(n):
            return set().union(*[live[m] for m in names if specs[m][0] == info[n][2]],
                               (jal_args or {}).get(n, set()))
        changed = True
        while changed:
            changed = False
            for n in names:
                new = info[n][0] | (live_out(n) - info[n][1])
                if not new <= live[n]:
                    live[n] |= new
                    changed = True
        for n in names:
            extra[n] |= live_out(n) - info[n][1]
    return extra


def head_spec():
    """The fetch head `[fetch_head, dispatch_jr + 4)` with both bound checks
    not taken (`trap = 0`, opcode ≤ 81): one segment ending in the `jr`
    through the jump table."""
    lo, hi = dfa.FETCH, int(JT["dispatch_jr"], 16) + 4
    path = {a: "nottaken" for a in range(lo, hi, 4)}
    name = f"seg_{lo:08x}_{hi:08x}"
    # s3 and s4 are the fetch's own outputs: not carried in
    spec, rows = seg_spec(lo, hi, path, name, True,
                          keep=[r for r in KEEP if r not in (19, 20)])
    return name, spec, rows


def prologue_specs(sites):
    """`luaV_execute`'s prologue `[entry, fetch_head)` (the C code before the
    loop), with the `trap` check `bnez s5` not taken (no hooks), as two
    segments cut where the arms' code joins it (`startfunc`, the first
    prologue address with an arm site: `OP_CALL`/`OP_TAILCALL` `goto
    startfunc`):

    * `[entry, startfunc)`: the frame (`addi sp,sp,-176`, the saves of `ra`,
      `s0 … s11`), `L`/`ci` into s0/s7, the jump table into s8;
    * `[startfunc, fetch_head)`: the loads of `ci->func`, `L->hookmask`,
      `ci->u.l.savedpc`, the closure and its `k`; s1 = 81, s2 = 3; `base`.

    The cut keeps the second segment's loads over its own entry memory, not
    over the first segment's store chain. Both thread the console
    output, and carry `gp` and the jump table (s8) through, the frame
    `Lua.Vm.Sim.vmRel_entry` needs."""
    lo, hi = Layout_symLuaVExecute(), dfa.FETCH
    joined = {a for a, _ in sites}
    cut = next(a for a in range(lo + 4, hi, 4) if a in joined)
    out = []
    for a, b in ((lo, cut), (cut, hi)):
        path = {x: "nottaken" for x in range(a, b, 4)}
        name = f"seg_{a:08x}_{b:08x}"
        spec, rows = seg_spec(a, b, path, name, True, keep=[3, 24])
        out.append((name, spec, rows))
    return out


def Layout_symLuaVExecute():
    """`luaV_execute`'s entry, as `Lua/Vm/Layout.lean` has it."""
    import re
    txt = (ROOT / "Lua/Vm/Layout.lean").read_text()
    return int(re.search(r"def symLuaVExecute : Nat := (0x[0-9a-f]+)", txt).group(1), 16)


def site_name_of(key):
    addr, cls = key
    arm = {"branch_taken": "_taken", "branch_nottaken": "_nottaken"}.get(cls, "")
    return f"site_{addr:08x}{arm}"


def render(only=None) -> dict[Path, str]:
    arms, specs, sites = collect(only)
    parts = gen_sites.load_parts(ROOT / "Lua/Vm/Code/LuaV_execute")
    dump = gen_sites.load_ast_dump(ROOT / "Lua/Vm/DecodeCheck/ast_dump.txt")
    files: dict[Path, str] = {}
    # the extra arms' own segments and sites (`EXTRA_ARMS`)
    base = {n for op, ns in arms if op not in EXTRA_ARMS for n in ns}
    xsegs = {op: [n for n in ns if n not in base] for op, ns in arms if op in EXTRA_ARMS}
    base_sites = set()
    for n in base:
        for row in specs[n][2]:
            p = row.split("\t")
            base_sites.add((int(p[0], 16), p[2]))
    xsites = {}
    for op, ns in xsegs.items():
        for n in ns:
            for row in specs[n][2]:
                p = row.split("\t")
                key = (int(p[0], 16), p[2])
                if key not in base_sites:
                    xsites.setdefault(op, {}).setdefault(key, row)
    xall = {k for d in xsites.values() for k in d}
    # site batteries
    keys = sorted(k for k in sites if k not in xall)
    site_mod = {}
    for i in range(0, len(keys), SITES_PER_MODULE):
        chunk = keys[i:i + SITES_PER_MODULE]
        mod = f"S{i // SITES_PER_MODULE:02d}"
        objs = []
        for n, key in enumerate(chunk, 1):
            p = sites[key].split("\t")
            objs.append(gen_sites.Site(int(p[0], 16), int(p[1], 16), p[2], p[3:], n))
            site_mod[site_name_of(key)] = f"{NS}.Sites.{mod}"
        text = gen_sites.emit_battery(
            objs, PRED, "", CODE_IMPORTS, "", NS, TEMPLATE, parts,
            "the F1 arms of luaV_execute (driver: scripts/gen_lua_arms.py)",
            ast_dump=dump)
        files[OUT / "Sites" / f"{mod}.lean"] = text
    for op, d in xsites.items():
        mod = "SX" + op[3:]
        objs = []
        for n, key in enumerate(sorted(d), 1):
            p = d[key].split("\t")
            objs.append(gen_sites.Site(int(p[0], 16), int(p[1], 16), p[2], p[3:], n))
            site_mod[site_name_of(key)] = f"{NS}.Sites.{mod}"
        files[OUT / "Sites" / f"{mod}.lean"] = gen_sites.emit_battery(
            objs, PRED, "", CODE_IMPORTS, "", NS, TEMPLATE, parts,
            f"the arm {op} of luaV_execute (driver: scripts/gen_lua_arms.py)",
            ast_dump=dump)
    # segment theorems
    xnames = {n for ns in xsegs.values() for n in ns}
    names = sorted((n for n in specs if n not in xnames), key=lambda n: (specs[n][0], n))
    groups = [(f"G{i // SEGS_PER_MODULE:02d}", names[i:i + SEGS_PER_MODULE])
              for i in range(0, len(names), SEGS_PER_MODULE)]
    groups += [("X" + op[3:], sorted(ns, key=lambda n: (specs[n][0], n))) for op, ns in xsegs.items()]
    seg_mods = []
    for mod, chunk in groups:
        seg_mods.append(mod)
        imports = {"Lua.Vm.Arms.Text", "Vsa.Sim.SegState"}
        bodies = []
        for name in chunk:
            spec = specs[name][1]
            for st in spec["steps"]:
                imports.add(site_mod[st["site"]])
            if spec.get("ok"):
                imports.add(OK_IMPORT)
            em = gen_segment.SegmentEmitter(spec)
            em.emit()
            bodies.append(em.body_text)
        text = "\n".join(f"import {m}" for m in sorted(imports))
        text += f"""

/-! {HEADER}

Segment theorems of the F1 arms of `luaV_execute`, `SegSt` to `SegSt`
(scripts/syi/gen_segment.py, `"boundary": "segst"`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim

namespace {NS}

""" + "\n\n".join(bodies) + f"\n\nend {NS}\n"
        files[OUT / "Segs" / f"{mod}.lean"] = text
    # the helpers: one battery and one segment module each
    for mod, battery, text in helper_all():
        files[OUT / "Sites" / f"{mod}.lean"] = battery
        files[OUT / "Segs" / f"{mod}.lean"] = text
        seg_mods.append(mod)
    # the fetch head: its own battery and segment (not shared with any arm)
    hname, hspec, hrows = head_spec()
    objs = []
    for n, row in enumerate(hrows, 1):
        p = row.split("\t")
        if (int(p[0], 16), p[2]) in sites:
            raise SystemExit(f"fetch-head site {p[0]} is also an arm site")
        objs.append(gen_sites.Site(int(p[0], 16), int(p[1], 16), p[2], p[3:], n))
    files[OUT / "HeadSites.lean"] = gen_sites.emit_battery(
        objs, PRED, "", CODE_IMPORTS, "", NS, TEMPLATE, parts,
        "the fetch head of luaV_execute (driver: scripts/gen_lua_arms.py)",
        ast_dump=dump)
    em = gen_segment.SegmentEmitter(hspec)
    em.emit()
    jt, fetch = int(JT["addr"], 16), dfa.FETCH
    files[OUT / "Head.lean"] = f"""import {NS}.HeadSites
import {NS}.RegsOk
import {NS}.Text
import Vsa.Sim.SegState

/-! {HEADER}

The fetch head of `luaV_execute` (`vmfetch` and `vmdispatch`, `lvm.c`), from
`experiments/census/luaV_execute_arms.json`: at `headPc` the loop tests
`trap` (s5), loads the instruction at `pc` (s11) into s4, sets s3 = pc + 4,
bounds the opcode by 81 (s1) and jumps through the {JT['entries']}-entry table
of {JT['entry_bytes']}-byte offsets at `jtBase` (s8, in `.rodata`): target =
`jtBase + sext(entry)`. `{hname}` is that run with both bound checks not taken,
ending at the `jr` (`dispatchPc`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim

namespace {NS}

/-- The fetch head: every arm jumps back here. -/
def headPc : BitVec 64 := 0x{fetch:08x}#64
/-- The dispatch `jr`. -/
def dispatchPc : BitVec 64 := 0x{int(JT['dispatch_jr'], 16):08x}#64
/-- The jump table's base (the `auipc`/`addi` of `luaV_execute`'s prologue). -/
def jtBase : Nat := 0x{jt:08x}
/-- The number of table entries (opcodes `0 … jtEntries - 1`). -/
def jtEntries : Nat := {JT['entries']}

{em.body_text}

end {NS}
"""
    # the prologue: its own battery and segments
    # `startfunc` is shared with the arms that `goto startfunc` (OP_CALL,
    # OP_TAILCALL): those sites come from the arm batteries
    psegs = prologue_specs(sites)
    pnames = [n for n, _, _ in psegs]
    objs, shared, seen = [], set(), set()
    for _, _, prows in psegs:
        for row in prows:
            p = row.split("\t")
            key = (int(p[0], 16), p[2])
            if key in sites:
                if sites[key] != row:
                    raise SystemExit(f"prologue site {p[0]} differs from the arm site")
                shared.add(site_mod[site_name_of(key)])
                continue
            if key in seen:
                continue
            seen.add(key)
            objs.append(gen_sites.Site(key[0], int(p[1], 16), p[2], p[3:], len(objs) + 1))
    files[OUT / "PrologueSites.lean"] = gen_sites.emit_battery(
        objs, PRED, "", CODE_IMPORTS, "", NS, TEMPLATE, parts,
        "the prologue of luaV_execute (driver: scripts/gen_lua_arms.py)",
        ast_dump=dump)
    pbodies = []
    for _, pspec, _ in psegs:
        em = gen_segment.SegmentEmitter(pspec)
        em.emit()
        pbodies.append(em.body_text)
    pname = " ".join(pnames)
    pbody = "\n\n".join(pbodies)
    pimports = "".join(f"import {m}\n" for m in sorted(shared))
    files[OUT / "Prologue.lean"] = f"""import {NS}.PrologueSites
{pimports}import {NS}.RegsOk
import {NS}.Text
import Vsa.Sim.SegState

/-! {HEADER}

The prologue of `luaV_execute` (`lvm.c`, up to `startfunc`'s `vmfetch`):
`addi sp,sp,-176` and the saves of `ra`, `s0 … s11`; `L` (a0) and `ci` (a1)
into s0 and s7; the jump table into s8; `startfunc`'s loads of `ci->func`
(t1), `trap = L->hookmask` (s5), `pc = ci->u.l.savedpc` (s11), the closure
(stored at `8(sp)`) and its `k` (stored at `0(sp)`); s1 = 81, s2 = 3; the
`trap` check `bnez s5` not taken; `base = ci->func + 1` (s9). The segments
`{pnames[0]}` (to `startfunc`) and `{pnames[1]}` (to the fetch head `headPc`). -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim

namespace {NS}

{pbody}

end {NS}
"""
    # the standalone arms' own modules are left out of the index and its counts
    solo = {"X" + op[3:] for op in STANDALONE}
    n_specs = len(specs) - sum(len(xsegs.get(op, [])) for op in STANDALONE)
    n_sites = len(sites) - sum(len(xsites.get(op, {})) for op in STANDALONE)
    n_arms = len(arms) - sum(1 for op, _ in arms if op in STANDALONE)
    files[ROOT / "Lua/Vm/Arms.lean"] = (
        "\n".join(f"import {NS}.Segs.{m}" for m in seg_mods if m not in solo)
        + f"\nimport {NS}.Head\nimport {NS}.Prologue"
        + f"\n\n/-! {HEADER}\n\nThe segment theorems of the F1 arms of `luaV_execute`: "
        f"{n_specs} segments ({n_sites} site lemmas) over {n_arms} arms, "
        f"the fetch head `{hname}` (`Lua/Vm/Arms/Head.lean`) and the prologue `{pname}` "
        "(`Lua/Vm/Arms/Prologue.lean`); "
        "`Lua/Vm/Arms/arms.tsv` lists each arm's segments. -/\n")
    files[OUT / "arms.tsv"] = ("# " + HEADER + "\nop\tsegments\n" + "".join(
        f"{op}\t{' '.join(ns)}\n" for op, ns in arms) + f"HEAD\t{hname}\nPROLOGUE\t{pname}\n")
    return files


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--check", action="store_true",
                    help="fail if a generated file differs from the committed one")
    ap.add_argument("--only", default=None,
                    help="comma-separated opcodes (for experiments; not with --check)")
    args = ap.parse_args()
    only = set(args.only.split(",")) if args.only else None
    files = render(only)
    if args.check:
        bad = [p for p, t in files.items() if not p.exists() or p.read_text() != t]
        stale = [p for d in ("Sites", "Segs") for p in (OUT / d).glob("*.lean")
                 if p not in files]
        for p in bad + stale:
            print(f"drift: {p.relative_to(ROOT)}", file=sys.stderr)
        return 1 if bad or stale else 0
    for d in ("Sites", "Segs"):
        (OUT / d).mkdir(parents=True, exist_ok=True)
        for p in (OUT / d).glob("*.lean"):
            if p not in files:
                p.unlink()
    for p, t in files.items():
        p.write_text(t)
    print(f"wrote {len(files)} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())

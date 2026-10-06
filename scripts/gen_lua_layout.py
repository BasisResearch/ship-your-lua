#!/usr/bin/env python3
"""Generate Lua/Vm/Layout.lean: the C layout of Lua 5.4.7's VM structures
as the bare-metal ELF sees them (rv64i, lp64, GCC 15.2.0 xPack).

Every number comes from the cross compiler, not from reading headers: a
probe file of `offsetof`/`sizeof`/tag constants is compiled with the same
RISCV_CC and flags as c/Makefile to assembly, and the `.dword` initialisers
are read back. Rerun after any change to the vendored source or flags:

    python3 scripts/gen_lua_layout.py            # write Lua/Vm/Layout.lean
    python3 scripts/gen_lua_layout.py --check    # drift check (exit 1)
"""
import glob, os, re, subprocess, sys, tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LUA = os.path.join(ROOT, "vendor/lua-5.4.7/src")
OUT = os.path.join(ROOT, "Lua/Vm/Layout.lean")
CC = os.environ.get("RISCV_CC") or (glob.glob(os.path.expanduser(
    "~/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin/riscv-none-elf-gcc")) + ["riscv-none-elf-gcc"])[0]
FLAGS = ["-std=gnu11", "-O2", "-march=rv64i", "-mabi=lp64", "-mcmodel=medany",
         "-DLUA_HTIF", "-DLUA_USE_JUMPTABLE=0",
         "-include", os.path.join(ROOT, "c/src/baremetal.h"), "-I" + LUA]

# (lean name, C expression, doc)
FIELDS = [
    # TValue / StackValue
    ("tvalueSize", "sizeof(TValue)", "`TValue`: 8-byte `Value` union + tag byte, padded"),
    ("tvalueValOff", "offsetof(TValue, value_)", ""),
    ("tvalueTagOff", "offsetof(TValue, tt_)", "the `tt_` tag byte"),
    ("stackValueSize", "sizeof(StackValue)", "one stack slot"),
    # lua_State
    ("stateSize", "sizeof(lua_State)", ""),
    ("stateStatusOff", "offsetof(lua_State, status)", ""),
    ("stateTopOff", "offsetof(lua_State, top)", "`L->top` (StkIdRel)"),
    ("stateGOff", "offsetof(lua_State, l_G)", ""),
    ("stateCiOff", "offsetof(lua_State, ci)", "`L->ci`, the current CallInfo"),
    ("stateStackLastOff", "offsetof(lua_State, stack_last)", ""),
    ("stateStackOff", "offsetof(lua_State, stack)", ""),
    ("stateOpenupvalOff", "offsetof(lua_State, openupval)", ""),
    ("stateTbclistOff", "offsetof(lua_State, tbclist)", ""),
    ("stateErrorJmpOff", "offsetof(lua_State, errorJmp)", ""),
    ("stateBaseCiOff", "offsetof(lua_State, base_ci)", ""),
    ("stateHookmaskOff", "offsetof(lua_State, hookmask)", ""),
    ("stateNCcallsOff", "offsetof(lua_State, nCcalls)", ""),
    # CallInfo
    ("ciSize", "sizeof(CallInfo)", ""),
    ("ciFuncOff", "offsetof(CallInfo, func)", ""),
    ("ciTopOff", "offsetof(CallInfo, top)", ""),
    ("ciPreviousOff", "offsetof(CallInfo, previous)", ""),
    ("ciNextOff", "offsetof(CallInfo, next)", ""),
    ("ciSavedpcOff", "offsetof(CallInfo, u.l.savedpc)", ""),
    ("ciTrapOff", "offsetof(CallInfo, u.l.trap)", ""),
    ("ciNextraargsOff", "offsetof(CallInfo, u.l.nextraargs)", ""),
    ("ciNresultsOff", "offsetof(CallInfo, nresults)", ""),
    ("ciCallstatusOff", "offsetof(CallInfo, callstatus)", ""),
    # closures, upvalues, protos
    ("lclosureProtoOff", "offsetof(LClosure, p)", ""),
    ("lclosureUpvalsOff", "offsetof(LClosure, upvals)", ""),
    ("lclosureNupvaluesOff", "offsetof(LClosure, nupvalues)", ""),
    ("cclosureFOff", "offsetof(CClosure, f)", ""),
    ("upvalVOff", "offsetof(UpVal, v.p)", ""),
    ("upvalValueOff", "offsetof(UpVal, u.value)", "closed value"),
    ("protoNumparamsOff", "offsetof(Proto, numparams)", ""),
    ("protoIsVarargOff", "offsetof(Proto, is_vararg)", ""),
    ("protoMaxstacksizeOff", "offsetof(Proto, maxstacksize)", ""),
    ("protoSizeupvaluesOff", "offsetof(Proto, sizeupvalues)", ""),
    ("protoSizekOff", "offsetof(Proto, sizek)", ""),
    ("protoSizecodeOff", "offsetof(Proto, sizecode)", ""),
    ("protoSizepOff", "offsetof(Proto, sizep)", ""),
    ("protoKOff", "offsetof(Proto, k)", ""),
    ("protoCodeOff", "offsetof(Proto, code)", ""),
    ("protoPOff", "offsetof(Proto, p)", ""),
    ("protoUpvaluesOff", "offsetof(Proto, upvalues)", ""),
    ("upvaldescSize", "sizeof(Upvaldesc)", ""),
    ("upvaldescInstackOff", "offsetof(Upvaldesc, instack)", ""),
    ("upvaldescIdxOff", "offsetof(Upvaldesc, idx)", ""),
    ("upvaldescKindOff", "offsetof(Upvaldesc, kind)", ""),
    # strings and tables
    ("tstringShrlenOff", "offsetof(TString, shrlen)", ""),
    ("tstringHashOff", "offsetof(TString, hash)", ""),
    ("tstringLnglenOff", "offsetof(TString, u.lnglen)", ""),
    ("tstringContentsOff", "offsetof(TString, contents)", ""),
    ("tableFlagsOff", "offsetof(Table, flags)", ""),
    ("tableLsizenodeOff", "offsetof(Table, lsizenode)", ""),
    ("tableAlimitOff", "offsetof(Table, alimit)", ""),
    ("tableArrayOff", "offsetof(Table, array)", ""),
    ("tableNodeOff", "offsetof(Table, node)", ""),
    ("tableLastfreeOff", "offsetof(Table, lastfree)", ""),
    ("tableMetatableOff", "offsetof(Table, metatable)", ""),
    ("nodeSize", "sizeof(Node)", ""),
    ("nodeKeyTtOff", "offsetof(Node, u.key_tt)", ""),
    ("nodeNextOff", "offsetof(Node, u.next)", ""),
    ("nodeKeyValOff", "offsetof(Node, u.key_val)", ""),
    # global_State
    ("gRegistryOff", "offsetof(global_State, l_registry)", ""),
    ("gSeedOff", "offsetof(global_State, seed)", ""),
    ("gGcstpOff", "offsetof(global_State, gcstp)", "`gcstp`: GCSTPUSR once main.c stops the collector"),
    ("gStrtOff", "offsetof(global_State, strt)", ""),
    ("gTmnameOff", "offsetof(global_State, tmname)", ""),
    ("gMtOff", "offsetof(global_State, mt)", ""),
    # common header
    ("gcTtOff", "offsetof(GCObject, tt)", "every collectable object's own tag byte"),
    ("gcMarkedOff", "offsetof(GCObject, marked)", ""),
]
TAGS = [
    ("vNil", "LUA_VNIL"), ("vEmpty", "LUA_VEMPTY"), ("vAbstkey", "LUA_VABSTKEY"),
    ("vFalse", "LUA_VFALSE"), ("vTrue", "LUA_VTRUE"),
    ("vNumInt", "LUA_VNUMINT"), ("vNumFlt", "LUA_VNUMFLT"),
    ("vShrStr", "ctb(LUA_VSHRSTR)"), ("vLngStr", "ctb(LUA_VLNGSTR)"),
    ("vTable", "ctb(LUA_VTABLE)"), ("vLcl", "ctb(LUA_VLCL)"), ("vLcf", "LUA_VLCF"),
    ("vCcl", "ctb(LUA_VCCL)"), ("vLightUserdata", "LUA_VLIGHTUSERDATA"),
    ("vUserdata", "ctb(LUA_VUSERDATA)"), ("vThread", "ctb(LUA_VTHREAD)"),
    ("gcstpUsr", "GCSTPUSR"), ("maxShortLen", "LUAI_MAXSHORTLEN"),
    ("numOpcodes", "NUM_OPCODES"),
]

# newlib's system-call ABI as htif.c and the C library see it (the OS
# boundary, Lua/Os/Htif.lean): `struct _reent`'s errno, `struct stat`,
# open flags, file-type bits, and errno numbers (newlib's, which differ from
# Linux's for some; TCB.Os.Errno.toNat is Linux's).
NEWLIB_HDRS = ["<sys/reent.h>", "<sys/stat.h>", "<fcntl.h>", "<errno.h>", "<sys/time.h>"]
ERRNOS = ["EPERM", "ENOENT", "EBADF", "EACCES", "EBUSY", "EEXIST", "EXDEV", "ENOTDIR",
          "EISDIR", "EINVAL", "EMFILE", "ESPIPE", "ENOSPC", "EROFS", "EMLINK",
          "ENAMETOOLONG", "ENOSYS", "ENOTEMPTY", "ELOOP", "EOVERFLOW"]
NEWLIB = [
    ("reentErrnoOff", "offsetof(struct _reent, _errno)", "`errno` is `_impure_ptr->_errno`"),
    ("statSize", "sizeof(struct stat)", ""),
    ("statModeOff", "offsetof(struct stat, st_mode)", "32-bit `mode_t`"),
    ("statNlinkOff", "offsetof(struct stat, st_nlink)", "16-bit `nlink_t`"),
    ("statSizeOff", "offsetof(struct stat, st_size)", "64-bit `off_t`"),
    ("sIfmt", "S_IFMT", ""), ("sIfchr", "S_IFCHR", ""), ("sIfreg", "S_IFREG", ""),
    ("sIfdir", "S_IFDIR", ""),
    ("timevalSecOff", "offsetof(struct timeval, tv_sec)", "64-bit `time_t` (`_gettimeofday`, the clock)"),
    ("timevalUsecOff", "offsetof(struct timeval, tv_usec)", "64-bit `suseconds_t`"),
    ("oAccmode", "O_ACCMODE", ""), ("oRdonly", "O_RDONLY", ""), ("oWronly", "O_WRONLY", ""),
    ("oRdwr", "O_RDWR", ""), ("oAppend", "O_APPEND", ""), ("oCreat", "O_CREAT", ""),
    ("oTrunc", "O_TRUNC", ""), ("oExcl", "O_EXCL", ""), ("oDirectory", "_FDIRECTORY", "`O_DIRECTORY` (hidden under -std=gnu11)"),
] + [("errno" + e, e, "") for e in ERRNOS]

# ELF symbols (from c/lua-riscv-htif.elf; the chunk lives in .rodata after
# .text, so these do not depend on which chunk is embedded)
ELF = os.path.join(ROOT, "c/lua-riscv-htif.elf")
SYMS = [("symStart", "_start"), ("symMain", "main"), ("symExit", "_exit"),
        ("symLuaVExecute", "luaV_execute"), ("symLuaDCall", "luaD_call"),
        ("symLuaDPrecall", "luaD_precall"), ("symLuaDThrow", "luaD_throw"),
        ("symLuaDRawrunprotected", "luaD_rawrunprotected"),
        ("symLuaPcallk", "lua_pcallk"), ("symLuaLLoadbufferx", "luaL_loadbufferx"),
        ("symLuaBPrint", "luaB_print"), ("symSetjmp", "setjmp"), ("symLongjmp", "longjmp"),
        ("symMalloc", "malloc"), ("symRealloc", "realloc"), ("symFree", "free"),
        ("symTohost", "tohost"), ("symChunkStart", "_chunk_start"), ("symEnd", "_end"),
        ("symHeapEnd", "__heap_end"), ("symStackTop", "__stack_top"),
        # c/src/htif.c's system-call functions and newlib's errno cell
        ("symOpen", "_open"), ("symClose", "_close"), ("symRead", "_read"),
        ("symWrite", "_write"), ("symLseek", "_lseek"), ("symFstat", "_fstat"),
        ("symIsatty", "_isatty"), ("symSbrk", "_sbrk"), ("symKill", "_kill"),
        ("symGetpid", "_getpid"), ("symImpurePtr", "_impure_ptr"),
        ("symStat", "_stat"), ("symUnlink", "_unlink"), ("symRename", "rename"),
        ("symMkdir", "mkdir"), ("symRmdir", "rmdir"), ("symLink", "_link"),
        ("symGettimeofday", "_gettimeofday"), ("symTimes", "_times")]

def elf_syms():
    nm = CC[:-3] + "nm"
    tab = {}
    for line in subprocess.run([nm, ELF], capture_output=True, text=True, check=True).stdout.splitlines():
        f = line.split()
        if len(f) == 3: tab[f[2]] = int(f[0], 16)
    return {n: tab[c] for n, c in SYMS}

def probe():
    src = ['#include "lprefix.h"', '#include <stddef.h>', '#include "lua.h"',
           '#include "lobject.h"', '#include "lstate.h"', '#include "lgc.h"',
           '#include "lopcodes.h"', '#include "lstring.h"']
    src += [f"#include {h}" for h in NEWLIB_HDRS]
    for name, expr, _ in FIELDS:
        src.append(f"const unsigned long lay_{name} = {expr};")
    for name, expr in TAGS:
        src.append(f"const unsigned long lay_{name} = {expr};")
    for name, expr, _ in NEWLIB:
        src.append(f"const unsigned long lay_{name} = {expr};")
    with tempfile.TemporaryDirectory() as d:
        c = os.path.join(d, "probe.c"); s = os.path.join(d, "probe.s")
        open(c, "w").write("\n".join(src) + "\n")
        subprocess.run([CC] + FLAGS + ["-S", "-o", s, c], check=True)
        asm = open(s).read()
    vals, cur = {}, None
    for line in asm.splitlines():
        m = re.match(r"^lay_(\w+):", line)
        if m: cur = m.group(1); continue
        m = re.match(r"^\s+\.dword\s+(-?\d+)", line)
        if m and cur: vals[cur] = int(m.group(1)); cur = None; continue
        m = re.match(r"^\s+\.zero\s+8\b", line)
        if m and cur: vals[cur] = 0; cur = None
    return vals

def render(vals):
    ver = subprocess.run([CC, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    out = ["/-! GENERATED by scripts/gen_lua_layout.py -- do not edit.",
           "",
           "C layout of Lua 5.4.7's VM structures in the bare-metal ELF",
           f"(`{ver}`, rv64i lp64 medany),",
           "read from the cross compiler's own `offsetof`/`sizeof`. -/",
           "", "namespace Lua.Vm.Layout", ""]
    for name, expr, doc in FIELDS:
        out.append(f"/-- `{expr}`{(' — ' + doc) if doc else ''} -/")
        out.append(f"def {name} : Nat := {vals[name]}")
    out.append("")
    out.append("/-! Type tags as stored in `tt_` (collectable variants carry bit 6, `ctb`). -/")
    for name, expr in TAGS:
        out.append(f"/-- `{expr}` -/")
        out.append(f"def {name} : Nat := {vals[name]}")
    out.append("")
    out.append("/-! newlib's system-call ABI (`struct _reent`, `struct stat`, `<fcntl.h>`, `<errno.h>`). -/")
    for name, expr, doc in NEWLIB:
        out.append(f"/-- `{expr}`{(' — ' + doc) if doc else ''} -/")
        out.append(f"def {name} : Nat := {vals[name]}")
    out.append("")
    out.append("/-! Symbol addresses in `c/lua-riscv-htif.elf` (`nm`). -/")
    sy = elf_syms()
    for name, c in SYMS:
        out.append(f"/-- `{c}` -/")
        out.append(f"def {name} : Nat := 0x{sy[name]:08x}")
    out += ["", "end Lua.Vm.Layout", ""]
    return "\n".join(out)

# ---------------------------------------------------------------- runtime
# `Lua/Vm/LayoutRt.lean`: the layout the runtime boundary `luaRuntimeReady`
# (Lua/Vm/Runtime.lean) reads beyond the VM's own structures: more
# `lua_State`/`global_State`/`CallInfo` fields, `struct lua_longjmp` (local to
# ldo.c, so the probe includes ldo.c), newlib's `jmp_buf`/`FILE`/`_reent`,
# and the addresses and sizes (`nm -S`) of the C runtime's globals.
OUT_RT = os.path.join(ROOT, "Lua/Vm/LayoutRt.lean")
RT_FIELDS = [
    ("stateAllowhookOff", "offsetof(lua_State, allowhook)", "`L->allowhook`"),
    ("stateNciOff", "offsetof(lua_State, nci)", "`L->nci` (16-bit)"),
    ("stateErrfuncOff", "offsetof(lua_State, errfunc)", "`L->errfunc` (`ptrdiff_t`)"),
    ("stateOldpcOff", "offsetof(lua_State, oldpc)", "`L->oldpc`"),
    ("gGCdebtOff", "offsetof(global_State, GCdebt)", "`g->GCdebt` (`l_mem`)"),
    ("gStrtHashOff", "offsetof(global_State, strt.hash)", "`g->strt.hash`"),
    ("gStrtNuseOff", "offsetof(global_State, strt.nuse)", "`g->strt.nuse` (int)"),
    ("gStrtSizeOff", "offsetof(global_State, strt.size)", "`g->strt.size` (int)"),
    ("gMainthreadOff", "offsetof(global_State, mainthread)", ""),
    ("gStrcacheOff", "offsetof(global_State, strcache)", "`g->strcache[STRCACHE_N][STRCACHE_M]`"),
    ("ljPreviousOff", "offsetof(struct lua_longjmp, previous)", "ldo.c's `struct lua_longjmp`"),
    ("ljBOff", "offsetof(struct lua_longjmp, b)", "the `jmp_buf`"),
    ("ljStatusOff", "offsetof(struct lua_longjmp, status)", ""),
    ("jmpBufSize", "sizeof(jmp_buf)", "newlib's riscv `jmp_buf` (setjmp stores 14 dwords: ra, s0-s11, sp)"),
    ("fileSize", "sizeof(FILE)", "newlib's `struct __sFILE`"),
    # lane F1-6: the `FILE` fields stdio's write path reads and writes
    ("fileBufPOff", "offsetof(FILE, _p)", "the next byte of the buffer"),
    ("fileROff", "offsetof(FILE, _r)", "read space left"),
    ("fileWOff", "offsetof(FILE, _w)", "write space left (`0` when line-buffered)"),
    ("fileFlagsOff", "offsetof(FILE, _flags)", "`__SLBF`, `__SWR`, … (`short`)"),
    ("fileFileOff", "offsetof(FILE, _file)", "the descriptor (`short`)"),
    ("fileBfBaseOff", "offsetof(FILE, _bf._base)", "the buffer"),
    ("fileBfSizeOff", "offsetof(FILE, _bf._size)", "its size"),
    ("fileLbfsizeOff", "offsetof(FILE, _lbfsize)", "`-_bf._size` when line-buffered"),
    ("fileCookieOff", "offsetof(FILE, _cookie)", "the hooks' argument (the `FILE`)"),
    ("fileWriteOff", "offsetof(FILE, _write)", "the write hook (`__swrite`)"),
    ("fileUbBaseOff", "offsetof(FILE, _ub._base)", "the ungetc buffer"),
    ("reentStdinOff", "offsetof(struct _reent, _stdin)", ""),
    ("reentStdoutOff", "offsetof(struct _reent, _stdout)", ""),
    ("reentStderrOff", "offsetof(struct _reent, _stderr)", ""),
    ("glueNextOff", "offsetof(struct _glue, _next)", "`struct _glue` (`__sglue`)"),
    ("glueNiobsOff", "offsetof(struct _glue, _niobs)", ""),
    ("glueIobsOff", "offsetof(struct _glue, _iobs)", ""),
    ("cistC", "CIST_C", "`callstatus` bit: a C function"),
    ("cistFresh", "CIST_FRESH", "`callstatus` bit: a fresh `luaV_execute` frame"),
    ("luaMinstack", "LUA_MINSTACK", "stack slots a C function may use"),
    ("extraStack", "EXTRA_STACK", "slots above `stack_last`"),
    ("luaNumtypes", "LUA_NUMTYPES", "length of `g->mt`"),
    ("luaTnil", "LUA_TNIL", ""), ("luaTboolean", "LUA_TBOOLEAN", ""),
    ("luaTnumber", "LUA_TNUMBER", ""), ("luaTstring", "LUA_TSTRING", ""),
    ("strcacheN", "STRCACHE_N", ""), ("strcacheM", "STRCACHE_M", ""),
    ("gcShrStr", "LUA_VSHRSTR", "a short `TString`'s own header tag (`GCObject.tt`: `luaC_newobj` stores the variant without `BIT_ISCOLLECTABLE`; only a `TValue`'s `tt_` has it)"),
    ("gcLngStr", "LUA_VLNGSTR", "a long `TString`'s own header tag"),
]
# (lean name, symbol, doc): address `<name>` and, where the size matters, `<name>Size`
RT_SYMS = [
    ("symGlobalPointer", "__global_pointer$", "`gp` after crt0"),
    ("symLuaDCallnoyield", "luaD_callnoyield", "`ccall` (inlined), the caller of `luaV_execute`"),
    ("symFCall", "f_call", ""),
    ("symLuaDPcall", "luaD_pcall", ""),
    ("symMallocAv", "__malloc_av_", "dlmalloc's bins; bin 0's `fd` is the top chunk"),
    ("symMallocSbrkBase", "__malloc_sbrk_base", ""),
    ("symMallocTopPad", "__malloc_top_pad", ""),
    ("symMallocMaxSbrked", "__malloc_max_sbrked_mem", ""),
    ("symMallocMallinfo", "__malloc_current_mallinfo", ""),
    ("symBrk", "brk.0", "htif.c `_sbrk`'s static break"),
    ("symStdioExitHandler", "__stdio_exit_handler", "non-NULL once `__sinit` ran"),
    ("symSglue", "__sglue", ""),
    ("symSf", "__sf", "the three standard `FILE`s"),
    ("symImpureData", "_impure_data", ""),
    ("symFsReady", "fs_ready", "htif.c"),
    ("symFds", "fds", "htif.c descriptor table"),
    ("symFiles", "files", "htif.c file table"),
]
RT_SIZED = {"symSf", "symFds", "symFiles", "symImpureData", "symSglue"}

def elf_syms_sized():
    nm = CC[:-3] + "nm"
    tab = {}
    for line in subprocess.run([nm, "-S", ELF], capture_output=True, text=True, check=True).stdout.splitlines():
        f = line.split()
        if len(f) == 4: tab[f[3]] = (int(f[0], 16), int(f[1], 16))
        elif len(f) == 3: tab.setdefault(f[2], (int(f[0], 16), None))
    return {n: tab[c] for n, c, _ in RT_SYMS}

def probe_rt():
    src = ['#include "ldo.c"', '#include <stdio.h>', '#include <setjmp.h>', '#include <sys/reent.h>']
    for name, expr, _ in RT_FIELDS:
        src.append(f"const unsigned long lay_{name} = {expr};")
    with tempfile.TemporaryDirectory() as d:
        c = os.path.join(d, "probe_rt.c"); s = os.path.join(d, "probe_rt.s")
        open(c, "w").write("\n".join(src) + "\n")
        subprocess.run([CC] + [f for f in FLAGS if f != "-Wall"] + ["-w", "-S", "-o", s, c], check=True)
        asm = open(s).read()
    vals, cur = {}, None
    for line in asm.splitlines():
        m = re.match(r"^lay_(\w+):", line)
        if m: cur = m.group(1); continue
        m = re.match(r"^\s+\.dword\s+(-?\d+)", line)
        if m and cur: vals[cur] = int(m.group(1)); cur = None; continue
        m = re.match(r"^\s+\.zero\s+8\b", line)
        if m and cur: vals[cur] = 0; cur = None
    return vals

def render_rt(vals):
    out = ["/-! GENERATED by scripts/gen_lua_layout.py -- do not edit.",
           "",
           "The runtime layout `luaRuntimeReady` (Lua/Vm/Runtime.lean) reads beyond",
           "`Lua/Vm/Layout.lean`: more `lua_State`/`global_State` fields, ldo.c's",
           "`struct lua_longjmp`, newlib's `jmp_buf`/`FILE`/`_reent`/`_glue`, and the",
           "addresses (and `nm -S` sizes) of the C runtime's globals in",
           "`c/lua-riscv-htif.elf`. -/",
           "", "namespace Lua.Vm.Layout", ""]
    for name, expr, doc in RT_FIELDS:
        out.append(f"/-- `{expr}`{(' — ' + doc) if doc else ''} -/")
        out.append(f"def {name} : Nat := {vals[name]}")
    out.append("")
    sy = elf_syms_sized()
    for name, c, doc in RT_SYMS:
        a, sz = sy[name]
        out.append(f"/-- `{c}`{(' — ' + doc) if doc else ''} -/")
        out.append(f"def {name} : Nat := 0x{a:08x}")
        if name in RT_SIZED:
            out.append(f"/-- `sizeof` of `{c}` (`nm -S`) -/")
            out.append(f"def {name}Size : Nat := {sz}")
    out += ["", "end Lua.Vm.Layout", ""]
    return "\n".join(out)

if __name__ == "__main__":
    outs = [(OUT, render(probe())), (OUT_RT, render_rt(probe_rt()))]
    if "--check" in sys.argv:
        ok = all(os.path.exists(p) and open(p).read() == t for p, t in outs)
        print("layout: ok" if ok else "layout: DRIFT (rerun scripts/gen_lua_layout.py)")
        sys.exit(0 if ok else 1)
    for p, t in outs:
        os.makedirs(os.path.dirname(p), exist_ok=True)
        open(p, "w").write(t)
        print(f"wrote {p}")

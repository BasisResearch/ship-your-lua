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
        ("symHeapEnd", "__heap_end"), ("symStackTop", "__stack_top")]

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
    for name, expr, _ in FIELDS:
        src.append(f"const unsigned long lay_{name} = {expr};")
    for name, expr in TAGS:
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
    out.append("/-! Symbol addresses in `c/lua-riscv-htif.elf` (`nm`). -/")
    sy = elf_syms()
    for name, c in SYMS:
        out.append(f"/-- `{c}` -/")
        out.append(f"def {name} : Nat := 0x{sy[name]:08x}")
    out += ["", "end Lua.Vm.Layout", ""]
    return "\n".join(out)

if __name__ == "__main__":
    text = render(probe())
    if "--check" in sys.argv:
        ok = os.path.exists(OUT) and open(OUT).read() == text
        print("layout: ok" if ok else "layout: DRIFT (rerun scripts/gen_lua_layout.py)")
        sys.exit(0 if ok else 1)
    os.makedirs(os.path.dirname(OUT), exist_ok=True)
    open(OUT, "w").write(text)
    print(f"wrote {OUT}")

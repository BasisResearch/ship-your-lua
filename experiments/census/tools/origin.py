"""function name -> origin object (source file or archive member)."""
import subprocess, re, os, glob
from lib import *

def archive_defs():
    m = {}
    for lib, path in [("libgcc", TC + "/lib/gcc/riscv-none-elf/15.2.0/rv64i/lp64/libgcc.a"),
                      ("libc", TC + "/riscv-none-elf/lib/rv64i/lp64/libc.a"),
                      ("libm", TC + "/riscv-none-elf/lib/rv64i/lp64/libm.a")]:
        out = subprocess.run([BIN + "nm", "-A", "--defined-only", path],
                             capture_output=True, text=True).stdout
        for line in out.splitlines():
            p = line.split()
            if len(p) == 3 and p[1] in ("T", "W"):
                member = p[0].split(":")[1]
                m.setdefault(p[2], f"{lib}:{member}")
    return m

def lua_defs():
    m = {}
    files = sorted(glob.glob(LUA_SRC + "/*.c")) + [os.path.dirname(os.path.abspath(LUA_ELF)) + "/src/main.c", os.path.dirname(os.path.abspath(LUA_ELF)) + "/src/htif.c"]
    for f in files:
        txt = open(f, errors="replace").read()
        for mm in re.finditer(r"^[A-Za-z_][\w \*\(\)]*?\b([A-Za-z_]\w*)\s*\([^;{]*\)\s*\{", txt, re.M):
            m.setdefault(mm.group(1), os.path.basename(f))
        for mm in re.finditer(r"^(?:LUA_API|LUALIB_API|LUAI_FUNC|LUAMOD_API)[^\n]*\n?\s*\(?([A-Za-z_]\w*)\)?\s*\(", txt, re.M):
            m.setdefault(mm.group(1), os.path.basename(f))
    return m

def origins(elf, funcs):
    syms = symbols(elf)
    loc = {}
    for (a, sz, typ, bind, name, f) in syms:
        if typ == "FUNC" and bind == "LOCAL" and f:
            loc[a] = f
    ar = archive_defs(); ld = lua_defs()
    res = {}
    for n in funcs:
        base = re.sub(r"\.(isra|constprop|part|cold)\.\d+", "", n)
        st = funcs[n]["start"]
        if st in loc: o = loc[st]
        elif base == "main" and elf == LUA_ELF: o = "main.c"
        elif n == "_start": o = "crt0.S"
        elif base in ld: o = ld[base]
        elif base in ar: o = ar[base]
        else: o = "?"
        res[n] = o
    return res

def family(o):
    if o in ("crt0.S", "htif.c", "main.c"): return "boot"
    if o.startswith("libgcc"): return "libgcc"
    if o.startswith("libm") or o.startswith("libm_a"): return "libm"
    if o.startswith("libc") : return "libc"
    if o.endswith(".c"): return "lua"
    return "?"

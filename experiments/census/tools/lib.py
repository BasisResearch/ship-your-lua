"""Shared parsing for the Lua disassembly census (objdump -d text + ELF bytes)."""
import re, struct, subprocess, os, collections

HOME = os.path.expanduser("~")
TC = HOME + "/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1"
BIN = TC + "/bin/riscv-none-elf-"
REPO = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
LUA_ELF = os.environ.get("LUA_ELF", REPO + "/c/lua-riscv-htif.elf")
SYI = os.environ.get("SYI", HOME + "/Documents/code/syi")
WHILE_ELF = SYI + "/c/while-riscv-htif.elf"
LUA_SRC = os.environ.get("LUA_SRC", REPO + "/vendor/lua-5.4.7/src")

func_re = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
inst_re = re.compile(r"^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)(?:\s+(.*))?$")
target_re = re.compile(r"([0-9a-f]+) <([^>+]+)(\+0x[0-9a-f]+)?>")

BRANCHES = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez",
            "bgez", "bltz", "bgtz", "ble", "bgt", "bleu", "bgtu"}


class Ins:
    __slots__ = ("addr", "word", "mn", "ops", "cmt", "func")

    def __init__(s, addr, word, mn, rest, func):
        s.addr, s.word, s.mn, s.func = addr, word, mn, func
        rest = rest or ""
        ops, _, cmt = rest.partition("#")
        s.ops = ops.strip()
        s.cmt = cmt.strip()

    def opl(s):
        return [o.strip() for o in s.ops.split(",")] if s.ops else []

    def target(s):
        """direct target of jal/j/branch (int) or None"""
        if s.mn in BRANCHES or s.mn in ("j", "jal"):
            m = target_re.search(s.ops)
            if m:
                return int(m.group(1), 16)
        return None

    def cmt_addr(s):
        m = target_re.search(s.cmt) if s.cmt else None
        return int(m.group(1), 16) if m else None


def parse_disasm(path):
    funcs = collections.OrderedDict()   # name -> {"start", "insts"}
    by_addr = {}
    cur = None
    for line in open(path):
        m = func_re.match(line)
        if m:
            cur = m.group(2)
            if cur in funcs:
                cur = f"{cur}@{int(m.group(1), 16):x}"
            funcs[cur] = {"start": int(m.group(1), 16), "insts": []}
            continue
        m = inst_re.match(line)
        if m and cur is not None:
            i = Ins(int(m.group(1), 16), m.group(2), m.group(3), m.group(4), cur)
            funcs[cur]["insts"].append(i)
            by_addr[i.addr] = i
    for n, f in funcs.items():
        f["end"] = f["insts"][-1].addr + 4 if f["insts"] else f["start"]
    return funcs, by_addr


class Elf:
    def __init__(self, path):
        self.data = open(path, "rb").read()
        d = self.data
        shoff, = struct.unpack_from("<Q", d, 0x28)
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", d, 0x3a)
        secs = []
        for i in range(shnum):
            name, typ, flags, addr, off, size = struct.unpack_from(
                "<IIQQQQ", d, shoff + i * shentsize)
            secs.append([name, typ, flags, addr, off, size])
        stroff = secs[shstrndx][4]
        self.sections = {}
        for name, typ, flags, addr, off, size in secs:
            nm = d[stroff + name: d.index(b"\0", stroff + name)].decode()
            self.sections[nm] = (addr, off, size, typ)

    def read(self, addr, n):
        for nm, (a, off, size, typ) in self.sections.items():
            if a and a <= addr and addr + n <= a + size and typ != 8:  # not NOBITS
                return self.data[off + addr - a: off + addr - a + n]
        return None

    def u32(self, addr):
        b = self.read(addr, 4)
        return struct.unpack("<I", b)[0] if b else None

    def s32(self, addr):
        b = self.read(addr, 4)
        return struct.unpack("<i", b)[0] if b else None

    def u64(self, addr):
        b = self.read(addr, 8)
        return struct.unpack("<Q", b)[0] if b else None


def symbols(path):
    """[(addr, size, type, bind, name, file)] from readelf -sW, with the FILE
    context of local symbols."""
    out = subprocess.run([BIN + "readelf", "-sW", path], capture_output=True,
                         text=True).stdout
    res = []
    curfile = None
    for line in out.splitlines():
        p = line.split()
        if len(p) < 8 or not p[0].endswith(":") or not p[0][:-1].isdigit():
            continue
        val, size, typ, bind, ndx, name = int(p[1], 16), int(p[2], 0) if not p[2].startswith("0x") else int(p[2], 16), p[3], p[4], p[6], p[7]
        if typ == "FILE":
            curfile = name
            continue
        res.append((val, size, typ, bind, name, curfile if bind == "LOCAL" else None))
    return res

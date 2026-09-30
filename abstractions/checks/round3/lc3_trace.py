"""Shared helpers for the round-3 callee checks (callee_census.py, lc3_footprint.py).

* `elf_for(luac)`: the committed ELF with the chunk region patched to `luac`
  (scripts/gen_lua_boot_witness.py `patched_elf`), cached in $LC3_WORK.
* `rows(elf)`: stream the Lean emulator's `--trace-all` rows as tuples
  (step, pc, npc, regs[31], mem) where mem is None or (kind 'L'/'S', width,
  addr, pre, post).  Nothing is written to disk.
* `ctx()`: the disassembly context (experiments/a1-falsifiers/armlib.py).
"""
import os, sys, subprocess, hashlib, bisect
from pathlib import Path

REPO = Path(__file__).resolve().parents[3]
MAIN = Path(os.path.expanduser("~/Documents/code/ship-your-lua"))
sys.path.insert(0, str(REPO / "scripts"))
sys.path.insert(0, str(REPO / "experiments/a1-falsifiers"))
EMU = os.environ.get("EMU") or str(
    next(p for p in [REPO / "riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator",
                     MAIN / "riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator"] if p.exists()))
LUAC = os.environ.get("LUAC") or str(MAIN / "c/luac")
WORK = Path(os.environ.get("LC3_WORK", "/tmp/lc3_work"))
WORK.mkdir(parents=True, exist_ok=True)

_lay = None


def lay():
    global _lay
    if _lay is None:
        import gen_lua_boot_witness as W
        _lay = W.layout()
    return _lay


def compile_lua(src):
    out = WORK / (Path(src).stem + ".luac")
    subprocess.run([LUAC, "-s", "-o", str(out), str(src)], check=True)
    return out


def elf_for(chunk_path):
    import gen_lua_boot_witness as W
    chunk = Path(chunk_path).read_bytes()
    h = hashlib.sha1(chunk).hexdigest()[:12]
    out = WORK / f"{Path(chunk_path).stem}_{h}.elf"
    if not out.exists():
        out.write_bytes(W.patched_elf(lay(), chunk))
    return out


def rows(elf, max_steps=60_000_000):
    p = subprocess.Popen([EMU, str(elf), "--trace-all", "--max-steps", str(max_steps)],
                         stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, bufsize=1 << 20)
    for line in p.stderr:
        if not line.startswith("T\t"):
            continue
        f = line.rstrip("\n").split("\t")
        regs = [int(x, 16) for x in f[4:35]]
        mem = None
        if len(f) > 38 and f[35][0] in "LS":
            mem = (f[35][0], int(f[35][1:]), int(f[36], 16), int(f[37], 16), int(f[38], 16))
        yield int(f[1]), int(f[2], 16), int(f[3], 16), regs, mem
    p.wait()


_ctx = None


def ctx():
    global _ctx
    if _ctx is None:
        import armlib
        _ctx = armlib.load()
        starts = sorted((f["start"], n) for n, f in _ctx["funcs"].items() if f["insts"])
        _ctx["start_list"] = [a for a, _ in starts]
        _ctx["start_name"] = dict(starts)
    return _ctx


def func_at(a):
    c = ctx()
    i = bisect.bisect_right(c["start_list"], a) - 1
    if i < 0:
        return None
    n = c["start_name"][c["start_list"][i]]
    return n if a < c["funcs"][n]["end"] else None


# register indices in the 31-entry regs list (x1..x31)
def R(regs, x):
    return 0 if x == 0 else regs[x - 1]


RA, SP, A0, A1, A2, A3 = 1, 2, 10, 11, 12, 13
S0, S7, S9, S11 = 8, 23, 25, 27

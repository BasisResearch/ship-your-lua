"""Lane F1-19: trace `luaL_tolstring` on the Sail emulator (the evidence for
`PrintFlt_Statement`, `PrintFn_Statement` and `TolInt_Statement` being true).

For every call of `luaL_tolstring` in a program's run: the `_malloc_r` calls
and their sizes, `luaS_resize` calls, and the static words (`.tohost` to the
heap) it loads and stores, by symbol.

    python3 experiments/print_alloc/probe.py experiments/print_alloc/fltprobe.lua

The chunk is compiled with the host `c/luac` (`make -C c host`, or `LUAC=`)
and patched into the committed ELF as the boot witness generator does.
"""
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts"))
import gen_lua_boot_witness as W  # noqa: E402

LUAC = os.environ.get("LUAC", str(ROOT / "c" / "luac"))


def main():
    src = Path(sys.argv[1])
    work = Path(tempfile.mkdtemp())
    chunk = work / (src.stem + ".luac")
    subprocess.run([LUAC, "-s", "-o", str(chunk), str(src)], check=True)
    lay = W.layout()
    elf = work / (src.stem + ".elf")
    elf.write_bytes(W.patched_elf(lay, chunk.read_bytes()))
    sym = {}
    for line in subprocess.run([W.GL.CC[:-3] + "nm", str(elf)], capture_output=True, text=True).stdout.splitlines():
        p = line.split()
        if len(p) == 3:
            sym.setdefault(p[2], int(p[0], 16))
    names = sorted((a, n) for n, a in sym.items())

    def symof(a):
        lo, hi = 0, len(names)
        while lo + 1 < hi:
            mid = (lo + hi) // 2
            if names[mid][0] <= a:
                lo = mid
            else:
                hi = mid
        return f"{names[lo][1]}+{a - names[lo][0]:#x}"

    tol, mal, res = sym["luaL_tolstring"], sym["_malloc_r"], sym["luaS_resize"]
    lo_s, hi_s = sym["tohost"], sym["__bss_end"]
    proc = subprocess.Popen([str(W.EMU), str(elf), "--trace-all", "--max-steps", "50000000"],
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
    cur, segs = None, []
    for line in proc.stderr:
        p = line.rstrip("\n").split("\t")
        if p[0] != "T":
            continue
        pc = int(p[2], 16)
        if cur is None and pc == tol:
            cur = dict(ret=int(p[4], 16), idx=int(p[14], 16), mallocs=[], loads={}, stores={}, resize=0, steps=0)
        if cur is not None:
            cur["steps"] += 1
            if pc == mal:
                cur["mallocs"].append(int(p[14], 16))
            if pc == res:
                cur["resize"] += 1
            if len(p) > 36 and p[35][:1] in ("L", "S"):
                a = int(p[36], 16)
                if lo_s <= a < hi_s:
                    d = cur["loads"] if p[35][0] == "L" else cur["stores"]
                    d[symof(a)] = d.get(symof(a), 0) + 1
            if pc == cur["ret"]:
                segs.append(cur)
                cur = None
    proc.wait()
    print("console:", proc.stdout.read())
    for i, c in enumerate(segs):
        print(f"luaL_tolstring #{i} idx={c['idx']} steps={c['steps']} mallocs={c['mallocs']} resize={c['resize']}")
        print("   loads :", dict(sorted(c["loads"].items())))
        print("   stores:", dict(sorted(c["stores"].items())))


if __name__ == "__main__":
    main()

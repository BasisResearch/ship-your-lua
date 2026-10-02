#!/usr/bin/env python3
"""Round 4, law L4-str on real traces.

> No store between two dispatch-head crossings lands in the bytes or the
> terminator of a string object reachable, at the first crossing, from a
> register `R[j]` (`j < maxstacksize`) or a constant `K[i]` of the running
> function.

Method (the round-3 L-C4 tooling, `abstractions/checks/round3/lc4_trace.py`):
patch the program's `luac -s` chunk into the ELF, stream the Lean Sail
emulator's `--trace-all`, keep a shadow memory (PT_LOAD bytes plus every
traced store; every traced load is checked against it). At each head
crossing (`lw s4,0(s11)`) collect the reachable strings: for each, its
header `[ts, ts + 24)` and its contents plus terminator
`[ts + 24, ts + 24 + len]`. Every store until the next crossing is checked
against both. Also at each crossing:

* the terminator byte is 0 (`TStringRepr`'s last conjunct);
* the object is disjoint from the Lua stack `[L->stack, L->stack_last +
  16 * EXTRA_STACK)`, `luaV_execute`'s C frame `[sp, sp + 176)`, the C stack
  below it, `L` and `ci` (the `Win`/`Scratch` regions of `VmRel`).

Stores into a header are reported apart (GC `marked`, a long string's
`extra`/`hash`); they are not the law's bytes. Each hit is attributed to
the head's opcode and to the storing function.

    python3 abstractions/checks/round4/lstr_trace.py [prog ...]

A prog is a stem of `c/tests/<stem>.luac` or `difftest/<stem>`.
"""
from __future__ import annotations

import argparse
import bisect
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
sys.path.insert(0, str(ROOT / "abstractions/checks/round3"))
import lc4_trace as T   # noqa: E402

BW = T.BW
OBJDUMP = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump"
GC_SHR, GC_LNG = 4, 20
EXTRA_STACK = 5
# the collector's marking and sweeping (a store by one of them means a GC cycle ran)
GCFNS = {"reallymarkobject", "propagatemark", "propagateall", "atomic", "sweeplist",
         "sweepstep", "sweepgen.isra.0", "entersweep", "singlestep", "luaC_step", "freeobj",
         "markbeingfnz", "remarkupvals", "restartcollection", "luaC_fullgc", "fullinc"}
DEFAULT = ["f4_strlite", "print_print", "f1_src", "difftest/f4_strings", "difftest/f1_arith",
           "difftest/f4_objects", "difftest/f2_tablelib"]


def symbols(elf):
    out = subprocess.run([str(OBJDUMP), "-t", str(elf)], capture_output=True, text=True).stdout
    fs = []
    for line in out.splitlines():
        p = line.split()
        if len(p) >= 6 and p[2] == "F" and p[3] == ".text":
            fs.append((int(p[0], 16), int(p[4], 16), p[-1]))
    fs.sort()
    return fs


def fn_of(fs, starts, pc):
    i = bisect.bisect_right(starts, pc) - 1
    if i >= 0 and fs[i][0] <= pc < fs[i][0] + max(fs[i][1], 4):
        return fs[i][2]
    return hex(pc)


def strings_at(sh, s9, maxs, proto):
    """{ts: (len, origin)} for the strings reachable from R[0..maxs) and K."""
    out = {}
    k, sizek = sh.rd(proto + 56, 8), sh.rd(proto + 20, 4)
    slots = [(s9 + 16 * j, f"R{j}") for j in range(maxs)] + \
            [(k + 16 * i, f"K{i}") for i in range(min(sizek, 4096))]
    for a, org in slots:
        if sh.byte(a + 8) in (T.V_SHR, T.V_LNG):
            ts = sh.rd(a, 8)
            tt = sh.byte(ts + 8)
            n = sh.byte(ts + 11) if tt == GC_SHR else sh.rd(ts + 16, 8) if tt == GC_LNG else None
            if n is not None and n < 1 << 20:
                out.setdefault(ts, (n, org))
    return out


def run(prog, work, max_steps, fs):
    starts = [f[0] for f in fs]
    if prog.startswith("difftest/"):
        stem = prog.split("/", 1)[1]
        chunk = work / f"{stem}.luac"
        subprocess.run([str(T.LUAC), "-s", "-o", str(chunk),
                        str(ROOT / "c/tests/difftest" / f"{stem}.lua")], check=True)
    elif prog.endswith(".lua"):
        stem = Path(prog).stem
        chunk = work / f"{stem}.luac"
        subprocess.run([str(T.LUAC), "-s", "-o", str(chunk), prog], check=True)
    else:
        stem, chunk = prog, ROOT / "c/tests" / f"{prog}.luac"
    lay = BW.layout()
    raw = BW.patched_elf(lay, chunk.read_bytes())
    elf = work / f"{stem}.elf"
    elf.write_bytes(raw)
    sh = T.Shadow(raw)
    st = dict(steps=0, heads=0, load_mismatch=0, strings_seen=0, long_seen=0, out_bytes=0,
              term_bad=0, overlap_win=0, gc_stores=0,
              body_hits=0, header_hits=0)
    body_cex, header_by, overlap_cex, term_cex = [], {}, [], []
    seen = set()
    watch_body, watch_hdr = {}, {}      # byte address -> ts
    meta = {}                           # ts -> (len, origin)
    op = "boot"
    ival, created = [], {}
    t0 = time.time()
    proc = subprocess.Popen([str(T.EMU), str(elf), "--trace-all", "--max-steps", str(max_steps)],
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                            bufsize=1 << 20)
    last = None
    for line in proc.stderr:
        if not line.startswith("T\t"):
            continue
        f = line.rstrip("\n").split("\t")
        last = f
        pc = int(f[2], 16)
        if len(f) > 35 and f[35] != "O":
            kind, w = f[35][0], int(f[35][1:])
            a = int(f[36], 16)
            if kind == "S":
                for b in range(a, a + w):
                    if b in watch_body:
                        st["body_hits"] += 1
                        ts = watch_body[b]
                        if len(body_cex) < 20:
                            body_cex.append((int(f[1]), op, fn_of(fs, starts, pc), hex(pc), hex(b),
                                             hex(ts), meta[ts]))
                        break
                    if b in watch_hdr:
                        st["header_hits"] += 1
                        ts = watch_hdr[b]
                        key = (op, fn_of(fs, starts, pc), b - ts)
                        header_by[key] = header_by.get(key, 0) + 1
                        break
                fnn = fn_of(fs, starts, pc)
                ival.append((a, w, fnn))
                if fnn in GCFNS:
                    st["gc_stores"] += 1
                sh.store(a, w, int(f[38], 16))
            else:
                pre = int(f[37], 16) & ((1 << (8 * w)) - 1)
                if sh.rd(a, w) != pre:
                    st["load_mismatch"] += 1
                    sh.store(a, w, pre)
        tail = 39 if len(f) > 35 and f[35] != "O" else 35
        if len(f) >= tail + 4 and f[tail] == "O" and int(f[tail + 3]) < 256:
            st["out_bytes"] += 1
        if pc == T.HEAD:
            rg = lambda r: int(f[3 + r], 16)
            s9, s7, sp, Lp = rg(25), rg(23), rg(2), rg(8)
            func = sh.rd(s7, 8)
            proto = sh.rd(sh.rd(func, 8) + 24, 8)
            maxs = sh.byte(proto + 12)
            code = sh.rd(proto + 64, 8)
            word = sh.rd(rg(27), 4)
            prev_op = op
            op = T.opname(word)
            st["heads"] += 1
            strs = strings_at(sh, s9, maxs, proto)
            # control: stores of the last interval into strings reachable only now
            # (a string being created: luaS_newlstr / internshrstr / memcpy)
            for ts, (n, org) in strs.items():
                if ts in meta:
                    continue
                for a, w, fn in ival:
                    if a < ts + 24 + n + 1 and ts < a + w:
                        key = (prev_op, fn)
                        created[key] = created.get(key, 0) + 1
            ival = []
            watch_body, watch_hdr, meta = {}, {}, {}
            stk, stk_last = sh.rd(Lp + 48, 8), sh.rd(Lp + 40, 8)
            wins = [("luastack", stk, stk_last + 16 * EXTRA_STACK), ("cframe", sp, sp + 176),
                    ("cstack", T.HEAP_END, T.STACK_TOP), ("L", Lp, Lp + 200), ("ci", s7, s7 + 64)]
            for ts, (n, org) in strs.items():
                meta[ts] = (n, org)
                lo, hi = ts, ts + 24 + n + 1
                for b in range(ts, ts + 24):
                    watch_hdr[b] = ts
                for b in range(ts + 24, hi):
                    watch_body[b] = ts
                if ts not in seen:
                    seen.add(ts)
                    st["strings_seen"] += 1
                    st["long_seen"] += n > 40
                    if sh.byte(ts + 24 + n) != 0:
                        st["term_bad"] += 1
                        term_cex.append((hex(ts), n, org))
                    for nm, a, b in wins:
                        if lo < b and a < hi:
                            st["overlap_win"] += 1
                            overlap_cex.append((hex(ts), n, org, nm))
    proc.wait()
    elf.unlink()
    st["steps"] = int(last[1]) + 1 if last else 0
    st["wall_s"] = round(time.time() - t0, 1)
    return stem, st, body_cex, header_by, overlap_cex, term_cex, created


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("progs", nargs="*", default=DEFAULT)
    ap.add_argument("--max-steps", type=int, default=30_000_000)
    a = ap.parse_args()
    fs = symbols(ROOT / "c/lua-riscv-htif.elf")
    with tempfile.TemporaryDirectory() as d:
        for p in a.progs:
            stem, st, body, hdr, ov, term, created = run(p, Path(d), a.max_steps, fs)
            print(f"{stem}: " + " ".join(f"{k}={v}" for k, v in st.items()))
            for c in body:
                print(f"  BODY-STORE step={c[0]} op={c[1]} fn={c[2]} pc={c[3]} addr={c[4]} "
                      f"ts={c[5]} (len, origin)={c[6]}")
            for (op, fn, off), n in sorted(hdr.items(), key=lambda kv: -kv[1]):
                print(f"  header store x{n}: op={op} fn={fn} offset=+{off}")
            for (op, fn), n in sorted(created.items(), key=lambda kv: -kv[1]):
                print(f"  control: creation store x{n}: op={op} fn={fn}")
            for c in ov[:10]:
                print(f"  OVERLAP ts={c[0]} len={c[1]} origin={c[2]} region={c[3]}")
            for c in term[:10]:
                print(f"  TERMINATOR!=0 ts={c[0]} len={c[1]} origin={c[2]}")
            sys.stdout.flush()


if __name__ == "__main__":
    main()

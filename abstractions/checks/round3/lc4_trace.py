#!/usr/bin/env python3
"""L-C4 (value law), trace side: decode the bytecode VM state from the real
machine at every dispatch-head crossing of a Sail run.

For each program:

1. patch its `luac -s` chunk into `c/lua-riscv-htif.elf` (the boot witness's
   `patched_elf`, so every program runs the committed text);
2. run the Lean Sail emulator with `--trace-all`, streaming stderr (the trace
   is never stored);
3. keep a shadow memory: the PT_LOAD bytes, then every traced store's landing
   bytes (`post`), in order; every traced load's `pre` bytes are checked
   against it (a replay self-check);
4. at every step at HEAD (`lw s4,0(s11)`, the fetch of `vmfetch`), decode:
   * `func = ci->func` (s7), `base` (s9; checked = func + 16), the closure and
     `Proto` from `func`'s payload, `code`, `maxstacksize`;
   * pc = (s11 - code) / 4, and the word the `lw` loads;
   * every register j < maxstacksize from its slot `base + 16 j` (tag byte at
     +8, payload at +0): nil (tag % 16 = 0), false/true, int, string (TString:
     short `shrlen` at +11 or long `lnglen` at +16, contents at +24), light C
     function `luaB_print`; anything else is undecodable (`?`);
   * the console so far (the `O` suffix's appended bytes).

It writes `<work>/<prog>.heads` (one line per head) and `<work>/<prog>.proto.lean`
(the program's `Proto`, from `scripts/gen_proto.py`) for `LC4Check.lean`,
which runs the real `Lua.Bytecode.step?` over them (`lc4_run.sh`).

    python3 abstractions/checks/round3/lc4_trace.py [--work DIR] [prog ...]

A prog is a stem of `c/tests/<stem>.luac`, or `difftest/<stem>` (compiled
from `c/tests/difftest/<stem>.lua` with `c/luac -s`).
"""
from __future__ import annotations

import argparse
import os
import struct
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
MAIN = Path(os.environ.get("SYL_MAIN", Path.home() / "Documents/code/ship-your-lua"))
sys.path.insert(0, str(ROOT / "scripts"))
import gen_lua_boot_witness as BW  # noqa: E402

EMU = next(p for p in [BW.EMU, MAIN / "riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator"]
           if p.exists())
LUAC = next(p for p in [ROOT / "c/luac", MAIN / "c/luac"] if p.exists())

HEAD = 0x8001bfe8          # lw s4,0(s11); checked against the ELF below
HEAD_WORD = 0x000daa03
SYM_PRINT = 0x80022f18     # Layout.symLuaBPrint
V_SHR, V_LNG, V_LCF = 68, 84, 22
TOHOST, END, HEAP_END, STACK_TOP = 0x8005c6c0, 0x8006ecd0, 0x87800000, 0x88000000
EXEC_FRAME = 176


def region(a, ctx):
    """Classify a store address against the previous head's context (L-C6)."""
    base, maxs, sp, ci, L, stk, stk_last = ctx
    if base <= a < base + 16 * maxs:
        return "slot"
    if sp <= a < sp + EXEC_FRAME:
        return "cframe"
    if TOHOST <= a < TOHOST + 16:
        return "tohost"
    if HEAP_END <= a < STACK_TOP:
        return "cstack-callee" if a < sp else "cstack-caller"
    if ci <= a < ci + 64:
        return "ci"
    if L <= a < L + 200:
        return "L"
    if stk <= a < stk_last + 16 * 6:
        return "luastack-other"
    if a < END:
        return "static"
    return "heap"

OPNAMES = []
for line in open(ROOT / "vendor/lua-5.4.7/src/lopcodes.h"):
    line = line.strip()
    if line.startswith("OP_") and "," in line:
        OPNAMES.append(line.split(",")[0][3:])

DEFAULT = ["while", "f1_ops", "f1b_bits", "print_print", "f1_src", "f4_strlite",
           "difftest/f1_arith", "difftest/f1_cond", "difftest/f1_for", "difftest/f1_while"]


class Shadow:
    def __init__(self, raw):
        self.vaddr, off, filesz = BW.pt_load(raw)
        self.img = bytearray(raw[off:off + filesz])
        self.w = {}

    def byte(self, a):
        b = self.w.get(a)
        if b is not None:
            return b
        i = a - self.vaddr
        return self.img[i] if 0 <= i < len(self.img) else 0

    def rd(self, a, n):
        return int.from_bytes(bytes(self.byte(a + i) for i in range(n)), "little")

    def store(self, a, n, v):
        for j in range(n):
            self.w[a + j] = (v >> (8 * j)) & 0xFF


def decode_val(sh, slot):
    t = sh.byte(slot + 8)
    x = sh.rd(slot, 8)
    if t % 16 == 0:
        return "n"
    if t == 1:
        return "b0"
    if t == 17:
        return "b1"
    if t == 3:
        return f"i{x - (1 << 64) if x >> 63 else x}"
    if t in (V_SHR, V_LNG):
        tt = sh.byte(x + 8)
        if tt == V_SHR - 64:   # the GC header holds the variant, without the collectable bit (gcShrStr)
            n = sh.byte(x + 11)
        elif tt == V_LNG - 64:  # gcLngStr
            n = sh.rd(x + 16, 8)
        else:
            return "?"
        if n > 1 << 16:
            return "?"
        return "s" + bytes(sh.byte(x + 24 + i) for i in range(n)).hex()
    if t == V_LCF and x == SYM_PRINT:
        return "p"
    return "?"


def opname(word):
    o = word & 0x7f
    return OPNAMES[o] if o < len(OPNAMES) else "?"


def close_interval(head, ctx, ival, lc6, shapes, cex):
    """L-C6: classify the stores of one head-to-head interval; return the
    register indices whose slots were stored."""
    op = opname(head[2])
    d = lc6.setdefault(op, {"steps": 0})
    d["steps"] += 1
    base = ctx[0]
    slots, toks, other = [], [], []
    for a, w in ival:
        c = region(a, ctx)
        d[c] = d.get(c, 0) + 1
        if c == "slot":
            j, off = divmod(a - base, 16)
            slots.append(j)
            toks.append((j, off, w))
        elif c not in ("cframe",):
            other.append((c, hex(a), w))
    if toks:
        j0 = min(t[0] for t in toks)
        shape = " ".join(f"r{j - j0}+{off}/{w}" for j, off, w in toks)
        shapes.setdefault(op, {})
        shapes[op][shape] = shapes[op].get(shape, 0) + 1
    if other and op not in ("CALL", "VARARGPREP", "RETURN", "RETURN0", "RETURN1"):
        cex.append((head[0], head[1], op, other[:6]))
    return slots


def run(prog, work, max_steps):
    if prog.startswith("difftest/"):
        stem = prog.split("/", 1)[1]
        chunk_path = work / f"{stem}.luac"
        subprocess.run([str(LUAC), "-s", "-o", str(chunk_path),
                        str(ROOT / "c/tests/difftest" / f"{stem}.lua")], check=True)
    else:
        stem = prog
        chunk_path = ROOT / "c/tests" / f"{stem}.luac"
    lay = BW.layout()
    raw = BW.patched_elf(lay, chunk_path.read_bytes())
    seg = BW.pt_load(raw)
    assert BW.text_word(raw, seg, HEAD) == HEAD_WORD, "HEAD is not lw s4,0(s11)"
    elf = work / f"{stem}.elf"
    elf.write_bytes(raw)
    # the Proto, for the Lean side
    ptmp = work / f"{stem}.proto.gen.lean"
    subprocess.run([sys.executable, str(ROOT / "scripts/gen_proto.py"), str(chunk_path),
                    "--name", "lc4Proto", "-o", str(ptmp), "--luac", str(LUAC)],
                   check=True, capture_output=True)
    txt = ptmp.read_text()
    body = txt[txt.index("namespace Lua.Programs"):]
    (work / f"{stem}.proto.lean").write_text(body)

    sh = Shadow(raw)
    out = bytearray()
    heads = []
    ival = []                   # stores since the last head: (addr, width)
    ctx = None
    lc6 = {}                    # op -> {"steps": n, class: count}
    shapes = {}                 # op -> {shape: count}
    lc6_cex = []
    stats = dict(steps=0, load_checks=0, load_mismatch=0, nonbyte_out=0, first_load_mismatch=None,
                 base_ne_func=0)
    t0 = time.time()
    proc = subprocess.Popen([str(EMU), str(elf), "--trace-all", "--max-steps", str(max_steps)],
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
                            bufsize=1 << 20)
    last = None
    for line in proc.stderr:
        if not line.startswith("T\t"):
            if line.startswith("TRACE-FUEL-OUT"):
                stats["fuel_out"] = True
            continue
        f = line.rstrip("\n").split("\t")
        last = f
        pc = int(f[2], 16)
        tail = 35
        if len(f) > 35 and f[35] != "O":
            kind, w = f[35][0], int(f[35][1:])
            a = int(f[36], 16)
            if kind == "S":
                sh.store(a, w, int(f[38], 16))
                ival.append((a, w))
            else:
                pre = int(f[37], 16) & ((1 << (8 * w)) - 1)
                stats["load_checks"] += 1
                if sh.rd(a, w) != pre:
                    stats["load_mismatch"] += 1
                    if stats["first_load_mismatch"] is None:
                        stats["first_load_mismatch"] = (int(f[1]), hex(pc), hex(a), w, hex(pre),
                                                        hex(sh.rd(a, w)))
                    sh.store(a, w, pre)
            tail = 39
        if pc == HEAD:
            rg = lambda r: int(f[3 + r], 16)  # x1 is f[4]
            s11, s9, s7 = rg(27), rg(25), rg(23)
            func = sh.rd(s7, 8)
            cl = sh.rd(func, 8)
            proto = sh.rd(cl + 24, 8)
            code = sh.rd(proto + 64, 8)
            maxs = sh.byte(proto + 12)
            if s9 != func + 16:
                stats["base_ne_func"] += 1
            word = sh.rd(s11, 4)
            bpc, rem = divmod(s11 - code, 4)
            regs = [decode_val(sh, s9 + 16 * j) for j in range(maxs)]
            if heads:
                heads[-1][-1].extend(close_interval(heads[-1], ctx, ival, lc6, shapes, lc6_cex))
            ival = []
            Lp = rg(8)
            ctx = (s9, maxs, rg(2), s7, Lp, sh.rd(Lp + 48, 8), sh.rd(Lp + 40, 8))
            heads.append((int(f[1]), bpc if rem == 0 else -1, word, s7, func, len(out), regs, []))
        if len(f) >= tail + 4 and f[tail] == "O":
            ob, oa, by = int(f[tail + 1]), int(f[tail + 2]), int(f[tail + 3])
            if by < 256:
                out.append(by)
            elif oa != ob:
                stats["nonbyte_out"] += 1
    proc.wait()
    if heads:   # the last head's interval runs to the end (RETURN: poscall, exit)
        heads[-1][-1].extend(close_interval(heads[-1], ctx, ival, lc6, shapes, lc6_cex))
    stats["lc6"] = lc6
    stats["shapes"] = shapes
    stats["lc6_cex"] = lc6_cex[:10]
    stats["lc6_cex_n"] = len(lc6_cex)
    stats["wall_s"] = round(time.time() - t0, 1)
    stats["steps"] = int(last[1]) + 1 if last else 0
    stats["heads"] = len(heads)
    stats["out_bytes"] = len(out)
    stats["funcs"] = sorted({h[4] for h in heads})
    stats["cis"] = sorted({h[3] for h in heads})
    ops = {}
    for h in heads:
        op = OPNAMES[h[2] & 0x7f] if (h[2] & 0x7f) < len(OPNAMES) else "?"
        ops[op] = ops.get(op, 0) + 1
    stats["ops"] = ops
    with open(work / f"{stem}.heads", "w") as fo:
        fo.write(out.hex() + "\n")
        for (st, bpc, word, ci, func, olen, regs, slots) in heads:
            sl = ",".join(map(str, sorted(set(slots)))) or "-"
            fo.write(f"{st} {bpc} {word} {ci} {func} {olen} {sl} {' '.join(regs)}\n")
    elf.unlink()
    return stem, stats


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("progs", nargs="*", default=DEFAULT)
    ap.add_argument("--work", default=str(ROOT / "abstractions/checks/round3/lc4_work"))
    ap.add_argument("--max-steps", type=int, default=50_000_000)
    a = ap.parse_args()
    work = Path(a.work)
    work.mkdir(parents=True, exist_ok=True)
    for p in a.progs:
        stem, st = run(p, work, a.max_steps)
        fl = st.pop("funcs")
        cis = st.pop("cis")
        ops = st.pop("ops")
        lc6 = st.pop("lc6"); shapes = st.pop("shapes"); cex = st.pop("lc6_cex")
        print(f"{stem}: " + " ".join(f"{k}={v}" for k, v in st.items()))
        print(f"  func values={[hex(x) for x in fl]} ci values={[hex(x) for x in cis]}")
        print(f"  head opcodes: {dict(sorted(ops.items(), key=lambda kv: -kv[1]))}")
        for op in sorted(lc6):
            print(f"  LC6 {op}: {lc6[op]} shapes={shapes.get(op, {})}")
        for c in cex:
            print(f"  LC6-CEX {c}")
        sys.stdout.flush()


if __name__ == "__main__":
    main()

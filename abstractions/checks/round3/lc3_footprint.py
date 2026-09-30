#!/usr/bin/env python3
"""Round 3, law L-C3 (callee frame law), checked on Sail traces of the ELF.

L-C3 as proposed: every call an F1 arm makes to a helper writes only within
a small per-helper footprint (its own stack frame plus declared outputs) and
returns a value that is a pure function of its inputs.

Method.  Stream `--trace-all` (lc3_trace.rows) of each program.  Keep a
shadow memory (the PT_LOAD image, then every traced store; loads are
checked against it).  Every call made from luaV_execute's code (a `jal`
whose successor has ra = pc+4) opens an activation with a snapshot of the
caller's state: sp, L (s0), ci (s7), base (s9), L->stack/stack_last/top,
ci->next, g = L->l_G, and the chunk's maxstacksize.  The activation ends
when control reaches pc+4 with the same sp; if sp rises above the call's sp
first, it is a non-return (longjmp).  Every store while it is open,
including nested callees', is classified by region against the snapshot.

Purity checks (against a Python oracle, not against the model):
  * soft-int helpers: a0 at return vs a0 OP a1 at entry
    (__muldi3 wrap-mul, __divdi3/__moddi3 C truncating div/rem,
    __udivdi3/__umoddi3 unsigned), and every store below the call's sp;
  * luaV_equalobj(L, t1, t2): a0 vs raw equality of the two TValues read
    from the shadow memory (strings by bytes: long strings by content);
  * l_strcmp(ts1, ts2): sign of a0 vs byte-wise comparison of the contents.

usage: lc3_footprint.py CHUNK.luac ... [--json OUT]
"""
import sys, json, struct, collections, argparse
from pathlib import Path
import lc3_trace as T

M64 = (1 << 64) - 1


def s64(x):
    return x - (1 << 64) if x >> 63 else x


def tdiv(a, b):
    q = abs(a) // abs(b)
    return q if (a < 0) == (b < 0) else -q


ORACLE = {
    "__muldi3": lambda a, b: (a * b) & M64,
    "__divdi3": lambda a, b: None if b == 0 else tdiv(s64(a), s64(b)) & M64,
    "__moddi3": lambda a, b: None if b == 0 else (s64(a) - tdiv(s64(a), s64(b)) * s64(b)) & M64,
    "__udivdi3": lambda a, b: None if b == 0 else a // b,
    "__hidden___udivdi3": lambda a, b: None if b == 0 else a // b,
    "__umoddi3": lambda a, b: None if b == 0 else a % b,
}

L_FIELDS = {"stateStatusOff": "status", "stateNciOff": "nci", "stateTopOff": "top", "stateGOff": "l_G",
            "stateCiOff": "ci", "stateStackLastOff": "stack_last", "stateStackOff": "stack",
            "stateOpenupvalOff": "openupval", "stateTbclistOff": "tbclist", "stateErrorJmpOff": "errorJmp",
            "stateBaseCiOff": "base_ci", "stateErrfuncOff": "errfunc", "stateNCcallsOff": "nCcalls",
            "stateOldpcOff": "oldpc", "stateHookmaskOff": "hookmask"}
CI_FIELDS = {"ciFuncOff": "func", "ciTopOff": "top", "ciPreviousOff": "previous", "ciNextOff": "next",
             "ciSavedpcOff": "savedpc", "ciTrapOff": "trap", "ciNextraargsOff": "nextraargs",
             "ciNresultsOff": "nresults", "ciCallstatusOff": "callstatus"}
G_NAMES = {16: "totalbytes", 24: "GCdebt", 48: "strt.hash", 56: "strt.nuse", 96: "seed/gcstopem",
           112: "allgc"}
G_SIZE = 1400  # sizeof(global_State) upper bound (strcache ends at 552 + 53*2*8)


class Shadow:
    def __init__(self, elf):
        raw = Path(elf).read_bytes()
        import gen_lua_boot_witness as W
        vaddr, off, filesz = W.pt_load(raw)
        self.m = bytearray(0x10000000)  # [0x80000000, 0x90000000)
        self.base = 0x80000000
        self.m[vaddr - self.base: vaddr - self.base + filesz] = raw[off: off + filesz]

    def st(self, a, w, v):
        o = a - self.base
        if 0 <= o and o + w <= len(self.m):
            self.m[o:o + w] = (v & ((1 << (8 * w)) - 1)).to_bytes(w, "little")

    def rd(self, a, w):
        o = a - self.base
        if 0 <= o and o + w <= len(self.m):
            return int.from_bytes(self.m[o:o + w], "little")
        return 0

    def bytes(self, a, n):
        o = a - self.base
        return bytes(self.m[o:o + n])


class Classifier:
    def __init__(self):
        lay = T.lay()
        self.lay = lay
        self.lf = sorted((lay[k], v) for k, v in L_FIELDS.items())
        self.cf = sorted((lay[k], v) for k, v in CI_FIELDS.items())
        syms = {}
        import subprocess
        out = subprocess.run([T.lay and __import__("lib").BIN + "nm", "-S", "--size-sort",
                              str(T.REPO / "c/lua-riscv-htif.elf")], capture_output=True, text=True).stdout
        self.dsyms = []
        for line in out.splitlines():
            f = line.split()
            if len(f) == 4 and f[2] in "bBdDgGsS":
                self.dsyms.append((int(f[0], 16), int(f[1], 16), f[3]))
        self.dsyms.sort()

    @staticmethod
    def field(tab, off):
        name = "?"
        for o, n in tab:
            if o <= off:
                name = n
        return name

    def classify(self, a, snap):
        lay = self.lay
        sp0 = snap["sp"]
        if sp0 - 0x100000 <= a < sp0:
            return "own-frame"
        if sp0 <= a < lay["symStackTop"]:
            if sp0 <= a < sp0 + 176:
                return "caller-frame:luaV_execute"
            return "caller-frame:above"
        L = snap["L"]
        if L <= a < L + lay["stateSize"]:
            off = a - L
            if lay["stateBaseCiOff"] <= off < lay["stateBaseCiOff"] + lay["ciSize"]:
                return "L->base_ci." + self.field(self.cf, off - lay["stateBaseCiOff"])
            return "L->" + self.field(self.lf, off)
        ci = snap["ci"]
        if ci <= a < ci + lay["ciSize"]:
            return "ci->" + self.field(self.cf, a - ci)
        nx = snap["ci_next"]
        if nx and nx <= a < nx + lay["ciSize"]:
            return "ci->next->" + self.field(self.cf, a - nx)
        g = snap["g"]
        if g <= a < g + G_SIZE:
            if a - g >= T.lay()["gStrcacheOff"]:
                return "G->strcache"
            return "G->" + G_NAMES.get((a - g) & ~7, f"+{a - g}")
        st, sl = snap["stack"], snap["stack_last"]
        if st <= a < sl + 16 * lay["extraStack"]:
            r = (a - snap["base"]) // 16
            if r < 0:
                return "luastack:below-base"
            if r < snap["maxstack"]:
                return "luastack:regs>=A" if r >= snap["A"] else "luastack:regs<A"
            return "luastack:above-regs"
        if lay["symTohost"] <= a < lay["symTohost"] + 16:
            return "htif:tohost/fromhost"
        for s, n, name in self.dsyms:
            if s <= a < s + n:
                return "data:" + name
        if lay["symEnd"] <= a < lay["symHeapEnd"]:
            return "heap"
        return f"other:{a:#x}"


def tvalue(sh, t):
    tag = sh.rd(t + 8, 1)
    val = sh.rd(t, 8)
    return tag, val


def tstring(sh, p):
    lay = T.lay()
    n = sh.rd(p + lay["tstringShrlenOff"], 1)
    if n == 0xFF:  # 5.4.7: shrlen = 0xFF marks a long string
        n = sh.rd(p + lay["tstringLnglenOff"], 8)
    return sh.bytes(p + lay["tstringContentsOff"], n)


def oracle_equalobj(sh, t1, t2):
    lay = T.lay()
    (g1, v1), (g2, v2) = tvalue(sh, t1), tvalue(sh, t2)
    if (g1 & 0x3F) != (g2 & 0x3F):
        if (g1 & 0xF) != (g2 & 0xF) or (g1 & 0xF) != 3:
            return 0
        return None  # int/float mixed: not in F1
    if g1 == lay["vNil"] or g1 in (lay["vFalse"], lay["vTrue"]):
        return 1
    if g1 == lay["vNumInt"]:
        return int(v1 == v2)
    if g1 == lay["vShrStr"]:
        return int(v1 == v2)
    if g1 == lay["vLngStr"]:
        return int(v1 == v2 or tstring(sh, v1) == tstring(sh, v2))
    if g1 == lay["vLcf"]:
        return int(v1 == v2)
    return None


def mksnap(sh, pr, insA):
    lay = T.lay()
    L, ci = T.R(pr, T.S0), T.R(pr, T.S7)
    func = sh.rd(ci + lay["ciFuncOff"], 8)
    cl = sh.rd(func, 8)
    proto = sh.rd(cl + lay["lclosureProtoOff"], 8)
    return dict(sp=T.R(pr, T.SP), L=L, ci=ci, base=T.R(pr, T.S9),
                stack=sh.rd(L + lay["stateStackOff"], 8),
                stack_last=sh.rd(L + lay["stateStackLastOff"], 8),
                ci_next=sh.rd(ci + lay["ciNextOff"], 8),
                g=sh.rd(L + lay["stateGOff"], 8),
                maxstack=sh.rd(proto + lay["protoMaxstacksizeOff"], 1), A=insA)


def run(progs):
    c = T.ctx()
    by = c["by_addr"]
    F = c["funcs"]["luaV_execute"]
    lo, hi = F["start"], F["end"]
    starts = {f["start"]: n for n, f in c["funcs"].items() if f["insts"]}
    ops = c["ops"]
    lay = T.lay()
    C = Classifier()
    foot = collections.defaultdict(collections.Counter)      # callee -> region -> stores
    acts = collections.Counter()
    noret = collections.Counter()
    byop = collections.defaultdict(set)                      # callee -> ops calling it
    purity = collections.defaultdict(lambda: [0, 0, []])     # callee -> [ok, bad, examples]
    below_sp_only = collections.defaultdict(lambda: [0, 0])
    loadmis = 0
    armown = collections.defaultdict(collections.Counter)  # op -> region -> stores by luaV_execute itself
    examples = collections.defaultdict(list)
    for prog in progs:
        elf = T.elf_for(prog)
        sh = Shadow(elf)
        op = None
        insA = 0
        headsnap = None
        act = None
        prev = None
        started = False
        for step, pc, npc, regs, mem in T.rows(elf):
            if pc == lo:
                started = True
            # activation end
            if act is not None:
                sp = T.R(regs, T.SP)
                if pc == act["ret"] and sp == act["snap"]["sp"]:
                    finish(act, regs, sh, purity, below_sp_only)
                    act = None
                elif sp > act["snap"]["sp"]:
                    noret[act["callee"]] += 1
                    act = None
            if mem:
                k, w, a, pre, post = mem
                if k == "L":
                    if sh.rd(a, w) != pre & ((1 << (8 * w)) - 1) and a >= 0x80000000 and not (lay["symTohost"] <= a < lay["symTohost"] + 16):
                        loadmis += 1
                else:
                    if act is None and headsnap is not None and lo <= pc < hi:
                        r = C.classify(a, headsnap)
                        if r.startswith("luastack:regs"):
                            d = (a - headsnap["base"]) // 16 - headsnap["A"]
                            r = "luastack:R[A]" if d == 0 else f"luastack:R[A+{d}]" if d > 0 else "luastack:R[<A]"
                        armown[op][r.replace("caller-frame:luaV_execute", "exec-frame")] += 1
                    if act is not None:
                        r = C.classify(a, act["snap"])
                        foot[act["callee"]][r] += 1
                        if (r.startswith("caller-frame") or r in ("luastack:regs<A", "luastack:below-base")) and len(examples[act["callee"] + ":" + r]) < 4:
                            examples[act["callee"] + ":" + r].append(
                                f"pc={pc:#x}({T.func_at(pc)}) a={a:#x} sp0={act['snap']['sp']:#x} w={w}")
                        act["regions"].add(r)
                        if r != "own-frame":
                            act["outside_sp"] = True
                    sh.st(a, w, post)
            if not started:
                prev = (pc, regs)
                continue
            if pc == c["HEAD"] and mem and act is None:
                op = ops[mem[3] & 0x7F]
                insA = (mem[3] >> 7) & 0xFF
                headsnap = mksnap(sh, regs, insA)
            # activation start: previous step was a linking jump inside luaV_execute
            if act is None and prev is not None and lo <= prev[0] < hi:
                pi = by.get(prev[0])
                if pi is not None and pi.mn in ("jal", "jalr") and T.R(regs, T.RA) == prev[0] + 4 \
                        and pc != prev[0] + 4:
                    snap = mksnap(sh, prev[1], insA)
                    callee = starts.get(pc, f"?{pc:#x}")
                    act = dict(callee=callee, ret=prev[0] + 4, snap=snap, regions=set(),
                               args=[T.R(regs, x) for x in (10, 11, 12, 13)], outside_sp=False, op=op)
                    acts[callee] += 1
                    byop[callee].add(op)
            prev = (pc, regs)
        if act is not None:
            noret[act["callee"] + "(run ended)"] += 1
    return dict(foot=foot, acts=acts, noret=noret, byop=byop, purity=purity,
                below_sp_only=below_sp_only, loadmis=loadmis, examples=examples, armown=armown)


def finish(act, regs, sh, purity, below):
    cal = act["callee"]
    a0 = T.R(regs, T.A0)
    b = below[cal]
    b[0 if not act["outside_sp"] else 1] += 1
    if cal in ORACLE:
        want = ORACLE[cal](act["args"][0], act["args"][1])
        p = purity[cal]
        if want == a0:
            p[0] += 1
        else:
            p[1] += 1
            if len(p[2]) < 3:
                p[2].append((hex(act["args"][0]), hex(act["args"][1]), hex(a0), want))
    elif cal == "luaV_equalobj":
        want = oracle_equalobj(sh, act["args"][1], act["args"][2])
        p = purity[cal]
        if want == (a0 & 0xFFFFFFFF):
            p[0] += 1
        else:
            p[1] += 1
            if len(p[2]) < 3:
                p[2].append((tvalue(sh, act["args"][1]), tvalue(sh, act["args"][2]), a0, want))
    elif cal == "l_strcmp":
        s1, s2 = tstring(sh, act["args"][0]), tstring(sh, act["args"][1])
        want = (s1 > s2) - (s1 < s2)
        got = s64(a0)
        got = (got > 0) - (got < 0)
        p = purity[cal]
        if got == want:
            p[0] += 1
        else:
            p[1] += 1
            if len(p[2]) < 3:
                p[2].append((s1, s2, got, want))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("chunks", nargs="+")
    ap.add_argument("--json")
    a = ap.parse_args()
    r = run(a.chunks)
    print(f"load/shadow mismatches: {r['loadmis']}")
    print("== activations from luaV_execute arms: callee, count, ops, non-returns ==")
    for cal, n in r["acts"].most_common():
        nb = r["below_sp_only"][cal]
        print(f"{cal:28s} acts={n:5d} noret={r['noret'][cal]:3d} only-own-frame={nb[0]} writes-outside={nb[1]}"
              f"  ops={','.join(sorted(map(str, r['byop'][cal])))}")
        for reg, k in sorted(r["foot"][cal].items(), key=lambda x: -x[1]):
            if reg != "own-frame":
                print(f"      {reg:40s} {k}")
    for k, v in r["noret"].items():
        if "(run ended)" in k:
            print("open at end of run:", k, v)
    print("== stores made by luaV_execute's own arm code, per opcode (region: count) ==")
    for o in sorted(r["armown"], key=str):
        print(f"  {str(o):11s} " + ", ".join(f"{k}:{v}" for k, v in sorted(r["armown"][o].items(), key=lambda x: -x[1])))
    print("== caller-frame store examples ==")
    for k, v in r["examples"].items():
        print(f"  {k}: " + "; ".join(v))
    print("== purity vs oracle ==")
    for cal, (ok, bad, ex) in r["purity"].items():
        print(f"{cal:22s} ok={ok} bad={bad} {ex}")
    if a.json:
        json.dump({k: ({kk: (dict(vv) if isinstance(vv, collections.Counter) else
                             (sorted(map(str, vv)) if isinstance(vv, set) else vv))
                        for kk, vv in v.items()} if isinstance(v, dict) else v)
                   for k, v in r.items()}, open(a.json, "w"), indent=1, default=str)


if __name__ == "__main__":
    main()

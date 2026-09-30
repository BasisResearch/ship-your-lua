#!/usr/bin/env python3
"""F2: enumerate every exit of the ADD, EQI and FORLOOP arms (and, for
comparison, every F1 arithmetic arm): each root-to-leaf path of the arm's
canonical continuation DAG (canon.py, stopping at other opcodes' jump-table
targets so that a fall-through into e.g. MMBIN's code would show up as
`arm MMBIN`).

For each exit: kind (head = back to the dispatch head; arm X = into
another opcode's code; noreturn f = error call; ret; reentry), the next pc
the head will fetch as an offset from the arm's own pc (s11 at entry; +4 is
"pc+1": the next bytecode, +8 is "pc+2": skip one, `jump` = computed from
sJ/sBx), whether trap (s5) is reloaded, the effectful calls made on the
path, and the pure helpers (soft-float/libgcc) its values go through.

usage: f2_exits.py [OP ...]"""
import sys, collections
import canon

DEFAULT = ["ADD", "EQI", "FORLOOP"]
ARITH = ["ADD", "SUB", "MUL", "MOD", "IDIV", "ADDI", "ADDK", "SUBK", "MULK", "MODK", "IDIVK",
         "BAND", "BOR", "BXOR", "SHL", "SHR", "BANDK", "BORK", "BXORK", "SHRI", "SHLI", "UNM", "BNOT"]


def calls_in(T, h, seen, eff, pure):
    if not (isinstance(h, str) and h in T.t) or h in seen:
        if isinstance(h, tuple):
            for x in h:
                calls_in(T, x, seen, eff, pure)
        return
    seen.add(h)
    op, args = T.t[h]
    if op == "call":
        eff.add(args[0])
    elif op.startswith("call:"):
        pure.add(op[5:])
    for a in args:
        calls_in(T, a, seen, eff, pure)


def next_pc(T, v, s11):
    if v == s11:
        return "+0"
    op, args = T.t[v]
    if op == "add" and args[0] == s11 and T.cval(args[1]) is not None:
        return f"+{T.cval(args[1])}"
    return "jump"


def exits(ctx, T, op):
    W = canon.Walker(ctx, T, op, stop_arms=True)
    R, mem = W.head_state()
    root = W.walk(ctx["arm_target"][op], R, mem, [], [])
    s11 = T.mk("in", "s11")
    s5 = T.mk("in", "s5")
    out = []

    def go(h, conds):
        o, a = T.t[h]
        if o == "br":
            go(a[1], conds + [(a[0], True)])
            go(a[2], conds + [(a[0], False)])
            return
        if o == "loop":
            out.append(dict(kind="loop", nextpc="-", trap="-", eff=[], pure=[], nconds=len(conds), stores=0))
            return
        kind, outs, m = a
        outs = dict(outs)
        eff, pure = set(), set()
        seen = set()
        for c, _ in conds:
            calls_in(T, c, seen, eff, pure)
        calls_in(T, tuple(outs.values()), seen, eff, pure)
        calls_in(T, m, seen, eff, pure)
        k = " ".join(str(x) for x in kind)
        npc = next_pc(T, outs["s11"], s11) if "s11" in outs else "-"
        trap = "-" if "s5" not in outs else ("same" if outs["s5"] == s5 else "reloaded")
        nst = len(m[1]) if isinstance(m, tuple) else 0
        out.append(dict(kind=k, nextpc=npc, trap=trap, eff=sorted(eff), pure=sorted(pure), nconds=len(conds),
                        stores=nst))
    go(root, [])
    return out


def main(ops):
    ctx = canon.context()
    T = canon.Terms()
    for op in ops:
        ex = exits(ctx, T, op)
        S = canon.arm_insts(ctx, op)
        sites = sorted(a for a in S if any(t in (ctx["HEAD"], ctx["HEAD_TRAP"]) for t in ctx["succ"](a)))
        print(f"== {op}: {len(ex)} exit paths; {len(S)} static insts; static head-return sites: "
              + " ".join(f"{a:x}:{ctx['by_addr'][a].mn}" for a in sites))
        c = collections.Counter((e["kind"], e["nextpc"], e["trap"], e["stores"], ",".join(e["eff"]), ",".join(e["pure"])) for e in ex)
        for (k, npc, trap, st, eff, pure), n in sorted(c.items()):
            print(f"  x{n:<3d} {k:22s} next={npc:5s} trap={trap:8s} stores={st} calls=[{eff}] helpers=[{pure}]")
    # summary for the arithmetic family: normal (head, no effectful call) exits
    print("\n== arithmetic family: normal exits (head, no effectful call) by next pc")
    for op in ARITH:
        ex = exits(ctx, T, op)
        norm = collections.Counter(e["nextpc"] for e in ex if e["kind"] == "head" and not e["eff"])
        other = collections.Counter(e["kind"].split()[0] + (":" + ",".join(e["eff"]) if e["eff"] else "")
                                    for e in ex if not (e["kind"] == "head" and not e["eff"]))
        print(f"  {op:6s} normal={dict(norm)} other={dict(other)}")


if __name__ == "__main__":
    main(sys.argv[1:] or DEFAULT)

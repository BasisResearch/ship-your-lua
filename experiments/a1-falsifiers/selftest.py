#!/usr/bin/env python3
"""Self-test of canon.py's invariances on the real luaV_execute code: perturb
the decoded instruction stream in ways that preserve semantics, re-run
liveness and the canonicaliser, and check every F1 arm's exact class is
unchanged.
  flip:   every conditional branch has its sense negated and its taken and
          fall-through successors swapped (branch polarity + block layout);
  sched:  N random swaps of adjacent, independent, non-control instructions
          inside a block (no register/slot dependence, no store involved
          with another memory access);
  rename: s6<->s10 and t0<->t1 swapped everywhere in luaV_execute;
  all:    the three together."""
import random, copy, sys
import canon


def roots(ctx):
    T = canon.Terms()
    return {op: canon.canon_arm(ctx, T, op)[1] for op in canon.armlib.f1_ops()}


def flip(ctx):
    for pc, d in ctx["dec"].items():
        if d.kind == "br":
            pred, x, y, sense = d.op
            d.op = (pred, x, y, not sense)
            d.tgt, d.fall = (d.fall or pc + 4), d.tgt


def regs_of(d):
    u = set(d.rs)
    w = {d.rd} if d.rd else set()
    return u, w


def sched(ctx, n, seed):
    rnd = random.Random(seed)
    pcs = sorted(ctx["dec"])
    lead = ctx["jtargets"] | {ctx["HEAD"], ctx["HEAD_TRAP"]}
    ok = ("alu", "alui", "const", "load", "store", "ldslot", "stslot")
    done = 0
    for _ in range(n * 20):
        if done >= n:
            break
        k = rnd.randrange(len(pcs) - 1)
        p, q = pcs[k], pcs[k + 1]
        a, b = ctx["dec"][p], ctx["dec"][q]
        if q != p + 4 or q in lead or a.kind not in ok or b.kind not in ok:
            continue
        if a.fall or b.fall:
            continue
        ua, wa = regs_of(a)
        ub, wb = regs_of(b)
        if wa & (ub | wb) or wb & ua:
            continue
        mem = ("load", "store")
        if a.kind in mem and b.kind in mem and "store" in (a.kind, b.kind):
            continue
        ctx["dec"][p], ctx["dec"][q] = b, a
        done += 1
    return done


def rename(ctx, pairs):
    m = {}
    for x, y in pairs:
        m[x], m[y] = y, x
    for d in ctx["dec"].values():
        d.rs = [m.get(r, r) for r in d.rs]
        if d.rd:
            d.rd = m.get(d.rd, d.rd)
        if d.kind == "br":
            pred, x, y, s = d.op
            d.op = (pred, m.get(x, x), m.get(y, y), s)


def main():
    base_ctx = canon.context()
    base = roots(base_ctx)
    ok = True
    for name in ("flip", "sched", "rename", "all"):
        ctx = canon.context()
        info = ""
        if name in ("flip", "all"):
            flip(ctx)
        if name in ("rename", "all"):
            rename(ctx, [("s6", "s10"), ("t0", "t1")])
        canon.analyse(ctx)
        if name in ("sched", "all"):
            info = f" ({sched(ctx, 3000, 1)} swaps)"
            canon.analyse(ctx)
        r = roots(ctx)
        bad = [op for op in base if r[op] != base[op]]
        print(f"{name:7s}{info}: {len(base) - len(bad)}/{len(base)} arms unchanged" + (f"  CHANGED: {bad}" if bad else ""))
        ok &= not bad
    # negative control: bump the immediate of the first `alui` on each arm's
    # entry block; the class should change unless that value is dead
    ctx = canon.context()
    changed = 0
    for op in base:
        pc = ctx["arm_target"][op]
        while ctx["dec"][pc].kind not in ("alui", "br", "j", "call", "tail", "ret", "jr"):
            pc += 4
        d = ctx["dec"][pc]
        if d.kind != "alui":
            continue
        d.imm += 1
        T = canon.Terms()
        if canon.canon_arm(ctx, T, op)[1] != base[op]:
            changed += 1
        d.imm -= 1
    print(f"negative control: {changed} arms changed class when one entry-block immediate was bumped")
    return ok


if __name__ == "__main__":
    sys.exit(0 if main() else 1)

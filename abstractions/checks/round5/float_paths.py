#!/usr/bin/env python3
"""Round 5 census: the float paths of every `FloatArms` field, read off the ELF.

For each arm (jump-table target in `experiments/census/luaV_execute_arms.tsv`)
it enumerates the acyclic paths of `luaV_execute` from the target to the
fetch head (or to a non-returning call, or to a call of a metamethod /
error helper, which ends the path as an `exit`). A path is a *float path*
when it calls a soft-float or libm routine (`SOFT`). Per arm it prints:

* `fp`: float paths; `ip`: the other paths (integer, error, metamethod);
* `calls`: the most soft-float calls on one float path, and the routines;
* `vforks`: on float paths, branches after the first soft-float call (forks
  on a routine's answer, or on a value it fed): each doubles the cases a
  hand proof splits on unless the split follows the machine;
* `tags`: tag loads (`lbu …,8(…)`-shaped: offset ≡ 8 mod 16 off a slot
  pointer) on float paths, i.e. the register reads the float path checks;
* `shared`: the fraction of the float paths' instructions that also lie on
  some non-float path (law L5-share on the machine).

    python3 abstractions/checks/round5/float_paths.py > abstractions/checks/round5/float_paths.out
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
import draft_f1_arms as dfa   # noqa: E402

SOFT = re.compile(r"^(__\w+df[23]|__floatsidf|__floatdidf|__fixdfdi|floor|fmod|pow)$")
EXIT = re.compile(r"^(luaT_\w+|luaG_\w+|luaV_equalobj|l_strcmp|luaV_tointeger\w*|luaV_tonumber_\w*)$")
HEADS = {dfa.FETCH, dfa.FETCH - 4}

FIELDS = ["LOADF", "DIV", "DIVK", "POW", "POWK", "ADD", "SUB", "MUL", "MOD", "IDIV", "BAND",
          "BOR", "BXOR", "SHL", "SHR", "ADDK", "SUBK", "MULK", "MODK", "IDIVK", "BANDK", "BORK",
          "BXORK", "ADDI", "SHRI", "SHLI", "UNM", "BNOT", "EQ", "LT", "LE", "EQK", "EQI", "LTI",
          "LEI", "GTI", "GEI", "FORPREP", "FORLOOP"]
DONE = {"LOADF", "EQI", "LTI", "GEI", "ADDI", "FORLOOP"}
CAP = 20000


def callee(raw):
    m = re.search(r"<([^>+]+)>", raw)
    return m.group(1) if m else None


def paths(g, t):
    out, stack = [], [(t, [], frozenset())]
    while stack and len(out) < CAP:
        a, p, on = stack.pop()
        if a in HEADS:
            out.append((p, "head")); continue
        if a not in g or a in on:
            out.append((p, "cut")); continue
        raw, succ, _ = g[a]
        p2 = p + [a]
        if raw.split()[0] == "jal":
            c = callee(raw)
            if c and (c in dfa.NORET or EXIT.match(c)):
                out.append((p2, "exit:" + c)); continue
        if not succ:
            out.append((p2, "end")); continue
        for s in succ:
            stack.append((s, p2, on | {a}))
    return out


def main():
    g = dfa.cfg()
    arms = {}
    for line in open(dfa.ARMS_TSV):
        f = line.rstrip("\n").split("\t")
        if f[1].startswith("OP_"):
            arms[f[1][3:]] = int(f[2], 16)
    print("field\tdone\tfp\tip\tcalls\tvforks\ttags\tshared\troutines")
    for name in FIELDS:
        ps = paths(g, arms[name])
        fl, other = [], []
        for p, how in ps:
            cs = [callee(g[a][0]) for a in p if g[a][0].split()[0] == "jal"]
            cs = [c for c in cs if c]
            (fl if any(SOFT.match(c) for c in cs) else other).append((p, cs))
        maxc, routines, vforks, tags = 0, set(), set(), set()
        for p, cs in fl:
            soft = [c for c in cs if SOFT.match(c)]
            maxc = max(maxc, len(soft)); routines |= set(soft)
            seen_call = False
            for a in p:
                raw = g[a][0]
                mn = raw.split()[0]
                if mn == "jal" and SOFT.match(callee(raw) or ""):
                    seen_call = True
                if seen_call and re.match(r"b(eq|ne|lt|ge|ltu|geu|eqz|nez|lez|gez|ltz|gtz)$", mn):
                    vforks.add(a)
                if mn == "lbu" and re.search(r",(8|24|40|56|-8)\(", raw):
                    tags.add(a)
        fins = {a for p, _ in fl for a in p}
        oins = {a for p, _ in other for a in p}
        sh = len(fins & oins) / len(fins) if fins else 0.0
        print(f"{name}\t{'y' if name in DONE else ''}\t{len(fl)}\t{len(other)}\t{maxc}\t"
              f"{len(vforks)}\t{len(tags)}\t{sh:.2f}\t{','.join(sorted(routines))}")


if __name__ == "__main__":
    main()

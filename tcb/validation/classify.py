#!/usr/bin/env python3
"""Group tcbcheck rejections by (call name, observed return, allowed set),
with counts and one example each.

    python3 tcb/validation/classify.py VERDICTS [--scripts ALL.scripts]
"""
import collections
import re
import sys


def shape(call):
    w = call.split()
    name = w[0]
    if name == "open":
        return f"open {w[-1]}"
    return name


def main():
    rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1])]
    groups = collections.defaultdict(list)
    for r in rows:
        if len(r) > 1 and r[1] == "rejected":
            name, _, step, call, obs, allowed = r[:6]
            obs_k = re.sub(r"num \d+", "num N", obs) if call.startswith(("open", "opendir")) else obs
            key = (call.split()[0], obs_k, allowed)
            groups[key].append((name, step, call))
    for key, ex in sorted(groups.items(), key=lambda kv: -len(kv[1])):
        print(f"{len(ex):5d}  {key[0]:8s} observed {key[1]!r:28s} allowed {key[2]!r}")
        for n, s, c in ex[:2]:
            print(f"         e.g. [{n}] step {s}: {c}")


if __name__ == "__main__":
    main()

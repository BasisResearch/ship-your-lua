#!/usr/bin/env python3
"""The abstraction-discovery gate (~/.claude/skills/abstraction-discovery, "The gate").

For each cluster in abstractions/clusters.tsv, collect its hand-proved
cases, order them by the time they were introduced (git blame of the
case's first line, or the first commit adding `theorem <name>` to its file
if earlier: restating an existing case is not a new case; uncommitted =
now), and measure cost = non-blank,
non-comment proof lines. FAIL when a cluster has reached N cases
(default 8) and the mean cost of its last quarter is not at least a
third below the mean of its first quarter:

    mean(last quarter) > (2/3) * mean(first quarter)

The failure message is "run /abstraction-discovery". The only exemption
is automation: a cluster whose last-quarter mean is <= FLOOR lines (default
3: one-line `decide`/generated proofs) is already at its floor.
Re-baselining after an adopted abstraction: a `baseline <id> <commit>` line
in abstractions/ROUND-*.md restricts the cluster to cases introduced after
that commit.

    python3 abstractions/gate.py [--n 8] [--floor 3] [--report]
"""
import argparse, fnmatch, glob, os, re, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(ROOT)
sys.path.insert(0, os.path.join(ROOT, "abstractions"))
from census import decls  # noqa: E402

ap = argparse.ArgumentParser()
ap.add_argument("--n", type=int, default=8)
ap.add_argument("--floor", type=float, default=3.0)
ap.add_argument("--report", action="store_true")
a = ap.parse_args()

def blame_time(path, line):
    r = subprocess.run(["git", "blame", "--porcelain", "-L", f"{line},{line}", "--", path],
                       capture_output=True, text=True)
    m = re.search(r"^committer-time (\d+)", r.stdout, re.M)
    if not m or r.stdout.startswith("0000000000000000000000000000000000000000"):
        return int(time.time()), "uncommitted"
    return int(m.group(1)), r.stdout.split()[0][:8]

def intro_time(path, line, name):
    """When a case was introduced: the blame time of its first line, or, if
    earlier, the first commit that added `theorem <name>` to its file (a
    change to an existing case's statement does not make it a new case)."""
    t, c = blame_time(path, line)
    r = subprocess.run(["git", "log", "--format=%ct", "-S", f"theorem {name} ", "--", path],
                       capture_output=True, text=True)
    ts = [int(x) for x in r.stdout.split()]
    return (min(ts), c) if ts and min(ts) < t else (t, c)

def commit_time(c):
    r = subprocess.run(["git", "show", "-s", "--format=%ct", c], capture_output=True, text=True)
    return int(r.stdout.strip() or 0)

baselines = {}
baseline_commit = {}
for f in glob.glob("abstractions/ROUND-*.md"):
    for m in re.finditer(r"^baseline\s+(\S+)\s+([0-9a-f]{7,40})", open(f).read(), re.M):
        baselines[m.group(1)] = commit_time(m.group(2))
        baseline_commit[m.group(1)] = m.group(2)

def files(g):
    return sorted(p for p in glob.glob(g, recursive=True) if os.path.isfile(p))

failed = False
for row in open("abstractions/clusters.tsv"):
    if not row.strip() or row.startswith("#"): continue
    cid, kind, sel, desc = row.rstrip("\n").split("\t")[:4]
    cases = []
    if kind == "ledger":
        # hand cost of GENERATED cases, recorded per case in proof order
        # (selector = ledger TSV :: glob of the generated theorems it must cover)
        lp, gg = sel.split("::", 1)
        led = [l.split("\t") for l in open(lp) if l.strip() and not l.startswith("#")]
        for i, r in enumerate(led):
            cases.append((i, float(r[1]), f"{lp}:{r[0]}"))
        covered = {r[0] for r in led}
        gen = set()
        for p in files(gg):
            gen |= set(re.findall(r"theorem\s+(?:\S+\.)?sim_([A-Z0-9]+)\b", open(p, errors="ignore").read()))
        missing = sorted(gen - covered)
        if missing:
            print(f"{cid}: generated cases with no ledger row: {missing} (add them to {lp})")
            failed = True
    else:
        fg, rx = sel.split("::", 1); rx = re.compile(rx)
        for p in files(fg):
            src = open(p, errors="ignore").read()
            if "GENERATED" in src[:400]: continue
            lines = src.splitlines()
            for d in decls(p):
                if not rx.search(d["name"]): continue
                if kind == "theorems":
                    t, c = intro_time(p, d["line"], d["name"]); cases.append((t, d["lines"], f"{p}:{d['line']} {d['name']}"))
                else:
                    # locate each arm's first line inside the declaration
                    k = d["line"]
                    for name, n in d["cases"]:
                        while k < len(lines) and not re.match(r"^\s+(case\s+%s\b|\|\s*@?\.?%s\b)" % (re.escape(name), re.escape(name)), lines[k]):
                            k += 1
                        if k >= len(lines): break
                        t, c = blame_time(p, k + 1); cases.append((t, n, f"{p}:{k+1} {d['name']}/{name}"))
                        k += 1
    if cid in baselines:
        if kind == "ledger":
            # a ledger is in proof order: drop the rows it already had at the baseline commit
            led = sel.split("::")[0]
            old = subprocess.run(["git", "show", f"{baseline_commit[cid]}:{led}"], capture_output=True, text=True).stdout
            k = sum(1 for l in old.splitlines() if l.strip() and not l.startswith("#"))
            cases = cases[max(k, 0):]
        else:
            cases = [x for x in cases if x[0] > baselines[cid]]
    cases.sort()
    n = len(cases)
    status = "ok"
    if n >= a.n:
        q = max(1, n // 4)
        first = sum(c for _, c, _ in cases[:q]) / q
        last = sum(c for _, c, _ in cases[-q:]) / q
        if last > a.floor and last > (2 / 3) * first:
            status = f"FAIL (first-quarter mean {first:.1f} lines, last-quarter mean {last:.1f}: not a third cheaper)"
            failed = True
        else:
            status = f"ok (first {first:.1f}, last {last:.1f})"
    print(f"{cid}: {n} cases — {status}")
    if a.report:
        for t, c, where in cases:
            print(f"    {t if kind == 'ledger' else time.strftime('%Y-%m-%d %H:%M', time.localtime(t))}  {c:6.1f}  {where}")
if failed:
    print("abstraction gate: FAIL — run /abstraction-discovery")
    sys.exit(1)
print("abstraction gate: ok")

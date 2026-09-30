#!/usr/bin/env python3
"""Which ship-your-interpreter modules can be copied as language-agnostic,
and which import edges tie the rest of the generator/library layer to the
WHILE semantics and representation.

    python3 experiments/port/port_census.py [--syi ~/Documents/code/syi] [--copyset]

A module is *tainted* if its import closure reaches a WHILE root
(`Vsa.While.*`, `Vsa.MemRepr*`, `Vsa.RuntimeRepr`, `Vsa.ElfBytes`).
Import closures follow THIS repository's import lines for every module
present here (ported modules whose WHILE imports were cut, and the WHILE-free
restatements in `Vsa/Sim/Generic/`), and ship-your-interpreter's for the rest.

`--copyset` checks the closure of every module in this repository's `Vsa/`
and `VsaIris/`: it must contain no WHILE root, and every `Vsa`/`VsaIris`
module it imports must be present here. The default report lists, for the
generator/library targets not yet ported (segment bridges, frame
metatheorems, allocator ledger, newlib/dlmalloc Iris proofs), the modules
that import a WHILE root directly: the edges Phase A0 still has to cut.
"""
import argparse, os, re, sys
from collections import defaultdict

sys.setrecursionlimit(100000)
ap = argparse.ArgumentParser()
ap.add_argument("--syi", default=os.path.expanduser("~/Documents/code/syi"))
ap.add_argument("--copyset", action="store_true")
a = ap.parse_args()


def load(base):
    g = {}
    for d in ["Vsa", "VsaIris"]:
        for dp, _, fs in os.walk(os.path.join(base, d)):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    m = os.path.relpath(p, base)[:-5].replace("/", ".")
                    imps = []
                    for line in open(p, errors="ignore"):
                        mm = re.match(r"\s*(?:public\s+)?import\s+(.*)", line)
                        if mm:
                            imps += [x.replace("«", "").replace("»", "") for x in mm.group(1).split()]
                    g[m] = imps
    return g


mods = load(a.syi)
here = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
local = load(here)
eff = dict(mods)
eff.update(local)   # this repository's import lines win


def root(m):
    return m.startswith("Vsa.While.") or m in (
        "Vsa.MemRepr", "Vsa.MemReprReadArrays", "Vsa.MemReprReadChildren",
        "Vsa.MemReprReadFields", "Vsa.MemReprWithin", "Vsa.RuntimeRepr", "Vsa.ElfBytes")


def clo(ms):
    acc, st = set(), list(ms)
    while st:
        m = st.pop()
        if m in acc or m not in eff: continue
        acc.add(m); st += eff[m]
    return acc


if a.copyset:
    acc = clo(local)
    bad = sorted(m for m in acc if root(m))
    missing = sorted({i for m in acc for i in eff[m]
                      if (i.startswith("Vsa.") or i.startswith("VsaIris.")) and i not in local})
    print(f"modules here: {len(local)}; WHILE roots in their closure: {bad or 'none'}; "
          f"imported but absent: {missing or 'none'}")
    sys.exit(1 if bad or missing else 0)

targets = ["Vsa.Sim.SegToTripleFramed", "Vsa.Sim.BridgeSeg", "Vsa.Sim.BridgeSegFull",
           "Vsa.Sim.FrameMeta", "Vsa.Sim.DeriveCase", "Vsa.Sim.SeparationLogic",
           "Vsa.Sim.MemPresence", "Vsa.Sim.DlHeap", "Vsa.Sim.AllocLedger",
           "VsaIris.Vsa.SymRun", "VsaIris.Vsa.Fprintf.Run", "VsaIris.Vsa.Stdout.Code",
           "VsaIris.Vsa.ExitH.RunWritten"] + [m for m in mods if m.startswith("VsaIris.Vsa.AllocSteps")]
todo = [t for t in targets if t not in local]
acc = clo(todo)
cuts = defaultdict(list)
for m in acc:
    if not root(m):
        for i in eff[m]:
            if root(i): cuts[i].append(m)
print(f"ported targets: {len(targets) - len(todo)} of {len(targets)}")
print(f"not yet ported: {' '.join(todo)}")
print(f"closure of the targets not yet ported: {len(acc)} modules")
print(f"modules importing a WHILE root directly: {len({m for v in cuts.values() for m in v})}")
for r, v in sorted(cuts.items()):
    print(f"\n{r} <- {len(v)}")
    for m in sorted(v): print(f"  {m}")

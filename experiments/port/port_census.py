#!/usr/bin/env python3
"""Which ship-your-interpreter modules can be copied as language-agnostic,
and which import edges tie the rest of the generator/library layer to the
WHILE semantics and representation.

    python3 experiments/port/port_census.py [--syi ~/Documents/code/syi] [--copyset]

A module is *tainted* if its import closure reaches a WHILE root
(`Vsa.While.*`, `Vsa.MemRepr*`, `Vsa.RuntimeRepr`, `Vsa.ElfBytes`).
`--copyset` prints the closure of the roots copied into this repository
(it must be taint-free); the default report lists, for the tainted
generator/library targets (segment bridges, frame metatheorems, allocator
ledger, newlib/dlmalloc Iris proofs), the modules that import a WHILE root
directly: the edges Phase A0 cuts.
"""
import argparse, json, os, re, sys
from collections import defaultdict

sys.setrecursionlimit(100000)
ap = argparse.ArgumentParser()
ap.add_argument("--syi", default=os.path.expanduser("~/Documents/code/syi"))
ap.add_argument("--copyset", action="store_true")
a = ap.parse_args()

mods = {}
for d in ["Vsa", "VsaIris"]:
    for dp, _, fs in os.walk(os.path.join(a.syi, d)):
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                m = os.path.relpath(p, a.syi)[:-5].replace("/", ".")
                imps = []
                for line in open(p, errors="ignore"):
                    mm = re.match(r"\s*(?:public\s+)?import\s+(.*)", line)
                    if mm:
                        imps += [x.replace("«", "").replace("»", "") for x in mm.group(1).split()]
                mods[m] = imps

def root(m):
    return m.startswith("Vsa.While.") or m in (
        "Vsa.MemRepr", "Vsa.MemReprReadArrays", "Vsa.MemReprReadChildren",
        "Vsa.MemReprReadFields", "Vsa.MemReprWithin", "Vsa.RuntimeRepr", "Vsa.ElfBytes")

def clo(ms):
    acc, st = set(), list(ms)
    while st:
        m = st.pop()
        if m in acc or m not in mods: continue
        acc.add(m); st += mods[m]
    return acc

if a.copyset:
    here = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    copied = set()
    for d in ["Vsa", "VsaIris"]:
        for dp, _, fs in os.walk(os.path.join(here, d)):
            copied |= {os.path.relpath(os.path.join(dp, f), here)[:-5].replace("/", ".")
                       for f in fs if f.endswith(".lean")}
    bad = [m for m in clo(copied) if root(m)]
    print(f"copied modules: {len(copied)}; WHILE roots in their closure: {bad or 'none'}")
    sys.exit(1 if bad else 0)

targets = ["Vsa.Sim.SegToTripleFramed", "Vsa.Sim.BridgeSeg", "Vsa.Sim.BridgeSegFull",
           "Vsa.Sim.FrameMeta", "Vsa.Sim.DeriveCase", "Vsa.Sim.SeparationLogic",
           "Vsa.Sim.MemPresence", "Vsa.Sim.DlHeap", "Vsa.Sim.AllocLedger",
           "VsaIris.Vsa.SymRun", "VsaIris.Vsa.Fprintf.Run", "VsaIris.Vsa.Stdout.Code",
           "VsaIris.Vsa.ExitH.RunWritten"] + [m for m in mods if m.startswith("VsaIris.Vsa.AllocSteps")]
acc = clo(targets)
cuts = defaultdict(list)
for m in acc:
    if not root(m):
        for i in mods[m]:
            if root(i): cuts[i].append(m)
print(f"closure of the generator/library targets: {len(acc)} modules")
print(f"modules importing a WHILE root directly: {len({m for v in cuts.values() for m in v})}")
for r, v in sorted(cuts.items()):
    print(f"\n{r} <- {len(v)}")
    for m in sorted(v): print(f"  {m}")

#!/usr/bin/env python3
"""Term-level census over a BUILT ship-your-interpreter checkout.

    python3 experiments/port/term/term_census.py --syi DIR closure OUT MOD... [c:CONST...]
    python3 experiments/port/term/term_census.py --syi DIR ranges  OUT MOD...
    python3 experiments/port/term/term_census.py --syi DIR meta    OUT MOD...
    python3 experiments/port/term/term_census.py --syi DIR revdeps OUT TARGETS_FILE MOD...

`closure` seeds every constant of the given modules (plus `c:` constants),
follows the constants their types and values (theorem bodies included) use,
descending only into WHILE-tainted modules, and writes `module<TAB>const<TAB>via`
for every reached constant of a tainted module or a WHILE root. This is how
PHASES A0.2 decided what each ported module needs: an empty WHILE-root set
means the import edges to the WHILE layer carry no WHILE constant, and the
reached declarations of tainted modules are what `Vsa/Sim/Generic/*` (or a
pruned copy) must supply. `ranges` prints declaration line ranges, `meta` the
metaprogram constants (tactics, macros, elaborators), `revdeps` every constant
depending on one of the targets.

DIR must be built at the commit the sources are copied from (`46b1eb8e`);
stale `.olean`s give stale answers. The riscv packages are taken from this
repository's `riscv-lean/`.
"""
import argparse, os, re, subprocess, sys

here = os.path.dirname(os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
tools = os.path.dirname(os.path.abspath(__file__))
ap = argparse.ArgumentParser()
ap.add_argument("--syi", required=True)
ap.add_argument("tool", choices=["closure", "ranges", "meta", "revdeps"])
ap.add_argument("rest", nargs="+")
a = ap.parse_args()


def load(base):
    g = {}
    for d in ["Vsa", "VsaIris"]:
        for dp, _, fs in os.walk(os.path.join(base, d)):
            for f in fs:
                if f.endswith(".lean"):
                    p = os.path.join(dp, f)
                    m = os.path.relpath(p, base)[:-5].replace("/", ".")
                    g[m] = [x for l in open(p, errors="ignore")
                            for mm in [re.match(r"\s*import\s+(.*)", l)] if mm for x in mm.group(1).split()]
    return g


def root(m):
    return m.startswith("Vsa.While.") or m in (
        "Vsa.MemRepr", "Vsa.MemReprReadArrays", "Vsa.MemReprReadChildren",
        "Vsa.MemReprReadFields", "Vsa.MemReprWithin", "Vsa.RuntimeRepr", "Vsa.ElfBytes")


lib = lambda p: os.path.join(p, ".lake", "build", "lib", "lean")
paths = [lib(a.syi)] + [lib(os.path.join(a.syi, ".lake", "packages", p)) for p in ["Cli", "Qq", "batteries", "ELFSage"]]
paths += [lib(os.path.join(a.syi, ".lake", "packages", "iris", "Iris"))]
paths += [lib(os.path.join(here, "riscv-lean", d)) for d in ["Lean_RV64D_executable", "lean-sail", "lean_emulator"]]
env = dict(os.environ, LEAN_PATH=":".join(paths))
src = {"closure": "Closure.lean", "ranges": "Ranges.lean", "meta": "Meta.lean", "revdeps": "RevDeps.lean"}[a.tool]
args = list(a.rest)
if a.tool == "closure":
    mods = load(a.syi)
    memo = {}
    def taint(m):
        if m in memo: return memo[m]
        memo[m] = False
        memo[m] = root(m) or any(taint(i) for i in mods.get(m, []) if i in mods)
        return memo[m]
    tl = os.path.join(os.path.dirname(os.path.abspath(args[0])), "tainted_modules.txt")
    open(tl, "w").write(" ".join(sorted(m for m in mods if taint(m) and not root(m))))
    args = [args[0], tl] + args[1:]
sys.exit(subprocess.run(["lean", "--run", os.path.join(tools, src)] + args, env=env, cwd=here).returncode)

#!/usr/bin/env python3
"""Dynamic PC coverage from traces/*.pcs.tsv (pc count before_exec after_exec)."""
import sys, json, glob, os, bisect, collections
sys.path.insert(0, os.path.dirname(__file__))
from lib import *
from origin import origins, family
funcs, by_addr = parse_disasm("lua_disasm.txt")
orig = origins(LUA_ELF, funcs)
reach = json.load(open("lua_reach.json"))
static = set(reach["reachable"]); direct_static = None
def load(p):
    d = {}
    for line in open(p):
        pc, c, b, a = line.split()
        d[int(pc, 16)] = (int(c), int(b), int(a))
    return d
runs = {os.path.basename(p)[:-8]: load(p) for p in sorted(glob.glob("traces/*.pcs.tsv"))}
def summarize(pcs):
    fs = collections.Counter(by_addr[p].func for p in pcs if p in by_addr)
    notin = [p for p in pcs if p not in by_addr]
    return {"pcs": len(pcs), "funcs": len(fs), "pcs_outside_text": len(notin),
            "insts_of_touched_funcs": sum(len(funcs[f]["insts"]) for f in fs),
            "unique_words": len({by_addr[p].word for p in pcs if p in by_addr}),
            "by_family": dict(collections.Counter(family(orig[f]) for f in fs)),
            "pcs_by_family": dict(collections.Counter(family(orig[by_addr[p].func]) for p in pcs if p in by_addr))}, set(fs)
out = {}
main = runs["lua-riscv-htif"]
allp = set(main); before = {p for p,(c,b,a) in main.items() if b}; after = {p for p,(c,b,a) in main.items() if a}
for name, S in [("while_all", allp), ("while_before_exec", before), ("while_after_exec", after),
                ("while_after_only", after - before), ("while_before_only", before - after)]:
    out[name], fs = summarize(S)
    if name == "while_after_exec": after_funcs = fs
    if name == "while_all": main_funcs = fs
dt = [k for k in runs if k != "lua-riscv-htif"]
U = set().union(*(set(runs[k]) for k in dt)); UA = set().union(*({p for p,(c,b,a) in runs[k].items() if a} for k in dt))
UB = set().union(*({p for p,(c,b,a) in runs[k].items() if b} for k in dt))
out["difftest_union_all"], ufuncs = summarize(U)
out["difftest_union_after_exec"], uafuncs = summarize(UA)
out["difftest_union_before_exec"], _ = summarize(UB)
out["everything_union"], evfuncs = summarize(U | allp)
out["everything_union_after_exec"], evafuncs = summarize(UA | after)
out["per_run"] = {k: {"pcs": len(v), "after_exec_pcs": sum(1 for x in v.values() if x[2]),
                      "funcs": len({by_addr[p].func for p in v if p in by_addr})} for k, v in runs.items()}
out["dynamic_not_static"] = sorted(evfuncs - static)
out["while_after_exec_funcs"] = sorted(after_funcs, key=lambda f: funcs[f]["start"])
out["union_after_exec_funcs"] = sorted(evafuncs, key=lambda f: funcs[f]["start"])
out["union_all_funcs"] = sorted(evfuncs, key=lambda f: funcs[f]["start"])
out["while_all_funcs"] = sorted(main_funcs, key=lambda f: funcs[f]["start"])
json.dump(out, open("dynamic.json", "w"), indent=1)
for k, v in out.items():
    if isinstance(v, dict) and "pcs" in v: print(k, {x: v[x] for x in ("pcs","funcs","insts_of_touched_funcs","unique_words","by_family","pcs_outside_text")})
print("dynamic_not_static", out["dynamic_not_static"])
print("while after-exec funcs:", " ".join(out["while_after_exec_funcs"]))

#!/usr/bin/env python3
"""Derived tables: per_origin.{tsv,md}, function_match.tsv, arms_table.md, numbers.json
(the headline numbers quoted in CENSUS.md, used for diffing reruns)."""
import json, collections, sys, os, glob
sys.path.insert(0, os.path.dirname(__file__))
from lib import *
from origin import origins, family

f, b = parse_disasm("lua_disasm.txt"); o = origins(LUA_ELF, f)
r = json.load(open("lua_reach.json")); d = json.load(open("dynamic.json"))
tm = json.load(open("template_match.json")); arms = json.load(open("luaV_execute_arms.json"))
cons = json.load(open("constructs.json"))


def pcs(p, col):
    S = set()
    for l in open(p):
        x = l.split()
        if col is None or int(x[col]): S.add(int(x[0], 16))
    return S


main = "traces/lua-riscv-htif.pcs.tsv"
W, WB, WA = pcs(main, None), pcs(main, 2), pcs(main, 3)
U, UA = set(), set()
for p in glob.glob("traces/*.pcs.tsv"):
    U |= pcs(p, None); UA |= pcs(p, 3)

# per-origin
def key(n):
    x = o[n]; fam = family(x)
    return x if fam in ("lua", "boot") else fam
rows = collections.defaultdict(collections.Counter)
S = set(r["reachable"])
for n, F in f.items():
    k = key(n); rows[k]["funcs"] += 1; rows[k]["insts"] += len(F["insts"])
    if n in S: rows[k]["static_f"] += 1; rows[k]["static_i"] += len(F["insts"])
    for nm, X in (("wB", WB), ("wA", WA), ("U", U), ("UA", UA)):
        t = sum(1 for i in F["insts"] if i.addr in X)
        if t: rows[k][nm + "_f"] += 1; rows[k][nm + "_pcs"] += t
cols = ["funcs", "insts", "static_f", "static_i", "wB_f", "wB_pcs", "wA_f", "wA_pcs", "U_f", "U_pcs", "UA_f", "UA_pcs"]
tot = collections.Counter()
with open("per_origin.tsv", "w") as t, open("per_origin.md", "w") as m:
    t.write("origin\t" + "\t".join(cols) + "\n"); m.write("| origin | " + " | ".join(cols) + " |\n|" + "---|" * (len(cols) + 1) + "\n")
    for k in sorted(rows, key=lambda k: -rows[k]["insts"]):
        t.write(k + "\t" + "\t".join(str(rows[k][c]) for c in cols) + "\n")
        m.write(f"| {k} | " + " | ".join(str(rows[k][c]) for c in cols) + " |\n"); tot += rows[k]
    t.write("TOTAL\t" + "\t".join(str(tot[c]) for c in cols) + "\n")
    m.write("| TOTAL | " + " | ".join(str(tot[c]) for c in cols) + " |\n")

# function_match.tsv
fm = tm["function_match"]
WD, WAD, UD = set(d["while_all_funcs"]), set(d["while_after_exec_funcs"]), set(d["union_all_funcs"])
with open("function_match.tsv", "w") as t:
    t.write("func\torigin\tinsts\tcategory\twhile_counterpart\tin_while_proof_scope\tstatic_reach\tdyn_while\tdyn_while_after_exec\tdyn_union\n")
    for n, v in fm.items():
        t.write(f"{n}\t{v['origin']}\t{v['n']}\t{v['cat']}\t{v['while'] or ''}\t{int(v['in_while_proof_scope'])}\t{int(n in S)}\t{int(n in WD)}\t{int(n in WAD)}\t{int(n in UD)}\n")

# arms table
F1 = set(arms["summary"]["F1_ops"])
with open("arms_table.md", "w") as t:
    t.write("| # | opcode | F1 | target | reach | excl | linear | br | tgt-hits while | tgt-hits union | callees (jal; xN = N sites) |\n")
    t.write("|---|---|---|---|---|---|---|---|---|---|---|\n")
    for a in arms["arms"]:
        c = ", ".join(k + (f" x{v}" if v > 1 else "") for k, v in a["callees"].items())
        t.write(f"| {a['index']} | {a['op'][3:]} | {'F1' if a['op'] in F1 else ''} | {a['target'][2:]} | {a['reach_insts']} | {a['exclusive_insts']} | {a['linear_from_target']} | {a['branches']} | {a['dispatch_count_while']} | {a['dispatch_count_union']} | {c} |\n")

# headline numbers
cen = json.load(open("lua_census.json"))
meta = {}
for p in glob.glob("traces/*.meta"):
    x = open(p).read().split()
    meta[os.path.basename(p)[:-5]] = {"steps": int(x[1]), "luaV_execute_entry_step": int(x[5])}
REUSE = ("identical_words", "identical_mod_reloc", "identical_body_other_name")
num = {
    "whole": {"funcs": len(f), "insts": sum(len(F["insts"]) for F in f.values()),
              "unique_words": len(cen["unique_words"]),
              "unique_mnemonics": len({v["mnemonic"] for v in cen["unique_words"].values()})},
    "luaV_execute_start": hex(f["luaV_execute"]["start"]),
    "static": {k: r[k] for k in ("direct_only", "address_flow", "all_address_taken_upper")},
    "jumptables": {"count": len(r["jumptables"]), "entries": sum(t["entries"] for t in r["jumptables"]),
                   "indirect_sites": collections.Counter(s["kind"] for s in r["indirect_sites"])},
    "dynamic": {k: {x: d[k][x] for x in ("pcs", "funcs", "unique_words")} for k in d if isinstance(d[k], dict) and "pcs" in d[k] and "funcs" in d[k] and k != "per_run"},
    "dynamic_not_static": d["dynamic_not_static"],
    "traces": meta,
    "template": tm["summary"], "sites": {k: {x: v[x] for x in ("pct", "blocks_pct")} for k, v in tm["sites"].items()},
    "decode_index": tm["decode_index"], "gen_fn": tm["gen_fn"],
    "arms": {"summary": {k: v for k, v in arms["summary"].items() if k not in ("F1_ops",)},
             "per_arm": {a["op"]: [a["reach_insts"], a["exclusive_insts"], a["linear_from_target"], a["dispatch_count_while"], a["dispatch_count_union"]] for a in arms["arms"]}},
    "constructs": {k: v["counts"] for k, v in cons["lua"].items()},
    "constructs_while": {k: v["counts"] for k, v in cons["while"].items()},
}
json.dump(num, open("numbers.json", "w"), indent=1, sort_keys=True)
print("wrote per_origin.{tsv,md} function_match.tsv arms_table.md numbers.json")

#!/usr/bin/env python3
"""luaV_execute opcode arms: map the switch jump table to OP_ names and
measure each arm as the set of luaV_execute instructions reachable from its
jump-table target over the intra-function CFG, stopping at the shared fetch
head (vmfetch, luaV_execute+0x7c), `ret`, tail jumps out of the function,
and calls to noreturn error functions."""
import sys, os, re, json, collections, glob
sys.path.insert(0, os.path.dirname(__file__))
from lib import *

funcs, by_addr = parse_disasm("lua_disasm.txt")
reach = json.load(open("lua_reach.json"))
F = funcs["luaV_execute"]
I = F["insts"]
lo, hi = F["start"], F["end"]
jt = [t for t in reach["jumptables"] if t["func"] == "luaV_execute"][0]
targets = [int(x, 16) for x in jt["targets"]]
src = open(LUA_SRC + "/lopcodes.h").read()
enum = src[src.index("typedef enum {\n/*----"):src.index("} OpCode;")]
ops = re.findall(r"^(OP_[A-Z0-9]+)", enum, re.M)
assert len(ops) == 83, len(ops)

# fetch head (vmfetch): the most frequent in-function jump target
_tc = collections.Counter(i.target() for i in I if i.target() and lo <= i.target() < hi)
FETCH = _tc.most_common(1)[0][0]    # bnez s5,<trap>; lw s4,0(s11); ... jr a5
DISPATCH_JR = int(jt["jr"], 16)
# default (index > bound) target: the bltu before the dispatch
default = None
for i in I:
    if i.addr < DISPATCH_JR and i.mn == "bltu" and i.addr > FETCH:
        default = i.target()
NORET = {"luaD_throw", "luaG_callerror", "luaG_concaterror", "luaG_errormsg",
         "luaG_forerror", "luaG_opinterror", "luaG_ordererror", "luaG_runerror",
         "luaG_tointerror", "luaG_typeerror", "luaM_toobig"}
starts = {f["start"]: n for n, f in funcs.items()}


def succ(i):
    t = i.target()
    nxt = i.addr + 4
    if i.mn == "ret" or (i.mn == "jr"):
        return []
    if i.mn == "j":
        return [t] if lo <= t < hi else []
    if i.mn == "jal":
        if starts.get(t) in NORET:
            return []
        return [nxt]
    if i.mn in BRANCHES:
        return [t, nxt] if lo <= t < hi else [nxt]
    return [nxt]


def arm(t):
    seen = set()
    work = [t]
    while work:
        a = work.pop()
        if a in seen or a == FETCH or not (lo <= a < hi):
            continue
        seen.add(a)
        work.extend(succ(by_addr[a]))
    return seen


pcs_while = {}
for line in open("traces/lua-riscv-htif.pcs.tsv"):
    p, c, b, a = line.split()
    pcs_while[int(p, 16)] = int(c)
pcs_union = collections.Counter()
for p in glob.glob("traces/*.pcs.tsv"):
    for line in open(p):
        x = line.split()
        pcs_union[int(x[0], 16)] += int(x[1])

arms = {}
for k, name in enumerate(ops):
    t = targets[k] if k < len(targets) else default
    arms[name] = {"index": k, "target": t, "set": arm(t)}
count = collections.Counter()
for a in arms.values():
    for x in a["set"]:
        count[x] += 1
rows = []
for name, a in arms.items():
    S = a["set"]
    callees = collections.Counter()
    ind = 0
    for x in S:
        i = by_addr[x]
        if i.mn == "jal":
            callees[starts.get(i.target(), hex(i.target()))] += 1
        if i.mn == "j" and not (lo <= i.target() < hi):
            callees["tail:" + starts.get(i.target(), hex(i.target()))] += 1
        if i.mn == "jalr":
            ind += 1
    # linear arm: from target to the first unconditional j/ret (fast path, straight)
    fast = 0
    a0 = a["target"]
    while True:
        i = by_addr[a0]
        fast += 1
        if i.mn in ("j", "ret", "jr") or (i.mn == "jal" and starts.get(i.target()) in NORET):
            break
        a0 += 4
    rows.append({
        "op": name, "index": a["index"], "target": hex(a["target"]),
        "reach_insts": len(S), "exclusive_insts": sum(1 for x in S if count[x] == 1),
        "linear_from_target": fast,
        "branches": sum(1 for x in S if by_addr[x].mn in BRANCHES),
        "callees": dict(sorted(callees.items())), "jalr": ind,
        "dispatch_count_while": pcs_while.get(a["target"], 0),
        "dispatch_count_union": pcs_union.get(a["target"], 0),
        "touched_insts_while": sum(1 for x in S if x in pcs_while),
        "touched_insts_union": sum(1 for x in S if x in pcs_union),
    })

F1 = ["OP_MOVE", "OP_LOADI", "OP_LOADF", "OP_LOADK", "OP_ADD", "OP_ADDI", "OP_ADDK",
      "OP_SUB", "OP_SUBK", "OP_MUL", "OP_MULK", "OP_MOD", "OP_MODK", "OP_IDIV", "OP_IDIVK",
      "OP_EQ", "OP_LT", "OP_LE", "OP_EQK", "OP_EQI", "OP_LTI", "OP_LEI", "OP_GTI", "OP_GEI",
      "OP_JMP", "OP_TEST", "OP_FORPREP", "OP_FORLOOP", "OP_RETURN0", "OP_RETURN1",
      "OP_RETURN", "OP_CALL", "OP_GETTABUP"]
f1set = set().union(*(arms[o]["set"] for o in F1))
allset = set().union(*(a["set"] for a in arms.values()))
fetch_block = [i for i in I if FETCH <= i.addr <= DISPATCH_JR]
summary = {
    "luaV_execute": {"start": hex(lo), "end": hex(hi), "insts": len(I), "bytes": hi - lo},
    "jump_table": {"addr": jt["table"], "entries": len(targets), "entry_bytes": 4,
                   "encoding": "int32 offset relative to table base (target = base + sext(entry))",
                   "bound_check": "bltu 81 < (i & 0x7f) -> default", "default_target": hex(default),
                   "distinct_targets": len(set(targets)), "dispatch_jr": hex(DISPATCH_JR),
                   "fetch_head": hex(FETCH), "fetch_dispatch_insts": len(fetch_block),
                   "jr_sites_in_luaV_execute": sum(1 for i in I if i.mn == "jr"),
                   "note": "OP_EXTRAARG (82) is out of table range -> default target"},
    "arms_union_insts": len(allset),
    "insts_not_in_any_arm": len(I) - len(allset),
    "F1_ops": F1, "F1_sum_reach": sum(arms[o]["set"].__len__() for o in F1),
    "F1_union_reach": len(f1set),
    "F1_sum_exclusive": sum(r["exclusive_insts"] for r in rows if r["op"] in F1),
    "F1_sum_linear": sum(r["linear_from_target"] for r in rows if r["op"] in F1),
    "ops_dispatched_while": [r["op"] for r in rows if r["dispatch_count_while"]],
    "ops_dispatched_union": [r["op"] for r in rows if r["dispatch_count_union"]],
    "total_dispatches_while": pcs_while.get(DISPATCH_JR, 0),
}
json.dump({"summary": summary, "arms": rows}, open("luaV_execute_arms.json", "w"), indent=1)
with open("luaV_execute_arms.tsv", "w") as f:
    f.write("idx\top\ttarget\treach\texclusive\tlinear\tbranches\tdisp_while\tdisp_union\tcallees\n")
    for r in rows:
        f.write(f"{r['index']}\t{r['op']}\t{r['target']}\t{r['reach_insts']}\t{r['exclusive_insts']}\t"
                f"{r['linear_from_target']}\t{r['branches']}\t{r['dispatch_count_while']}\t{r['dispatch_count_union']}\t"
                + ",".join(f"{k}" + (f"x{v}" if v > 1 else "") for k, v in r["callees"].items()) + "\n")
print(json.dumps(summary, indent=1))

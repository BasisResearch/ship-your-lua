#!/usr/bin/env python3
"""Round 3, step 1 (b): how many DISTINCT callee functions A1 needs contracts for.

Static part (objdump of c/lua-riscv-htif.elf, no execution):
  * each F1 arm (Lua/Fragment.lean's F1 opcodes) is walked inside luaV_execute
    from its jump-table target to the dispatch head (stopping at other arms'
    targets); its `jal` targets are its direct callees;
  * the call graph: `jal` = call, `j` into another function's start = tail
    call, `jalr` with a link = indirect call.  Indirect calls are resolved by
    the table INDIRECT (each entry checked dynamically below) or listed as
    unresolved;
  * groups: (a) arms' normal callees, (b) error paths, (c) CALL/RETURN and
    the exit chain after luaV_execute returns, (d) stack growth / CI
    allocation; transitive closures with and without the boundary cuts
    CUT (GC step, luaV_execute re-entry through metamethods).

Dynamic part (--dyn): every function entered (pc = its first instruction)
from luaV_execute's first entry to the end of the run, attributed to the
opcode whose arm was executing (last dispatch-head fetch), or to `post`
after the outermost luaV_execute returned.

usage: callee_census.py [--dyn] [--json OUT]
"""
import sys, json, collections, argparse
from pathlib import Path
import lc3_trace as T

NORET = {"luaD_throw", "luaG_callerror", "luaG_concaterror", "luaG_errormsg",
         "luaG_forerror", "luaG_opinterror", "luaG_ordererror", "luaG_runerror",
         "luaG_tointerror", "luaG_typeerror", "luaM_toobig", "abort", "exit", "_exit", "longjmp"}

# indirect call sites resolved by hand (the dynamic trace checks them)
INDIRECT = {
    "luaD_precall": ["luaB_print"],          # precallC: the C function (F1: print only)
    "luaM_realloc_": ["l_alloc"],            # g->frealloc
    "luaM_malloc_": ["l_alloc"],
    "luaM_shrinkvector_": ["l_alloc"],
    "luaM_growaux_": ["l_alloc"],
    "luaM_free_": ["l_alloc"],
    "__sfvwrite_r": ["__swrite"],            # fp->_write
    "_fflush_r": ["__swrite"],
    "__sflush_r": ["__swrite", "__sseek"],
}

CUT = {"luaC_step", "luaC_fullgc", "luaV_execute", "luaD_call", "luaD_callnoyield",
       "luaT_callTMres", "luaT_callTM"}

POST_FRAMES = ["ccall", "luaD_callnoyield", "f_call", "luaD_rawrunprotected", "luaD_pcall",
               "lua_pcallk", "main"]


def graph(c):
    fs = c["funcs"]
    starts = {f["start"]: n for n, f in fs.items() if f["insts"]}
    G, IND = {}, {}
    for n, f in fs.items():
        out, ind = set(), []
        for i in f["insts"]:
            t = i.target()
            if i.mn == "jal" and t in starts:
                out.add(starts[t])
            elif i.mn == "j" and t in starts and starts[t] != n:
                out.add(starts[t])
            elif i.mn == "jalr":
                ind.append(i.addr)
        out |= set(INDIRECT.get(n, []))
        G[n] = out
        IND[n] = ind
    return G, IND


def arm_callees(c, op):
    by = c["by_addr"]
    F = c["F"]
    lo, hi = F["start"], F["end"]
    stop = {c["HEAD"], c["HEAD_TRAP"], c["JR"]} | {t for o, t in c["arm_target"].items() if o != op}
    starts = {f["start"]: n for n, f in c["funcs"].items() if f["insts"]}
    seen, todo, calls = set(), [c["arm_target"][op]], set()
    while todo:
        a = todo.pop()
        if a in seen or a in stop or not (lo <= a < hi):
            continue
        seen.add(a)
        i = by[a]
        t = i.target()
        if i.mn == "jal":
            if t in starts:
                calls.add(starts[t])
            if starts.get(t) in NORET:
                continue
            todo.append(a + 4)
        elif i.mn == "j":
            todo.append(t)
        elif i.mn in ("jr", "ret"):
            continue
        elif t is not None:  # branch
            todo += [t, a + 4]
        else:
            todo.append(a + 4)
    return calls, len(seen)


def closure(G, roots, cut=frozenset()):
    seen, todo = set(), list(roots)
    while todo:
        n = todo.pop()
        if n in seen:
            continue
        seen.add(n)
        if n in cut:
            continue
        todo += G.get(n, ())
    return seen


def static(c):
    G, IND = graph(c)
    f1 = __import__("armlib").f1_ops()
    per_op = {}
    for op in f1:
        calls, n = arm_callees(c, op)
        per_op[op] = dict(direct=sorted(calls), insts=n)
    errs = {x for v in per_op.values() for x in v["direct"] if x in NORET}
    normal = {op: [x for x in v["direct"] if x not in NORET] for op, v in per_op.items()}
    arm_ops = [o for o in f1 if o not in ("CALL", "RETURN", "RETURN0", "RETURN1", "VARARGPREP")]
    groups = {
        "a_arms": set(x for o in arm_ops for x in normal[o]),
        "b_errors": errs | {"luaD_throw", "longjmp", "fprintf", "exit"},
        "c_call_return": set(x for o in ("CALL", "RETURN", "RETURN0", "RETURN1") for x in normal[o])
        | {"exit"} | set(POST_FRAMES),
        "d_stack_growth": {"luaD_growstack", "luaD_reallocstack", "luaE_extendCI",
                           "luaT_adjustvarargs"} | set(normal.get("VARARGPREP", [])),
    }
    res = {}
    allc, allcut = set(), set()
    for g, roots in groups.items():
        full = closure(G, roots)
        cut = closure(G, roots, CUT)
        allc |= full
        allcut |= cut
        res[g] = dict(roots=sorted(roots), closure=len(full), closure_cut=len(cut),
                      cut_members=sorted(cut))
    unresolved = sorted({f"{n}@{hex(a)}" for n in allcut for a in IND.get(n, [])
                         if n not in INDIRECT})
    size = {n: len(c["funcs"][n]["insts"]) for n in c["funcs"]}
    res["total"] = dict(closure=len(allc), closure_cut=len(allcut),
                        insts_cut=sum(size.get(n, 0) for n in allcut))
    res["unresolved_indirect_in_cut"] = unresolved
    res["per_op"] = per_op
    return res, G


def dynamic(progs):
    c = T.ctx()
    starts = {f["start"]: n for n, f in c["funcs"].items() if f["insts"]}
    LV = c["funcs"]["luaV_execute"]["start"]
    ops = c["ops"]
    per = collections.defaultdict(lambda: collections.defaultdict(set))
    allf = collections.Counter()
    for prog in progs:
        elf = T.elf_for(prog)
        started, cur, ret = False, None, None
        for step, pc, npc, regs, mem in T.rows(elf):
            if pc == LV and not started:
                started, cur = True, "entry"
                ret = (T.R(regs, T.RA), T.R(regs, T.SP))
            if not started:
                continue
            if cur != "post" and pc == ret[0] and T.R(regs, T.SP) == ret[1]:
                cur = "post"
            elif cur != "post" and pc == c["HEAD"] and mem:
                cur = ops[mem[3] & 0x7F] if (mem[3] & 0x7F) < len(ops) else "?"
            if pc in starts:
                per[Path(prog).stem][cur].add(starts[pc])
                allf[starts[pc]] += 1
    return per, allf


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--dyn", nargs="*", default=None, help=".luac chunks to trace")
    ap.add_argument("--json")
    a = ap.parse_args()
    c = T.ctx()
    res, G = static(c)
    print("== static ==")
    for g in ("a_arms", "b_errors", "c_call_return", "d_stack_growth"):
        r = res[g]
        print(f"{g}: roots={len(r['roots'])} closure={r['closure']} closure(cut GC/reentry)={r['closure_cut']}")
        print("   roots:", " ".join(r["roots"]))
    print("total distinct:", res["total"])
    print("unresolved indirect sites in the cut closure:", len(res["unresolved_indirect_in_cut"]),
          " ".join(res["unresolved_indirect_in_cut"][:40]))
    print("per-op direct callees:")
    for op, v in res["per_op"].items():
        print(f"  {op:11s} insts={v['insts']:4d} {' '.join(v['direct'])}")
    if a.dyn is not None:
        per, allf = dynamic(a.dyn)
        print("== dynamic (functions entered after luaV_execute's entry) ==")
        tot = set()
        for prog, d in per.items():
            s = set().union(*d.values())
            tot |= s
            print(f"{prog}: {len(s)} functions")
            for op in sorted(d):
                print(f"   {op:10s} {len(d[op]):3d} {' '.join(sorted(d[op]))}")
        print("union:", len(tot))
        res["dynamic"] = {p: {o: sorted(s) for o, s in d.items()} for p, d in per.items()}
        res["dynamic_union"] = sorted(tot)
    if a.json:
        json.dump(res, open(a.json, "w"), indent=1, default=list)


if __name__ == "__main__":
    main()

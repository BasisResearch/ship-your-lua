#!/usr/bin/env python3
"""Counts of C-construct idioms in the Lua ELF vs the WHILE ELF."""
import sys, os, re, json, collections
sys.path.insert(0, os.path.dirname(__file__))
from lib import *
from origin import origins, family

REGS_ARG = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"]


def analyse(disasm, elfpath, reachjson, subsets):
    funcs, by_addr = parse_disasm(disasm)
    orig = origins(elfpath, funcs)
    reach = json.load(open(reachjson))
    starts = {f["start"]: n for n, f in funcs.items()}
    out = {}
    for sname, S in subsets(funcs, orig, reach).items():
        c = collections.Counter()
        varargs = []
        for n in S:
            ins = funcs[n]["insts"]
            for k, i in enumerate(ins):
                o = i.opl()
                t = i.target()
                callee = starts.get(t) if i.mn in ("jal", "j") and t else None
                # TValue tag loads: lbu at offset = 8 (mod 16) — the tt_ byte of a 16-byte TValue
                if i.mn == "lbu":
                    m = re.match(r"(-?\d+)\((\w+)\)", o[1])
                    if m and int(m.group(1)) % 16 == 8:
                        c["lbu_off_8mod16(tt_ tag load)"] += 1
                        rd = o[0]
                        # followed within 4 insts by a mask/compare/branch on the tag reg
                        for j in ins[k + 1:k + 5]:
                            jo = j.opl()
                            if rd in jo[1:] and (j.mn in BRANCHES or j.mn in ("andi", "addi", "addiw", "xori")):
                                c["  ...tag load feeding andi/addi/branch within 4"] += 1
                                break
                    c["lbu_total"] += 1
                if i.mn in BRANCHES:
                    c["branches"] += 1
                if i.mn == "jalr":
                    c["jalr (indirect call)"] += 1
                if i.mn == "jr" and o != ["ra"]:
                    c["jr non-ret (table or indirect tail)"] += 1
                if callee:
                    kind = "call" if i.mn == "jal" else "tail"
                    if callee != "__sbprintf" and re.match(r"__\w*(df|sf|tf)\d?$", callee) or callee.startswith("__float") or callee.startswith("__fix") \
                            or callee.startswith("__extend") or callee.startswith("__trunc"):
                        c[f"softfloat {kind} sites"] += 1
                        c[f"  sf:{callee}"] += 1
                    if callee in ("__muldi3", "__divdi3", "__moddi3", "__udivdi3", "__umoddi3",
                                  "__hidden___udivdi3", "__divsi3", "__udivsi3", "__modsi3", "__umodsi3", "__mulsi3"):
                        c[f"softint mul/div {kind} sites"] += 1
                    if "tf" in callee and callee.startswith("__"):
                        c["128-bit long double (tf) call sites"] += 1
                    if callee in ("setjmp", "_setjmp"):
                        c["setjmp call sites"] += 1
                    if callee in ("longjmp", "_longjmp"):
                        c["longjmp call sites"] += 1
                    if callee in ("memcpy", "memmove", "memset"):
                        c[f"{callee} call sites"] += 1
                    if kind == "tail":
                        c["tail-call j to another function"] += 1
                    else:
                        c["direct jal call sites"] += 1
                if i.mn in ("lh", "lhu", "sh"):
                    c["16-bit lh/lhu/sh"] += 1
                if i.mn == "lb":
                    c["lb (signed byte)"] += 1
                if i.mn in ("lwu",):
                    c["lwu"] += 1
                if i.mn == "ebreak":
                    c["ebreak (isolated null-deref trap)"] += 1
                if i.mn in ("sll", "srl", "sra", "sllw", "srlw", "sraw"):
                    c["variable shifts"] += 1
                if i.mn == "lui":
                    c["lui"] += 1
            # varargs prologue: stores of a1..a7 (or a2..a7) in the first 24 instructions
            first = ins[:24]
            stored = {x.opl()[0] for x in first if x.mn == "sd" and x.opl() and "(sp)" in x.opl()[1]
                      or (x.mn == "sd" and x.opl() and "(t1)" in x.ops)}
            if {"a5", "a6", "a7"} <= stored and len(stored & set(REGS_ARG[1:])) >= 5:
                varargs.append(n)
        c["varargs functions (a5,a6,a7 spilled in prologue)"] = len(varargs)
        c["jump tables (distinct)"] = sum(1 for t in reach["jumptables"] if t["func"] in S)
        c["jump table entries"] = sum(t["entries"] for t in reach["jumptables"] if t["func"] in S)
        out[sname] = {"counts": dict(sorted(c.items())), "varargs_functions": varargs,
                      "jumptable_funcs": sorted({t["func"] for t in reach["jumptables"] if t["func"] in S}),
                      "jalr_funcs": dict(collections.Counter(s["func"] for s in reach["indirect_sites"]
                                                           if s["func"] in S and s["kind"] == "call"))}
    return out


def lua_subsets(funcs, orig, reach):
    dyn = json.load(open("dynamic.json"))
    return {"whole": list(funcs),
            "whole_lua_origin": [n for n in funcs if family(orig[n]) == "lua"],
            "whole_lib_origin": [n for n in funcs if family(orig[n]) in ("libc", "libgcc", "libm")],
            "static_reach": reach["reachable"],
            "dyn_union": dyn["union_all_funcs"],
            "luaV_execute": ["luaV_execute"]}


def while_subsets(funcs, orig, reach):
    return {"whole": list(funcs), "static_reach": reach["reachable"]}


res = {"lua": analyse("lua_disasm.txt", LUA_ELF, "lua_reach.json", lua_subsets),
       "while": analyse("while_disasm.txt", WHILE_ELF, "while_reach.json", while_subsets)}
json.dump(res, open("constructs.json", "w"), indent=1)
keys = sorted(set().union(*(set(v["counts"]) for e in res.values() for v in e.values())))
cols = [("lua", k) for k in res["lua"]] + [("while", k) for k in res["while"]]
print("metric\t" + "\t".join(f"{a}:{b}" for a, b in cols))
for k in keys:
    print(k + "\t" + "\t".join(str(res[a][b]["counts"].get(k, 0)) for a, b in cols))
for a, b in cols:
    print(a, b, "varargs:", " ".join(res[a][b]["varargs_functions"][:60]))

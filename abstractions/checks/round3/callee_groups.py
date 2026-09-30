#!/usr/bin/env python3
"""Group the dynamic callee census (callee_census.py --json) into the round-3
clusters: arm helpers (normal paths), error chains, CALL print, RETURN/exit,
entry/VARARGPREP/stack growth.  F1 opcodes only (Lua/Fragment.lean).
usage: callee_groups.py census.json"""
import json, sys, collections
import lc3_trace as T
import armlib
c = T.ctx(); r = json.load(open(sys.argv[1]))
F1 = set(armlib.f1_ops())
size = lambda n: len(c['funcs'][n]['insts']) if n in c['funcs'] else 0
ERRPROGS = {'lc3_div0': 'IDIV', 'lc3_forerr': 'FORPREP', 'lc3_opint': 'MMBINI'}
G = collections.defaultdict(set); nonf1 = set()
for prog, d in r['dynamic'].items():
    for op, fs in d.items():
        if op in ('entry',):
            continue
        if ERRPROGS.get(prog) == op:
            G['b_error_chain'] |= set(fs); continue
        if op == 'CALL': G['c_call_print'] |= set(fs)
        elif op in ('post', 'RETURN', 'RETURN0', 'RETURN1'): G['c_return_exit'] |= set(fs)
        elif op == 'VARARGPREP': G['d_varargprep'] |= set(fs)
        elif op in F1: G['a_arm_helpers'] |= set(fs)
        else: nonf1.add(op)
growth = {'luaD_growstack', 'luaD_reallocstack', 'correctstack', 'luaM_realloc_', 'luaC_step', 'luaE_setdebt', 'luaG_traceexec'}
G['d_stack_growth'] = G['c_call_print'] & growth
allf = set().union(*G.values())
for g in sorted(G):
    print(f"{g:16s} {len(G[g]):4d} functions {sum(map(size, G[g])):6d} insts: {' '.join(sorted(G[g]))}")
print(f"TOTAL distinct {len(allf)} functions, {sum(map(size, allf))} instructions")
only = {g: len(G[g] - set().union(*(G[h] for h in G if h != g))) for g in G}
print("exclusive to group:", only)
print("non-F1 ops seen in difftests (excluded):", sorted(nonf1))

#!/usr/bin/env python3
"""Function-level template match of the Lua ELF against the WHILE ELF, plus
per-instruction / per-basic-block classification with syi's
disasm_to_sites.classify (the gen_sites.py site classes), gen_fn.py size
budgets, and syi decode_index.tsv word coverage."""
import sys, os, re, json, collections, hashlib
sys.path.insert(0, os.path.dirname(__file__))
from lib import *
from origin import origins, family
import disasm_to_sites as d2s

lf, lba = parse_disasm("lua_disasm.txt")
wf, wba = parse_disasm("while_disasm.txt")
lorig = origins(LUA_ELF, lf)
reach = json.load(open("lua_reach.json"))
dyn = json.load(open("dynamic.json"))
syi_scope = set(json.load(open(SYI + "/experiments/disasm_reachable.json"))["reachable"])
decode_idx = set()
for line in open(SYI + "/scripts/decode_index.tsv"):
    if line.strip() and not line.startswith("#"):
        decode_idx.add(line.split("\t")[0].lower())

hexaddr = re.compile(r"\b[0-9a-f]{6,16} <([^>]+)>")


def norm(fs, n):
    """body modulo absolute addresses: branch/call targets -> <sym+off>,
    auipc hi20 -> *, pc-relative lo12 (with `# addr <sym>`) -> sym"""
    out = []
    starts = {f["start"]: canon(k) for k, f in fs.items()}
    auipc_regs = set()
    for i in fs[n]["insts"]:
        ops = hexaddr.sub(lambda m: "<" + re.sub(r"@[0-9a-f]+", "", m.group(1)) + ">", i.ops)
        o = i.opl()
        if i.mn == "auipc":
            ops = ops.split(",")[0] + ",*"
        else:
            base = None
            if i.mn in ("addi", "jalr") and len(o) >= 2:
                base = o[1]
            m2 = re.search(r"\((\w+)\)", i.ops)
            if m2:
                base = m2.group(1)
            if base == "gp":
                ops = re.sub(r"-?\b(0x)?[0-9]+\b(?=\(|$)", "*", ops) + " #GP"
            elif base in auipc_regs and i.cmt_addr() is not None:
                tgt = i.cmt_addr()
                ops = re.sub(r"-?\b(0x)?[0-9]+\b(?=\(|$)", "*", ops) + \
                    " #" + starts.get(tgt, "DATA")
        if i.mn == "auipc":
            auipc_regs.add(o[0])
        elif o and i.mn not in BRANCHES and i.mn not in ("sd", "sw", "sh", "sb", "j", "jr", "ret") \
                and not (i.mn in ("addi", "ld") and base_is_same(o)):
            auipc_regs.discard(o[0])
        out.append(i.mn + " " + ops)
    return out


def base_is_same(o):
    # `addi a5,a5,lo` / `ld a5,lo(a5)` after auipc a5 keep a5 as a pc-rel address
    return False


def canon(n):
    return re.sub(r"@[0-9a-f]+$", "", n)


wbyname = {}
for n in wf:
    wbyname.setdefault(canon(n), []).append(n)
wbody = collections.defaultdict(list)
for n in wf:
    wbody[hashlib.sha1("\n".join(norm(wf, n)).encode()).hexdigest()].append(n)

fmatch = {}
for n in lf:
    lw = [i.word for i in lf[n]["insts"]]
    ln = norm(lf, n)
    cat = "new"
    other = None
    for wn in wbyname.get(canon(n), []):
        other = wn
        if [i.word for i in wf[wn]["insts"]] == lw:
            cat = "identical_words"; break
        if norm(wf, wn) == ln:
            cat = "identical_mod_reloc"; break
        cat = "same_name_differs"
    if cat in ("new", "same_name_differs"):
        h = hashlib.sha1("\n".join(ln).encode()).hexdigest()
        if h in wbody and cat == "new":
            cat = "identical_body_other_name"; other = wbody[h][0]
    if cat == "same_name_differs":
        a, b = norm(wf, other), ln
        import difflib
        sm = difflib.SequenceMatcher(None, a, b, autojunk=False)
        fmatch[n] = {"cat": cat, "while": other, "ratio": round(sm.ratio(), 3),
                     "n_lua": len(b), "n_while": len(a)}
    else:
        fmatch[n] = {"cat": cat, "while": other}
    fmatch[n]["in_while_proof_scope"] = bool(other and canon(other) in syi_scope)
    fmatch[n]["origin"] = lorig[n]
    fmatch[n]["family"] = family(lorig[n])
    fmatch[n]["n"] = len(lf[n]["insts"])

sets = {
    "whole": list(lf),
    "static_reach": reach["reachable"],
    "dyn_while": dyn["while_all_funcs"],
    "dyn_while_after_exec": dyn["while_after_exec_funcs"],
    "dyn_union": dyn["union_all_funcs"],
    "dyn_union_after_exec": dyn["union_after_exec_funcs"],
}
dyn_pcs_while = set()
dyn_pcs_union = set()
for line in open("traces/lua-riscv-htif.pcs.tsv"):
    dyn_pcs_while.add(int(line.split()[0], 16))
import glob
for p in glob.glob("traces/*.pcs.tsv"):
    for line in open(p):
        dyn_pcs_union.add(int(line.split()[0], 16))

report = {}
for sname, S in sets.items():
    c = collections.Counter(); ci = collections.Counter(); cs = collections.Counter()
    for n in S:
        c[fmatch[n]["cat"]] += 1; ci[fmatch[n]["cat"]] += fmatch[n]["n"]
        if fmatch[n]["in_while_proof_scope"] and fmatch[n]["cat"] in (
                "identical_words", "identical_mod_reloc", "identical_body_other_name"):
            cs["reused_and_in_while_proof_scope"] += fmatch[n]["n"]
    report[sname] = {"funcs": dict(c), "insts": dict(ci), "total_funcs": len(S),
                     "total_insts": sum(ci.values()), **cs}
# instruction-weighted by executed PCs
for sname, P in (("pcs_while", dyn_pcs_while), ("pcs_union", dyn_pcs_union)):
    c = collections.Counter(fmatch[lba[p].func]["cat"] for p in P if p in lba)
    report[sname] = {"pcs_by_cat": dict(c), "total": len(P)}

# ---------------------------------------------------------- site classification
def classify_ins(i):
    rows = d2s.classify(i.addr, int(i.word, 16), f"{i.mn} {i.ops}", {})
    un = [r for r in rows if r.cls is None and r.comment and r.comment.startswith("#UNSUPPORTED")]
    if un:
        why = un[0].comment.split("[")[-1].rstrip("]")
        return False, why
    return True, rows[-1].cls


def blocks_of(fs, n):
    insts = fs[n]["insts"]
    leaders = {insts[0].addr}
    addrs = {i.addr for i in insts}
    for k, i in enumerate(insts):
        t = i.target()
        if i.mn in BRANCHES or i.mn in ("j", "jr", "ret", "jalr", "jal"):
            if k + 1 < len(insts):
                leaders.add(insts[k + 1].addr)
        if t is not None and t in addrs and i.mn != "jal":
            leaders.add(t)
    for jt in reach["jumptables"]:
        if jt["func"] == n:
            leaders |= {int(x, 16) for x in jt["targets"]}
    bl = []
    cur = []
    for i in insts:
        if i.addr in leaders and cur:
            bl.append(cur); cur = []
        cur.append(i)
    if cur:
        bl.append(cur)
    return bl


site_stats = {}
unsupp_reason = {}
for sname, S, P in (("static_reach", reach["reachable"], None),
                    ("dyn_while", dyn["while_all_funcs"], dyn_pcs_while),
                    ("dyn_union", dyn["union_all_funcs"], dyn_pcs_union),
                    ("while_elf_whole", None, None)):
    fs = wf if sname == "while_elf_whole" else lf
    S = list(wf) if S is None else S
    ni = nok = 0; nb = nbok = 0; why = collections.Counter(); mnw = collections.Counter()
    for n in S:
        for b in blocks_of(fs, n):
            if P is not None and not any(i.addr in P for i in b):
                continue
            nb += 1
            allok = True
            for i in b:
                if P is not None and i.addr not in P:
                    continue
                ni += 1
                ok, w = classify_ins(i)
                if ok:
                    nok += 1
                else:
                    allok = False; why[w] += 1; mnw[i.mn] += 1
            nbok += allok
    site_stats[sname] = {"insts": ni, "site_classified": nok, "pct": round(100 * nok / ni, 1),
                         "blocks": nb, "blocks_all_classified": nbok,
                         "blocks_pct": round(100 * nbok / nb, 1),
                         "unsupported_by_reason": dict(why.most_common()),
                         "unsupported_by_mnemonic": dict(mnw.most_common())}

# gen_fn budgets (<=150 instrs, <=20 branches) and whether it has constructs gen_fn
# has no terminator class for (jalr, table jr)
def genfn_ok(fs, n):
    ins = fs[n]["insts"]
    nbr = sum(1 for i in ins if i.mn in BRANCHES)
    bad = [i.mn for i in ins if i.mn == "jalr" or (i.mn == "jr" and i.ops != "ra")]
    return len(ins) <= 150 and nbr <= 20, bool(bad)

gf = {}
for sname, S in (("static_reach", reach["reachable"]), ("dyn_while", dyn["while_all_funcs"]),
                 ("dyn_union", dyn["union_all_funcs"])):
    c = collections.Counter()
    for n in S:
        ok, ind = genfn_ok(lf, n)
        c["within_budget" if ok else "over_budget"] += 1
        if ok and not ind:
            c["within_budget_no_indirect"] += 1
        if ok and not ind and fmatch[n]["cat"] not in ("identical_words", "identical_mod_reloc", "identical_body_other_name"):
            c["within_budget_no_indirect_and_new"] += 1
    gf[sname] = dict(c)

# decode table coverage
dec = {}
for sname, P in (("whole", {i.addr for f in lf.values() for i in f["insts"]}),
                 ("static_reach", {i.addr for n in reach["reachable"] for i in lf[n]["insts"]}),
                 ("dyn_while", dyn_pcs_while), ("dyn_union", dyn_pcs_union)):
    W = {lba[p].word for p in P if p in lba}
    dec[sname] = {"unique_words": len(W), "in_syi_decode_index": len(W & decode_idx),
                  "pct": round(100 * len(W & decode_idx) / len(W), 1)}

json.dump({"function_match": fmatch, "summary": report, "sites": site_stats,
           "gen_fn": gf, "decode_index": dec}, open("template_match.json", "w"), indent=1)
print(json.dumps({"summary": report, "sites": site_stats, "gen_fn": gf, "decode_index": dec}, indent=1))

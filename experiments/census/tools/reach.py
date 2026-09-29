#!/usr/bin/env python3
"""Static reachability for an objdump -d text + ELF, resolving
  * switch jump tables (auipc/addi base; slli; add; lw; add base; jr) -> intra-fn,
  * indirect calls (jalr / non-table jr) by address-flow closure:
    a function whose address is materialised (auipc+addi `# addr <fn>`)
    in reachable code, or stored as an 8-byte pointer inside a data object
    that reachable code (or a reachable data object) references, is added.

usage: reach.py DISASM ELF ROOT OUT.json
"""
import sys, json, bisect, collections
from lib import *

disasm, elfpath, root, outp = sys.argv[1:5]
funcs, by_addr = parse_disasm(disasm)
elf = Elf(elfpath)
starts = {f["start"]: n for n, f in funcs.items()}
fstarts = sorted((f["start"], f["end"], n) for n, f in funcs.items())
fs_keys = [s for s, _, _ in fstarts]


def func_of(addr):
    i = bisect.bisect_right(fs_keys, addr) - 1
    if i >= 0 and fstarts[i][0] <= addr < fstarts[i][1]:
        return fstarts[i][2]
    return None


def reg_of(op):
    return op.strip()


# ---------------------------------------------------------------- jump tables
def find_def(insts, idx, reg):
    """walk backwards from idx-1 to the latest instruction writing reg"""
    for j in range(idx - 1, -1, -1):
        o = insts[j].opl()
        if o and o[0] == reg and insts[j].mn not in BRANCHES and insts[j].mn not in (
                "sd", "sw", "sh", "sb", "j", "jr", "ret"):
            return j
    return None


def lla_value(insts, j):
    """if insts[j] is `addi r,r,imm # addr <sym>` after auipc -> addr"""
    i = insts[j]
    if i.mn == "addi" and i.cmt_addr() is not None:
        return i.cmt_addr()
    return None


jumptables = []     # dicts
table_jr = set()
indirect = []       # (func, addr, mn, ops, kind)
for n, f in funcs.items():
    insts = f["insts"]
    for k, i in enumerate(insts):
        if i.mn not in ("jr", "jalr"):
            continue
        o = i.opl()
        if i.mn == "jr" and o == ["ra"]:
            continue
        rt = o[0]
        tbl = None
        if i.mn == "jr":
            j = find_def(insts, k, rt)
            if j is not None and insts[j].mn == "add":
                a, b = insts[j].opl()[1], insts[j].opl()[2]
                # one operand comes from a lw, the other is the table base
                for ent, base in ((a, b), (b, a)):
                    je = find_def(insts, j, ent)
                    if je is None or insts[je].mn != "lw":
                        continue
                    jb = find_def(insts, k, base) if base != rt else find_def(insts, j, base)
                    jb = find_def(insts, j, base)
                    if jb is None:
                        continue
                    tb = lla_value(insts, jb)
                    if tb is None:
                        continue
                    tbl = tb
                    break
        if tbl is None:
            indirect.append((n, i.addr, i.mn, i.ops,
                             "call" if i.mn == "jalr" else "tailjump"))
            continue
        # bound: nearest preceding bltu/bgeu against a li constant
        bound = None
        for j in range(k - 1, max(-1, k - 25), -1):
            b = insts[j]
            if b.mn in ("bltu", "bgeu"):
                x, y = b.opl()[0], b.opl()[1]
                for r, isk_first in ((x, True), (y, False)):
                    jd = find_def(insts, j, r)
                    if bound is None and jd is not None and insts[jd].mn == "li":
                        kv = int(insts[jd].opl()[1], 0)
                        if b.mn == "bltu" and isk_first:    # K < idx -> default
                            bound = kv + 1
                        elif b.mn == "bgeu" and not isk_first:  # idx >= K -> default
                            bound = kv
                        elif b.mn == "bltu" and not isk_first:  # idx < K -> in range?
                            bound = kv
                        elif b.mn == "bgeu" and isk_first:   # K >= idx...
                            bound = kv + 1
                if bound is not None:
                    break
        # read entries
        ents = []
        e = 0
        limit = bound if bound is not None else 4096
        while e < limit:
            v = elf.s32(tbl + 4 * e)
            if v is None:
                break
            tgt = tbl + v
            if func_of(tgt) != n:
                break
            ents.append(tgt)
            e += 1
        table_jr.add(i.addr)
        jumptables.append({"func": n, "jr": hex(i.addr), "table": hex(tbl),
                           "bound_from_cmp": bound, "entries": len(ents),
                           "targets": [hex(t) for t in ents]})

# dedupe tables (same table used by several jr sites)
uniq_tables = {t["table"]: t for t in jumptables}

# ---------------------------------------------------------------- data objects
syms = symbols(elfpath)
dsyms = sorted({(a, sz, nm) for (a, sz, typ, bind, nm, f) in syms
                if typ in ("OBJECT", "NOTYPE") and a >= 0x80000000
                and not (funcs and func_of(a))})
dkeys = [a for a, _, _ in dsyms]
sec_ranges = [(a, a + size, nm) for nm, (a, off, size, typ) in elf.sections.items()
              if a and nm not in (".text",) and typ != 8]


def data_region(addr):
    """the data object containing addr: sized symbol, else [addr, next symbol)"""
    i = bisect.bisect_right(dkeys, addr) - 1
    if i >= 0:
        a, sz, nm = dsyms[i]
        if sz and a <= addr < a + sz:
            return (a, a + sz, nm)
    nxt = dkeys[i + 1] if i + 1 < len(dkeys) else addr + 8
    nm = dsyms[i][2] + f"+{addr - dsyms[i][0]:#x}" if i >= 0 else f"anon_{addr:x}"
    for lo, hi, snm in sec_ranges:
        if lo <= addr < hi:
            return (addr, max(min(nxt, hi), addr + 1), nm)
    return (addr, addr, nm)   # bss / not file-backed: no initial pointers


def pointers_in(lo, hi):
    out = []
    a = (lo + 7) & ~7
    while a + 8 <= hi:
        v = elf.u64(a)
        if v is not None and 0x80000000 <= v < 0x90000000:
            out.append(v)
        a += 8
    return out

# ---------------------------------------------------------------- closure
edges = collections.defaultdict(set)
lla_funcs = collections.defaultdict(set)
lla_data = collections.defaultdict(set)
for n, f in funcs.items():
    for i in f["insts"]:
        t = i.target()
        if t is not None:
            tn = starts.get(t)
            if tn and tn != n:
                edges[n].add(tn)
            elif func_of(t) not in (None, n):   # jump into middle of another fn
                edges[n].add(func_of(t))
        ca = i.cmt_addr()
        if ca is not None and i.mn not in ("jal", "j") and i.mn not in BRANCHES:
            if ca in starts:
                lla_funcs[n].add(starts[ca])
            elif func_of(ca) is None:
                lla_data[n].add(ca)


def closure(root_list, use_indirect=True):
    seenf, seend = set(), set()
    work = [("f", r) for r in root_list]
    via = {}
    while work:
        kind, x = work.pop()
        if kind == "f":
            if x in seenf or x not in funcs:
                continue
            seenf.add(x)
            for y in edges[x]:
                work.append(("f", y))
            if use_indirect:
                for y in lla_funcs[x]:
                    via.setdefault(y, f"lla in {x}")
                    work.append(("f", y))
                for a in lla_data[x]:
                    work.append(("d", data_region(a)))
        else:
            if x in seend:
                continue
            seend.add(x)
            lo, hi, nm = x
            for p in pointers_in(lo, hi):
                if p in starts:
                    via.setdefault(starts[p], f"ptr in data {nm}")
                    work.append(("f", starts[p]))
                elif func_of(p) is None:
                    work.append(("d", data_region(p)))
    return seenf, seend, via


direct, _, _ = closure([root], use_indirect=False)
reach, dreach, via = closure([root])
# all address-taken (upper bound)
all_taken = set()
for n in funcs:
    all_taken |= lla_funcs[n]
for nm, (a, off, size, typ) in elf.sections.items():
    if a and nm != ".text" and typ != 8:
        for p in pointers_in(a, a + size):
            if p in starts:
                all_taken.add(starts[p])
upper, _, _ = closure([root] + sorted(all_taken), use_indirect=True)

ninst = lambda S: sum(len(funcs[n]["insts"]) for n in S)
words = lambda S: {i.word for n in S for i in funcs[n]["insts"]}
res = {
    "root": root,
    "n_funcs_total": len(funcs),
    "n_insts_total": ninst(funcs),
    "direct_only": {"funcs": len(direct), "insts": ninst(direct), "unique_words": len(words(direct))},
    "address_flow": {"funcs": len(reach), "insts": ninst(reach), "unique_words": len(words(reach)),
                     "data_objects_reached": len(dreach)},
    "all_address_taken_upper": {"funcs": len(upper), "insts": ninst(upper), "unique_words": len(words(upper)),
                                "n_address_taken": len(all_taken)},
    "indirect_via": {k: via.get(k, "direct callee of an indirectly-reached fn") for k in sorted(reach - direct)},
    "reachable": sorted(reach, key=lambda n: funcs[n]["start"]),
    "unreachable": sorted(set(funcs) - reach, key=lambda n: funcs[n]["start"]),
    "jumptables": list(uniq_tables.values()),
    "jumptable_jr_sites": len(table_jr),
    "indirect_sites": [dict(func=a, addr=hex(b), mn=c, ops=d, kind=e) for a, b, c, d, e in indirect],
}
json.dump(res, open(outp, "w"), indent=1)
print(json.dumps({k: v for k, v in res.items() if k in (
    "n_funcs_total", "n_insts_total", "direct_only", "address_flow",
    "all_address_taken_upper", "jumptable_jr_sites")}, indent=1))
print("jump tables:", len(uniq_tables), "entries total:", sum(t["entries"] for t in uniq_tables.values()))
print("indirect sites:", collections.Counter(x[4] for x in indirect))

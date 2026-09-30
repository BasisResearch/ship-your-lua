#!/usr/bin/env python3
"""F1 (candidate C8): count equivalence classes of the 54 F1 opcode arms
under canon.py's canonical form, and price a shared-prefix (phylogeny) tree.

Pre-registered rules (abstractions/ROUND-1.md, "Carried to round 2"):
  orbits DEAD if {MUL,ADD,SUB} or {MULK,ADDK,SUBK} do not merge mod ALU op,
         or if there are more than ~30 classes for the 54 arms;
  shared-prefix tree DEAD if MST(edit distance) / total arm size > 0.4.
The MST is over all 54 arms (pre-registered); a sensitivity run drops the five
call/return/for-prep arms (CALL, RETURN, RETURN0, RETURN1, FORPREP).

Writes f1_classes.tsv and f1_orbits.json next to this script."""
import os, json, collections
import canon

HERE = os.path.dirname(os.path.abspath(__file__))


def lev(a, b):
    if len(a) < len(b):
        a, b = b, a
    prev = list(range(len(b) + 1))
    for i, x in enumerate(a, 1):
        cur = [i] + [0] * len(b)
        for j, y in enumerate(b, 1):
            cur[j] = min(prev[j] + 1, cur[j - 1] + 1, prev[j - 1] + (x != y))
        prev = cur
    return prev[-1]


def mst(seqs):
    names = list(seqs)
    n = len(names)
    D = {}
    for i in range(n):
        for j in range(i + 1, n):
            D[i, j] = D[j, i] = lev(seqs[names[i]], seqs[names[j]])
    intree = {0}
    best = {j: (D[0, j], 0) for j in range(1, n)}
    edges = []
    while best:
        j = min(best, key=lambda k: best[k][0])
        w, i = best.pop(j)
        edges.append((names[i], names[j], w))
        intree.add(j)
        for k in best:
            if D[j, k] < best[k][0]:
                best[k] = (D[j, k], j)
    return edges


def main():
    ctx = canon.context()
    T = canon.Terms()
    ops = canon.armlib.f1_ops()
    arms = {}
    for op in ops:
        W, root, trunc = canon.canon_arm(ctx, T, op)
        assert not trunc, op
        toks, sig = canon.linearise(T, root)
        _, sig_alu = canon.linearise(T, root, alu=True)
        S = canon.arm_insts(ctx, op)
        raw = [f"{ctx['by_addr'][a].mn} {ctx['by_addr'][a].ops}" for a in sorted(S)]
        arms[op] = dict(exact=root, alu=T.alu_hash(root, 1), alu2=T.alu_hash(root, 2),
                        tokens=len(toks), sig=sig, sig_alu=sig_alu, raw=raw, insts=len(S),
                        target=hex(ctx["arm_target"][op]))
    out = {"n_arms": len(ops), "elf": canon.armlib.LUA_ELF}
    for lvl in ("exact", "alu", "alu2"):
        cl = collections.defaultdict(list)
        for op in ops:
            cl[arms[op][lvl]].append(op)
        out[lvl] = {"classes": len(cl), "merged": sorted([v for v in cl.values() if len(v) > 1])}
    fam = lambda xs: len({arms[x]["alu"] for x in xs}) == 1
    out["rule_mul_add_sub_merge"] = {"MUL,ADD,SUB": fam(["MUL", "ADD", "SUB"]),
                                     "MULK,ADDK,SUBK": fam(["MULK", "ADDK", "SUBK"]),
                                     "MUL,MULK": fam(["MUL", "MULK"])}
    # shared-prefix tree
    SUB = [o for o in ops if o not in ("CALL", "RETURN", "RETURN0", "RETURN1", "FORPREP")]
    for key, seqkey, sel in (("mst_canon_exact", "sig", ops),
                             ("mst_canon_alu", "sig_alu", ops),
                             ("mst_raw", "raw", ops),
                             ("sensitivity_49_canon_alu", "sig_alu", SUB),
                             ("sensitivity_49_raw", "raw", SUB)):
        seqs = {op: arms[op][seqkey] for op in sel}
        edges = mst(seqs)
        tot = sum(len(s) for s in seqs.values())
        w = sum(e[2] for e in edges)
        root = min(len(s) for s in seqs.values())
        out[key] = {"total_size": tot, "mst_weight": w, "fraction": round(w / tot, 3),
                    "fraction_with_root": round((w + root) / tot, 3),
                    "edges": sorted(edges, key=lambda e: e[2])}
    json.dump(out, open(os.path.join(HERE, "f1_orbits.json"), "w"), indent=1)
    with open(os.path.join(HERE, "f1_classes.tsv"), "w") as f:
        f.write("op\ttarget\tinsts\ttokens\texact\tmodALU\tmodALU+cmp\n")
        for op in ops:
            a = arms[op]
            f.write(f"{op}\t{a['target']}\t{a['insts']}\t{a['tokens']}\t{a['exact']}\t{a['alu']}\t{a['alu2']}\n")
    for lvl in ("exact", "alu", "alu2"):
        print(f"{lvl:6s}: {out[lvl]['classes']} classes; merged {out[lvl]['merged']}")
    print("rule 1 (merge mod ALU):", out["rule_mul_add_sub_merge"])
    for key in ("mst_canon_exact", "mst_canon_alu", "mst_raw", "sensitivity_49_canon_alu", "sensitivity_49_raw"):
        m = out[key]
        print(f"{key}: MST {m['mst_weight']} / {m['total_size']} = {m['fraction']} (with root {m['fraction_with_root']})")


if __name__ == "__main__":
    main()

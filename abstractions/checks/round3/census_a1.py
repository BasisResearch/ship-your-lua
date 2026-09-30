#!/usr/bin/env python3
"""ROUND-3 §1 census of the A1 obligations (hand Lean + generator lines).

For every A1 commit (the history of Lua/Vm/Sim, gen_lua_arm.py, RegsOk):
  * hand Lean declarations of the A1 files, each attributed to the commit that
    introduced its name (git log -S, oldest first) and classified by SHAPE
    (what is re-proved) into a cluster;
  * the non-blank, non-comment lines each commit added to the generator
    (gen_lua_arm.py: per-kind templates), the segment generators, and the hand
    Lean files.
Prints a per-commit table and a per-cluster table (count, lines, first/last
quarter mean in introduction order).

    python3 abstractions/checks/round3/census_a1.py
"""
import os, re, subprocess, collections

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "../../.."))
os.chdir(ROOT)
LEAN = ["Lua/Vm/Sim/Close.lean", "Lua/Vm/Sim/StepK.lean", "Lua/Vm/Sim/Step.lean",
        "Lua/Vm/Sim/Mem.lean", "Lua/Vm/Sim/Bits.lean", "Lua/Vm/Sim/Rel.lean",
        "Lua/Vm/Sim/Dispatch.lean", "Lua/Vm/Sim/Entry.lean",
        "Lua/Vm/RegsOk.lean", "Lua/Vm/Arms/RegsOk.lean"]
GEN = ["scripts/gen_lua_arm.py"]
SEGGEN = ["scripts/gen_lua_arms.py", "scripts/syi/gen_segment.py", "scripts/draft_f1_arms.py",
          "scripts/syi/disasm_to_segment.py"]

def git(*a):
    return subprocess.run(["git", *a], capture_output=True, text=True, check=True).stdout

COMMITS = [l.split(" ", 1) for l in git("log", "--reverse", "--format=%h %s", "--",
           *LEAN, *GEN).splitlines()]
ORDER = {h: i for i, (h, _) in enumerate(COMMITS)}

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)?"
                  r"(theorem|lemma|def|abbrev|structure|inductive|macro|syntax|elab)\s+\"?([^\s:({\"]+)")
TOP = re.compile(r"^(?:@\[|/--|/-!|theorem|lemma|def|abbrev|structure|inductive|instance|example|"
                 r"namespace|end|section|open|variable|set_option|mutual|noncomputable|private|protected|"
                 r"macro|syntax|elab|macro_rules|#)")

def strip_comments(lines):
    out, depth = [], 0
    for l in lines:
        s = l
        res = ""
        i = 0
        while i < len(s):
            if s.startswith("/-", i): depth += 1; i += 2; continue
            if depth and s.startswith("-/", i): depth -= 1; i += 2; continue
            if not depth and s.startswith("--", i): break
            if not depth: res += s[i]
            i += 1
        out.append(res)
    return out

def decls(path):
    raw = open(path).read().splitlines()
    lines = strip_comments(raw)
    out, i = [], 0
    while i < len(raw):
        m = DECL.match(raw[i])
        if m:
            j = i + 1
            while j < len(raw) and not TOP.match(raw[j]): j += 1
            n = sum(1 for l in lines[i:j] if l.strip())
            out.append((m.group(2), m.group(1), n))
            i = j
        else:
            i += 1
    return out

# Shape clusters: what is re-proved, over what varying data.
RULES = [
    ("c-frame", r"^(Core\.(write|update|forloop|jump|text_of|frame_of|kptr_of)|insert_frame|getElem\?_insert_out|"
                r"slotStore|SlotStore|store_s|ForStore|forloop_store|output_congr|pin_eq|trap_of_frame|"
                r"bytesT1_writeMap8_out|getElem_writeMap8|bytesT8_writeMap8|stData_int)"),
    ("c-regsok", r"^(RegsOk|Quiet|isSome_of|alu|jal|store|btaken|bnottaken|jr)$|^RegsOk\."),
    ("a-kernel-inversion", r"^(step_|cond_|jumpTo_|mapM|upd$|supported_regTop|opcode_table|opNum_of_op)"),
    ("a-guard", r"^(guard_|mb_n?lt|zext_tag_beq|nibble_|snez_tag|seqz_tag|tag_false_bit|ValRepr\.)"),
    ("a-alu-value", r"(_val|nextjump_pc)$"),
    ("d-field-arith", r"^(sext|and255|field|addiw_bias|ult_one_sub|kraw_eq|sbraw_eq|scraw_eq|bitb|const_|"
                      r"extract_sext|shr_lt|opcode_mask|imm12|add_imm|shl_ofNat|slot_addr|slot_toNat|sdData|"
                      r"stData_zext|ofNat_bias|bytesT[48]_at|ld_slot)"),
    ("d-tactic", r"^(slot_arith|len_arith|arm_arith)$"),
    ("d-read-congr", r"^(bytesT[48]_congr|slot_congr|slotTag|slotVal|Rodata|jt|armTarget|rodata_below|rdLE)"),
]

def cluster(name, path):
    for c, rx in RULES[:2]:
        if re.search(rx, name): return c
    if path.endswith(("Rel.lean", "Dispatch.lean", "Entry.lean")):
        return "setup-relation/dispatch/entry"
    for c, rx in RULES[2:]:
        if re.search(rx, name): return c
    return "other"

def first_commit(name, path):
    hs = git("log", "--reverse", "--format=%h", "-S", name, "--", path).split()
    for h in hs:
        if h in ORDER: return h
    return hs[0] if hs else "?"

def added_lines(commit, paths):
    """non-blank, non-comment added lines (approximate: '+' lines of the diff)."""
    d = git("show", "--format=", "-U0", commit, "--", *paths)
    n = 0
    for l in d.splitlines():
        if l.startswith("+") and not l.startswith("+++"):
            s = l[1:].strip()
            if s and not s.startswith(("--", "#", "/-", "-/", "\"\"\"")): n += 1
    return n

def main():
    rows = []
    for p in LEAN:
        for name, kind, n in decls(p):
            rows.append((first_commit(name, p), p, name, kind, n, cluster(name, p)))
    rows.sort(key=lambda r: ORDER.get(r[0], 999))
    print("## per commit (added non-blank non-comment lines)\n")
    print("| commit | subject | gen_lua_arm.py | segment gens | hand Lean (new decls, lines by cluster) |")
    print("|---|---|---|---|---|")
    for h, subj in COMMITS:
        byc = collections.Counter()
        for r in rows:
            if r[0] == h: byc[r[5]] += r[4]
        print(f"| {h} | {subj[:70]} | {added_lines(h, GEN)} | {added_lines(h, SEGGEN)} | "
              + ", ".join(f"{c} {n}" for c, n in byc.most_common()) + " |")
    print("\n## per cluster (declarations in introduction order)\n")
    print("| cluster | decls | lines | first-quarter mean | last-quarter mean | examples |")
    print("|---|---|---|---|---|---|")
    by = collections.defaultdict(list)
    for r in rows: by[r[5]].append(r)
    for c, rs in sorted(by.items()):
        ns = [r[4] for r in rs]; q = max(1, len(ns) // 4)
        print(f"| {c} | {len(rs)} | {sum(ns)} | {sum(ns[:q])/q:.1f} | {sum(ns[-q:])/q:.1f} | "
              + ", ".join(f"{r[2]}({r[4]},{r[0]})" for r in rs[:3]) + " … "
              + ", ".join(f"{r[2]}({r[4]},{r[0]})" for r in rs[-2:]) + " |")
    print("\n## all declarations\n")
    for r in rows: print("\t".join(map(str, r)))

main()

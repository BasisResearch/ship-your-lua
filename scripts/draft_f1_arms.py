#!/usr/bin/env python3
"""Draft every F1 arm of luaV_execute with scripts/syi/disasm_to_segment.py.

Each arm is the set of luaV_execute instructions reachable from its jump
table target (experiments/census/luaV_execute_arms.tsv) without passing the
fetch head (`fetch_head` in luaV_execute_arms.json), as in experiments/census/tools/arms.py. It is cut
into straight-line segments at branch targets and after every control
transfer; each segment is classified by disasm_to_sites.py and drafted by
disasm_to_segment.py, which fails on any instruction it cannot draft. The
check is that every instruction of every F1 arm lands in a draft as a step.

    python3 scripts/draft_f1_arms.py [-o experiments/census/demo/f1_arm_drafts.tsv]
        [--json-dir DIR]     # also write every draft
"""
import argparse
import csv
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "scripts/syi"))
import disasm_to_sites as d2s        # noqa: E402
import disasm_to_segment as d2seg    # noqa: E402

ARMS_TSV = ROOT / "experiments/census/luaV_execute_arms.tsv"
ARMS_JSON = ROOT / "experiments/census/luaV_execute_arms.json"
_S = json.load(open(ARMS_JSON))["summary"]
LO, HI = int(_S["luaV_execute"]["start"], 16), int(_S["luaV_execute"]["end"], 16)
FETCH = int(_S["jump_table"]["fetch_head"], 16)
F1_EXTRA_OPS = {"OP_VARARGPREP"}     # F1 in Lua/Fragment.lean
NORET = {"luaD_throw", "luaG_callerror", "luaG_concaterror", "luaG_errormsg",
         "luaG_forerror", "luaG_opinterror", "luaG_ordererror",
         "luaG_runerror", "luaG_tointerror", "luaG_typeerror", "luaM_toobig"}


def cfg():
    """{addr: (row, successors, ends_segment)} over luaV_execute."""
    out = {}
    for addr, word, raw in d2s.disassemble(d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF,
                                           LO, HI):
        row = d2s.classify(addr, word, raw, {addr: "taken"})[-1]
        c, o, nxt = row.cls, row.ops, addr + 4
        if c is None:
            raise SystemExit(f"unsupported instruction at 0x{addr:x}: {raw}")
        if c.startswith("branch_"):
            tgt = (addr + d2s.sext(int(o[3], 16), 13)) % 2**64
            succ, end = [s for s in (tgt, nxt) if LO <= s < HI], True
        elif c == "j":
            tgt = (addr + d2s.sext(int(o[0], 16), 21)) % 2**64
            succ, end = ([tgt] if LO <= tgt < HI else []), True
        elif c == "jal":
            callee = re.search(r"<([^>+]+)>", raw)
            dead = callee is not None and callee.group(1) in NORET
            succ, end = ([] if dead else [nxt]), dead
        elif c == "jr" or (c == "jalr" and o[0] == "0"):
            succ, end = [], True
        else:
            succ, end = [nxt], False
        out[addr] = (raw, succ, end)
    return out


def arm(g, t):
    seen, work = set(), [t]
    while work:
        a = work.pop()
        if a in seen or a == FETCH or a not in g:
            continue
        seen.add(a)
        work.extend(g[a][1])
    return seen


def segments(g, reach, target):
    leaders = {target} | {s for a in reach for s in g[a][1]
                          if g[a][2] or s != a + 4}
    segs, cur = [], None
    for a in sorted(reach):
        if cur is not None and (a in leaders or a != cur[1]):
            segs.append(cur)
            cur = None
        cur = (cur[0], a + 4) if cur else (a, a + 4)
        if g[a][2]:
            segs.append(cur)
            cur = None
    if cur:
        segs.append(cur)
    return segs


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("-o", "--output", type=Path, default=None)
    ap.add_argument("--json-dir", type=Path, default=None)
    args = ap.parse_args()
    f1 = set(json.load(open(ARMS_JSON))["summary"]["F1_ops"]) | F1_EXTRA_OPS
    g = cfg()
    rows = [("op", "target", "reach", "segments", "drafted_insts",
             "site_steps", "call_steps", "steps_without_battery")]
    tot = [0, 0, 0]
    for r in csv.DictReader(open(ARMS_TSV), delimiter="\t"):
        if r["op"] not in f1:
            continue
        t = int(r["target"], 16)
        reach = arm(g, t)
        if len(reach) != int(r["reach"]):
            raise SystemExit(f"{r['op']}: reach {len(reach)} != census {r['reach']}")
        drafted = sites = calls = nobat = 0
        segs = segments(g, reach, t)
        for k, (lo, hi) in enumerate(segs):
            path = {a: "nottaken" for a in range(lo, hi, 4)}
            last = hi - 4
            if g[last][2] and g[last][1] and g[last][1][0] != hi:
                path[last] = "taken"          # a branch ending the segment
            lines = []
            for addr, word, raw in d2s.disassemble(
                    d2s.DEFAULT_OBJDUMP, d2s.DEFAULT_ELF, lo, hi):
                lines += [x.tsv() for x in d2s.classify(addr, word, raw, path)]
            name = f"tr_{r['op'].lower()}_s{k:02d}"
            try:
                spec = d2seg.draft(lo, hi, lines, "<elf>", name)
            except ValueError as e:
                raise SystemExit(f"{r['op']} segment 0x{lo:x}-0x{hi:x}: {e}")
            steps = spec["steps"]
            s = sum(1 for x in steps if x["class"] != "call")
            if s != (hi - lo) // 4:
                raise SystemExit(f"{name}: {s} site steps for {(hi - lo) // 4} insts")
            drafted += s
            sites += s
            calls += len(steps) - s
            nobat += sum(1 for x in steps if "site_battery" in x or "gen_segment" in x)
            if args.json_dir:
                args.json_dir.mkdir(parents=True, exist_ok=True)
                (args.json_dir / f"{name}.json").write_text(
                    json.dumps(spec, indent=2, ensure_ascii=False) + "\n")
        if drafted != len(reach):
            raise SystemExit(f"{r['op']}: drafted {drafted} of {len(reach)}")
        rows.append((r["op"], r["target"], len(reach), len(segs), drafted,
                     sites, calls, nobat))
        tot[0] += len(reach)
        tot[1] += len(segs)
        tot[2] += nobat
    text = "\n".join("\t".join(map(str, x)) for x in rows) + "\n"
    text += (f"# {len(rows) - 1} F1 arms, {tot[0]} arm instructions in "
             f"{tot[1]} segments, all drafted; {tot[2]} steps need a site "
             f"class gen_sites.py/gen_segment.py lacks\n")
    if args.output:
        args.output.write_text(text)
    sys.stdout.write(text)


if __name__ == "__main__":
    main()

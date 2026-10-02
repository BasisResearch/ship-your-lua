#!/usr/bin/env python3
"""Round 4, law L4-call: diff the kit's call frames against the generator.

For every call segment of an F1 arm (a segment of `scripts/gen_lua_arms.py`
ending in a `jal` to a SUMMARISED helper), compute mechanically:

* `need`: the registers the generated segments at the return address demand
  as pins (their `SegSt` pre-state, after the generator's liveness pass),
  minus the helper's results (`RESULTS`);
* `hand`: the register set of the frame the kit states for that callee
  (`HFrame` for the soft-int helpers and `luaV_tointeger`; `KFrame` plus the
  `sp` pin `equalobj_sum` returns, for `luaV_equalobj`), read from
  `Lua/Vm/Sim/Kit/Run.lean`;
* `vals`: per frame register, its value at the call composed along every
  path of generated segments from the arm's jump-table target, by
  substituting each segment's post pins into the next one's pre pins. `head`
  means the value the register held at the fetch head (unchanged in the arm).

Prints one block per call site and a summary line. Read-only: generates
nothing.

    python3 abstractions/checks/round4/lcall_frames.py [--ops OP_MOD,OP_EQ]
"""
import argparse
import csv
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts/syi"))
import gen_lua_arms as G          # noqa: E402
import gen_segment                # noqa: E402
import draft_f1_arms as dfa       # noqa: E402

RUN = (ROOT / "Lua/Vm/Sim/Kit/Run.lean").read_text()


def frame_regs(struct):
    m = re.search(rf"def {struct}\.pins.*?:=\s*\[(.*?)\]", RUN, re.S)
    return {f"x{n}" for n in re.findall(r"Register\.x(\d+)", m.group(1))}


HFRAME, KFRAME = frame_regs("HFrame"), frame_regs("KFrame")
HAND = {"__muldi3": HFRAME, "__moddi3": HFRAME, "__divdi3": HFRAME,
        "__hidden___udivdi3": HFRAME, "luaV_tointeger": HFRAME,
        "luaV_equalobj": KFRAME | {"x2"}}
DEFAULT_OPS = sorted(G.SIM_OPS)


def callee_of(g, hi):
    raw = g[hi - 4][0]
    if raw.split()[0] != "jal":
        return None
    return re.search(r"<([^>+]+)>", raw).group(1)


def subst(expr, env, mem):
    expr = re.sub(r"\bv(\d+)\b", lambda m: env.get(f"x{m.group(1)}", f"v{m.group(1)}"), expr)
    return re.sub(r"\bm0\b", mem, expr)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--ops", default=",".join(DEFAULT_OPS))
    ap.add_argument("--full", action="store_true")
    args = ap.parse_args()
    ops = set(args.ops.split(","))
    g = dfa.cfg()
    targets = {r["op"]: int(r["target"], 16)
               for r in csv.DictReader(open(dfa.ARMS_TSV), delimiter="\t")}
    arms, specs, _ = G.collect(ops)
    ems = {}
    for n, (lo, spec, _) in specs.items():
        em = gen_segment.SegmentEmitter(spec)
        em.emit()
        ems[n] = em
    sites = mism = 0
    for op, names in sorted(arms):
        by_lo = {}
        for n in names:
            by_lo.setdefault(specs[n][0], []).append(n)
        calls = {}   # call segment -> list of (env at call) along each path
        # paths from the jump-table target; env: reg -> expression over head values
        head_env = {f"x{r}": "head" for r in range(32)}
        work = [(targets[op], {}, "m0", 0)]
        seen_paths = 0
        while work and seen_paths < 4000:
            pc, env, mem, depth = work.pop()
            for n in by_lo.get(pc, []):
                em = ems[n]
                hi = int(n.split("_")[2], 16)
                post = {r: subst(v, env, mem) for r, v in em.pins}
                # registers not pinned keep their env value (unknown if never pinned)
                nenv = dict(env)
                nenv.update(post)
                nmem = subst(em.mem_expr, env, mem) if em.mem_expr else mem
                if len(nmem) > 400:
                    nmem = f"M{depth + 1}"
                cal = callee_of(g, hi)
                if cal in G.SUMMARISED:
                    calls.setdefault(n, []).append(nenv)
                    # continue at the return: the frame kept, the results fresh
                    if depth < 60 and hi in by_lo:
                        renv = {r: v for r, v in nenv.items() if r in HAND.get(cal, set())}
                        renv.update({r: f"ret_{cal}_{r}" for r in G.RESULTS.get(cal, set())})
                        work.append((hi, renv, f"Mret_{cal}", depth + 1))
                    continue
                m = re.match(r"\(?(0x[0-9a-f]+)#64", em.end_pc)
                if m and depth < 60:
                    nxt = int(m.group(1), 16)
                    if nxt != dfa.FETCH and nxt in by_lo:
                        work.append((nxt, nenv, nmem, depth + 1))
                seen_paths += 1
        for n, envs in sorted(calls.items()):
            hi = int(n.split("_")[2], 16)
            cal = callee_of(g, hi)
            ret_segs = by_lo.get(hi, [])
            need = set().union(*[{p["reg"] for p in specs[m][1]["pins"]} for m in ret_segs]) \
                - G.RESULTS.get(cal, set())
            hand = HAND.get(cal, set())
            sites += 1
            missing, surplus = need - hand, hand - need
            ok = not missing
            mism += 0 if ok and not surplus else 1
            print(f"{op:12s} {n} -> {cal} (return 0x{hi:08x}, {len(envs)} path(s))")
            print(f"    need  {sorted(need, key=lambda r: int(r[1:]))}")
            print(f"    hand  {'= need' if hand == need else sorted(hand, key=lambda r: int(r[1:]))}"
                  + (f"   MISSING {sorted(missing)}" if missing else "")
                  + (f"   SURPLUS {sorted(surplus)}" if surplus else ""))
            for r in sorted(need, key=lambda r: int(r[1:])):
                vals = {e.get(r, f"v{r[1:]}") for e in envs}
                vals = {("head" if v == f"v{r[1:]}" else v) for v in vals}
                full = args.full
                if vals != {"head"}:
                    shown = [v if full or len(v) < 160 else v[:157] + "..." for v in sorted(vals)]
                    print(f"    {r:4s} in-arm: {' | '.join(shown)}")
    print(f"\n{sites} call sites; {mism} with hand != need")


if __name__ == "__main__":
    main()

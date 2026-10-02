#!/usr/bin/env python3
"""Round 4, law L4-loop: every machine loop the remaining F1 arms and their
helpers meet, read off the ELF's disassembly.

A loop is a back edge: a branch or `j` inside one function whose target is
at or below it. For each loop it prints the head, the latch, the body's
instruction count, where the exit test sits (`bottom`: the latch's branch is
the only exit; `top`: an exit branch at the head; `mid`: an exit elsewhere),
the loop-carried registers (written in the body and read at or after the
head before any write), the body's stores and its calls.

Roots: the F1 arms of `luaV_execute` still open (by jump-table target,
`experiments/census/luaV_execute_arms.tsv`; their reach as in
`scripts/draft_f1_arms.py`) and the helper functions named on the command
line or in ROOTS, followed through direct `jal`s (`--depth`, default 0: only
the roots; `-1`: the whole static call graph).

    python3 abstractions/checks/round4/loops.py [--depth N] [--fns a,b]
"""
import argparse
import csv
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "scripts"))
sys.path.insert(0, str(ROOT / "scripts/syi"))
import draft_f1_arms as dfa   # noqa: E402

OBJDUMP = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump"
ELF = ROOT / "c/lua-riscv-htif.elf"
ARMS = ["OP_FORPREP", "OP_IDIV", "OP_IDIVK", "OP_SHL", "OP_SHR", "OP_SHLI", "OP_SHRI", "OP_UNM",
        "OP_EQ", "OP_EQK", "OP_LT", "OP_LE", "OP_CALL", "OP_VARARGPREP", "OP_RETURN",
        "OP_RETURN0", "OP_RETURN1", "OP_LOADNIL", "OP_BANDK", "OP_BORK", "OP_BXORK"]
ROOTS = ["luaV_tointeger", "luaV_tonumber_", "luaV_idiv", "luaV_mod", "luaV_shiftl", "__divdi3",
         "__moddi3", "__hidden___udivdi3", "__umoddi3", "__muldi3", "luaV_equalobj",
         "luaS_eqlngstr", "memcmp", "l_strcmp", "strcmp", "strlen", "strcoll",
         "luaT_adjustvarargs", "luaF_close", "luaF_closeupval", "luaD_precall", "luaD_poscall",
         "luaB_print", "luaT_trybinTM", "luaO_str2num", "l_str2int", "l_str2d", "luaO_tostring",
         "luaS_newlstr", "luaS_hash", "internshrstr", "luaL_tolstring"]
NORET = dfa.NORET | {"abort", "_exit", "luaG_runerror", "luaG_forerror", "luaG_opinterror",
                     "luaG_tointerror", "luaG_ordererror", "luaG_typeerror"}
BR = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz",
      "bgtz", "bgt", "ble", "bgtu", "bleu"}
REG = r"\b(zero|ra|sp|gp|tp|t[0-6]|s[0-9]|s1[01]|a[0-7]|fp)\b"


def disasm():
    syms, ins = {}, {}
    out = subprocess.run([str(OBJDUMP), "-d", "--no-show-raw-insn", "-M", "no-aliases=0",
                          str(ELF)], capture_output=True, text=True).stdout
    cur = None
    for line in out.splitlines():
        m = re.match(r"^([0-9a-f]+) <([^>]+)>:", line)
        if m:
            cur = m.group(2)
            syms.setdefault(cur, int(m.group(1), 16))
            continue
        m = re.match(r"^\s*([0-9a-f]+):\s+(\S+)\s*(.*)$", line)
        if m and cur:
            ins[int(m.group(1), 16)] = (cur, m.group(2), m.group(3))
    return syms, ins


def target(op, args):
    m = re.search(r"\b([0-9a-f]+) <", args)
    return int(m.group(1), 16) if m and (op in BR or op in ("j", "jal")) else None


def rw(op, args):
    """(written, read) register names of one instruction (approximate)."""
    regs = re.findall(REG, args.split("<")[0])
    if op in BR or op.startswith("s") and op in ("sb", "sh", "sw", "sd", "fsd", "fsw"):
        return set(), set(regs)
    if op in ("j",):
        return set(), set()
    if op == "jal":
        return {"ra", "a0", "a1"}, set()
    if op in ("jr", "ret"):
        return set(), set(regs) or {"ra"}
    if not regs:
        return set(), set()
    return {regs[0]}, set(regs[1:])


def succs(a, ins, lo_hi):
    """Intra-procedural successors of the instruction at `a` (a `jal` falls through)."""
    _, op, args = ins[a]
    t = target(op, args)
    if op in BR:
        out = [t, a + 4]
    elif op == "j":
        out = [t]
    elif op == "jal" and args.split("<")[-1].rstrip(">").split("+")[0] in NORET:
        out = []
    elif op in ("jr", "ret", "mret") or (op == "jalr" and args.startswith("zero")):
        out = []
    else:
        out = [a + 4]
    return [x for x in out if x is not None and x in lo_hi]


def natural_loops(entry, nodes, ins, stop=None):
    """Back edges (DFS: an edge to a node on the stack) from `entry` over
    `nodes`, and each one's natural loop body."""
    sg = {a: [x for x in succs(a, ins, nodes) if x != stop] for a in nodes}
    pred = {}
    for a, ss in sg.items():
        for x in ss:
            pred.setdefault(x, []).append(a)
    back, state = [], {}
    stack = [(entry, iter(sg.get(entry, [])))]
    state[entry] = 1
    while stack:
        a, it = stack[-1]
        nxt = next(it, None)
        if nxt is None:
            state[a] = 2
            stack.pop()
            continue
        if state.get(nxt) == 1:
            back.append((nxt, a))
        elif nxt not in state:
            state[nxt] = 1
            stack.append((nxt, iter(sg.get(nxt, []))))
    out = []
    for h, l in back:
        body, work = {h}, [l]
        while work:
            x = work.pop()
            if x not in body:
                body.add(x)
                work += pred.get(x, [])
        out.append((h, l, body, sg))
    return out, set(state)


def describe(h, latch, body, sg, ins):
    exits = sorted(a for a in body for x in sg[a] if x not in body)
    stores, calls, written = [], [], set()
    for a in sorted(body):
        _, op, args = ins[a]
        if op in ("sb", "sh", "sw", "sd"):
            stores.append(f"{op} {args.split('#')[0].strip()}")
        if op in ("jal", "jalr"):
            calls.append(args.split("<")[-1].rstrip(">") if "<" in args else args)
        written |= rw(op, args)[0]
    carried = set()
    for a in sorted(body):
        carried |= rw(*ins[a][1:])[1] & written
    where = ("bottom" if exits == [latch] else "top" if exits == [h] else "mid")
    return (f"  loop head 0x{h:08x} latch 0x{latch:08x} ({len(body)} ins, latch `{ins[latch][1]}`, "
            f"exit {where} @{','.join(hex(e) for e in exits) or '-'})\n"
            f"      carried {sorted(carried)}; stores {stores or '-'}; calls {calls or '-'}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--depth", type=int, default=0)
    ap.add_argument("--fns", default=",".join(ROOTS))
    ap.add_argument("--quiet-loopfree", action="store_true")
    a = ap.parse_args()
    syms, ins = disasm()
    byfn = {}
    for addr, (fn, _, _) in ins.items():
        byfn.setdefault(fn, set()).add(addr)
    # arms
    g = dfa.cfg()
    tgts = {r["op"]: int(r["target"], 16)
            for r in csv.DictReader(open(dfa.ARMS_TSV), delimiter="\t")}
    print("== F1 arms of luaV_execute (inline code, up to the fetch head)")
    for op in ARMS:
        reach = dfa.arm(g, tgts[op])
        ls, _ = natural_loops(tgts[op], reach, ins, stop=dfa.FETCH)
        callees = sorted({ins[x][2].split("<")[-1].rstrip(">") for x in reach
                          if ins[x][1] == "jal"})
        print(f"{op}: {len(reach)} ins, {len(ls)} loop(s); jal -> {', '.join(callees) or '-'}")
        for h, l, body, sg in ls:
            print(describe(h, l, body, sg, ins))
    print("\n== helpers (whole function bodies)")
    todo = [(f, 0) for f in a.fns.split(",")]
    done = set()
    total = {"fns": 0, "loopy": 0, "loops": 0}
    while todo:
        f, d = todo.pop(0)
        if f in done or f not in byfn:
            continue
        done.add(f)
        ls, addrs = natural_loops(syms[f], byfn[f], ins)
        callees = sorted({ins[x][2].split("<")[-1].rstrip(">").split("+")[0] for x in addrs
                          if ins[x][1] == "jal"})
        total["fns"] += 1
        total["loopy"] += bool(ls)
        total["loops"] += len(ls)
        if ls or not a.quiet_loopfree:
            print(f"{f} [{len(addrs)} ins, depth {d}]: {len(ls)} loop(s); "
                  f"jal -> {', '.join(callees) or '-'}")
            for h, l, body, sg in ls:
                print(describe(h, l, body, sg, ins))
        if a.depth < 0 or d < a.depth:
            todo += [(c, d + 1) for c in callees]
    print(f"\n{total['fns']} functions, {total['loopy']} with loops, {total['loops']} back edges")


if __name__ == "__main__":
    main()

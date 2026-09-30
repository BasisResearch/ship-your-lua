#!/usr/bin/env python3
"""Law check (abstraction-discovery step 2), NOT a proof: L-A1, "LuaSem is
the graph of the fuel-indexed interpreter", tested differentially. Random
F1 programs (well-scoped, bounded loops) are run by host lua and by
`luaRun` (the interpreter proved sound for LuaSem); every program must be
AstSupported and the outputs must agree.

    python3 abstractions/checks/graph_law.py [N] [seed]
"""
import json, os, random, subprocess, sys, tempfile
ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
N = int(sys.argv[1]) if len(sys.argv) > 1 else 40
rng = random.Random(int(sys.argv[2]) if len(sys.argv) > 2 else 1)

BIN = ["+", "-", "*", "//", "%", "&", "|", "~", "<<", ">>"]
CMP = ["<", "<=", ">", ">=", "==", "~="]

class G:
    def __init__(s): s.scopes = [[]]; s.n = 0; s.depth = 0; s.loop = 0; s.prot = set()
    def vars(s): return [v for sc in s.scopes for v in sc]
    def fresh(s): s.n += 1; return f"v{s.n}"
    def expr(s, d=0):
        vs = s.vars(); r = rng.random()
        if d > 2 or r < 0.3:
            return rng.choice(vs) if vs and rng.random() < 0.6 else str(rng.randint(-9, 99))
        if r < 0.75:
            op = rng.choice(BIN); b = s.expr(d + 1)
            if op in ("//", "%"): b = f"({b}) * 0 + {rng.randint(1, 7)}"   # nonzero divisor
            if op in ("<<", ">>"): b = str(rng.randint(0, 70))
            return f"({s.expr(d + 1)} {op} {b})"
        if r < 0.85: return f"(-{s.expr(d + 1)})"
        return f"({s.expr(d + 1)} {rng.choice(['and', 'or'])} {s.expr(d + 1)})"
    def cond(s):
        c = f"{s.expr(1)} {rng.choice(CMP)} {s.expr(1)}"
        return f"not ({c})" if rng.random() < 0.2 else c
    def block(s, k):
        s.scopes.append([]); out = []
        for _ in range(k): out += s.stat()
        s.scopes.pop(); return out
    def stat(s):
        s.depth += 1; r = rng.random(); vs = s.vars(); out = []
        if s.depth > 3 or r < 0.3:
            v = s.fresh(); out = [f"local {v} = {s.expr()}"]; s.scopes[-1].append(v)
        elif r < 0.45 and [v for v in vs if v not in s.prot]:
            out = [f"{rng.choice([v for v in vs if v not in s.prot])} = {s.expr()}"]
        elif r < 0.6:
            out = [f"print({', '.join(s.expr() for _ in range(rng.randint(1, 3)))})"]
        elif r < 0.7:
            out = [f"if {s.cond()} then"] + s.block(2) + ["else"] + s.block(1) + ["end"]
        elif r < 0.8:
            i = s.fresh(); s.scopes.append([i]); s.loop += 1
            body = s.block(2); s.loop -= 1; s.scopes.pop()
            out = [f"for {i} = {rng.randint(-3, 3)}, {rng.randint(-3, 6)}, {rng.choice([1, 2, -1, 3])} do"] + body + ["end"]
        elif r < 0.9:
            c = s.fresh(); out = [f"local {c} = 0"]; s.scopes[-1].append(c); s.loop += 1; s.prot.add(c)
            body = s.block(2); s.loop -= 1
            skip = ["if " + s.cond() + " then goto continue end"] if rng.random() < 0.4 else []
            lab = ["::continue::"] if skip else []
            out += [f"while {c} < {rng.randint(1, 5)} do", f"{c} = {c} + 1"] + skip + body + lab + ["end"]
        elif s.loop:
            out = [f"if {s.cond()} then break end"]
        else:
            c = s.fresh(); out = [f"local {c} = 0"]; s.scopes[-1].append(c); s.prot.add(c)
            out += ["repeat", f"{c} = {c} + 1"] + s.block(1) + [f"until {c} >= {rng.randint(1, 4)}"]
        s.depth -= 1; return out

def main():
    tmp = tempfile.mkdtemp(prefix="graphlaw")
    names, expected = [], []
    for i in range(N):
        g = G(); src = "\n".join(g.block(rng.randint(4, 9)) + [f"print({' , '.join(g.vars()[:3]) or '0'})"]) + "\n"
        f = os.path.join(tmp, f"p{i}.lua"); open(f, "w").write(src)
        try:
            r = subprocess.run([os.path.join(ROOT, "c/lua"), f], capture_output=True, text=True, timeout=10)
        except subprocess.TimeoutExpired:
            print("timeout (generator bug)", f); continue
        if r.returncode != 0: continue          # runtime error (e.g. arithmetic on a boolean): skip
        out = os.path.join(tmp, f"P{i}.lean")
        g2 = subprocess.run([sys.executable, os.path.join(ROOT, "scripts/gen_ast.py"), f, "--name", f"p{i}", "-o", out],
                            capture_output=True, text=True)
        if g2.returncode != 0: print("parse failure", f, g2.stderr[:200]); continue
        names.append((i, out)); expected.append(r.stdout)
    runner = os.path.join(tmp, "Run.lean")
    with open(runner, "w") as fh:
        fh.write("import Lua.Ast.Exec\nimport Lua.Vm.Host\n")
        body = []
        for (i, out), exp in zip(names, expected):
            src = open(out).read().split("\n", 1)[1]    # drop its import line
            body.append(src)
        fh.write("\n".join(body))
        fh.write("\nopen Lua.Ast Lua.Vm Lua.Programs in\ndef cases : List (String × Chunk × String) := [\n")
        fh.write(",\n".join(f"  (\"p{i}\", p{i}, {json.dumps(exp)})" for (i, _), exp in zip(names, expected)))
        fh.write("]\n\nopen Lua.Ast Lua.Vm in\ndef main : IO UInt32 := do\n  let mut bad := 0\n"
                 "  for (n, c, exp) in cases do\n"
                 "    if !(supBlock ⟨[], false, [], []⟩ false c) then IO.println s!\"{n}: not AstSupported\"; bad := bad + 1\n"
                 "    let got := luaRun binaryHost 200000 c\n"
                 "    if got != some exp then IO.println s!\"{n}: MISMATCH {got}\"; bad := bad + 1\n"
                 f"  IO.println s!\"graph law: {len(names)} programs, {{bad}} failures\"\n  pure (if bad == 0 then 0 else 1)\n")
    r = subprocess.run(["lake", "env", "lean", "--run", runner], cwd=ROOT, capture_output=True, text=True)
    print(r.stdout[-3000:], r.stderr[-2000:])
    print("programs in", tmp)
    sys.exit(r.returncode)

main()

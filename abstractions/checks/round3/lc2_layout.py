#!/usr/bin/env python3
"""Round 3, law L-C2 (layout law), checked against the ELF.

L-C2: two F1 arms whose opcodes share a kernel combinator (`opKernel`,
Lua/Bytecode/Semantics.lean) differ only in their compiled branch layout, so
one proof keyed by the combinator's decision tree covers all of them.

Method (read-only; no lake):
  * canonical forms from the round-2 falsifier canonicaliser
    (experiments/a1-falsifiers/canon.py: symbolic execution from the dispatch
    head, invariant under register renaming, scheduling, branch polarity and
    block layout), re-hashed at progressively coarser abstraction levels:
      L0 exact            canon.py's root hash
      L1 modALU           canon.py level 1 (add/sub/and/or/xor/__muldi3 -> ALU)
      L2 modALU+cmp       canon.py level 2 (compare predicates -> CMP,
                          branch successors unordered)
      L3 +params          L2, and every constant -> K, every pure ALU/shift/slt
                          op -> ALU: "the ALU op, immediates/constants and the
                          compare predicate abstracted to a parameter"
      L4 +helper leaf     L3, and every pure libgcc/libm helper call -> HELPER
      L3p pure values  L3, and every maximal pure computation -> F(its non-pure
                          leaves: loads, calls, inputs): values and predicates are
                          parameters, operand access (which slot, K via 0(sp)) stays
      L4p              L3p with the pure helpers (__muldi3, __divdi3, ...) inside F
      L5 skeleton+calls   only the decision tree: branch nodes (unordered
                          successors), exits (kind, #stores), and the names of
                          the non-pure calls on the path (memory epochs)
      L6 skeleton         L5 without call names: the bare branch/exit shape
  * P1, P3p, P4p, P5: L1, L3p, L4p, L5 of the F1-pruned tree (prune_dom:
    every TValue tag byte ranges over `ValRepr`'s tags, no float; branches
    decided by one tag are evaluated per tag value and dead successors
    dropped. The float subtrees are exactly what the proved arms discharge
    with `ValRepr.ne_float`).
  * raw layout: the arm's conditional-branch mnemonics in address order (what
    gen_lua_arm.py's polarity strings and its TAG_TEST/FLOAT_TEST/ARITH_*
    layout dicts encode).
  * per combinator (and per combinator + operand form) the number of distinct
    classes at each level and of raw layouts. L-C2 predicts 1 class per
    combinator at some level that still distinguishes combinators, with
    more than one raw layout.
  * hand cost by category, from git: for every arm commit, the added
    non-blank non-comment lines of the hand files, split into
      row     ARMS/ARMS2 table rows (+ SIM_OPS in gen_lua_arms.py)
      layout  branch-layout data (ARITH_RR/BIT/RK, CMPI, TAG_TEST, FLOAT_TEST,
              SETTAG, TAGSLOT)
      kind    generator template code (PRE2/FACTS2/paths, walkers, ...)
      lean    hand Lean (Close/StepK/Step/Rel/Mem/Entry/Bits)

usage: python3 abstractions/checks/round3/lc2_layout.py [--json OUT]
Writes lc2_arms.tsv next to this script and prints the summary.
"""
import os, sys, re, json, ast, hashlib, subprocess, collections

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(os.path.dirname(HERE)))
sys.path.insert(0, os.path.join(REPO, "experiments/a1-falsifiers"))
import canon  # noqa: E402

# ---------------------------------------------------------------- kernels
# opcode -> (combinator, operand form / primitive family), read off opKernel
KERNEL = {}
for ops, comb, form in [
    ("MOVE", "setR:move", "reg"), ("LOADI", "setR:move", "imm"), ("LOADK", "setR:move", "k"),
    ("LOADFALSE LOADTRUE", "setR:move", "imm"), ("LFALSESKIP", "setR:move", "imm+skip"),
    ("GETTABUP", "setR:move", "upval-lookup"),
    ("LOADNIL", "setNils", "range"),
    ("ADD SUB MUL BAND BOR BXOR", "opArith", "RR"), ("MOD IDIV", "opArith", "RR/div"),
    ("SHL SHR", "opArith", "RR/shift"),
    ("ADDK SUBK MULK BANDK BORK BXORK", "opArith", "RK"), ("MODK IDIVK", "opArith", "RK/div"),
    ("ADDI", "opArith", "RI"), ("SHRI SHLI", "opArith", "RI/shift"),
    ("MMBIN", "mmbin", "RR"), ("MMBINI", "mmbin", "RI"), ("MMBINK", "mmbin", "RK"),
    ("UNM BNOT", "setR:δ", "unary-num"), ("NOT", "setR:δ", "unary-truth"),
    ("JMP", "jump", "sJ"), ("VARARGPREP", "jump", "adjustvarargs"),
    ("EQ", "docondjump", "RR/eq"), ("LT LE", "docondjump", "RR/order"),
    ("EQK", "docondjump", "RK/eq"), ("EQI", "docondjump", "RI/eq"),
    ("LTI LEI GTI GEI", "docondjump", "RI/order"), ("TEST", "docondjump", "truth"),
    ("TESTSET", "testsetK", "truth"), ("FORPREP", "forprepK", ""), ("FORLOOP", "forloopK", ""),
    ("CALL", "callK", ""), ("RETURN RETURN0 RETURN1", "final", "")]:
    for o in ops.split():
        KERNEL[o] = (comb, form)

# ---------------------------------------------------------------- abstraction levels
ALU3 = {"add", "sub", "and", "or", "xor", "addw", "subw", "sll", "srl", "sra", "sllw", "srlw",
        "sraw", "call:__muldi3", "ALU", "ALUw"}
CMP3 = {"EQ", "LT", "LTU", "slt", "sltu"}


def rehash(T, root, level, cache):
    """L3 (level 3) and L4 (level 4) hashes over canon's term DAG."""
    def go(h):
        if not (isinstance(h, str) and h in T.t):
            return h
        key = h
        if key in cache:
            return cache[key]
        op, args = T.t[h]
        if op == "c":
            r = "K"
            cache[key] = r
            return r
        aop = op
        if op in ALU3:
            aop = "ALU"
        elif op in CMP3:
            aop = "CMP"
        elif op.startswith("call:"):
            base = op[5:]
            aop = "FALU" if base in ("__adddf3", "__subdf3", "__muldf3", "__divdf3") else op
            if level >= 4:
                aop = "HELPER"
            if base in ("__gedf2", "__ledf2", "__eqdf2", "__ltdf2", "__gtdf2", "__unorddf2"):
                aop = "FCMP"

        def amap(x):
            if isinstance(x, str) and x in T.t:
                return go(x)
            if isinstance(x, tuple):
                return tuple(amap(y) for y in x)
            return x
        ah = [amap(x) for x in args]
        if op == "mem":
            ah[1] = tuple(sorted(ah[1], key=str))
        elif op == "call":
            ah[3] = tuple(sorted(ah[3], key=str))
        elif op == "exit":
            ah[2] = (ah[2][0], tuple(sorted(ah[2][1], key=str)))
        if aop in ("ALU", "CMP", "FALU", "FCMP", "HELPER") or op in canon.COMMUT:
            ah = sorted(ah, key=str)
        if op == "br":
            ah = [ah[0]] + sorted(ah[1:], key=str)
        r = hashlib.sha1(repr((aop, tuple(ah))).encode()).hexdigest()[:16]
        cache[key] = r
        return r
    return go(root)


PURE_OPS = ALU3 | CMP3 | {"ext", "c", "mul", "div", "rem"}


def rehash_pure(T, root, helpers_pure, cache):
    """L3p / L4p: every maximal pure computation (ALU, shifts, compares,
    extensions, constants; and at L4p the pure libgcc/libm helpers) is replaced
    by F(the set of its non-pure leaves): the decision tree keyed by WHAT is
    loaded, tested, called and stored, with every value a parameter function
    of its inputs. Operand access forms stay (a `K` operand's address has the
    `ld 0(sp)` leaf)."""
    def pure(op):
        return op in PURE_OPS or (op.startswith("call:") and helpers_pure)

    def leaves(h, acc, seen):
        if not (isinstance(h, str) and h in T.t) or h in seen:
            return
        seen.add(h)
        op, args = T.t[h]
        if pure(op):
            for a in args:
                leaves(a, acc, seen)
        else:
            acc.add(go(h))

    def go(h):
        if not (isinstance(h, str) and h in T.t):
            return h
        if h in cache:
            return cache[h]
        op, args = T.t[h]
        if pure(op):
            acc = set()
            leaves(h, acc, set())
            r = hashlib.sha1(repr(("F", tuple(sorted(acc)))).encode()).hexdigest()[:16]
            cache[h] = r
            return r

        def amap(x):
            if isinstance(x, str) and x in T.t:
                return go(x)
            if isinstance(x, tuple):
                return tuple(amap(y) for y in x)
            return x
        ah = [amap(x) for x in args]
        aop = op
        if op == "mem":
            ah[1] = tuple(sorted(ah[1], key=str))
        elif op == "call":
            ah[3] = tuple(sorted(ah[3], key=str))
        elif op == "exit":
            ah[2] = (ah[2][0], tuple(sorted(ah[2][1], key=str)))
        elif op.startswith("call:"):
            ah = sorted(ah, key=str)
        if op == "br":
            ah = [ah[0]] + sorted(ah[1:], key=str)
        r = hashlib.sha1(repr((aop, tuple(ah))).encode()).hexdigest()[:16]
        cache[h] = r
        return r
    return go(root)


FLOAT_TAG = 0x13   # LUA_VNUMFLT


def prune_f1(T, root):
    """The tree under F1's value domain: no register or constant holds a
    float (`ValRepr` has no tag-19 case; `ValRepr.ne_float`), so at every
    branch `EQ(x, 19)` only the not-equal successor is live."""
    memo = {}
    c19 = T.const(FLOAT_TAG)

    def go(h):
        if h in memo:
            return memo[h]
        op, args = T.t[h]
        if op == "br":
            cond, t, f = args
            cop, cargs = T.t[cond]
            if cop == "EQ" and c19 in cargs[:2]:
                r = go(f)
            else:
                r = T.mk("br", cond, go(t), go(f))
        else:
            r = h
        memo[h] = r
        return r
    return go(root)


# `ValRepr`'s tags (Lua/Vm/Sim/Rel.lean, Layout.lean): nil variants (t % 16 = 0),
# false, true, integer, short/long string, light C function. No float (19).
F1_TAGS = frozenset({0, 16, 32, 1, 17, 3, 68, 84, 22})
M64 = (1 << 64) - 1


HEAD_CONST = {"s2": 3, "s1": 81}   # VmRel's Pins: s2 = LUA_VNUMINT, s1 = 81


def addr_roots(T, h, acc):
    op, args = T.t[h]
    if op == "in":
        acc.add(args[0])
    elif op == "ld":
        b, off = canon.split_addr(T, args[2])
        if T.t[b] == ("in", ("sp",)) and off == 0:
            acc.add("k")
        elif T.t[b] == ("in", ("s11",)) and off == 0:
            acc.add("ins")     # the fetched instruction (lw s4,0(s11))
        else:
            acc.add("ld")
    elif op != "c":
        for a in args:
            if isinstance(a, str) and a in T.t:
                addr_roots(T, a, acc)


def is_tag_load(T, h):
    """a TValue tag byte of a Lua register (address from `base`, s9) or of a
    constant (address from `k`, the `ld 0(sp)`)"""
    op, args = T.t[h]
    if op != "ld" or args[0] != 1:
        return False
    _, off = canon.split_addr(T, args[2])
    if off % 16 != 8:
        return False
    acc = set()
    addr_roots(T, args[2], acc)
    return acc <= {"s9", "ins", "k", "sp@0"} and bool(acc & {"s9", "k", "sp@0"})


def ev(T, h, env):
    """value of a pure term under env (tag term -> value); None if unknown"""
    if h in env:
        return env[h]
    op, args = T.t[h]
    if op == "in" and args[0] in HEAD_CONST:
        return HEAD_CONST[args[0]]
    if op == "c":
        return args[0] & M64
    if op == "ext":
        w, signed, v = args
        x = ev(T, v, env)
        if x is None:
            return None
        x &= (1 << (8 * w)) - 1
        return (canon.sx(x, 8 * w) & M64) if signed else x
    if op in ("add", "sub", "and", "or", "xor", "sll", "srl", "sra", "slt", "sltu",
              "addw", "subw", "sllw", "srlw", "sraw"):
        a, b = (ev(T, x, env) for x in args)
        if a is None or b is None:
            return None
        return T.cval(canon.ev_alu(T, op, T.const(a), T.const(b))) & M64
    return None


def tag_terms(T, h, acc):
    op, args = T.t[h]
    if is_tag_load(T, h):
        acc.add(h)
        return
    if op in ("c",) or (op == "in" and args[0] in HEAD_CONST):
        return
    if op in ("ld", "in", "clob", "ret0", "ret1") or op.startswith("call"):
        acc.add(None)   # depends on something other than a tag
        return
    for a in args:
        if isinstance(a, str) and a in T.t:
            tag_terms(T, a, acc)


def prune_dom(T, root):
    """The tree under F1's value domain: every TValue tag byte a path tests
    (an `lbu` at offset 8) ranges over `ValRepr`'s tags; a branch whose
    condition depends on one tag is evaluated for each remaining tag value,
    and a successor with no value left is dead. Subsumes prune_f1."""
    def go(h, dom):
        op, args = T.t[h]
        if op != "br":
            return h
        cond, t, f = args
        pred, a, b = T.t[cond][0], T.t[cond][1][0], T.t[cond][1][1]
        acc = set()
        tag_terms(T, a, acc); tag_terms(T, b, acc)
        if None in acc or len(acc) != 1:
            return T.mk("br", cond, go(t, dom), go(f, dom))
        (x,) = acc
        vals = dom.get(x, F1_TAGS)
        yes, no = set(), set()
        for v in vals:
            va, vb = ev(T, a, {x: v}), ev(T, b, {x: v})
            r = {"EQ": va == vb, "LT": canon.sx(va) < canon.sx(vb), "LTU": va < vb}[pred]
            (yes if r else no).add(v)
        if not yes:
            return go(f, {**dom, x: frozenset(no)})
        if not no:
            return go(t, {**dom, x: frozenset(yes)})
        return T.mk("br", cond, go(t, {**dom, x: frozenset(yes)}), go(f, {**dom, x: frozenset(no)}))
    return go(root, {})


def calls_of_mem(T, m):
    """names of the non-pure calls that opened the epochs of memory term m"""
    out = []
    seen = set()

    def go(h):
        if not (isinstance(h, str) and h in T.t) or h in seen:
            return
        seen.add(h)
        op, args = T.t[h]
        if op == "call":
            out.append(args[0].split(".")[0])
        for a in args:
            if isinstance(a, tuple):
                for y in a:
                    go(y) if isinstance(y, str) else None
            elif isinstance(a, str):
                go(a)
    go(m)
    return tuple(sorted(set(out)))


def skeleton(T, root, with_calls):
    memo = {}

    def go(h):
        if h in memo:
            return memo[h]
        op, args = T.t[h]
        if op == "br":
            _, t, f = args
            r = ("br",) + tuple(sorted([go(t), go(f)], key=repr))
        elif op == "exit":
            kind, outs, mem = args
            nst = len(mem[1]) if isinstance(mem, tuple) else 0
            k = kind[0] if kind[0] in ("head", "ret", "reentry", "indirect") else kind
            r = ("exit", k, nst) + ((calls_of_mem(T, mem[0] if isinstance(mem, tuple) else mem),)
                                    if with_calls else ())
            if with_calls and kind[0] in ("noreturn", "tail"):
                r = r + (kind[1],)
        elif op == "loop":
            r = ("loop", args[0])
        else:
            r = (op,)
        memo[h] = hashlib.sha1(repr(r).encode()).hexdigest()[:16]
        return memo[h]
    return go(root)


def branches(T, root):
    seen, n = set(), 0

    def go(h):
        nonlocal n
        if h in seen:
            return
        seen.add(h)
        op, args = T.t[h]
        if op == "br":
            n += 1
            go(args[1]); go(args[2])
    go(root)
    return n


def helper_calls(T, root):
    """pure helpers and non-pure callees mentioned anywhere under root"""
    pure, impure, seen = set(), set(), set()

    def go(x):
        if isinstance(x, tuple):
            for y in x:
                go(y)
            return
        if not (isinstance(x, str) and x in T.t) or x in seen:
            return
        seen.add(x)
        op, args = T.t[x]
        if op.startswith("call:"):
            pure.add(op[5:])
        if op == "call":
            impure.add(args[0].split(".")[0])
        if op == "exit" and args[0][0] in ("noreturn", "tail"):
            impure.add(args[0][1].split(".")[0])
        go(args)
    go(root)
    return sorted(pure), sorted(impure)


def raw_layout(ctx, op):
    S = canon.arm_insts(ctx, op)
    return tuple(ctx["by_addr"][a].mn for a in sorted(S) if ctx["dec"][a].kind == "br")


# ---------------------------------------------------------------- git accounting
GEN = "scripts/gen_lua_arm.py"
LEAN = ["Lua/Vm/Sim/Close.lean", "Lua/Vm/Sim/StepK.lean", "Lua/Vm/Sim/Step.lean",
        "Lua/Vm/Sim/Rel.lean", "Lua/Vm/Sim/Mem.lean", "Lua/Vm/Sim/Entry.lean", "Lua/Vm/Sim/Bits.lean"]
ROWS = {"ARMS", "ARMS2"}
LAYOUT = {"ARITH_RR", "ARITH_BIT", "ARITH_RK", "CMPI", "TAG_TEST", "FLOAT_TEST", "SETTAG", "TAGSLOT"}
OPERAND = {"ARITH_PRE", "ARITH_FACTS", "arith_pre", "arith_facts", "KFACTS", "KPARAM", "KLOAD", "NORM",
           "S_A", "S_I", "SB", "NLT"}
INFRA = {"walk", "chain2", "subst", "get2", "fix_pin", "x27_to", "x21_trap", "pins2", "done2",
         "close_skip", "wrap", "seg_module", "_SEG_MOD", "render", "render_arm2", "render_arm", "main",
         "chain", "targets", "pre2", "facts2", "indent", "gtag", "tag_guard", "float_guard", "CANON",
         "PINS", "_VAR", "pin_regs", "post_regs", "n_hyps", "get", "OUT", "HEADER", "HEAD", "Expr",
         "Import", "ImportFrom", "ROOT", "If", "?"}
# commit -> arms it proves (Lean opcode names); relation/setup commits are not charged
ARM_COMMITS = [
    ("c9ba3ef", ["MOVE", "LOADI", "JMP"]),
    ("8a41a25", ["ADD", "EQI", "FORLOOP"]),       # bake-off 2 hand setup (StepK, Close)
    ("684a56e", ["ADD", "EQI", "FORLOOP"]),
    ("791175d", ["SUB"]), ("c089fc8", ["ADDI"]), ("57422fb", ["ADDK", "SUBK"]),
    ("a7380f0", ["BAND", "BOR", "BXOR"]), ("3079c33", ["LTI", "GTI", "LEI", "GEI"]),
    ("c031ca4", ["LOADTRUE", "LOADFALSE", "LFALSESKIP", "LOADK"]), ("a8957c6", ["BNOT"]),
    ("8358d37", ["NOT", "TEST", "TESTSET"])]


def git(*a):
    return subprocess.run(["git", "-C", REPO] + list(a), capture_output=True, text=True).stdout


def code_line(l):
    s = l.strip()
    return bool(s) and not s.startswith("#") and not s.startswith("--")


def owner_map(src):
    """line number -> top-level name of gen_lua_arm.py"""
    own = {}
    try:
        t = ast.parse(src)
    except SyntaxError:
        return own
    for n in t.body:
        nm = getattr(n, "name", None)
        if nm is None and isinstance(n, ast.Assign) and hasattr(n.targets[0], "id"):
            nm = n.targets[0].id
        for i in range(n.lineno, (n.end_lineno or n.lineno) + 1):
            own[i] = nm or type(n).__name__
    return own


def added_lines(commit, path):
    """(new line number, text) of the lines the commit adds to path"""
    diff = git("show", "--format=", "-U0", commit, "--", path)
    out, ln = [], None
    for l in diff.splitlines():
        m = re.match(r"@@ -\S+ \+(\d+)(?:,(\d+))? @@", l)
        if m:
            ln = int(m.group(1))
            continue
        if ln is None or l.startswith("+++") or l.startswith("---"):
            continue
        if l.startswith("+"):
            out.append((ln, l[1:]))
            ln += 1
        elif not l.startswith("-"):
            ln += 1
    return out


def lean_code(lines):
    """added Lean code lines, doc/comment blocks removed"""
    n, inc = 0, False
    for _, l in lines:
        s = l.strip()
        if inc:
            if "-/" in s:
                inc = False
            continue
        if s.startswith("/-"):
            inc = "-/" not in s
            continue
        if code_line(s):
            n += 1
    return n


def commit_costs():
    rows = []
    for c, arms in ARM_COMMITS:
        cat = collections.Counter()
        src = git("show", f"{c}:{GEN}")
        own = owner_map(src)
        # docstring lines inside functions count as comments: approximate by
        # dropping lines of triple-quoted text that are not Lean templates is
        # not possible; templates ARE the Lean text, so count every code line
        for ln, l in added_lines(c, GEN):
            if not code_line(l):
                continue
            nm = own.get(ln, "?")
            cat["row" if nm in ROWS else "layout" if nm in LAYOUT else "operand" if nm in OPERAND
                else "infra" if nm in INFRA else "kind"] += 1
        for ln, l in added_lines(c, "scripts/gen_lua_arms.py"):
            if code_line(l) and ("OP_" in l):
                cat["row"] += 1
        for p in LEAN:
            k = lean_code(added_lines(c, p))
            if k:
                cat["lean"] += k
        rows.append((c, arms, dict(cat)))
    return rows


# ---------------------------------------------------------------- main
def main():
    ctx = canon.context()
    T = canon.Terms()
    ops = canon.armlib.f1_ops()
    proved = {}
    import importlib.util
    spec = importlib.util.spec_from_file_location("gla", os.path.join(REPO, "scripts/gen_lua_arm.py"))
    src = open(os.path.join(REPO, "scripts/gen_lua_arm.py")).read()
    for m in re.finditer(r'"OP_([A-Z0-9]+)": \("[A-Z0-9]+", "\w+", "(\w+)"', src):
        proved[m.group(1)] = m.group(2)
    ledger = {}
    for l in open(os.path.join(REPO, "abstractions/ledger/a1-arm-sim.tsv")):
        if l.startswith("#") or not l.strip():
            continue
        f = l.rstrip("\n").split("\t")
        ledger[f[0]] = float(f[1])
    c3, c4, c3p, c4p = {}, {}, {}, {}
    A = {}
    for op in ops:
        W, root, trunc = canon.canon_arm(ctx, T, op)
        assert not trunc, op
        pure, impure = helper_calls(T, root)
        pr = prune_dom(T, root)
        A[op] = dict(
            comb=KERNEL[op][0], form=KERNEL[op][1], kind=proved.get(op, ""),
            L0=root, L1=T.alu_hash(root, 1), L2=T.alu_hash(root, 2),
            L3=rehash(T, root, 3, c3), L4=rehash(T, root, 4, c4),
            L3p=rehash_pure(T, root, False, c3p), L4p=rehash_pure(T, root, True, c4p),
            L5=skeleton(T, root, True), L6=skeleton(T, root, False),
            P1=T.alu_hash(pr, 1), P3p=rehash_pure(T, pr, False, c3p), P4p=rehash_pure(T, pr, True, c4p),
            P5=skeleton(T, pr, True), Pbr=branches(T, pr), Ppure=helper_calls(T, pr)[0],
            Pcall=helper_calls(T, pr)[1],
            layout=raw_layout(ctx, op), nbr=branches(T, root),
            pure=pure, impure=impure, cost=ledger.get(op))
    LV = ["L0", "L1", "L2", "L3", "L4", "L3p", "L4p", "L5", "L6", "P1", "P3p", "P4p", "P5"]
    res = {"n": len(ops), "levels": {}, "per_comb": {}, "per_form": {}}
    for lv in LV + ["layout"]:
        res["levels"][lv] = len({A[o][lv] for o in ops})
    # per combinator
    for key in ("comb", "form2"):
        groups = collections.defaultdict(list)
        for o in ops:
            g = A[o]["comb"] if key == "comb" else A[o]["comb"] + "/" + A[o]["form"]
            groups[g].append(o)
        out = {}
        for g, os_ in sorted(groups.items()):
            out[g] = dict(arms=os_, **{lv: len({A[o][lv] for o in os_}) for lv in LV + ["layout"]})
        res["per_comb" if key == "comb" else "per_form"] = out
    # the finest level at which each combinator is one class
    def finest(os_):
        for lv in LV:
            if len({A[o][lv] for o in os_}) == 1:
                return lv
        return "none"
    for g, d in res["per_comb"].items():
        d["one_class_at"] = finest(d["arms"])
    for g, d in res["per_form"].items():
        d["one_class_at"] = finest(d["arms"])
    # does a level still separate combinators? (classes shared across combinators)
    for lv in LV:
        cl = collections.defaultdict(set)
        for o in ops:
            cl[A[o][lv]].add(A[o]["comb"])
        res.setdefault("cross_comb", {})[lv] = sorted(
            [sorted(o for o in ops if A[o][lv] == h) for h, cs in cl.items() if len(cs) > 1])
    res["commits"] = commit_costs()
    # write the arm table
    with open(os.path.join(HERE, "lc2_arms.tsv"), "w") as f:
        f.write("op\tcombinator\tform\tgen_kind\tledger_hand\tbranches\t" + "\t".join(LV)
                + "\traw_layout\tpure_helpers\tcallees\tF1_branches\tF1_pure_helpers\tF1_callees\n")
        for o in ops:
            a = A[o]
            f.write("\t".join([o, a["comb"], a["form"], a["kind"], "" if a["cost"] is None else str(a["cost"]),
                               str(a["nbr"])] + [a[lv] for lv in LV]
                              + [" ".join(a["layout"]), ",".join(a["pure"]), ",".join(a["impure"]),
                                 str(a["Pbr"]), ",".join(a["Ppure"]), ",".join(a["Pcall"])]) + "\n")
    # summary
    print(f"{len(ops)} F1 opcodes (Lua/Fragment.lean)")
    print("classes:", {lv: res["levels"][lv] for lv in LV + ["layout"]})
    print("combinators:", len(res["per_comb"]), " combinator+form:", len(res["per_form"]))
    for title, tab in (("per combinator", res["per_comb"]), ("per combinator+form", res["per_form"])):
        print(f"\n{title}: arms | classes L0..L6 | raw layouts | one class at")
        for g, d in tab.items():
            print(f"  {g:28s} {len(d['arms']):2d} | " + " ".join(str(d[lv]) for lv in LV)
                  + f" | {d['layout']} | {d['one_class_at']}  {' '.join(d['arms'])}")
    print("\nclasses spanning several combinators:")
    for lv in LV:
        print(f"  {lv}: {res['cross_comb'][lv]}")
    print("\nhand lines per arm commit (row / layout / kind / lean):")
    tot = collections.Counter()
    for c, arms, cat in res["commits"]:
        tot.update(cat)
        print(f"  {c} {','.join(arms):34s} {cat}")
    print("  total", dict(tot))
    # ---- ledger order: was each proved arm a new tree, a new layout, or a row?
    KEY = "P3p"
    order = [l.split("\t")[0] for l in open(os.path.join(REPO, "abstractions/ledger/a1-arm-sim.tsv"))
             if l.strip() and not l.startswith("#")]
    seen_tree, seen_lay, seen_kind = set(), set(), set()
    cat_cost = collections.defaultdict(list)
    print(f"\nproved arms in ledger order (tree = {KEY} class of the F1-pruned tree):")
    for o in order:
        a = A[o]
        t, lay = a[KEY], (a[KEY], a["layout"])
        c = "new-tree" if t not in seen_tree else "new-layout" if lay not in seen_lay else "row"
        k = "new-kind" if a["kind"] not in seen_kind else "same-kind"
        seen_tree.add(t); seen_lay.add(lay); seen_kind.add(a["kind"])
        cat_cost[c].append(a["cost"])
        a["ledger_cat"] = c
        print(f"  {o:11s} {a['kind']:9s} {k:9s} {c:10s} {a['cost']}")
    for c, v in cat_cost.items():
        print(f"  {c:10s} n={len(v):2d} total={sum(v):6.1f} mean={sum(v)/len(v):5.1f}")
    res["ledger_cat"] = {c: (len(v), sum(v)) for c, v in cat_cost.items()}
    print(f"\nunproved arms: predicted category against the proved set ({KEY}):")
    for o in ops:
        a = A[o]
        if a["cost"] is not None:
            continue
        pure_calls = [h for h in a["Ppure"]]
        need = sorted(set(pure_calls) | set(a["Pcall"]))
        if a["comb"] == "final":
            c = "not sim-shaped (Final clause)"
        elif a[KEY] in seen_tree:
            c = "row" if (a[KEY], a["layout"]) in seen_lay else "new-layout"
        else:
            c = "new-tree"
        a["pred"] = c
        print(f"  {o:11s} {a['comb'] + '/' + a['form']:24s} {c:12s} F1-branches={a['Pbr']:3s} callees={need}"
              .replace("F1-branches=" + a["Pbr"], "F1-branches=" + str(a["Pbr"])) if isinstance(a["Pbr"], str)
              else f"  {o:11s} {a['comb'] + '/' + a['form']:24s} {c:12s} F1-branches={a['Pbr']:3d} callees={need}")
    print(f"\nmulti-arm {KEY} trees: arms | combinators | raw layouts")
    trees = collections.defaultdict(list)
    for o in ops:
        trees[A[o][KEY]].append(o)
    for h, os_ in sorted(trees.items(), key=lambda kv: kv[1]):
        if len(os_) > 1:
            print(f"  {' '.join(os_):34s} | {sorted({A[o]['comb'] for o in os_})} | "
                  f"{len({A[o]['layout'] for o in os_})}")
    tr = {A[o][KEY] for o in ops if A[o]["comb"] != "final"}
    print(f"\ndistinct {KEY} trees over the {sum(1 for o in ops if A[o]['comb'] != 'final')} sim-shaped arms: {len(tr)};"
          f" over the 25 proved: {len({A[o][KEY] for o in order})}")
    if "--json" in sys.argv:
        json.dump(dict(res, arms=A), open(sys.argv[sys.argv.index("--json") + 1], "w"), indent=1, default=list)
    return A, res


if __name__ == "__main__":
    main()

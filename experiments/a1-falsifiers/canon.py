#!/usr/bin/env python3
"""F1 (candidate C8): canonical forms of the luaV_execute opcode arms, invariant
under register renaming, instruction scheduling, branch polarity and block
layout.  Read-only over c/lua-riscv-htif.elf.

Method (one arm):
  * Start at the dispatch head (`lw s4,0(s11)`) with every register an input
    term `in(r)`, run the head symbolically to the `jr`, then continue at the
    arm's jump-table target.  So the arm's inputs are head inputs (s11 = pc,
    memory), and `i`, `pc+1` are terms over them.
  * Symbolic execution with hash-consed terms (structural SHA-1): temporaries
    disappear (renaming invariance: only the dispatch-head register interface
    is named); pure ops are a DAG (scheduling invariance); commutative ops sort
    their arguments by hash; constants fold; `add(add(x,c1),c2)` folds.
  * Memory: calls to non-pure functions are barriers that open a new epoch;
    within an epoch stores form a set; a load's memory argument is the epoch
    plus the stores of the epoch that may alias it (same width and not
    provably disjoint; sp-relative vs other never alias).  Store-to-load
    forwarding on an exact address/width match.  So loads and stores move
    freely past non-aliasing neighbours.  libgcc/libm helpers
    (__muldi3, __adddf3, __gedf2, floor, ...) are pure ops, not barriers.
  * Control: the arm is unfolded as a tree of continuations.  Every
    conditional branch is normalised to one of EQ/LT/LTU with a (true, false)
    pair of successor continuations (beq/bne, blt/bge, bgt/ble, the -z forms),
    EQ's operands sorted: branch polarity and block layout vanish.  A path
    stops at the dispatch head (both `j <trap check>` and `beqz s5,<fetch>`),
    at another opcode's jump-table target, at `ret`, at a tail jump, at a
    noreturn call, or at a back edge (a `loop(k)` marker, k = blocks back).
    At a join with an identical live state (global liveness) the continuation
    is shared (DAG), so the unfolding stays small.
  * An exit records the live-out registers' terms (liveness at the exit
    target) and the memory state.
The arm's class is its root continuation hash, computed twice: "exact", and
"mod ALU" where add/sub/and/or/xor (and their -w forms), `__muldi3` and the
soft-float {__adddf3,__subdf3,__muldf3} map to one symbol ALU / FALU and are
treated as commutative.

Linearisation (for the shared-prefix tree): the continuation DAG is printed
depth-first; each term is one token the first time a path needs it (its
operands named v0, v1, ... by first definition), in a topological order with
hash tie-break; each branch is one token; a shared continuation printed
earlier is one `ref` token.

usage: canon.py [--json OUT] [--ops ALL|F1]
"""
import sys, os, re, json, hashlib, collections, itertools
import armlib

REGS = ["zero", "ra", "sp", "gp", "tp", "t0", "t1", "t2", "s0", "s1"] + \
       [f"a{i}" for i in range(8)] + [f"s{i}" for i in range(2, 12)] + [f"t{i}" for i in range(3, 7)]
CALLER = {"ra", "t0", "t1", "t2", "t3", "t4", "t5", "t6"} | {f"a{i}" for i in range(8)}
ARGS = [f"a{i}" for i in range(8)]
MASK = (1 << 64) - 1

PURE = {  # libgcc / libm helpers: pure functions of their arguments
    "__muldi3": 2, "__divdi3": 2, "__moddi3": 2, "__hidden___udivdi3": 2, "__udivdi3": 2,
    "__umoddi3": 2, "__adddf3": 2, "__subdf3": 2, "__muldf3": 2, "__divdf3": 2,
    "__gedf2": 2, "__ledf2": 2, "__eqdf2": 2, "__nedf2": 2, "__ltdf2": 2, "__gtdf2": 2,
    "__unorddf2": 2, "__floatdidf": 1, "__floatsidf": 1, "__fixdfdi": 1, "floor": 1,
    "fmod": 2, "pow": 2,
}
LIBC = {"memcpy": 3, "memset": 3, "memcmp": 3, "strcmp": 2, "strlen": 1, "strcoll": 2}
ALU_MAP = {"add": "ALU", "sub": "ALU", "and": "ALU", "or": "ALU", "xor": "ALU",
           "addw": "ALUw", "subw": "ALUw",
           "call:__muldi3": "ALU",
           "call:__adddf3": "FALU", "call:__subdf3": "FALU", "call:__muldf3": "FALU"}
CMP_MAP = {"EQ": "CMP", "LT": "CMP", "LTU": "CMP", "slt": "CMP", "sltu": "CMP",
           "call:__gedf2": "FCMP", "call:__ledf2": "FCMP", "call:__eqdf2": "FCMP",
           "call:__ltdf2": "FCMP", "call:__gtdf2": "FCMP"}
COMMUT = {"add", "and", "or", "xor", "addw", "call:__muldi3", "call:__adddf3",
          "call:__muldf3", "ALU", "ALUw", "FALU"}


def sx(v, bits=64):
    v &= (1 << bits) - 1
    return v - (1 << bits) if v >> (bits - 1) else v


# ------------------------------------------------------------------ arities
def c_arities():
    src = ""
    for root, _, fs in os.walk(armlib.LUA_SRC):
        for f in fs:
            if f.endswith((".c", ".h")):
                src += open(os.path.join(root, f), errors="replace").read()
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
    ar = {}
    # declarations/definitions only: at column 0, a type before the name
    for m in re.finditer(r"^(?!return\b)[A-Za-z_][\w \t\*]*?[\s\*]([A-Za-z_]\w*)\s*\(([^;{}()]*(?:\([^()]*\)[^;{}()]*)*)\)\s*[;{]", src, re.M):
        name, params = m.group(1), m.group(2).strip()
        if name in ar or name in ("if", "while", "for", "switch", "return", "sizeof"):
            continue
        if params in ("", "void"):
            ar[name] = (0, False)
        else:
            ps = [p for p in params.split(",")]
            var = ps[-1].strip() == "..."
            ar[name] = (len(ps) - (1 if var else 0), var)
    return ar


AR = None


def arity(fn):
    global AR
    if AR is None:
        AR = c_arities()
    base = fn.split(".")[0]
    if base in PURE:
        return PURE[base], False
    if base in LIBC:
        return LIBC[base], False
    if base in AR:
        return AR[base]
    return 8, True


# ------------------------------------------------------------------ decode
class D:
    __slots__ = ("kind", "op", "rd", "rs", "imm", "w", "signed", "tgt", "fn", "fall")


LOADS = {"lb": (1, 1), "lh": (2, 1), "lw": (4, 1), "ld": (8, 1), "lbu": (1, 0), "lhu": (2, 0), "lwu": (4, 0)}
STORES = {"sb": 1, "sh": 2, "sw": 4, "sd": 8}
RR = {"add", "sub", "and", "or", "xor", "sll", "srl", "sra", "slt", "sltu", "addw", "subw", "sllw", "srlw", "sraw"}
RI = {"addi": "add", "andi": "and", "ori": "or", "xori": "xor", "slli": "sll", "srli": "srl", "srai": "sra",
      "slti": "slt", "sltiu": "sltu", "addiw": "addw", "slliw": "sllw", "srliw": "srlw", "sraiw": "sraw"}
BR = {"beq", "bne", "blt", "bge", "bltu", "bgeu", "beqz", "bnez", "blez", "bgez", "bltz", "bgtz",
      "bgt", "ble", "bgtu", "bleu"}
memre = re.compile(r"(-?\d+)\((\w+)\)")
# luaV_execute's frame: slots 32..63 have their address taken (addi aN,sp,32/40/48:
# &i / &n arguments of luaV_tointeger etc.) and stay in the memory model; every
# other sp slot (k, cl, spills, callee-saved) is treated as a register, so a
# spill is renamed away like any other temporary.
TAKEN = (32, 64)


def decode(i, ctx):
    d = D()
    d.rd, d.rs, d.imm, d.tgt, d.fn, d.w, d.signed, d.fall = None, [], None, None, None, None, None, None
    mn, o = i.mn, i.opl()
    d.op = mn
    if mn in LOADS:
        d.kind = "load"; d.rd = o[0]; m = memre.match(o[1]); d.imm = int(m.group(1)); d.rs = [m.group(2)]
        d.w, d.signed = LOADS[mn]
        if d.rs == ["sp"] and not TAKEN[0] <= d.imm < TAKEN[1]:
            d.kind = "ldslot"; d.rs = [f"sp@{d.imm}"]
    elif mn in STORES:
        d.kind = "store"; m = memre.match(o[1]); d.imm = int(m.group(1)); d.rs = [m.group(2), o[0]]
        d.w = STORES[mn]
        if d.rs[0] == "sp" and not TAKEN[0] <= d.imm < TAKEN[1]:
            d.kind = "stslot"; d.rd = f"sp@{d.imm}"; d.rs = [o[0]]
    elif mn in RR:
        d.kind = "alu"; d.rd = o[0]; d.rs = [o[1], o[2]]
    elif mn in RI:
        d.kind = "alui"; d.op = RI[mn]; d.rd = o[0]; d.rs = [o[1]]; d.imm = int(o[2], 0)
    elif mn == "mv":
        d.kind = "alui"; d.op = "add"; d.rd = o[0]; d.rs = [o[1]]; d.imm = 0
    elif mn == "li":
        d.kind = "const"; d.rd = o[0]; d.imm = int(o[1], 0)
    elif mn == "lui":
        d.kind = "const"; d.rd = o[0]; d.imm = sx(int(o[1], 0) << 12, 32)
    elif mn == "auipc":
        d.kind = "const"; d.rd = o[0]; d.imm = sx(i.addr + sx(int(o[1], 0) << 12, 32))
    elif mn in ("neg", "negw"):
        d.kind = "alu"; d.op = "sub" if mn == "neg" else "subw"; d.rd = o[0]; d.rs = ["zero", o[1]]
    elif mn == "not":
        d.kind = "alui"; d.op = "xor"; d.rd = o[0]; d.rs = [o[1]]; d.imm = -1
    elif mn == "sext.w":
        d.kind = "alui"; d.op = "addw"; d.rd = o[0]; d.rs = [o[1]]; d.imm = 0
    elif mn == "zext.b":
        d.kind = "alui"; d.op = "and"; d.rd = o[0]; d.rs = [o[1]]; d.imm = 255
    elif mn == "seqz":
        d.kind = "alui"; d.op = "sltu"; d.rd = o[0]; d.rs = [o[1]]; d.imm = 1
    elif mn == "snez":
        d.kind = "alu"; d.op = "sltu"; d.rd = o[0]; d.rs = ["zero", o[1]]
    elif mn == "sgtz":
        d.kind = "alu"; d.op = "slt"; d.rd = o[0]; d.rs = ["zero", o[1]]
    elif mn == "sltz":
        d.kind = "alu"; d.op = "slt"; d.rd = o[0]; d.rs = [o[1], "zero"]
    elif mn in BR:
        d.kind = "br"; d.tgt = i.target()
        if mn.endswith("z"):
            a = o[0]; base = mn[:-1]
            d.rs = [a, "zero"]     # b<cc>z a == b<cc> a,zero
            d.op = base
        else:
            d.rs = [o[0], o[1]]
        # normalise to (pred, x, y, sense): taken iff pred(x,y) == sense
        a, b = d.rs
        d.op = {"beq": ("EQ", a, b, True), "bne": ("EQ", a, b, False),
                "blt": ("LT", a, b, True), "bge": ("LT", a, b, False),
                "bgt": ("LT", b, a, True), "ble": ("LT", b, a, False),
                "bltu": ("LTU", a, b, True), "bgeu": ("LTU", a, b, False),
                "bgtu": ("LTU", b, a, True), "bleu": ("LTU", b, a, False)}[d.op]
    elif mn == "j":
        t = i.target()
        d.tgt = t
        d.kind = "j" if ctx["lo"] <= t < ctx["hi"] else "tail"
        if d.kind == "tail":
            d.fn = ctx["starts"].get(t, hex(t))
    elif mn == "jal":
        d.kind = "call"; d.tgt = i.target(); d.fn = ctx["starts"].get(d.tgt, hex(d.tgt))
        if len(o) == 2 and o[0] != "ra":
            raise ValueError(i.ops)
    elif mn == "ret":
        d.kind = "ret"
    elif mn == "jr":
        d.kind = "jr"; d.rs = [o[0]]
    elif mn == "jalr":
        d.kind = "jalr"; d.rs = [o[-1].split("(")[-1].rstrip(")")] if "(" in o[-1] else [o[-1]]
    else:
        raise ValueError(f"unhandled {mn} {i.ops} at {i.addr:x}")
    return d


# ------------------------------------------------------------------ context + liveness
def context():
    a = armlib.load()
    F = a["F"]
    ctx = dict(a)
    ctx["lo"], ctx["hi"] = F["start"], F["end"]
    I = a["I"]
    ctx["dec"] = {i.addr: decode(i, ctx) for i in I}
    targets = set(a["arm_target"].values())
    ctx["targets"] = targets
    ctx["target_op"] = {t: op for op, t in a["arm_target"].items()}
    return analyse(ctx)


def analyse(ctx):
    """successors, use/def and liveness over ctx["dec"] (re-run after a
    perturbation of ctx["dec"])."""
    I = ctx["I"]
    targets = ctx["targets"]

    def succ(pc):
        d = ctx["dec"][pc]
        if d.kind == "br":
            return [d.tgt, d.fall or pc + 4]
        if d.kind == "j":
            return [d.tgt]
        if d.kind in ("tail", "ret"):
            return []
        if d.kind == "jr":
            return sorted(targets)
        if d.kind == "call" and d.fn in armlib.NORET:
            return []
        return [pc + 4]
    ctx["succ"] = succ

    def usedef(pc):
        d = ctx["dec"][pc]
        if d.kind == "call" or d.kind == "tail":
            n, var = arity(d.fn)
            u = set(ARGS[:n]) | ({"sp"} if var else set())
            return u, (CALLER if d.kind == "call" else set())
        if d.kind == "jalr":
            return set(ARGS) | set(d.rs), CALLER
        if d.kind == "ret":
            # luaV_execute is void; callee-saved were reloaded before the ret
            return {"ra", "sp"} | {f"s{i}" for i in range(12)}, set()
        u = set(r for r in d.rs if r != "zero")
        return u, ({d.rd} if d.rd and d.rd != "zero" else set())
    ctx["usedef"] = usedef
    # backward liveness to fixpoint over luaV_execute
    pcs = [i.addr for i in I]
    preds = collections.defaultdict(list)
    for p in pcs:
        for s in succ(p):
            preds[s].append(p)
    UD = {p: usedef(p) for p in pcs}
    live_in = {p: frozenset() for p in pcs}
    work = list(reversed(pcs))
    inq = set(work)
    while work:
        p = work.pop()
        inq.discard(p)
        out = set()
        for s in succ(p):
            out |= live_in.get(s, set())
        u, dfs = UD[p]
        new = frozenset(u | (out - dfs))
        if new != live_in[p]:
            live_in[p] = new
            for q in preds[p]:
                if q not in inq:
                    inq.add(q); work.append(q)
    ctx["live"] = live_in
    ctx["jtargets"] = set(t for p in pcs for t in succ(p) if ctx["dec"][p].kind in ("br", "j")) | targets
    ctx["jtargets"] |= set(p + 4 for p in pcs if ctx["dec"][p].kind == "br")
    return ctx


# ------------------------------------------------------------------ terms
class Terms:
    """hash-consed terms; id = sha1 of (op, args) in exact mode; the ALU-mode
    hash is computed separately over the same DAG."""

    def __init__(self):
        self.t = {}       # h -> (op, args)   args: tuple of h or ints/strings
        self.alu = {}
        self.alu2 = {}

    def mk(self, op, *args):
        key = repr((op, args))
        h = hashlib.sha1(key.encode()).hexdigest()[:16]
        if h not in self.t:
            self.t[h] = (op, args)
        return h

    def const(self, v):
        return self.mk("c", sx(v))

    def cval(self, h):
        op, a = self.t[h]
        return a[0] if op == "c" else None

    def alu_hash(self, h, level=1):
        """level 1 ("mod ALU"): ALU_MAP.  level 2 ("mod ALU+cmp", a looser
        reading, not the pre-registered one): also every comparison predicate
        (EQ/LT/LTU/slt/sltu -> CMP, soft-float compares -> FCMP), and a
        branch's two successors as an unordered pair."""
        cache = self.alu if level == 1 else self.alu2
        if h in cache:
            return cache[h]
        if h not in self.t:
            return h   # literal
        op, args = self.t[h]
        aop = ALU_MAP.get(op, op)
        if level == 2:
            aop = CMP_MAP.get(aop, aop)

        def amap(x):
            if isinstance(x, str) and x in self.t:
                return self.alu_hash(x, level)
            if isinstance(x, tuple):
                return tuple(amap(y) for y in x)
            return x
        ah = [amap(x) for x in args]
        # store sets are sorted by exact hash; re-sort them by this level's hash
        if op == "mem":
            ah[1] = tuple(sorted(ah[1]))
        elif op == "call":
            ah[3] = tuple(sorted(ah[3]))
        elif op == "exit":
            ah[2] = (ah[2][0], tuple(sorted(ah[2][1])))
        if aop in COMMUT or aop in ("CMP", "FCMP"):
            ah = sorted(ah, key=str)
        if op in ("EQ",):
            ah = sorted(ah[:2], key=str) + list(ah[2:])
        if op == "br" and level == 2:
            ah = [ah[0]] + sorted(ah[1:])
        r = hashlib.sha1(repr((aop, tuple(ah))).encode()).hexdigest()[:16]
        cache[h] = r
        return r


def ev_alu(T, op, a, b):
    ca, cb = T.cval(a), T.cval(b)
    if ca is not None and cb is not None:
        x, y = ca & MASK, cb & MASK
        r = {"add": x + y, "sub": x - y, "and": x & y, "or": x | y, "xor": x ^ y,
             "sll": x << (y & 63), "srl": x >> (y & 63), "sra": sx(x) >> (y & 63),
             "slt": int(sx(x) < sx(y)), "sltu": int(x < y),
             "addw": sx(x + y, 32), "subw": sx(x - y, 32), "sllw": sx((x << (y & 31)), 32),
             "srlw": sx((x & 0xffffffff) >> (y & 31), 32), "sraw": sx(sx(x, 32) >> (y & 31), 32)}[op]
        return T.const(r)
    # identities
    if op in ("add", "or", "xor") and cb == 0:
        return a
    if op in ("add", "or", "xor") and ca == 0:
        return b
    if op == "sub" and cb == 0:
        return a
    if op in ("sll", "srl", "sra") and cb == 0:
        return a
    if op == "and" and cb == -1:
        return a
    if op == "sub" and cb is not None:
        op, b, cb = "add", T.const(-cb), -cb
    if op == "add" and cb is not None:
        aop, aargs = T.t[a]
        if aop == "add" and T.cval(aargs[1]) is not None:
            return ev_alu(T, "add", aargs[0], T.const(T.cval(aargs[1]) + cb))
    if op == "add" and ca is not None:
        return ev_alu(T, "add", b, a)
    if op in COMMUT and cb is None and ca is None:
        a, b = sorted([a, b])
    return T.mk(op, a, b)


def split_addr(T, h):
    op, a = T.t[h]
    if op == "add" and T.cval(a[1]) is not None:
        return a[0], T.cval(a[1])
    return h, 0


# ------------------------------------------------------------------ symbolic walk
class Budget(Exception):
    pass


class Walker:
    def __init__(self, ctx, T, own_op, limit=4000, stop_arms=False):
        self.ctx, self.T, self.own = ctx, T, own_op
        self.stop_arms = stop_arms
        self.memo = {}
        self.nodes = 0
        self.limit = limit
        self.exits = []          # (path-cond list, kind, detail) for F2
        self.sp_in = T.mk("in", "sp")

    def get(self, R, r):
        return R[r] if r in R else self.T.mk("in", r)

    def head_state(self):
        T = self.T
        R = {r: T.mk("in", r) for r in REGS}
        R["zero"] = T.const(0)
        mem = (T.mk("epoch0"), ())
        pc = self.ctx["HEAD"]
        while True:
            d = self.ctx["dec"][pc]
            if d.kind == "jr":
                return R, mem
            if d.kind == "br":      # the bound check: in range
                pc += 4
                continue
            R, mem = self.step(d, R, mem, pc)
            pc += 4

    def load(self, d, R, mem):
        T = self.T
        addr = ev_alu(T, "add", R[d.rs[0]], T.const(d.imm))
        epoch, stores = mem
        base, off = split_addr(T, addr)
        # forwarding
        for s in reversed(stores):
            sw, saddr, sval = T.t[s][1]
            if saddr == addr and sw == d.w:
                if d.w == 8:
                    return sval
                return T.mk("ext", d.w, d.signed, sval)
        al = tuple(sorted(s for s in stores if self.alias(addr, d.w, s)))
        m = T.mk("mem", epoch, al) if al else epoch
        return T.mk("ld", d.w, d.signed, addr, m)

    def alias(self, addr, w, s):
        T = self.T
        sw, saddr, _ = T.t[s][1]
        if sw != w:
            return False
        b1, o1 = split_addr(T, addr)
        b2, o2 = split_addr(T, saddr)
        if (b1 == self.sp_in) != (b2 == self.sp_in):
            return False
        if b1 == b2:
            return not (o1 + w <= o2 or o2 + sw <= o1)
        return True

    def step(self, d, R, mem, pc):
        T = self.T
        R = dict(R)
        k = d.kind
        if k == "alu":
            v = ev_alu(T, d.op, R[d.rs[0]], R[d.rs[1]])
        elif k == "alui":
            v = ev_alu(T, d.op, R[d.rs[0]], T.const(d.imm))
        elif k == "const":
            v = T.const(d.imm)
        elif k == "load":
            v = self.load(d, R, mem)
        elif k == "ldslot":
            v = R.get(d.rs[0]) or T.mk("in", d.rs[0])
            if d.w != 8:
                v = T.mk("ext", d.w, d.signed, v)
        elif k == "stslot":
            v = R[d.rs[0]]
        elif k == "store":
            addr = ev_alu(T, "add", R[d.rs[0]], T.const(d.imm))
            val = R[d.rs[1]]
            st = T.mk("st", d.w, addr, val)
            epoch, stores = mem
            # a later store to the same address/width replaces the earlier one
            stores = tuple(s for s in stores if not (T.t[s][1][1] == addr and T.t[s][1][0] == d.w)) + (st,)
            return R, (epoch, tuple(sorted(stores)))
        elif k == "call":
            n, var = arity(d.fn)
            if var:
                n = max(n, self.awritten_hint(R))
            args = tuple(R[a] for a in ARGS[:n])
            base = d.fn.split(".")[0]
            if base in PURE:
                opn = "call:" + base
                if opn in COMMUT and len(args) == 2:
                    args = tuple(sorted(args))
                r = T.mk(opn, *args)
                for c in CALLER:
                    R[c] = T.mk("clob", c)
                R["a0"] = r
                return R, mem
            epoch, stores = mem
            call = T.mk("call", d.fn, args, epoch, stores)
            for c in CALLER:
                R[c] = T.mk("clob", c)
            R["a0"] = T.mk("ret0", call)
            R["a1"] = T.mk("ret1", call)
            return R, (T.mk("epoch", call), ())
        else:
            raise ValueError(k)
        if d.rd != "zero":
            R[d.rd] = v
        return R, mem

    def awritten_hint(self, R):
        # varargs: count a-regs that hold something other than a clobber/input
        n = 0
        for i, a in enumerate(ARGS):
            op = self.T.t.get(R[a], ("?",))[0]
            if op not in ("clob", "in"):
                n = i + 1
        return n

    # a continuation node is ('br', pred, x, y, t, f) | ('exit', kind, outs, mem) | ('loop', k)
    def exit_node(self, kind, R, mem, live, conds):
        outs = tuple((r, self.get(R, r)) for r in sorted(live) if r != "zero")
        self.exits.append((list(conds), kind, dict(outs)))
        return self.T.mk("exit", kind, outs, mem)

    def walk(self, pc, R, mem, path, conds):
        """returns the continuation hash starting at pc"""
        ctx, T = self.ctx, self.T
        start = pc
        steps = 0
        while True:
            steps += 1
            if steps > 5000:
                raise Budget()
            if pc in (ctx["HEAD"], ctx["HEAD_TRAP"]):
                return self.exit_node(("head",), R, mem, ctx["live"][ctx["HEAD_TRAP"]], conds)
            if pc == ctx["lo"]:
                return self.exit_node(("reentry", 0), R, mem, ctx["live"][pc], conds)
            if self.stop_arms and pc in ctx["targets"] and ctx["target_op"][pc] != self.own \
                    and pc != ctx["default"]:   # the default target is shared tail code
                return self.exit_node(("arm", ctx["target_op"][pc]), R, mem, ctx["live"][pc], conds)
            if pc in ctx["jtargets"] or pc == start:
                if pc in path:
                    return T.mk("loop", len(path) - path.index(pc))
                key = (pc, tuple(self.get(R, r) for r in sorted(ctx["live"][pc])), mem)
                if key in self.memo:
                    return self.memo[key]
                path = path + [pc]
                h = self.walk_block(pc, R, mem, path, conds)
                self.memo[key] = h
                return h
            return self.walk_block(pc, R, mem, path, conds)

    def walk_block(self, pc, R, mem, path, conds):
        ctx, T = self.ctx, self.T
        first = True
        while True:
            if not first and (pc in ctx["jtargets"] or pc in (ctx["HEAD"], ctx["HEAD_TRAP"])):
                return self.walk(pc, R, mem, path, conds)
            first = False
            d = ctx["dec"][pc]
            self.nodes += 1
            if self.nodes > self.limit * 50:
                raise Budget()
            if d.kind == "br":
                pred, x, y, sense = d.op
                a, b = R[x], R[y]
                if pred == "EQ":
                    a, b = sorted([a, b])
                ca, cb = T.cval(a), T.cval(b)
                if ca is not None and cb is not None:
                    val = {"EQ": ca == cb, "LT": ca < cb, "LTU": (ca & MASK) < (cb & MASK)}[pred]
                    pc = d.tgt if val == sense else (d.fall or pc + 4)
                    if d.fall:
                        return self.walk(pc, R, mem, path, conds)
                    continue
                cond = T.mk(pred, a, b)
                taken = self.walk(d.tgt, R, mem, path, conds + [(cond, sense)])
                fall = self.walk(d.fall or pc + 4, R, mem, path, conds + [(cond, not sense)])
                t, f = (taken, fall) if sense else (fall, taken)
                return T.mk("br", cond, t, f)
            if d.kind == "j":
                return self.walk(d.tgt, R, mem, path, conds)
            if d.kind == "tail":
                return self.exit_node(("tail", d.fn), R, mem, set(ARGS[:arity(d.fn)[0]]) | {"sp"}, conds)
            if d.kind == "ret":
                return self.exit_node(("ret",), R, mem, {"sp"}, conds)
            if d.kind == "call" and d.fn in armlib.NORET:
                n, var = arity(d.fn)
                if var:
                    n = max(n, self.awritten_hint(R))
                return self.exit_node(("noreturn", d.fn), R, mem, set(ARGS[:n]), conds)
            if d.kind in ("jr", "jalr"):
                return self.exit_node(("indirect",), R, mem, set(ARGS) | set(d.rs), conds)
            R, mem = self.step(d, R, mem, pc)
            pc += 4


def canon_arm(ctx, T, op, stop_arms=False):
    W = Walker(ctx, T, op, stop_arms=stop_arms)
    R, mem = W.head_state()
    try:
        root = W.walk(ctx["arm_target"][op], R, mem, [], [])
        trunc = False
    except Budget:
        root, trunc = None, True
    return W, root, trunc


# ------------------------------------------------------------------ linearisation
def subterms_of(T):
    def subterms(a):
        if isinstance(a, str) and a in T.t:
            yield a
        elif isinstance(a, tuple):
            for y in a:
                yield from subterms(y)
    return subterms


def linearise(T, root, alu=False):
    """tokens of the continuation DAG (see module doc)."""
    toks = []
    sig = []      # position-free twin of toks: operands shown by their op, not their name
    shared = {}
    subterms = subterms_of(T)

    def osig(a):
        if isinstance(a, str) and a in T.t:
            op, args = T.t[a]
            if op in ("c", "in", "clob"):
                return f"{op}:{args[0]}"
            return ALU_MAP.get(op, op) if alu else op
        if isinstance(a, tuple):
            return f"T{len(a)}"
        return str(a)

    def term_tokens(h, names):
        # post-order, children in hash order -> topological with hash tie-break
        if h in names or h not in T.t:
            return
        op, args = T.t[h]
        if op in ("in", "c", "epoch0", "clob"):
            names[h] = f"{op}:{args[0] if args else ''}"
            return
        for x in sorted(set(subterms(args)), key=(T.alu_hash if alu else None)):
            term_tokens(x, names)
        names[h] = f"v{sum(1 for v in names.values() if v.startswith('v'))}"

        def nm(a):
            if isinstance(a, str) and a in names:
                return names[a]
            if isinstance(a, tuple):
                return "(" + ",".join(nm(x) for x in a) + ")"
            return str(a)
        opn = ALU_MAP.get(op, op) if alu else op
        toks.append(f"{names[h]}={opn}(" + ",".join(nm(a) for a in args) + ")")
        sig.append(f"{opn}(" + ",".join(osig(a) for a in args) + ")")

    def cont(h, names):
        if h in shared:
            toks.append(f"ref{shared[h]}")
            sig.append("ref")
            return
        op, args = T.t[h]
        if op == "br":
            cond, t, f = args
            term_tokens(cond, names)
            shared[h] = len(shared)
            toks.append(f"br {names[cond]}")
            sig.append(f"br {osig(cond)}")
            cont(t, dict(names))
            cont(f, dict(names))
        elif op == "exit":
            kind, outs, mem = args
            term_tokens(mem[0], names)
            for s in mem[1]:
                term_tokens(s, names)
            for r, v in outs:
                term_tokens(v, names)
            shared[h] = len(shared)
            ch = [(r, v) for r, v in outs if T.t.get(v, ("",))[0] != "in" or T.t[v][1][0] != r]
            toks.append("exit " + repr(kind) + " " + ",".join(f"{r}={names.get(v, v)}" for r, v in ch))
            sig.append("exit " + repr(kind) + " " + ",".join(f"{r}={osig(v)}" for r, v in ch))
        elif op == "loop":
            toks.append(f"loop{args[0]}")
            sig.append(f"loop{args[0]}")
    if root is not None:
        cont(root, {})
    return toks, sig


def arm_insts(ctx, op, stop_arms=False):
    """static reach set (as census arms.py, but stopping at both head entries
    and at other arms' targets)"""
    seen, work = set(), [ctx["arm_target"][op]]
    while work:
        a = work.pop()
        if a in seen or a in (ctx["HEAD"], ctx["HEAD_TRAP"]) or a < ctx["HEAD_TRAP"] or not (ctx["lo"] <= a < ctx["hi"]):
            continue
        if stop_arms and a in ctx["targets"] and ctx["target_op"][a] != op:
            continue
        seen.add(a)
        work.extend(ctx["succ"](a) if ctx["dec"][a].kind != "jr" else [])
    return seen


def main():
    ctx = context()
    T = Terms()
    ops = armlib.f1_ops() if "--all" not in sys.argv else ctx["ops"][:-1]
    res = {}
    for op in ops:
        W, root, trunc = canon_arm(ctx, T, op)
        res[op] = dict(root=root, alu=T.alu_hash(root) if root else None, trunc=trunc,
                       toks=linearise(T, root)[0], insts=len(arm_insts(ctx, op)),
                       exits=len(W.exits))
    return ctx, T, res


if __name__ == "__main__":
    ctx, T, res = main()
    for op, r in res.items():
        print(op, r["root"], r["alu"], r["trunc"], len(r["toks"]), r["insts"], r["exits"])

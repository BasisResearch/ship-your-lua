#!/usr/bin/env python3
"""Parse an F1 Lua source file into a Lean `Lua.Ast.Chunk` term
(`Lua/Ast/Syntax.lean`), so the source side of translation validation is a
Lean term generated from the same file `luac` compiles.

    python3 scripts/gen_ast.py c/tests/f1_ops.lua --name f1OpsAst \
        -o Lua/Programs/F1OpsAst.lean [--check]

A small recursive-descent parser for the F1 subset, following lparser.c's
grammar and operator priorities (`subexpr`, `priority[]`):

  stat    ::= ';' | 'local' Name {',' Name} ['=' exp {',' exp}]
            | Name '=' exp | 'print' '(' [exp {',' exp}] ')'
            | 'while' exp 'do' block 'end' | 'repeat' block 'until' exp
            | 'if' exp 'then' block {'elseif' exp 'then' block} ['else' block] 'end'
            | 'for' Name '=' exp ',' exp [',' exp] 'do' block 'end' | 'break'
  exp     ::= 'nil' | 'true' | 'false' | Int | Name | '(' exp ')'
            | ('not' | '-') exp | exp binop exp
  binop   ::= 'or' | 'and' | '<' | '<=' | '>' | '>=' | '==' | '~=' | '+' | '-'
            | '*' | '//' | '%'

Translation notes (each is what lparser.c does):
  * `elseif c then b` is `else if c then b end` (test_then_block chains);
  * a missing `for` step is the integer 1 (fornum: `luaK_int(fs, reg, 1)`);
  * an integer literal is decimal (< 2^63, else a float: rejected) or hex
    (wraps modulo 2^64, as l_str2int); unary minus is kept as `neg`.
Anything else (floats, strings, calls other than `print(...)` statements,
globals, multiple assignment, `do`, `goto`, `return`, functions, tables,
bitwise, `/`, `^`, `..`, `#`) is rejected: it is not in the F1 AST.
"""
import argparse, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

KEYWORDS = {"and", "break", "do", "else", "elseif", "end", "false", "for", "function",
            "goto", "if", "in", "local", "nil", "not", "or", "repeat", "return", "then",
            "true", "until", "while"}
SYMBOLS = ["//", "==", "~=", "<=", ">=", "<<", ">>", "::", "...", "..",
           "+", "-", "*", "/", "%", "^", "#", "&", "~", "|", "<", ">", "=",
           "(", ")", "{", "}", "[", "]", ";", ":", ",", "."]

class Unsupported(Exception):
    pass

def lex(src):
    toks, i, n = [], 0, len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n":
            i += 1
        elif src.startswith("--", i):
            m = re.match(r"--\[(=*)\[", src[i:])
            if m:
                close = "]" + m.group(1) + "]"
                j = src.find(close, i + len(m.group(0)))
                if j < 0: raise Unsupported("unfinished long comment")
                i = j + len(close)
            else:
                j = src.find("\n", i)
                i = n if j < 0 else j + 1
        elif c.isalpha() or c == "_":
            m = re.match(r"[A-Za-z_][A-Za-z0-9_]*", src[i:])
            w = m.group(0); i += len(w)
            toks.append(("kw", w) if w in KEYWORDS else ("name", w))
        elif c.isdigit() or (c == "." and i + 1 < n and src[i + 1].isdigit()):
            m = re.match(r"0[xX][0-9a-fA-F]+(?![.pP0-9a-zA-Z_])", src[i:])
            if m:
                toks.append(("int", int(m.group(0), 16) % 2**64)); i += len(m.group(0))
                continue
            m = re.match(r"[0-9]+(?![.eExX0-9a-zA-Z_])", src[i:])
            if not m: raise Unsupported(f"non-integer numeral at offset {i}")
            v = int(m.group(0))
            if v >= 2**63: raise Unsupported(f"numeral {v} is a float in Lua")
            toks.append(("int", v)); i += len(m.group(0))
        elif c in "\"'" or src.startswith("[[", i) or re.match(r"\[=+\[", src[i:]):
            raise Unsupported("string literal")
        else:
            for s in SYMBOLS:
                if src.startswith(s, i):
                    toks.append(("sym", s)); i += len(s); break
            else:
                raise Unsupported(f"unexpected character {c!r}")
    toks.append(("eof", None))
    return toks

# lparser.c priority[]: {left, right}
BINOPS = {"or": ("or", 1, 1), "and": ("and", 2, 2),
          "<": ("lt", 3, 3), "<=": ("le", 3, 3), ">": ("gt", 3, 3), ">=": ("ge", 3, 3),
          "==": ("eq", 3, 3), "~=": ("ne", 3, 3),
          "+": ("add", 10, 10), "-": ("sub", 10, 10),
          "*": ("mul", 11, 11), "//": ("idiv", 11, 11), "%": ("mod", 11, 11)}
UNSUPPORTED_BINOPS = {"|", "~", "&", "<<", ">>", "..", "/", "^"}
UNARY_PRIORITY = 12

class Parser:
    def __init__(s, toks): s.t, s.i = toks, 0
    def peek(s, k=0): return s.t[s.i + k]
    def next(s): tok = s.t[s.i]; s.i += 1; return tok
    def check(s, kind, val=None):
        tok = s.peek()
        return tok[0] == kind and (val is None or tok[1] == val)
    def expect(s, kind, val=None):
        if not s.check(kind, val): raise Unsupported(f"expected {val or kind}, got {s.peek()}")
        return s.next()
    def name(s): return s.expect("name")[1]

    def binop(s):
        kind, v = s.peek()
        if kind in ("kw", "sym") and v in BINOPS: return BINOPS[v]
        if kind == "sym" and v in UNSUPPORTED_BINOPS: raise Unsupported(f"operator {v}")
        return None

    def expr(s, limit=0):
        if s.check("kw", "not"):
            s.next(); e = ("not", s.expr(UNARY_PRIORITY))
        elif s.check("sym", "-"):
            s.next(); e = ("neg", s.expr(UNARY_PRIORITY))
        elif s.check("sym", "#") or s.check("sym", "~"):
            raise Unsupported(f"unary {s.peek()[1]}")
        else:
            e = s.simple()
        while True:
            op = s.binop()
            if op is None or op[1] <= limit: return e
            s.next()
            e2 = s.expr(op[2])
            e = (op[0], e, e2) if op[0] in ("and", "or") else ("binop", op[0], e, e2)

    def simple(s):
        kind, v = s.next()
        if kind == "int": return ("int", v)
        if kind == "kw" and v == "nil": return ("nil",)
        if kind == "kw" and v in ("true", "false"): return ("bool", v)
        if kind == "name":
            if s.check("sym", "(") or s.check("sym", ".") or s.check("sym", "[") \
                    or s.check("sym", ":"):
                raise Unsupported(f"call/index of {v} in an expression")
            return ("var", v)
        if kind == "sym" and v == "(":
            e = s.expr(); s.expect("sym", ")"); return e
        raise Unsupported(f"expression starting with {v!r}")

    def exprlist(s):
        es = [s.expr()]
        while s.check("sym", ","): s.next(); es.append(s.expr())
        return es

    def block(s):
        ss = []
        while not (s.check("eof") or any(s.check("kw", k) for k in ("end", "else", "elseif", "until"))):
            st = s.stat()
            if st is not None: ss.append(st)
        return ss

    def stat(s):
        kind, v = s.peek()
        if kind == "sym" and v == ";": s.next(); return None
        if kind == "kw":
            if v == "local":
                s.next()
                if s.check("kw", "function"): raise Unsupported("local function")
                xs = [s.name()]
                while s.check("sym", ","): s.next(); xs.append(s.name())
                if s.check("sym", "<"): raise Unsupported("local attribute")
                es = []
                if s.check("sym", "="): s.next(); es = s.exprlist()
                if len(xs) == 1 and len(es) == 1: return ("local", xs[0], es[0])
                return ("locals", xs, es)
            if v == "while":
                s.next(); c = s.expr(); s.expect("kw", "do"); b = s.block(); s.expect("kw", "end")
                return ("while", c, b)
            if v == "repeat":
                s.next(); b = s.block(); s.expect("kw", "until"); c = s.expr()
                return ("repeat", b, c)
            if v == "if":
                s.next(); return s.if_rest()
            if v == "for":
                s.next(); x = s.name()
                if not s.check("sym", "="): raise Unsupported("generic for")
                s.next(); a = s.expr(); s.expect("sym", ","); b = s.expr()
                c = ("int", 1)
                if s.check("sym", ","): s.next(); c = s.expr()
                s.expect("kw", "do"); body = s.block(); s.expect("kw", "end")
                return ("for", x, a, b, c, body)
            if v == "break": s.next(); return ("break",)
            raise Unsupported(f"statement {v}")
        if kind == "name":
            s.next()
            if s.check("sym", "(") and v == "print":
                s.next(); args = [] if s.check("sym", ")") else s.exprlist()
                s.expect("sym", ")"); return ("print", args)
            if s.check("sym", "="):
                s.next(); return ("assign", v, s.expr())
            raise Unsupported(f"statement starting with {v} {s.peek()[1]!r}")
        raise Unsupported(f"statement starting with {v!r}")

    def if_rest(s):
        c = s.expr(); s.expect("kw", "then"); t = s.block()
        if s.check("kw", "elseif"):
            s.next(); return ("if", c, t, [s.if_rest()])
        e = []
        if s.check("kw", "else"): s.next(); e = s.block()
        s.expect("kw", "end")
        return ("if", c, t, e)

def lean_str(x):
    assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", x)
    return f'"{x}"'

def lean_e(e):
    k = e[0]
    if k == "nil": return ".nil"
    if k == "bool": return f"(.bool {e[1]})"
    if k == "int": return f"(.int {e[1]})"
    if k == "var": return f"(.var {lean_str(e[1])})"
    if k == "binop": return f"(.binop .{e[1]} {lean_e(e[2])} {lean_e(e[3])})"
    if k in ("and", "or"): return f"(.{k} {lean_e(e[1])} {lean_e(e[2])})"
    if k in ("neg", "not"): return f"(.{k} {lean_e(e[1])})"
    raise AssertionError(e)

def lean_es(es): return "[" + ", ".join(lean_e(e) for e in es) + "]"

def lean_block(ss, ind):
    if not ss: return "[]"
    inner = ind + "  "
    return "[\n" + ",\n".join(inner + lean_s(st, inner) for st in ss) + "]"

def lean_s(st, ind):
    k = st[0]
    if k == "local": return f".local_ {lean_str(st[1])} {lean_e(st[2])}"
    if k == "locals":
        return f".locals [{', '.join(lean_str(x) for x in st[1])}] {lean_es(st[2])}"
    if k == "assign": return f".assign {lean_str(st[1])} {lean_e(st[2])}"
    if k == "print": return f".print {lean_es(st[1])}"
    if k == "break": return ".break_"
    if k == "while": return f".while_ {lean_e(st[1])} {lean_block(st[2], ind)}"
    if k == "repeat": return f".repeat_ {lean_block(st[1], ind)} {lean_e(st[2])}"
    if k == "if":
        return f".if_ {lean_e(st[1])} {lean_block(st[2], ind)} {lean_block(st[3], ind)}"
    if k == "for":
        return (f".numFor {lean_str(st[1])} {lean_e(st[2])} {lean_e(st[3])} {lean_e(st[4])} "
                f"{lean_block(st[5], ind)}")
    raise AssertionError(st)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("source"); ap.add_argument("--name", required=True)
    ap.add_argument("-o", "--out", required=True); ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    src = open(a.source).read()
    try:
        p = Parser(lex(src)); chunk = p.block(); p.expect("eof")
    except Unsupported as e:
        sys.exit(f"{a.source}: not in the F1 AST: {e}")
    rel = os.path.relpath(os.path.abspath(a.source), ROOT)
    shown = src.replace("-/", "- /").rstrip("\n") + "\n"
    t = (f"import Lua.Ast.Syntax\n\n/-! GENERATED by scripts/gen_ast.py from `{rel}` -- do not edit.\n\n"
         f"```lua\n{shown}```\n-/\n\nnamespace Lua.Programs\n\nopen Lua.Ast\n\n"
         f"/-- The F1 AST of `{rel}`. -/\ndef {a.name} : Chunk := {lean_block(chunk, '')}\n\n"
         f"end Lua.Programs\n")
    if a.check:
        ok = os.path.exists(a.out) and open(a.out).read() == t
        print(f"{a.out}: {'ok' if ok else 'DRIFT'}"); sys.exit(0 if ok else 1)
    os.makedirs(os.path.dirname(a.out) or ".", exist_ok=True); open(a.out, "w").write(t)
    print("wrote", a.out)

main()

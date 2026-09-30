#!/usr/bin/env python3
"""A parser for all of Lua 5.4, emitting the Lean deep embedding
`Lua.Ast.Chunk` (`Lua/Ast/Syntax.lean`, the manual's §9 "The Complete Syntax
of Lua").

    python3 scripts/gen_ast.py c/tests/while.lua --name whileAst \
        -o Lua/Programs/WhileAst.lean [--check]
    python3 scripts/gen_ast.py --roundtrip [--luac c/luac] FILE.lua ...
    python3 scripts/gen_ast.py --differential [--luac c/luac] FILE.lua ...

The lexer is `llex.c` and the parser is `lparser.c` (Lua 5.4.7), function by
function:

* lexer: long brackets `[==[ ]==]` (first newline skipped, `\\r\\n`/`\\n\\r`
  normalised), long and short comments, every escape (`\\a \\b \\f \\n \\r \\t
  \\v \\\\ \\" \\'`, `\\<newline>`, `\\xXX`, `\\z`, `\\ddd` <= 255, `\\u{X}` <=
  7FFFFFFF), and `read_numeral`'s liberal scan followed by `luaO_str2num`
  (`l_str2int`: decimal overflow falls back to a float, hex wraps mod 2^64;
  `l_str2d`: decimal and hex floats, `inf`/`nan` rejected). A float is kept
  as its IEEE-754 bits. `luaL_loadfile`'s UTF-8 BOM and `#` first line are
  skipped.
* parser: `subexpr`'s priority table and `UNARY_PRIORITY`; `exprstat`'s
  call-or-assignment rule (a statement that is not an assignment must be a
  call, and an assignment target must be a variable: "syntax error"); `return`
  last in a block; `funcargs` (`(...)`, a table constructor, a string).
* the static checks lparser makes, with its algorithm (`BlockCnt`, pending
  gotos, `movegotosout`, `createlabel`'s "last no-op statement" rule,
  `labelstat` creating the no-op statements after a label first):
  `break` outside a loop, no visible label for a `goto`, a `goto` jumping into
  the scope of a local, a label already visible, unknown attributes, multiple
  `<close>` variables in one `local`, assignment to a `<const>`/`<close>`
  variable (also via `function f()`), `...` outside a vararg function, and
  more than 200 local variables in a function.

Implementation limits that depend on code generation are not enforced (the
255-register limit, 255 upvalues, 200 C levels of nesting, "control structure
too long"): the parser accepts a superset there, never a subset.

The AST keeps what the manual's grammar keeps: every statement including `;`
and labels, parentheses (`prefixexp ::= '(' exp ')'`), `a.b` apart from
`a["b"]`, method calls, and the three `args` forms. The F1 fragment is *not*
enforced here: that is the Lean predicate `AstSupported`.

`--roundtrip` checks each file against the host luac: parse, pretty-print,
re-parse to the same AST, then `luac -p` accepts the printed text and
`luac -l -l` of the original and of the printed text agree (with line
numbers, addresses and file names normalised). `--differential` checks that
this parser and `luac -p` accept the same token-level mutants of each file.
"""
import argparse, os, re, struct, subprocess, sys, tempfile, random

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

class LuaSyntaxError(Exception):
    pass

# ---------------------------------------------------------------- lexer (llex.c)

RESERVED = ["and", "break", "do", "else", "elseif", "end", "false", "for", "function",
            "goto", "if", "in", "local", "nil", "not", "or", "repeat", "return", "then",
            "true", "until", "while"]
RESERVED_SET = set(RESERVED)
EOZ = -1

def isalpha_(c): return c != EOZ and (65 <= c <= 90 or 97 <= c <= 122 or c == 95)
def isdigit_(c): return c != EOZ and 48 <= c <= 57
def isalnum_(c): return isalpha_(c) or isdigit_(c)
def isxdigit_(c): return c != EOZ and (isdigit_(c) or 65 <= c <= 70 or 97 <= c <= 102)
def isspace_(c): return c in (32, 9, 10, 11, 12, 13)
def hexavalue(c): return c - 48 if isdigit_(c) else (c | 0x20) - 87

def float_bits(x): return struct.unpack("<Q", struct.pack("<d", x))[0]

DEC_FLOAT = re.compile(rb"(?:[0-9]+\.?[0-9]*|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
HEX_FLOAT = re.compile(rb"0[xX](?:[0-9a-fA-F]+\.?[0-9a-fA-F]*|\.[0-9a-fA-F]+)(?:[pP][+-]?[0-9]+)?")

def str2num(s):
    """`luaO_str2num` on a numeral the lexer read (no sign, no spaces):
    ('int', bits) or ('flt', ieee bits), or None (malformed)."""
    # l_str2int
    if s[:2] in (b"0x", b"0X"):
        if len(s) > 2 and all(isxdigit_(c) for c in s[2:]):
            return ("int", int(s[2:], 16) % 2**64)
    elif s and all(isdigit_(c) for c in s):
        v = int(s)
        if v <= 2**63 - 1:
            return ("int", v)
    # l_str2d ('n' anywhere: inf/nan rejected)
    if re.search(rb"[nN]", s):
        return None
    if re.search(rb"[xX]", s):
        if not HEX_FLOAT.fullmatch(s): return None
        m = re.fullmatch(rb"0[xX]([0-9a-fA-F]*)\.?([0-9a-fA-F]*)(?:[pP]([+-]?[0-9]+))?", s)
        mant = (m.group(1) + m.group(2)).decode()
        e = int(m.group(3) or b"0") - 4 * len(m.group(2))
        # exact rational, rounded once (strtod / float.fromhex semantics)
        return ("flt", float_bits(float.fromhex("0x" + (mant or "0") + "p" + str(e))))
    if not DEC_FLOAT.fullmatch(s): return None
    return ("flt", float_bits(float(s.decode())))

class Lexer:
    def __init__(self, src):
        # luaL_loadfilex: skip a UTF-8 BOM, then a first line starting with '#'
        if src.startswith(b"\xef\xbb\xbf"): src = src[3:]
        if src.startswith(b"#"):
            j = src.find(b"\n")
            src = b"\n" + (src[j + 1:] if j >= 0 else b"")
        self.s, self.i, self.line = src, 0, 1

    def cur(self): return self.s[self.i] if self.i < len(self.s) else EOZ
    def peekc(self, k=1): return self.s[self.i + k] if self.i + k < len(self.s) else EOZ
    def next(self): self.i += 1
    def err(self, msg): raise LuaSyntaxError(f"{self.line}: {msg}")

    def is_newline(self): return self.cur() in (10, 13)

    def inclinenumber(self):
        old = self.cur(); self.next()
        if self.is_newline() and self.cur() != old: self.next()
        self.line += 1

    def skip_sep(self):
        """At '[' or ']': count '='s; returns count+2 if well formed, 1 for a
        lone bracket, 0 for an unfinished '[=...'."""
        s = self.cur(); self.next(); count = 0
        while self.cur() == 61: self.next(); count += 1
        return count + 2 if self.cur() == s else (1 if count == 0 else 0)

    def read_long_string(self, is_string, sep):
        line = self.line
        self.next()  # 2nd '['
        if self.is_newline(): self.inclinenumber()
        buf = bytearray()
        while True:
            c = self.cur()
            if c == EOZ:
                self.err(f"unfinished long {'string' if is_string else 'comment'} (starting at line {line})")
            elif c == 93:  # ']'
                j = self.i
                if self.skip_sep() == sep:
                    self.next(); break
                buf += self.s[j:self.i]
            elif c in (10, 13):
                buf.append(10); self.inclinenumber()
            else:
                buf.append(c); self.next()
        return bytes(buf)

    def read_string(self, delim):
        self.next()
        buf = bytearray()
        while self.cur() != delim:
            c = self.cur()
            if c == EOZ or c in (10, 13):
                self.err("unfinished string")
            if c != 92:
                buf.append(c); self.next(); continue
            self.next()  # '\\'
            c = self.cur()
            simple = {97: 7, 98: 8, 102: 12, 110: 10, 114: 13, 116: 9, 118: 11,
                      92: 92, 34: 34, 39: 39}
            if c in simple:
                buf.append(simple[c]); self.next()
            elif c == 120:  # \xXX
                r = 0
                for _ in range(2):
                    self.next()
                    if not isxdigit_(self.cur()): self.err("hexadecimal digit expected")
                    r = (r << 4) + hexavalue(self.cur())
                buf.append(r); self.next()
            elif c == 117:  # \u{XXX}
                self.next()
                if self.cur() != 123: self.err("missing '{'")
                self.next()
                if not isxdigit_(self.cur()): self.err("hexadecimal digit expected")
                r = hexavalue(self.cur()); self.next()
                while isxdigit_(self.cur()):
                    if r > (0x7FFFFFFF >> 4): self.err("UTF-8 value too large")
                    r = (r << 4) + hexavalue(self.cur()); self.next()
                if self.cur() != 125: self.err("missing '}'")
                self.next()
                buf += utf8esc(r)
            elif c in (10, 13):
                self.inclinenumber(); buf.append(10)
            elif c == EOZ:
                pass  # error on the next loop iteration
            elif c == 122:  # \z
                self.next()
                while isspace_(self.cur()):
                    if self.is_newline(): self.inclinenumber()
                    else: self.next()
            else:
                if not isdigit_(c): self.err("invalid escape sequence")
                r = 0
                for _ in range(3):
                    if not isdigit_(self.cur()): break
                    r = 10 * r + self.cur() - 48; self.next()
                if r > 255: self.err("decimal escape too large")
                buf.append(r)
        self.next()
        return bytes(buf)

    def read_numeral(self):
        start = self.i
        expo = (69, 101)  # Ee
        first = self.cur(); self.next()
        if first == 48 and self.cur() in (88, 120):
            self.next(); expo = (80, 112)  # Pp
        while True:
            if self.cur() in expo:
                self.next()
                if self.cur() in (43, 45): self.next()
            elif isxdigit_(self.cur()) or self.cur() == 46:
                self.next()
            else:
                break
        if isalpha_(self.cur()): self.next()  # numeral touching a letter: force an error
        r = str2num(self.s[start:self.i])
        if r is None: self.err("malformed number near '%s'" % self.s[start:self.i].decode("latin-1"))
        return r

    def token(self):
        """llex: (kind, value, line)."""
        while True:
            c = self.cur()
            if c in (10, 13): self.inclinenumber(); continue
            if c in (32, 12, 9, 11): self.next(); continue
            line = self.line
            if c == 45:  # '-'
                self.next()
                if self.cur() != 45: return ("-", None, line)
                self.next()
                if self.cur() == 91:
                    sep = self.skip_sep()
                    if sep >= 2:
                        self.read_long_string(False, sep); continue
                while not self.is_newline() and self.cur() != EOZ: self.next()
                continue
            if c == 91:  # '['
                sep = self.skip_sep()
                if sep >= 2: return ("string", self.read_long_string(True, sep), line)
                if sep == 0: self.err("invalid long string delimiter")
                return ("[", None, line)
            two = {61: [(61, "==")], 60: [(61, "<="), (60, "<<")], 62: [(61, ">="), (62, ">>")],
                   47: [(47, "//")], 126: [(61, "~=")], 58: [(58, "::")]}
            if c in two:
                self.next()
                for c2, tok in two[c]:
                    if self.cur() == c2: self.next(); return (tok, None, line)
                return (chr(c), None, line)
            if c in (34, 39): return ("string", self.read_string(c), line)
            if c == 46:  # '.'
                if self.peekc() == 46:
                    self.next(); self.next()
                    if self.cur() == 46: self.next(); return ("...", None, line)
                    return ("..", None, line)
                if not isdigit_(self.peekc()): self.next(); return (".", None, line)
                return self.read_numeral() + (line,)
            if isdigit_(c): return self.read_numeral() + (line,)
            if c == EOZ: return ("eof", None, line)
            if isalpha_(c):
                j = self.i
                while isalnum_(self.cur()): self.next()
                w = self.s[j:self.i].decode()
                return (w, None, line) if w in RESERVED_SET else ("name", w, line)
            self.next()
            return (chr(c), None, line)

def utf8esc(x):
    if x < 0x80: return bytes([x])
    out, mfb = [], 0x3F
    while True:
        out.append(0x80 | (x & 0x3F)); x >>= 6; mfb >>= 1
        if x <= mfb: break
    out.append(((~mfb << 1) | x) & 0xFF)
    return bytes(reversed(out))

def lex(src):
    lx, toks = Lexer(src), []
    while True:
        t = lx.token(); toks.append(t)
        if t[0] == "eof": return toks

# ---------------------------------------------------------------- parser (lparser.c)

# priority[] : {left, right}
BINOPS = {"+": ("add", 10, 10), "-": ("sub", 10, 10), "*": ("mul", 11, 11),
          "%": ("mod", 11, 11), "^": ("pow", 14, 13), "/": ("div", 11, 11),
          "//": ("idiv", 11, 11), "&": ("band", 6, 6), "|": ("bor", 4, 4),
          "~": ("bxor", 5, 5), "<<": ("shl", 7, 7), ">>": ("shr", 7, 7),
          "..": ("concat", 9, 8), "==": ("eq", 3, 3), "<": ("lt", 3, 3),
          "<=": ("le", 3, 3), "~=": ("ne", 3, 3), ">": ("gt", 3, 3),
          ">=": ("ge", 3, 3), "and": ("and", 2, 2), "or": ("or", 1, 1)}
UNOPS = {"not": "not", "-": "neg", "~": "bnot", "#": "len"}
UNARY_PRIORITY = 12
MAXVARS = 200

class Var:  # Vardesc
    def __init__(s, name, kind): s.name, s.kind = name, kind  # kind: reg | const | close

class BlockCnt:
    def __init__(s, prev, nactvar, firstlabel, firstgoto, isloop):
        s.prev, s.nactvar, s.firstlabel, s.firstgoto, s.isloop = prev, nactvar, firstlabel, firstgoto, isloop

class FuncState:
    def __init__(s, prev, is_vararg, nlabels):
        s.prev, s.is_vararg, s.vars, s.nactvar, s.bl = prev, is_vararg, [], 0, None
        s.firstlabel = nlabels

class Parser:
    def __init__(s, toks):
        s.t, s.i = toks, 0
        s.labels = []  # dyd->label: [name, line, nactvar]
        s.gotos = []   # dyd->gt:    [name, line, nactvar]
        s.fs = None

    # -- tokens
    def tok(s): return s.t[s.i][0]
    def val(s): return s.t[s.i][1]
    def line(s): return s.t[s.i][2]
    def lookahead(s): return s.t[s.i + 1][0]
    def adv(s): s.i += 1
    def err(s, msg): raise LuaSyntaxError(f"{s.line()}: {msg} near {s.tok()!r}")
    def testnext(s, k):
        if s.tok() == k: s.adv(); return True
        return False
    def check(s, k):
        if s.tok() != k: s.err(f"'{k}' expected")
    def checknext(s, k): s.check(k); s.adv()
    def check_match(s, what, who, line):
        if not s.testnext(what): s.err(f"'{what}' expected (to close '{who}' at line {line})")
    def str_checkname(s):
        s.check("name"); v = s.val(); s.adv(); return v
    def block_follow(s, withuntil):
        k = s.tok()
        return k in ("else", "elseif", "end", "eof") or (k == "until" and withuntil)

    # -- variables and scopes
    def new_localvar(s, name, kind="reg"):
        fs = s.fs
        if len(fs.vars) + 1 > MAXVARS: s.err("too many local variables (limit is 200)")
        fs.vars.append(Var(name, kind))
    def adjustlocalvars(s, n): s.fs.nactvar += n
    def removevars(s, tolevel):
        fs = s.fs
        del fs.vars[tolevel:]; fs.nactvar = tolevel

    def resolve(s, name):
        """singlevaraux: the Var this name denotes (local or upvalue), or None
        for a global."""
        fs = s.fs
        while fs is not None:
            for v in reversed(fs.vars[:fs.nactvar]):
                if v.name == name: return v
            fs = fs.prev
        return None

    def check_readonly(s, var):
        if var[0] == "name":
            v = s.resolve(var[1])
            if v is not None and v.kind != "reg":
                raise LuaSyntaxError(f"{s.line()}: attempt to assign to const variable '{var[1]}'")

    def enterblock(s, isloop):
        fs = s.fs
        fs.bl = BlockCnt(fs.bl, fs.nactvar, len(s.labels), len(s.gotos), isloop)

    def leaveblock(s):
        fs, bl = s.fs, s.fs.bl
        s.removevars(bl.nactvar)
        if bl.isloop: s.createlabel("break", 0, False)
        del s.labels[bl.firstlabel:]
        fs.bl = bl.prev
        if bl.prev is not None:  # movegotosout
            for g in s.gotos[bl.firstgoto:]: g[2] = bl.nactvar
        elif bl.firstgoto < len(s.gotos):
            g = s.gotos[bl.firstgoto]
            if g[0] == "break": raise LuaSyntaxError(f"break outside a loop at line {g[1]}")
            raise LuaSyntaxError(f"no visible label '{g[0]}' for <goto> at line {g[1]}")

    def findlabel(s, name):
        for lb in s.labels[s.fs.firstlabel:]:
            if lb[0] == name: return lb
        return None

    def createlabel(s, name, line, last):
        fs = s.fs
        lb = [name, line, fs.bl.nactvar if last else fs.nactvar]
        s.labels.append(lb)
        # solvegotos: pending gotos of the current block with this name
        i = fs.bl.firstgoto
        while i < len(s.gotos):
            g = s.gotos[i]
            if g[0] == name:
                if g[2] < lb[2]:
                    v = fs.vars[g[2]].name
                    raise LuaSyntaxError(f"<goto {name}> at line {g[1]} jumps into the scope of local '{v}'")
                del s.gotos[i]
            else:
                i += 1

    def open_func(s, is_vararg):
        s.fs = FuncState(s.fs, is_vararg, len(s.labels))
        s.fs.firstgoto = len(s.gotos)
        s.enterblock(False)

    def close_func(s):
        s.leaveblock()
        s.fs = s.fs.prev

    # -- grammar
    def mainfunc(s):
        s.open_func(True)
        b = s.statlist()
        s.check("eof")
        s.close_func()
        return b

    def statlist(s):
        """block ::= {stat} [retstat]"""
        stats = []
        while not s.block_follow(True):
            if s.tok() == "return":
                s.adv()
                return ("block", stats, s.retstat())
            stats += s.statement()
        return ("block", stats, None)

    def block(s):
        s.enterblock(False)
        b = s.statlist()
        s.leaveblock()
        return b

    def retstat(s):
        es = [] if (s.block_follow(True) or s.tok() == ";") else s.explist()
        s.testnext(";")
        return es

    def statement(s):
        """One statement; returns a list (labelstat also parses the no-op
        statements that follow a label)."""
        line = s.line(); k = s.tok()
        if k == ";": s.adv(); return [("semi",)]
        if k == "if": return [s.ifstat(line)]
        if k == "while":
            s.adv(); c = s.expr(); s.enterblock(True); s.checknext("do")
            b = s.block(); s.check_match("end", "while", line); s.leaveblock()
            return [("while", c, b)]
        if k == "do":
            s.adv(); b = s.block(); s.check_match("end", "do", line)
            return [("do", b)]
        if k == "for": return [s.forstat(line)]
        if k == "repeat":
            s.adv(); s.enterblock(True); s.enterblock(False)
            stats = s.statlist()
            s.check_match("until", "repeat", line)
            c = s.expr()
            s.leaveblock(); s.leaveblock()
            return [("repeat", stats, c)]
        if k == "function":
            s.adv(); fn = s.funcname()
            if not fn[1] and fn[2] is None: s.check_readonly(("name", fn[0]))
            body = s.body(fn[2] is not None, line)
            return [("function", fn, body)]
        if k == "local":
            s.adv()
            if s.testnext("function"):
                x = s.str_checkname(); s.new_localvar(x); s.adjustlocalvars(1)
                return [("localfunction", x, s.body(False, s.line()))]
            return [s.localstat()]
        if k == "::":
            s.adv(); x = s.str_checkname()
            return s.labelstat(x, line)
        if k == "return": s.err("unexpected 'return'")  # handled by statlist
        if k == "break":
            s.adv(); s.gotos.append(["break", line, s.fs.nactvar])
            return [("break",)]
        if k == "goto":
            s.adv(); x = s.str_checkname()
            if s.findlabel(x) is None: s.gotos.append([x, line, s.fs.nactvar])
            return [("goto", x)]
        return [s.exprstat()]

    def labelstat(s, x, line):
        s.checknext("::")
        rest = []
        while s.tok() in (";", "::"): rest += s.statement()
        if s.findlabel(x) is not None:
            raise LuaSyntaxError(f"label '{x}' already defined")
        s.createlabel(x, line, s.block_follow(False))
        return [("label", x)] + rest

    def ifstat(s, line):
        clauses = [s.test_then_block()]
        while s.tok() == "elseif": clauses.append(s.test_then_block())
        els = None
        if s.testnext("else"): els = s.block()
        s.check_match("end", "if", line)
        return ("if", clauses[0][0], clauses[0][1], clauses[1:], els)

    def test_then_block(s):
        s.adv()  # IF / ELSEIF
        c = s.expr(); s.checknext("then")
        return (c, s.block())

    def forstat(s, line):
        s.enterblock(True)
        s.adv(); x = s.str_checkname()
        if s.tok() == "=":
            for _ in range(3): s.new_localvar("(for state)")
            s.new_localvar(x)
            s.adv(); a = s.expr(); s.checknext(","); b = s.expr()
            c = s.expr() if s.testnext(",") else None
            s.adjustlocalvars(3)
            body = s.forbody(1)
            st = ("fornum", x, a, b, c, body)
        elif s.tok() in (",", "in"):
            for _ in range(4): s.new_localvar("(for state)")
            xs = [x]; s.new_localvar(x)
            while s.testnext(","):
                y = s.str_checkname(); xs.append(y); s.new_localvar(y)
            s.checknext("in")
            es = s.explist()
            s.adjustlocalvars(4)
            body = s.forbody(len(xs))
            st = ("forin", xs, es, body)
        else:
            s.err("'=' or 'in' expected")
        s.check_match("end", "for", line)
        s.leaveblock()
        return st

    def forbody(s, nvars):
        s.checknext("do")
        s.enterblock(False)
        s.adjustlocalvars(nvars)
        b = s.block()
        s.leaveblock()
        return b

    def funcname(s):
        x = s.str_checkname(); fields = []; method = None
        while s.testnext("."): fields.append(s.str_checkname())
        if s.testnext(":"): method = s.str_checkname()
        return (x, fields, method)

    def body(s, ismethod, line):
        s.open_func(False)
        s.checknext("(")
        if ismethod: s.new_localvar("self"); s.adjustlocalvars(1)
        params, vararg = [], False
        if s.tok() != ")":
            while True:
                if s.tok() == "name":
                    p = s.str_checkname(); params.append(p); s.new_localvar(p)
                elif s.tok() == "...":
                    s.adv(); vararg = True
                else:
                    s.err("<name> or '...' expected")
                if vararg or not s.testnext(","): break
        s.adjustlocalvars(len(params))
        s.fs.is_vararg = vararg
        s.checknext(")")
        b = s.statlist()
        s.check_match("end", "function", line)
        s.close_func()
        return ("body", params, vararg, b)

    def localstat(s):
        atts, nclose = [], 0
        while True:
            x = s.str_checkname(); kind = "reg"
            if s.testnext("<"):
                a = s.str_checkname(); s.checknext(">")
                if a == "const": kind = "const"
                elif a == "close": kind = "close"
                else: raise LuaSyntaxError(f"{s.line()}: unknown attribute '{a}'")
            s.new_localvar(x, kind)
            if kind == "close":
                nclose += 1
                if nclose > 1: raise LuaSyntaxError("multiple to-be-closed variables in local list")
            atts.append((x, kind))
            if not s.testnext(","): break
        es = s.explist() if s.testnext("=") else []
        s.adjustlocalvars(len(atts))
        return ("local", atts, es)

    def exprstat(s):
        p = s.suffixedexp()
        if s.tok() in ("=", ","):
            targets = [p]
            while s.testnext(","): targets.append(s.suffixedexp())
            vs = []
            for t in targets:
                if t[0] != "var": s.err("syntax error")
                s.check_readonly(t[1]); vs.append(t[1])
            s.checknext("=")
            return ("assign", vs, s.explist())
        if p[0] != "call": s.err("syntax error")
        return ("call", p[1])

    def explist(s):
        es = [s.expr()]
        while s.testnext(","): es.append(s.expr())
        return es

    def primaryexp(s):
        if s.tok() == "(":
            line = s.line(); s.adv(); e = s.expr(); s.check_match(")", "(", line)
            return ("paren", e)
        if s.tok() == "name":
            x = s.val(); s.adv(); return ("var", ("name", x))
        s.err("unexpected symbol")

    def suffixedexp(s):
        p = s.primaryexp()
        while True:
            k = s.tok()
            if k == ".":
                s.adv(); p = ("var", ("field", p, s.str_checkname()))
            elif k == "[":
                s.adv(); e = s.expr(); s.checknext("]"); p = ("var", ("index", p, e))
            elif k == ":":
                s.adv(); m = s.str_checkname(); p = ("call", ("method", p, m, s.funcargs()))
            elif k in ("(", "string", "{"):
                p = ("call", ("call", p, s.funcargs()))
            else:
                return p

    def funcargs(s):
        k = s.tok(); line = s.line()
        if k == "(":
            s.adv()
            es = [] if s.tok() == ")" else s.explist()
            s.check_match(")", "(", line)
            return ("explist", es)
        if k == "{": return ("table", s.constructor())
        if k == "string": v = s.val(); s.adv(); return ("string", v)
        s.err("function arguments expected")

    def constructor(s):
        line = s.line(); s.checknext("{"); fields = []
        while True:
            if s.tok() == "}": break
            if s.tok() == "name" and s.lookahead() == "=":
                x = s.str_checkname(); s.adv(); fields.append(("name", x, s.expr()))
            elif s.tok() == "[":
                s.adv(); k = s.expr(); s.checknext("]"); s.checknext("=")
                fields.append(("index", k, s.expr()))
            else:
                fields.append(("exp", s.expr()))
            if not (s.testnext(",") or s.testnext(";")): break
        s.check_match("}", "{", line)
        return fields

    def simpleexp(s):
        k = s.tok(); v = s.val()
        if k == "flt": s.adv(); return ("float", v)
        if k == "int": s.adv(); return ("int", v)
        if k == "string": s.adv(); return ("string", v)
        if k == "nil": s.adv(); return ("nil",)
        if k == "true": s.adv(); return ("true",)
        if k == "false": s.adv(); return ("false",)
        if k == "...":
            if not s.fs.is_vararg: s.err("cannot use '...' outside a vararg function")
            s.adv(); return ("vararg",)
        if k == "{": return ("table", s.constructor())
        if k == "function":
            line = s.line(); s.adv(); return ("function", s.body(False, line))
        return ("prefix", s.suffixedexp())

    def expr(s, limit=0):
        k = s.tok()
        if k in UNOPS:
            s.adv(); e = ("unop", UNOPS[k], s.expr(UNARY_PRIORITY))
        else:
            e = s.simpleexp()
        while s.tok() in BINOPS and BINOPS[s.tok()][1] > limit:
            op, _, right = BINOPS[s.tok()]
            s.adv()
            e = ("binop", op, e, s.expr(right))
        return e

def parse(src):
    """Parse a Lua 5.4 chunk (bytes) to its AST, or raise LuaSyntaxError."""
    return Parser(lex(src)).mainfunc()

# ---------------------------------------------------------------- pretty-printer

BINOP_SYM = {v[0]: k for k, v in BINOPS.items()}
UNOP_SYM = {v: k for k, v in UNOPS.items()}

def pr_string(b):
    out = []
    for c in b:
        if c == 34: out.append('\\"')
        elif c == 92: out.append("\\\\")
        elif 32 <= c < 127: out.append(chr(c))
        else: out.append("\\%03d" % c)
    return '"' + "".join(out) + '"'

def pr_float(bits):
    x = struct.unpack("<d", struct.pack("<Q", bits))[0]
    if x == float("inf"): return "1e9999"
    assert x == x and x >= 0, x  # a numeral is never negative or NaN
    return x.hex()

def pr_int(v):
    return str(v) if v < 2**63 else "0x%x" % v

def pr_exp(e):
    k = e[0]
    if k in ("nil", "true", "false"): return k
    if k == "int": return pr_int(e[1])
    if k == "float": return pr_float(e[1])
    if k == "string": return pr_string(e[1])
    if k == "vararg": return "..."
    if k == "function": return "function" + pr_body(e[1])
    if k == "prefix": return pr_prefix(e[1])
    if k == "table": return pr_table(e[1])
    if k == "binop": return f"{pr_exp(e[2])} {BINOP_SYM[e[1]]} {pr_exp(e[3])}"
    if k == "unop": return f"{UNOP_SYM[e[1]]} {pr_exp(e[2])}"
    raise AssertionError(e)

def pr_prefix(p):
    if p[0] == "var": return pr_var(p[1])
    if p[0] == "call": return pr_call(p[1])
    return "(" + pr_exp(p[1]) + ")"

def pr_var(v):
    if v[0] == "name": return v[1]
    if v[0] == "index": return f"{pr_prefix(v[1])}[{pr_exp(v[2])}]"
    return f"{pr_prefix(v[1])}.{v[2]}"

def pr_call(c):
    if c[0] == "call": return pr_prefix(c[1]) + pr_args(c[2])
    return f"{pr_prefix(c[1])}:{c[2]}{pr_args(c[3])}"

def pr_args(a):
    if a[0] == "explist": return "(" + ", ".join(pr_exp(e) for e in a[1]) + ")"
    if a[0] == "table": return pr_table(a[1])
    return pr_string(a[1])

def pr_table(fs):
    def f(x):
        if x[0] == "index": return f"[{pr_exp(x[1])}] = {pr_exp(x[2])}"
        if x[0] == "name": return f"{x[1]} = {pr_exp(x[2])}"
        return pr_exp(x[1])
    return "{" + ", ".join(f(x) for x in fs) + "}"

def pr_body(b, ind=""):
    params = list(b[1]) + (["..."] if b[2] else [])
    return "(" + ", ".join(params) + ")\n" + pr_block(b[3], ind + "  ") + ind + "end"

def pr_block(b, ind):
    out = "".join(ind + pr_stat(st, ind) + "\n" for st in b[1])
    if b[2] is not None:
        out += ind + "return" + (" " + ", ".join(pr_exp(e) for e in b[2]) if b[2] else "") + "\n"
    return out

ATTRIB_SYM = {"reg": "", "const": " <const>", "close": " <close>"}

def pr_stat(st, ind):
    k = st[0]; i2 = ind + "  "
    if k == "semi": return ";"
    if k == "assign":
        return ", ".join(pr_var(v) for v in st[1]) + " = " + ", ".join(pr_exp(e) for e in st[2])
    if k == "call": return pr_call(st[1])
    if k == "label": return f"::{st[1]}::"
    if k == "break": return "break"
    if k == "goto": return f"goto {st[1]}"
    if k == "do": return "do\n" + pr_block(st[1], i2) + ind + "end"
    if k == "while": return f"while {pr_exp(st[1])} do\n" + pr_block(st[2], i2) + ind + "end"
    if k == "repeat": return "repeat\n" + pr_block(st[1], i2) + ind + f"until {pr_exp(st[2])}"
    if k == "if":
        out = f"if {pr_exp(st[1])} then\n" + pr_block(st[2], i2)
        for c, b in st[3]: out += ind + f"elseif {pr_exp(c)} then\n" + pr_block(b, i2)
        if st[4] is not None: out += ind + "else\n" + pr_block(st[4], i2)
        return out + ind + "end"
    if k == "fornum":
        step = f", {pr_exp(st[4])}" if st[4] is not None else ""
        return f"for {st[1]} = {pr_exp(st[2])}, {pr_exp(st[3])}{step} do\n" + pr_block(st[5], i2) + ind + "end"
    if k == "forin":
        return (f"for {', '.join(st[1])} in {', '.join(pr_exp(e) for e in st[2])} do\n"
                + pr_block(st[3], i2) + ind + "end")
    if k == "function":
        x, fields, method = st[1]
        name = ".".join([x] + fields) + (f":{method}" if method is not None else "")
        # the implicit `self` of a method is not written
        return f"function {name}" + pr_body(st[2], ind)
    if k == "localfunction": return f"local function {st[1]}" + pr_body(st[2], ind)
    if k == "local":
        out = "local " + ", ".join(x + ATTRIB_SYM[a] for x, a in st[1])
        return out + (" = " + ", ".join(pr_exp(e) for e in st[2]) if st[2] else "")
    raise AssertionError(st)

def pretty(chunk): return pr_block(chunk, "")

# ---------------------------------------------------------------- Lean emitter

def lean_name(x):
    assert re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", x), x
    return f'"{x}"'

def lean_bytes(b): return "[" + ", ".join(str(c) for c in b) + "]"

def lean_list(xs): return "[" + ", ".join(xs) + "]"

def lean_opt(x, f): return "none" if x is None else f"(some {f(x)})"

def le(e):
    k = e[0]
    if k in ("nil", "true", "false"): return "." + k
    if k == "int": return f"(.numeral (.int {e[1]}))"
    if k == "float": return f"(.numeral (.float 0x{e[1]:016x}))"
    if k == "string": return f"(.string {lean_bytes(e[1])})"
    if k == "vararg": return ".vararg"
    if k == "function": return f"(.functiondef {lbody(e[1], '')})"
    if k == "prefix": return f"(.prefixexp {lp(e[1])})"
    if k == "table": return f"(.tableconstructor {lfields(e[1])})"
    if k == "binop": return f"(.binop .{e[1]} {le(e[2])} {le(e[3])})"
    if k == "unop": return f"(.unop .{e[1]} {le(e[2])})"
    raise AssertionError(e)

def lp(p):
    if p[0] == "var": return f"(.var {lv(p[1])})"
    if p[0] == "call": return f"(.functioncall {lc(p[1])})"
    return f"(.paren {le(p[1])})"

def lv(v):
    if v[0] == "name": return f"(.name {lean_name(v[1])})"
    if v[0] == "index": return f"(.index {lp(v[1])} {le(v[2])})"
    return f"(.field {lp(v[1])} {lean_name(v[2])})"

def lc(c):
    if c[0] == "call": return f"(.call {lp(c[1])} {la(c[2])})"
    return f"(.method {lp(c[1])} {lean_name(c[2])} {la(c[3])})"

def la(a):
    if a[0] == "explist": return f"(.explist {lean_list([le(e) for e in a[1]])})"
    if a[0] == "table": return f"(.tableconstructor {lfields(a[1])})"
    return f"(.string {lean_bytes(a[1])})"

def lfields(fs):
    def f(x):
        if x[0] == "index": return f"(.index {le(x[1])} {le(x[2])})"
        if x[0] == "name": return f"(.name {lean_name(x[1])} {le(x[2])})"
        return f"(.exp {le(x[1])})"
    return lean_list([f(x) for x in fs])

def lbody(b, ind):
    return (f"(.mk {lean_list([lean_name(x) for x in b[1]])} {'true' if b[2] else 'false'} "
            f"{lblock(b[3], ind)})")

def lblock(b, ind):
    ret = lean_opt(b[2], lambda es: lean_list([le(e) for e in es]))
    if not b[1]: return f"(.mk [] {ret})"
    inner = ind + "  "
    return ("(.mk [\n" + ",\n".join(inner + ls(st, inner) for st in b[1]) + f"] {ret})")

def ls(st, ind):
    k = st[0]
    if k == "semi": return ".semi"
    if k == "assign": return f".assign {lean_list([lv(v) for v in st[1]])} {lean_list([le(e) for e in st[2]])}"
    if k == "call": return f".functioncall {lc(st[1])}"
    if k == "label": return f".label {lean_name(st[1])}"
    if k == "break": return ".break_"
    if k == "goto": return f".goto_ {lean_name(st[1])}"
    if k == "do": return f".do_ {lblock(st[1], ind)}"
    if k == "while": return f".while_ {le(st[1])} {lblock(st[2], ind)}"
    if k == "repeat": return f".repeat_ {lblock(st[1], ind)} {le(st[2])}"
    if k == "if":
        eifs = lean_list([f"({le(c)}, {lblock(b, ind)})" for c, b in st[3]])
        return f".if_ {le(st[1])} {lblock(st[2], ind)} {eifs} {lean_opt(st[4], lambda b: lblock(b, ind))}"
    if k == "fornum":
        return (f".fornum {lean_name(st[1])} {le(st[2])} {le(st[3])} {lean_opt(st[4], le)} "
                f"{lblock(st[5], ind)}")
    if k == "forin":
        return (f".forin {lean_list([lean_name(x) for x in st[1]])} "
                f"{lean_list([le(e) for e in st[2]])} {lblock(st[3], ind)}")
    if k == "function":
        x, fields, method = st[1]
        fn = f"⟨{lean_name(x)}, {lean_list([lean_name(y) for y in fields])}, {lean_opt(method, lean_name)}⟩"
        return f".function_ {fn} {lbody(st[2], ind)}"
    if k == "localfunction": return f".localfunction {lean_name(st[1])} {lbody(st[2], ind)}"
    if k == "local":
        atts = lean_list([f"⟨{lean_name(x)}, .{a}⟩" for x, a in st[1]])
        return f".local_ {atts} {lean_list([le(e) for e in st[2]])}"
    raise AssertionError(st)

def lean_file(rel, src, name, chunk):
    shown = src.decode("utf-8").replace("-/", "- /").rstrip("\n") + "\n"
    return (f"import Lua.Ast.Syntax\n\n/-! GENERATED by scripts/gen_ast.py from `{rel}` -- do not edit.\n\n"
            f"```lua\n{shown}```\n-/\n\nnamespace Lua.Programs\n\nopen Lua.Ast\n\n"
            f"/-- The AST of `{rel}`. -/\ndef {name} : Chunk := {lblock(chunk, '')}\n\n"
            f"end Lua.Programs\n")

# ---------------------------------------------------------------- checks against luac

def listing(luac, path):
    r = subprocess.run([luac, "-p", "-l", "-l", path], capture_output=True)
    if r.returncode != 0: return None, r.stderr.decode("latin-1")
    out = r.stdout.decode("latin-1")
    out = re.sub(r"<[^>]*:\d+,\d+>", "<src>", out)       # function <file:first,last>
    out = re.sub(r"0x[0-9a-f]+", "0x?", out)             # proto addresses
    out = re.sub(r"^(\t\d+\t)\[\d+\]", r"\1[?]", out, flags=re.M)  # instruction lines
    return out, None

def roundtrip(luac, files):
    bad = 0
    with tempfile.TemporaryDirectory() as tmp:
        for f in files:
            src = open(f, "rb").read()
            try:
                ast = parse(src)
            except LuaSyntaxError as e:
                ok, err = listing(luac, f)
                if ok is None: print(f"{f}: rejected by both (ok): {e}"); continue
                print(f"{f}: FAIL: parser rejects valid Lua: {e}"); bad += 1; continue
            text = pretty(ast).encode("ascii")
            p = os.path.join(tmp, "rt.lua"); open(p, "wb").write(text)
            try:
                ast2 = parse(text)
            except LuaSyntaxError as e:
                print(f"{f}: FAIL: printed text does not re-parse: {e}"); bad += 1; continue
            if ast2 != ast: print(f"{f}: FAIL: re-parse gives a different AST"); bad += 1; continue
            l1, e1 = listing(luac, f)
            l2, e2 = listing(luac, p)
            if l1 is None: print(f"{f}: FAIL: parser accepts, luac rejects: {e1}"); bad += 1; continue
            if l2 is None: print(f"{f}: FAIL: luac rejects the printed text: {e2}"); bad += 1; continue
            if l1 != l2: print(f"{f}: FAIL: luac -l -l listings differ"); bad += 1; continue
            print(f"{f}: ok ({len(l1.splitlines())} listing lines)")
    return bad

def differential(luac, files, n, seed):
    """Token-level mutants (delete, duplicate or swap a token span): this
    parser accepts exactly when `luac -p` does."""
    rng = random.Random(seed); bad = 0; tried = 0; acc = 0
    with tempfile.TemporaryDirectory() as tmp:
        p = os.path.join(tmp, "m.lua")
        for f in files:
            src = open(f, "rb").read()
            spans = [m.span() for m in re.finditer(rb"\S+", src)]
            if not spans: continue
            for _ in range(n):
                i = rng.randrange(len(spans)); a, b = spans[i]
                j = rng.randrange(len(spans)); c, d = spans[j]
                op = rng.randrange(4)
                if op == 0: m = src[:a] + src[b:]
                elif op == 1: m = src[:a] + src[c:d] + b" " + src[a:]
                elif op == 2: m = src[:a] + b" " + src[c:d] + b" " + src[b:]
                else: m = src[:a] + rng.choice([b"goto x", b"::x::", b"break", b"local y <const> = 1 y = 2",
                                                 b"...", b"local z <close>, w <close>", b"return",
                                                 b"::y:: ::y::", b"0x1p", b"3..2", b"'\\q'",
                                                 b"local a <foo>", b"do goto e end local q ::e:: print(q)"]) + b" " + src[a:]
                open(p, "wb").write(m)
                try: parse(m); mine = True; err = ""
                except LuaSyntaxError as e: mine = False; err = str(e)
                except RecursionError: mine = None
                r = subprocess.run([luac, "-p", p], capture_output=True)
                theirs = r.returncode == 0
                tried += 1; acc += theirs
                if mine is None: continue
                if mine != theirs:
                    msg = r.stderr.decode("latin-1").strip()
                    if not theirs and re.search(r"too many|overflow|control structure too long|registers", msg):
                        continue  # implementation limits: not enforced (documented)
                    bad += 1
                    print(f"{f}: MISMATCH (parser {'accepts' if mine else 'rejects: ' + err}; luac: {msg or 'accepts'})")
                    open(p + f".{bad}", "wb").write(m)
    print(f"differential: {tried} mutants, {acc} valid, {bad} mismatches")
    return bad

# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sources", nargs="+")
    ap.add_argument("--name"); ap.add_argument("-o", "--out")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--roundtrip", action="store_true")
    ap.add_argument("--differential", type=int, metavar="N", default=0)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--luac", default=os.path.join(ROOT, "c", "luac"))
    a = ap.parse_args()
    sys.setrecursionlimit(20000)
    if a.roundtrip or a.differential:
        bad = roundtrip(a.luac, a.sources) if a.roundtrip else 0
        if a.differential: bad += differential(a.luac, a.sources, a.differential, a.seed)
        sys.exit(1 if bad else 0)
    if len(a.sources) != 1 or not a.name or not a.out: ap.error("need one source, --name and -o")
    src = open(a.sources[0], "rb").read()
    try:
        chunk = parse(src)
    except LuaSyntaxError as e:
        sys.exit(f"{a.sources[0]}: syntax error: {e}")
    rel = os.path.relpath(os.path.abspath(a.sources[0]), ROOT)
    t = lean_file(rel, src, a.name, chunk)
    if a.check:
        ok = os.path.exists(a.out) and open(a.out).read() == t
        print(f"{a.out}: {'ok' if ok else 'DRIFT'}"); sys.exit(0 if ok else 1)
    os.makedirs(os.path.dirname(a.out) or ".", exist_ok=True); open(a.out, "w").write(t)
    print("wrote", a.out)

if __name__ == "__main__":
    main()

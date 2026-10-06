#!/usr/bin/env python3
"""Programs for the end-to-end differential test of the bytecode semantics
(`Lua/Bytecode/Semantics.lean`: `Value.flt`, `δ`, `fastArith`,
`forprepK`/`forloopK`, `Value.show`, string coercion) against the ELF on
Sail (`run_sem.sh`).

Writes, next to this file:
  sem_<k>.lua      programs inside `Supported` (one main chunk, no tables or
                   functions, globals only `print`) that print many lines;
  sem_err_<k>.lua  programs that print one line and then raise an error (the
                   ELF exits nonzero, `Lua.Bytecode.run` gives `none`).
Every operand comes from a local assigned from a literal, so host `luac`
cannot constant-fold the operation (it would fold with the host's libm).
NaN is made at run time (`zero / zero`), -NaN as `-nan`, inf as `big * ten`.
Deterministic (seeded).
"""
import os, random, re, struct, glob

HERE = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(20261006)
MAXI = 2**63 - 1

def dbl(b): return struct.unpack('<d', struct.pack('<Q', b & (2**64 - 1)))[0]

# A value is a Lua expression over the prelude's locals; ints are tagged so
# the generator can avoid integer division by zero in the main programs.
PRELUDE = ("local zero = 0.0 local nan = zero / zero local big = 1e308 local ten = 10 "
           "local inf = big * ten local mi = -9223372036854775807 - 1\n"
           "local a, b, s, t = 0, 0, 0, 0\n")

def I(n):
    if n == -2**63: return ('mi', 'int', n)
    return (str(n), 'int', n)
def F(x, src=None):
    if src is None:
        r = repr(x)
        if r == 'inf': src = 'inf'
        elif r == '-inf': src = '-inf'
        else: src = r if ('.' in r or 'e' in r or 'n' in r) else r + '.0'
    return (src, 'flt', x)
NAN = ('nan', 'flt', float('nan'))
NNAN = ('-nan', 'flt', float('nan'))
LITINF = ('1e999', 'flt', float('inf'))       # an inf constant (LOADK)

INTS = [I(n) for n in [0, 1, -1, 2, 3, -3, 7, -7, 10, -10, 255, 123456789,
                       2**53 - 1, 2**53, 2**53 + 1, 2**62, MAXI, -MAXI, -2**63]]
FLTS = [F(x) for x in [0.0, 0.5, -0.5, 1.5, -2.25, 3.0, -3.0, 7.75, -7.75, 0.1, 0.2,
                       1e308, -1e308, 5e-324, 2.2250738585072014e-308, 1e-310,
                       2.0**53, 2.0**53 + 2, 2.0**63, -2.0**63, 1e300, 123456.789, 1e15,
                       1e16, 2.0, -1.0, 2.0**62]] + \
       [('-0.0', 'flt', -0.0), F(float('inf')), F(float('-inf')), NAN, NNAN, LITINF]
ALL = INTS + FLTS

def pick(srcs, pool):
    d = {v[0]: v for v in pool}
    return [d[s] for s in srcs]

CORE = pick(['0', '1', '-1', '3', '-7', '9007199254740993', '9223372036854775807', 'mi',
             '4611686018427387904', '0.0', '-0.0', '0.5', '-2.25', '3.0', '7.75', '0.1',
             '1e+308', '5e-324', '1e-310', '9.223372036854776e+18', '-9.223372036854776e+18',
             'inf', '-inf', 'nan', '-nan', '9007199254740992.0'], ALL)

ARITH = ['+', '-', '*', '/', '//', '%', '^']

def write(name, body):
    with open(os.path.join(HERE, name + '.lua'), 'w') as f:
        f.write(PRELUDE + body)

def chunks(lines, n):
    return [lines[i:i + n] for i in range(0, len(lines), n)]

def arith_line(x, y, lhs='a', rhs='b'):
    ops = [o for o in ARITH
           if not (o in ('//', '%') and x[1] == 'int' and y[1] == 'int' and y[2] == 0)]
    return f"{lhs} = {x[0]} {rhs} = {y[0]} print(" + ", ".join(f"{lhs} {o} {rhs}" for o in ops) + ")"

files = []

# 1. binary arithmetic: CORE x CORE, plus random pairs over ALL
pairs = [(x, y) for x in CORE for y in CORE]
pairs += [(rng.choice(ALL), rng.choice(ALL)) for _ in range(150)]
# negative divisors, fractional parts, int // -1 and minint
for x in pick(['7', '-7', '10', '-10', '9223372036854775807', 'mi', '7.75', '-7.75', '1.5'], ALL):
    for y in pick(['-1', '3', '-3', '-0.5', '0.5', '-2.25', '2.0', '-1.0', 'inf', '-inf'], ALL):
        pairs.append((x, y))
for i, ch in enumerate(chunks([arith_line(x, y) for x, y in pairs], 160), 1):
    write(f'sem_arith_{i}', "\n".join(ch) + "\n"); files.append(f'sem_arith_{i}')

# 2. comparisons
CMPV = pick(['0', '1', '-1', '9007199254740991', '9007199254740992', '9007199254740993',
             '9223372036854775807', 'mi', '4611686018427387904', '0.0', '-0.0', '0.5', '-0.5',
             '9007199254740992.0', '9007199254740994.0', '9.223372036854776e+18',
             '-9.223372036854776e+18', 'inf', '-inf', 'nan', '1e+308', '5e-324', '2.0', '-1.0'], ALL)
CMPV += [F(9.223372036854775e18), F(-9.223372036854778e18), F(-5e-324), I(MAXI - 1), I(-MAXI)]
cl = [f"a = {x[0]} b = {y[0]} print(a < b, a <= b, a == b, a ~= b, a > b, a >= b)"
      for x in CMPV for y in CMPV]
for i, ch in enumerate(chunks(cl, 150), 1):
    write(f'sem_cmp_{i}', "\n".join(ch) + "\n"); files.append(f'sem_cmp_{i}')
# comparisons against constants (EQK/EQI/LTI/LEI/GTI/GEI, float immediates)
kl = []
for x in ALL:
    kl.append(f"a = {x[0]} print(a == 1, a == 1.0, a == 2.5, a == \"1\", a ~= 0, a ~= 0.0, "
              f"a < 3, a <= 3.0, a > -2, a >= -2, a < 1.5, a >= 0.5, 3 < a, -2.0 >= a)")
kl.append('a = "10" b = "9" print(a < b, a <= b, a == b, a > b, a .. "" == "10", "" < a)')
kl.append('a = "a" b = "ab" print(a < b, a <= b, a == b, a > b, a >= "a", a ~= "a")')
write('sem_cmpk', "\n".join(kl) + "\n"); files.append('sem_cmpk')

# 3. bitwise: integers and integral floats in range
BITV = pick(['0', '1', '-1', '3', '-7', '255', '123456789', '9223372036854775807', 'mi',
             '9007199254740993', '0.0', '-0.0', '3.0', '2.0', '-1.0', '9007199254740992.0',
             '-9.223372036854776e+18', '4.611686018427388e+18', '1000000000000000.0'], ALL)
SH = pick(['0', '1', '-1', '3', '-7', '3.0', '-1.0'], ALL) + [I(63), I(64), I(-63), I(-64), I(100), F(62.0)]
bl = []
for x in BITV:
    for y in BITV:
        bl.append(f"a = {x[0]} b = {y[0]} print(a & b, a | b, a ~ b)")
    for y in SH:
        bl.append(f"a = {x[0]} b = {y[0]} print(a << b, a >> b)")
    bl.append(f"a = {x[0]} print(~a, a & 0xFF, a | 1, a ~ 3, a << 2, a >> 1, 1 << a, a >> 63, a << -1)")
for i, ch in enumerate(chunks(bl, 300), 1):
    write(f'sem_bit_{i}', "\n".join(ch) + "\n"); files.append(f'sem_bit_{i}')

# 4. unary minus, not, tostring through `..`, `#`
ul = [f"a = {x[0]} print(-a, not a, a .. \"\", #(a .. \"\"), a .. \"x\", -(-a))" for x in ALL]
STRS = ['"10"', '"1.5"', '"0x10"', '"0x1p4"', '"1e2"', '" 7 "', '" 2 "', '"-3"',
        '"0x7fffffffffffffff"', '"0xffffffffffffffff"', '"9223372036854775808"',
        '"  0x1P-2  "', '"0.1"', '"-0"', '"2"', '"3"', '"1e999"', '"0xA.8p0"', '"-0.0"',
        '"9007199254740993"', '"\\t5\\n"', '"0"']
ul += [f"s = {x} print(-s, s .. 1, #s, s .. 1.5)" for x in STRS]
write('sem_unm', "\n".join(ul) + "\n"); files.append('sem_unm')

# 5. string coercion in arithmetic
def tonum(lit):
    s = lit.strip('"').encode().decode('unicode_escape').strip()
    if re.fullmatch(r'[+-]?\d+', s):
        n = int(s)
        return ('int', n) if -2**63 <= n <= MAXI else ('flt', float(n))
    if re.fullmatch(r'[+-]?0[xX][0-9a-fA-F]+', s):
        return ('int', int(s, 16))
    return ('flt', None)
def sline(x, y):
    isstr = lambda v: isinstance(v, str)
    tx = tonum(x) if isstr(x) else (x[1], x[2])
    ty = tonum(y) if isstr(y) else (y[1], y[2])
    xs = x if isstr(x) else x[0]
    ys = y if isstr(y) else y[0]
    ops = [o for o in ARITH if not (o in ('//', '%') and tx[0] == 'int' and ty[0] == 'int'
                                    and (ty[1] == 0 or ty[1] % 2**64 == 0))]
    return f"s = {xs} t = {ys} print(" + ", ".join(f"s {o} t" for o in ops) + ")"
SNUM = pick(['0', '1', '-1', '3', '-7', '9223372036854775807', '0.0', '-0.0', '0.5', '-2.25',
             'inf', 'nan', '3.0', '1e+308'], ALL)
sl = []
for x in STRS[:12]:
    for y in STRS[:12]:
        sl.append(sline(x, y))
for x in STRS:
    for y in SNUM:
        sl.append(sline(x, y)); sl.append(sline(y, x))
sl += ['s = "10" print(s + 1, s * 2, s - 0.5, s // 3, s % 3, s ^ 2, s / 4)',
       's = "1.5" t = "2" print(s * t, s + t, s // t, s % t)',
       's = "0x1p4" print(s + 0, s * 1, s // 1)', 's = "1e2" print(s // 3, s % 3)',
       's = " 7 " t = "3" print(s % t, s // t)', 's = "2" t = "0.5" print(s ^ t)',
       's = "3" print(s / 2, 2 / s, 1 - s, 0.5 + s, s + 0.0)']
for i, ch in enumerate(chunks(sl, 300), 1):
    write(f'sem_str_{i}', "\n".join(ch) + "\n"); files.append(f'sem_str_{i}')

# 6. printing floats (constants and computed), and `..` of them
FP = [1.0, 100.0, 1e15, 1e16, 2.0**53, 1e-5, 5e-324, 1e14, 123456789012345.0,
      1234567890123456.0, 0.1, 1e21, 1e-7, 3.14159265358979, 1e100, 1e-100, 0.5, 2.5e-5,
      1.7976931348623157e308, 2.2250738585072014e-308, 99999999999999.9, 999999999999999.0,
      0.30000000000000004, 1e+300, 4.9406564584124654e-324, 6.02214076e23, 1.0000000000000002]
for _ in range(120):
    kind = rng.random()
    if kind < 0.4: x = dbl(rng.getrandbits(64))
    elif kind < 0.7: x = rng.uniform(-1e6, 1e6)
    elif kind < 0.85: x = round(rng.uniform(-1e4, 1e4), rng.randint(0, 6))
    else: x = float(rng.randint(-2**60, 2**60))
    if x != x or x in (float('inf'), float('-inf')): continue
    FP.append(x)
pl = []
for x in FP:
    v = F(x)
    pl.append(f"a = {v[0]} b = -a print(a, b, a .. \"\", b .. \"x\")")
pl += ['a = 0.1 b = 0.2 print(a + b, a * 3, (a + b) .. "")',
       'a = 1 b = 3 print(a / b, 2 / b, a / 7, 1e15 + a, a .. "", 1e100 .. "x")',
       'a = 2 b = 53 print(a ^ b, a ^ 63, a ^ 64, a ^ -1074, a ^ 1023, a ^ 1024)',
       'a = 0.0 print(a, -a, a .. "", -a .. "", inf, -inf, nan, -nan, inf .. "", nan .. "")',
       'a = 1e300 b = 1e10 print(a * b, -a * b, a * b - a * b, 1.5 .. "", ten // 3.0, ten % -3.0)']
write('sem_print', "\n".join(pl) + "\n"); files.append('sem_print')

# 7. numeric for
LOOPS = [
    'for i = 0.5, 3 do print(i) end',
    'for i = 1, 2, 0.25 do print(i) end',
    'for i = 3, 1, -0.5 do print(i) end',
    'for i = 1.0, 3 do print(i) end',
    'for i = 1, 3, 1.0 do print(i) end',
    'for i = 0.1, 1, 0.1 do print(i) end',
    'for i = 1, 3.7 do print(i) end',
    'for i = 3, 1.2, -1 do print(i) end',
    'for i = -1, -3.5, -1 do print(i) end',
    'for i = 1, 0 do print(i) end',
    'for i = 1, -inf do print(i) end',
    'for i = 1, inf do print(i) if i >= 4 then break end end',
    'for i = 1.0, inf do print(i) if i >= 4 then break end end',
    'for i = 1, nan do print(i) end',
    'for i = 1, nan, -1 do print(i) if i < -2 then break end end',
    'for i = 1.0, nan do print(i) end',
    'for i = nan, 3 do print(i) end',
    'for i = "1", 3 do print(i) end',
    'for i = 1, "3" do print(i) end',
    'for i = 1, 3, "1" do print(i) end',
    'for i = "0x10", 18 do print(i) end',
    'for i = " 2 ", "4.5" do print(i) end',
    'for i = 9223372036854775800, 1e300 do print(i) end',
    'for i = mi + 3, -1e300, -1 do print(i) end',
    'for i = 9223372036854775806, 9223372036854775807 do print(i) end',
    'for i = mi, mi + 2 do print(i) end',
    'for i = 1, 9223372036854775807, 4611686018427387904 do print(i) end',
    'for i = 9007199254740990.0, 9007199254740994.0, 2 do print(i) end',
    'for i = 9007199254740991, 9007199254740994.0 do print(i) end',
    'for i = 1e308, inf, 1e308 do print(i) if i > 1e308 then break end end',
    'for i = -0.0, 1 do print(i) end',
    'for i = 0, -0.0 do print(i) end',
    'for i = 1, 3 do for j = i, 3, 0.5 do print(i, j) end end',
    'for i = 3, 1, -1 do for j = 1.5, i do print(i * j, i // j, i % j) end end',
    'for i = 1, 2 do local x = i * 0.5 while x < 2 do print(x) x = x + 0.75 end end',
    'for i = 2.5, 1, -0.5 do if i == 2 then print("two", i) elseif i < 2 then print("lt", i) end end',
]
ll = []
for n, L in enumerate(LOOPS, 1):
    ll.append(f'print("loop {n}")')
    ll.append(L)
write('sem_for', "\n".join(ll) + "\n"); files.append('sem_for')

# error programs: each prints one line, then raises
ERRS = {
    'idiv0': 'a = 5 b = 0 print(a) print(a // b)',
    'mod0': 'a = 5 b = 0 print(a) print(a % b)',
    'idivk0': 'a = mi print(a) print(a // 0)',
    'modk0': 'a = -1 print(a) print(a % 0)',
    'stridiv0': 's = "7" t = "0" print(s) print(s // t)',
    'strarith': 's = "abc" print(s) print(s + 1)',
    'strnan': 's = "nan" print(s) print(s * 2)',
    'strbit': 's = "3" print(s) print(s | 0)',
    'bitfrac': 'a = 1.5 b = 0 print(a) print(a | b)',
    'bitrange': 'a = 1e100 b = 1 print(a) print(a & b)',
    'bitnan': 'print(nan) print(nan ~ 1)',
    'bnotfrac': 'a = 2.5 print(a) print(~a)',
    'shlinf': 'a = 1 print(a) print(a << inf)',
    'unmstr': 's = "abc" print(s) print(-s)',
    'cmpstr': 'a = 1 s = "2" print(a) print(a < s)',
    'forstep0': 'print(1) for i = 1, 3, 0 do print(i) end',
    'forstep0f': 'print(1) for i = 1.0, 3, 0.0 do print(i) end',
    'forstepneg0': 'b = -0.0 print(b) for i = 1, 3, b do print(i) end',
    'forinitstr': 's = "x" print(s) for i = s, 3 do print(i) end',
    'forlimitstr': 's = "y" print(s) for i = 1, s do print(i) end',
    'forstepstr': 's = "z" print(s) for i = 1, 3, s do print(i) end',
}
for k, body in ERRS.items():
    write(f'sem_err_{k}', body + "\n")

# drop stale programs
keep = set(files) | {f'sem_err_{k}' for k in ERRS}
for p in glob.glob(os.path.join(HERE, 'sem_*.lua')):
    if os.path.basename(p)[:-4] not in keep:
        os.remove(p)

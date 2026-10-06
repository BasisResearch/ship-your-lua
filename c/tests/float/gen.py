#!/usr/bin/env python3
"""Vectors for the differential tests of `Lua/Num/Decimal.lean` against the ELF.

Writes, next to this file:
  fmt.vec    one double per line, as its 64 bits in hex;
  fmt_*.lua  print `tostring` of each (`tostringbuff`, `%.14g`);
  parse.vec  one Lua string per line, as its bytes in hex;
  parse_*.lua print `tonumber` of each (`luaO_str2num`): `nil`, `I <int>`,
             or `F <tostring> <bits as int64>`.
`scripts/test_decimal.lean` computes the same lines from the `.vec` files;
`run.sh` compares them with the ELF on Sail. Deterministic (seeded).
"""
import os, random, re, struct
from decimal import Decimal, getcontext

getcontext().prec = 2000
HERE = os.path.dirname(os.path.abspath(__file__))
rng = random.Random(20261006)

def bits(x): return struct.unpack('<Q', struct.pack('<d', x))[0]
def dbl(b): return struct.unpack('<d', struct.pack('<Q', b & (2**64 - 1)))[0]
def nxt(x, d=1): return dbl(bits(x) + d) if x >= 0 else dbl(bits(x) - d)

# ---------------------------------------------------------------- fmt
F = []
F += [0, 1 << 63, 0x7ff0000000000000, 0xfff0000000000000, 0x7ff8000000000000,
      0xfff8000000000000, 0x7ff0000000000001, 0x7ff4000000000000,
      0xfff0000000000001, 0x7fffffffffffffff, 0xffffffffffffffff]
# subnormals and the normal boundary
F += [1, 2, 3, 0x000fffffffffffff, 0x0008000000000000, 0x400, 0x8000000000000001,
      0x0010000000000000, 0x0010000000000001, 0x7fefffffffffffff, 0xffefffffffffffff]
F += [rng.randrange(1, 1 << 52) for _ in range(20)]
# named values
for x in [1e15, 1e16, 2.0**53, 2.0**53 + 2, 2.0**53 - 1, 2.0**63, 2.0**64, 1e21, 1e22,
          1e23, 100000000000000.5, 123456789012345.0, 99999999999999.0,
          999999999999999.0, 99999999999999.5, 1e14, 1e14 - 1, 0.1, 0.2, 0.3,
          0.1 + 0.2, 1 / 3, 2 / 3, 1e-4, 1e-5, 0.00012345678901234, 1e308, 1e-308,
          1e-320, 2.5, 0.5, 1.5, 100.0, -1.0, 3.14159, 1e100, 2.0**-1074,
          9.99999999999995e-5, 9.999999999999949e-5, 9.99999999999995e-6,
          # integer ties at the 14th digit (`keepsZeros`): kept zeros, bumps, carries
          100000000000005.0, 100000000000015.0, 100000000000095.0, 120000000000005.0,
          999999999999995.0, 999999999999985.0, 649981820981505.0, 100000000000025.0,
          99999999999995.0, 4503599627370495.0]:
    F += [bits(x), bits(-x)]
# powers of two and ten
F += [bits(2.0**k) for k in range(-1074, 1024, 9)]
for k in range(-323, 309, 3):
    x = float('1e%d' % k)
    F += [bits(x), bits(nxt(x)), bits(nxt(x, -1))]
# 14-digit boundaries: 9.99999999999995·10^k and neighbours
for k in range(-8, 22):
    x = float('9.99999999999995e%d' % k)
    F += [bits(x), bits(nxt(x)), bits(nxt(x, -1))]
# exact ties at the 15th significant digit
for _ in range(25):
    a = rng.randrange(10**12, 10**13)
    F += [bits(a + 0.25), bits(a + 0.75)]
    b = rng.randrange(10**11, 10**12)
    F += [bits(b + f) for f in (0.125, 0.375, 0.625, 0.875)]
    c = rng.randrange(10**13, 10**14) * 10 + 5
    F += [bits(float(c)), bits(rng.randrange(10**13, 10**14) + 0.5)]
# random bit patterns (finite) and log-uniform values around the %e/%f switch
F += [rng.randrange(0, 0x7ff0000000000000) | (rng.randrange(2) << 63) for _ in range(150)]
F += [bits(10 ** rng.uniform(-7, 17)) for _ in range(120)]
F += [bits(float('%.*g' % (rng.randrange(1, 8), 10 ** rng.uniform(-5, 15)))) for _ in range(60)]

# ---------------------------------------------------------------- parse
P = []
P += ["0", "-0", "  12  ", "0x10", "0XFF", "0xffffffffffffffff", "0x10000000000000000",
      "9223372036854775807", "9223372036854775808", "-9223372036854775808",
      "-9223372036854775809", "18446744073709551616", "1 2", "", " ", "0x", "+0x1",
      "-0x1", "00012", "1\0", "\0", "1\0 ", "+", "-", "+-1", "--1", "0x-1", "1e5 n"]
P += ["1.5", ".5", "5.", "1e5", "1E+05", "1e-5", "  -0.0  ", "\t1.5\n", "1e", "1e+", "e5",
      ".", "-.", "1.5e3.2", "0.1", "0.2", "0.3", "-0.5e-3", "1.e1", "+.5", ".e1", "0e5",
      "0.000", "000.000e-99999", "\t\n\v\f\r 1.5 \t\n\v\f\r", "1.5x", "1..5", "1e+-5",
      "1e0005", "1e-0", "100000000000000.5", "123456789012345.0", "1e15", "1e16",
      "9007199254740992.0", "9007199254740993.0", "9007199254740995.0",
      "9007199254740993.00000000000000000001", "9007199254740992.99999999999999999",
      "1e308", "1.7976931348623157e308", "1.7976931348623158e308",
      "1.7976931348623159e308", "1e309", "1e-324", "4.9e-324", "5e-324", "3e-324",
      "2.4703282292062327e-324", "2.4703282292062328e-324",
      "2.2250738585072011e-308", "2.2250738585072012e-308", "2.2250738585072014e-308",
      "1e19999", "1e-19999", "1e20000", "1e400", "-1e-400", "1e999999999999999999"]
# n/N: rejected (l_str2d)
P += ["inf", "nan", "-inf", "1n", "0x1n", "1.5n", "infinity", "NaN", "  nan  ", "1e5N",
      "0x1pn", "INF", "i", "0xan"]
# hex floats, including gethex's deviations from correct rounding
P += ["0x1p4", "0x1.8", "0x.8", "0X1P-1", "0x1p", "0x1p+", "0x.", "0x0.", "0x.p1",
      "0x0.p1", "-0x0p0", "0x.0p1", "0x1.fffffffffffffp1023", "0x1.fffffffffffff8p1023",
      "0x1.fffffffffffff7ffp1023", "0x1p1024", "0x1p-1074", "0x1p-1075", "0x1.8p-1075",
      "0x1.00000000000001p-1075", "0x1p-1076", "0x0.0000000000001p-1022",
      "0x0.00000000000008p-1022", "0x0.00000000000018p-1022", "0x40000000000003p0",
      "0x80000000000006p0", "0x80000000000005p0", "0x80000000000007p0",
      "0x100000000000005p0", "0x10000000000000ap0", "0x1.00000000000008p0",
      "0x1.00000000000018p0", "0x1.000000000000081p0", "0x1p4294967296",
      "0x1p4294967297", "0x1p2147483647", "0x1p2147483648", "0x1p-2147483648",
      "0x1p-4294967295", "-0x1p-5000", "0x1P+3", "0x1p-0", " 0x1p4 ", "0x10.8p0",
      "0xABCDEFp-4", "0x00000.0001p0", "-0x.1"]
for _ in range(60):
    nd = rng.randrange(1, 22)
    ds = ''.join(rng.choice('0123456789abcdefABCDEF') for _ in range(nd))
    if rng.random() < 0.6:
        i = rng.randrange(0, nd + 1)
        ds = ds[:i] + '.' + ds[i:]
    if ds == '.':
        ds = '1.'
    s = ('-' if rng.random() < 0.3 else '') + '0x' + ds
    if '.' not in ds or rng.random() < 0.8:
        s += 'p%d' % rng.randrange(-1150, 1100)
    P.append(s)
# random decimals: 1-40 significant digits, the whole exponent range
for _ in range(150):
    nd = rng.randrange(1, 41)
    ds = str(rng.randrange(1, 10)) + ''.join(rng.choice('0123456789') for _ in range(nd - 1))
    e = rng.randrange(-345, 315)
    i = rng.randrange(0, nd + 1)
    P.append(('-' if rng.random() < 0.2 else '') + ds[:i] + '.' + ds[i:] + 'e%d' % e)
# shortest round trips and 16-digit neighbours of random doubles
for _ in range(40):
    x = dbl(rng.randrange(0, 0x7ff0000000000000))
    P += [repr(x), '%.16g' % x]
# exact binary midpoints (ties to even) and just around them
for k in range(45):
    if k < 8:
        b = rng.randrange(1, 1 << 52)                 # subnormal
    elif k < 10:
        b = 0x7fefffffffffffff - (k - 8)                # the overflow boundary
    else:
        b = rng.randrange(0x0010000000000000, 0x7fefffffffffffff)
    lo, hi = Decimal(dbl(b)), Decimal(dbl(b + 1)) if b != 0x7fefffffffffffff else Decimal(2) ** 1024
    mid = (lo + hi) / 2
    s = format(mid, 'f') if abs(mid.adjusted()) < 30 else format(mid, 'e')
    P.append(s)
    m, _, ex = format(mid, 'e').partition('e')
    P.append(m + '1e' + ex)                            # just above
    P.append(format(mid - Decimal(10) ** (mid.adjusted() - 60), 'e'))   # just below

# strtod's exponent saturation (strtod.c:412-416) needs 20k-character
# numerals; they go last, in their own program (`_strtod_l`'s bignum path on
# 20,006 digits is slow on Sail)
LONG = ["0." + "0" * 20005 + "1e20010", "1" + "0" * 20005 + "e-20010"]

def lua_str(s):
    """A Lua expression for the byte string `s` (runs of 64+ equal bytes
    through `string.rep`, to keep the chunk under the ELF's 64 KiB region)."""
    def lit(t):
        out = []
        for ch in t.encode('latin-1'):
            out.append(chr(ch) if 32 <= ch < 127 and ch not in (34, 92) else '\\%03d' % ch)
        return '"' + ''.join(out) + '"'
    parts = []
    for m in re.finditer(r'(.)\1{63,}|(?:(.)(?!\2{63}))+', s, re.S):
        t = m.group(0)
        if len(t) >= 64 and t == t[0] * len(t):
            parts.append('string.rep(%s, %d)' % (lit(t[0]), len(t)))
        else:
            parts.append(lit(t))
    return ' .. '.join(parts) if parts else '""'

SHOW = ('local function show(x)\n'
        '  if x == nil then return "nil" end\n'
        '  local t = tostring(x)\n'
        '  if t:find("^%-?%d+$") then return "I " .. t end\n'
        '  return "F " .. t .. " " .. (string.unpack("<i8", string.pack("<d", x)))\n'
        'end\n')

def emit(name, items, head, body, budget=40000, tail=()):
    """Write `name`_1.lua, `name`_2.lua, ... each with at most `budget` bytes of
    vector source, and the `tail` items in one last program; `run.sh`
    concatenates their outputs in order."""
    for old in os.listdir(HERE):
        if old.startswith(name + '_') and old.endswith('.lua'):
            os.remove(os.path.join(HERE, old))
    chunks, cur, size = [], [], 0
    for it in items:
        if cur and size + len(it) > budget:
            chunks.append(cur); cur, size = [], 0
        cur.append(it); size += len(it) + 2
    chunks.append(cur)
    if tail:
        chunks.append(list(tail))
    for i, c in enumerate(chunks, 1):
        with open(os.path.join(HERE, '%s_%d.lua' % (name, i)), 'w') as f:
            f.write('-- GENERATED by c/tests/float/gen.py: %s, part %d of %d (%d vectors)\n'
                    % (head, i, len(chunks), len(c)))
            f.write('local V = {\n' + ''.join(x + ',\n' for x in c) + '}\n' + body)
    return len(chunks)

with open(os.path.join(HERE, 'fmt.vec'), 'w') as f:
    f.writelines('%016x\n' % b for b in F)
with open(os.path.join(HERE, 'parse.vec'), 'w') as f:
    f.writelines(s.encode('latin-1').hex() + '\n' for s in P + LONG)
nf = emit('fmt', ['0x%016x' % b for b in F], 'tostring of doubles from their bits',
          'local pack, unpack = string.pack, string.unpack\n'
          'for i = 1, #V do print((unpack("<d", pack("<i8", V[i])))) end\n')
np = emit('parse', [lua_str(s) for s in P], 'tonumber of strings',
          SHOW + 'for i = 1, #V do print(show(tonumber(V[i]))) end\n',
          tail=[lua_str(s) for s in LONG])
print('fmt: %d vectors in %d programs, parse: %d vectors in %d programs' % (len(F), nf, len(P) + len(LONG), np))

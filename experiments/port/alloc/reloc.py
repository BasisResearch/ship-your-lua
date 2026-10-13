"""Relocate a ship-your-interpreter allocator proof file from the WHILE ELF's
addresses to the Lua ELF's: address literals (hex and decimal, pcs by
instruction alignment, data by symbol + offset) and pc-suffixed identifiers
(`st_<pc>`, `axT_<pc>`, `jalx_<pc>`, `epi_<pc>`, ...).

    python3 reloc.py SRC DST
Unmapped values are reported on stderr (and left unchanged).
"""
import json, re, sys, os
R = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'relmap.json')))
PC = {int(k): v for k, v in R['pc'].items() if v is not None}
DATA = R['data']
def mapv(v):
    if v in PC: return PC[v]
    for n, (a, b, s) in DATA.items():
        if v == a: return b
    cands = set()
    for n, (a, b, s) in DATA.items():
        if a <= v <= a + max(s, 0) and (v < a + s or v == a + s or s == 0):
            if s == 0 and v != a: continue
            cands.add(b + (v - a))
    if len(cands) == 1: return cands.pop()
    if len(cands) > 1: return ('AMBIG', sorted(cands))
    return None
bad = []
def lit(m):
    s = m.group(0)
    v = int(s, 0)
    if not (0x80000000 <= v < 0x90000000): return s
    r = mapv(v)
    if r is None or isinstance(r, tuple):
        bad.append((s, r)); return s
    if s.startswith('0x'): return f'0x{r:08x}'
    return str(r)
def ident(m):
    v = int(m.group(1), 16)
    if v in PC: return f'{PC[v]:08x}'
    if 0x80000000 <= v < 0x90000000: bad.append((m.group(0), 'ident'))
    return m.group(0)
src, dst = sys.argv[1], sys.argv[2]
t = open(src).read()
t = re.sub(r'(?<=[A-Za-z0-9]_)([0-9a-f]{8})(?![0-9a-zA-Z])', ident, t)
t = re.sub(r'(?<![0-9a-zA-Z_])(0x[0-9a-fA-F]{8}|\d{10})(?![0-9a-zA-Z])', lit, t)
open(dst, 'w').write(t)
for b in bad: print('UNMAPPED', os.path.basename(src), b, file=sys.stderr)

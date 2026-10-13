"""WHILE-ELF -> Lua-ELF relocation maps for the allocator: pcs (by instruction
alignment, per function) and data addresses (by symbol + offset)."""
import subprocess, re, difflib, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from diff2 import norm
T = '/data/home/kirancodes/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-'
L = '/data/home/kirancodes/Documents/code/ship-your-lua/c/lua-riscv-htif.elf'
W = '/data/home/kirancodes/Documents/code/syi/c/while-riscv-htif.elf'
FUNCS = ['malloc', 'free', 'realloc', '_malloc_r', '_free_r', '_realloc_r', '_malloc_trim_r', '_sbrk_r', '_sbrk',
         '__malloc_lock', '__malloc_unlock', '__retarget_lock_acquire_recursive',
         '__retarget_lock_release_recursive', 'memcpy', 'memmove']
def syms(e):
    d = {}
    for l in subprocess.run([T + 'nm', '-S', '-n', e], capture_output=True, text=True).stdout.splitlines():
        p = l.split()
        if len(p) == 4: d.setdefault(p[3], (int(p[0], 16), int(p[1], 16)))
        elif len(p) == 3: d.setdefault(p[2], (int(p[0], 16), 0))
    return d
SL, SW = syms(L), syms(W)
def insns(e, s, name):
    a, n = s[name]
    out = subprocess.run([T + 'objdump', '-d', '--no-show-raw-insn', f'--start-address={a}', f'--stop-address={a + n}', e],
                         capture_output=True, text=True).stdout
    r = []
    for l in out.splitlines():
        m = re.match(r'^\s*([0-9a-f]+):\s+(.*)$', l)
        if m:
            t = re.sub(r'<[^>]*>', '', m.group(2)).strip()
            def rel(mm):
                v = int(mm.group(0), 16)
                return f'@{v - a:x}' if a <= v < a + n else 'SYM'
            t = re.sub(r'\b8[0-9a-f]{7}\b', rel, t)
            r.append((int(m.group(1), 16), norm(t)))
    return r
pcmap = {}; extra = []
for f in FUNCS:
    if f not in SW or f not in SL: print('skip', f); continue
    w, l = insns(W, SW, f), insns(L, SL, f)
    sm = difflib.SequenceMatcher(a=[x[1] for x in w], b=[x[1] for x in l], autojunk=False)
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            for k in range(i2 - i1): pcmap[w[i1 + k][0]] = l[j1 + k][0]
        else:
            extra.append((f, tag, [(hex(p), t) for p, t in w[i1:i2]], [(hex(p), t) for p, t in l[j1:j2]]))
            # map the WHILE instruction(s) to the first of the Lua replacement
            for k in range(i2 - i1): pcmap[w[i1 + k][0]] = l[j1 + min(k, j2 - j1 - 1)][0] if j2 > j1 else None
    # the function end (one past the last instruction)
    pcmap[SW[f][0] + SW[f][1]] = SL[f][0] + SL[f][1]
DATA = ['__malloc_av_', '__sglue', '_impure_data', '__malloc_sbrk_base', '__malloc_trim_threshold', '_impure_ptr',
        'brk.0', '__malloc_max_total_mem', '__malloc_max_sbrked_mem', '__malloc_top_pad', '__stdio_exit_handler',
        'errno', '__malloc_current_mallinfo', '__sf', '_end', '__heap_end', '__global_pointer$',
        '__lock___malloc_recursive_mutex', 'tohost', '_start']
datamap = {n: (SW[n][0], SL[n][0], SW[n][1]) for n in DATA}
json.dump({'pc': {str(k): v for k, v in pcmap.items()}, 'data': datamap, 'extra': extra},
          open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'relmap.json'), 'w'), indent=1)
for e in extra: print(e)
print(len(pcmap), 'pcs')
for n, (a, b, s) in datamap.items(): print(f'{n:35s} 0x{a:x} -> 0x{b:x} ({s})')

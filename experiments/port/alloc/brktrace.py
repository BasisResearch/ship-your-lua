"""Trace every _malloc_r call on the Sail emulator: n, the break before and
after, and the bound brk' <= brk + n + 16384 + 4096 (MallocPost.brk_hi)."""
import subprocess, sys, re, os, tempfile
T = '/data/home/kirancodes/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-'
EMU = '/data/home/kirancodes/Documents/code/ship-your-lua/riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator'
elf = sys.argv[1]
sym = {}
for l in subprocess.run([T + 'nm', elf], capture_output=True, text=True).stdout.splitlines():
    p = l.split()
    if len(p) == 3: sym.setdefault(p[2], int(p[0], 16))
mr, sb = sym['_malloc_r'], sym['_sbrk']
# _malloc_r's returns: every `ret` in its body
dis = subprocess.run([T + 'objdump', '-d', f'--start-address={mr}', f'--stop-address={sym["__malloc_lock"]}', elf],
                     capture_output=True, text=True).stdout
rets = [int(m.group(1), 16) for m in re.finditer(r'^\s*([0-9a-f]+):\s+\S+\s+ret', dis, re.M)]
pcs = [mr, sb] + rets
fd, pf = tempfile.mkstemp(); os.write(fd, ''.join(f'0x{p:x}\n' for p in pcs).encode()); os.close(fd)
r = subprocess.run([EMU, elf, '--trace-pcs', pf, '--max-steps', sys.argv[2] if len(sys.argv) > 2 else '400000000'],
                   capture_output=True, text=True)
calls = []; cur = None; brk = None; viol = 0
for l in r.stderr.splitlines():
    f = l.split('\t')
    if f[0] != 'T': continue
    pc = int(f[2], 16); x = [None] + [int(v, 16) for v in f[4:35]]
    if pc == sb:
        # first instruction: ld a5, brk.0 -> pre value of the load is the break
        cur_brk = int(f[37], 16) if len(f) > 37 else None
        if cur is not None:
            cur['sbrk'].append((x[10] if x[10] < 2**63 else x[10] - 2**64, cur_brk))
    elif pc == mr:
        cur = dict(n=x[11], sbrk=[])
    elif pc in rets and cur is not None:
        cur['ret'] = x[10]; calls.append(cur); cur = None
for c in calls:
    if not c['sbrk']: continue
    b0 = c['sbrk'][0][1]; tot = sum(i for i, _ in c['sbrk'])
    ok = tot <= c['n'] + 16384 + 4096
    viol += not ok
    print(f"n={c['n']:8d} brk0=0x{b0:x} sbrks={[i for i,_ in c['sbrk']]} growth={tot} slack={c['n'] + 16384 + 4096 - tot} ret=0x{c['ret']:x} {'OK' if ok else 'VIOLATION'}")
print('calls', len(calls), 'extending', sum(1 for c in calls if c['sbrk']), 'violations', viol)
print('max growth - n:', max((sum(i for i, _ in c['sbrk']) - c['n'] for c in calls if c['sbrk'][1:] or c['sbrk']), default=None))

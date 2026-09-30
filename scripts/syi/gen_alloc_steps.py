#!/usr/bin/env python3
"""Generate the allocator's code bytes and its per-instruction step table.

Outputs (do not hand-edit):

* `VsaIris/Vsa/AllocCode.lean`: `allocText`, the code bytes of every
  allocator function (`FUNCS`) plus the `_impure_ptr` word, as a balanced
  append tree of 16-byte chunks. It also emits `alloc_at_<pc>` (the four code
  bytes at `pc`, the shape `chain_facts` consumes), `alloc_code_<pc>` (a jal
  or `sltu`/`sltiu` site's code footprint lies in `allocText`) and
  `alloc_impure` (the `_impure_ptr` word).
* `VsaIris/Vsa/AllocSteps/Part<k>.lean`: per instruction, one `#derive_case`
  segment (two for a branch: taken `axT_`, fall-through `axF_`) and one step
  lemma `VsaIris.Sym.st_<pc>` over `AW` (`AllocRun.lean`). Its continuation is
  the successor's symbolic state. Each `jal` site also gets `JalExec`
  (`jalx_<pc>`).
* `VsaIris/Vsa/AllocSteps.lean`: the aggregator.

Kinds: ALU, loads, stores, branches, `j`, `ret`, `jal`, and `sltu`/`sltiu`
(outside `MKind`): those go through VSA's observational ALU step as one `SWP`
step (`swp_aluRR` + `AluStep`, `AllocSltu.lean`), with the execute lemma
`execute_rtype_sltu_char`/`execute_itype_sltiu_char`.

ship-your-lua changes (ATTRIBUTION.md):

* The ELF is the Lua image, `c/lua-riscv-htif.elf`, read directly with the
  xPack `objdump`/`nm` (no `experiments/disasm.txt`); `ROOT` is the
  repository root.
* `FUNCS` is the call closure of `malloc`, `free`, `realloc`, `_malloc_r`,
  `_free_r` and `_realloc_r` in that ELF (every `jal` target, transitively);
  `gp` (`__global_pointer$`) and the `_impure_ptr` word are read from it.
* Decode is `Vsa.Sim.decodeW (w := 0x<hex>#32)` (rule R15): the `jalx_`
  lemmas use it, and `chain_facts` closes the decode leaves with it; no
  decode-table import.
* `sltu`/`sltiu` get generated step lemmas (the WHILE ELF's one was
  hand-written in `AllocSltu.lean`).
* The WHILE interpreter's `--target env` is dropped (the Lua ELF has no
  `env.c`).

Usage: python3 scripts/syi/gen_alloc_steps.py [--check]
"""
import pathlib
import re
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]   # scripts/syi/../..
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
ELF = ROOT / 'c/lua-riscv-htif.elf'
TOOLS = pathlib.Path.home() / 'toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin'
OBJDUMP, NM = str(TOOLS / 'riscv-none-elf-objdump'), str(TOOLS / 'riscv-none-elf-nm')
CFG = dict(
    P='alloc', RUN='AW',
    ROOTS=['malloc', 'free', 'realloc', '_malloc_r', '_free_r', '_realloc_r'],
    CODE_OUT='VsaIris/Vsa/AllocCode.lean', STEPS_DIR='VsaIris/Vsa/AllocSteps',
    STEPS_MOD='VsaIris.Vsa.AllocSteps', RUN_MOD='VsaIris.Vsa.AllocRun',
    WHO='The allocator\'s')
P, RUN = CFG['P'], CFG['RUN']
PER_FILE = 120

# ---------------------------------------------------------------- the ELF
SYM = {}
for l in subprocess.run([NM, '-n', str(ELF)], capture_output=True, text=True,
                        check=True).stdout.splitlines():
    parts = l.split()
    if len(parts) == 3:
        SYM.setdefault(parts[2], int(parts[0], 16))
GPV = SYM['__global_pointer$']


def elf_bytes(lo, n):
    """`n` bytes of the ELF image at `lo` (`objdump -s`)."""
    out = subprocess.run([OBJDUMP, '-s', f'--start-address=0x{lo:x}',
                          f'--stop-address=0x{lo + n:x}', str(ELF)],
                         capture_output=True, text=True, check=True).stdout
    bs = {}
    for l in out.splitlines():
        m = re.match(r'^ ([0-9a-f]{8,16}) ((?:[0-9a-f]{2,8} ){1,4})', l)
        if m:
            a = int(m.group(1), 16)
            for b in bytes.fromhex(m.group(2).replace(' ', '')):
                bs[a] = b
                a += 1
    return [bs[lo + i] for i in range(n)]


IMPURE = (SYM['_impure_ptr'], elf_bytes(SYM['_impure_ptr'], 8))

W, FN, MN = {}, {}, {}
fn = None
for l in subprocess.run([OBJDUMP, '-d', str(ELF)], capture_output=True, text=True,
                        check=True).stdout.splitlines():
    m = re.match(r'^([0-9a-f]+) <(.*)>:$', l)
    if m:
        fn = m.group(2)
        continue
    m = re.match(r'^\s+([0-9a-f]+):\t([0-9a-f]{8})\s+\t(\S+)', l)
    if m:
        pc = int(m.group(1), 16)
        W[pc] = int(m.group(2), 16)
        FN[pc] = fn
        MN[pc] = m.group(3)

from rv_steps import M64, sext, lit64, fields, i12, sx12, classify_word  # noqa: E402
from rv_steps import src as _src  # noqa: E402

# the call closure of the roots
BY_FN = {}
for pc, f in FN.items():
    BY_FN.setdefault(f, []).append(pc)
FUNCS, work = [], list(CFG['ROOTS'])
while work:
    f = work.pop()
    if f in FUNCS:
        continue
    FUNCS.append(f)
    for pc in BY_FN[f]:
        c, d = classify_word(pc, W[pc], GPV)
        if c in ('jal', 'j', 'br') and FN.get(d['tgt']) != f:
            work.append(FN[d['tgt']])       # calls and tail jumps
FUNCS.sort(key=lambda f: SYM[f])
W = {pc: w for pc, w in W.items() if FN[pc] in FUNCS}
PCS = sorted(W)
CFG['CODE_DOC'] = [
    '/-! The allocator\'s code bytes (the call closure of `malloc`, `free`, `realloc`,',
    '`_malloc_r`, `_free_r`, `_realloc_r` in `c/lua-riscv-htif.elf`: '
    + ', '.join(f'`{f}`' for f in FUNCS) + ')',
    'and the `_impure_ptr` word, as a balanced append tree of 16-byte chunks. -/']

from rv_steps import src as _src  # noqa: E402


def src(r):
    return _src(r, GPV)


def classify(pc):
    return classify_word(pc, W[pc], GPV)


def sltu_kind(pc):
    """`('sltu', rd, rs1, rs2)` / `('sltiu', rd, rs1, imm12)` for the two ALU
    shapes outside `MKind`, else None."""
    f = fields(W[pc])
    if f['op'] == 0x33 and f['f3'] == 3 and f['f7'] == 0 and f['rd'] != 0:
        return ('sltu', f['rd'], f['rs1'], f['rs2'])
    if f['op'] == 0x13 and f['f3'] == 3 and f['rd'] != 0:
        return ('sltiu', f['rd'], f['rs1'], f['immI'] & 0xfff)
    return None


# ---------------------------------------------------------------- the code bytes
text = []
for pc in PCS:
    w = W[pc]
    for i in range(4):
        text.append((pc + i, (w >> (8 * i)) & 0xff))
for i, b in enumerate(IMPURE[1]):
    text.append((IMPURE[0] + i, b))
CH = 16
chunks = [text[i:i + CH] for i in range(0, len(text), CH)]
where = {a: j for j, c in enumerate(chunks) for (a, _) in c}
BYTE = dict(text)


def node_name(lo, hi):
    return f'{P}Chunk{lo}' if hi - lo == 1 else f'{P}Node{lo}_{hi}'


node_defs = []


def build(lo, hi):
    if hi - lo == 1:
        return
    mid = (lo + hi) // 2
    build(lo, mid)
    build(mid, hi)
    node_defs.append(f'def {node_name(lo, hi)} : List (Nat × BitVec 8) :=\n'
                     f'  {node_name(lo, mid)} ++ {node_name(mid, hi)}\n')


build(0, len(chunks))
ROOT_NODE = node_name(0, len(chunks))


def mem_proof(a):
    """Proof term of `(a, BYTE[a]) ∈ allocText`."""
    j = where[a]
    leaf = f'(by decide : ((0x{a:x} : Nat), (0x{BYTE[a]:02x}#8 : BitVec 8)) ∈ {P}Chunk{j})'
    path = []
    lo, hi = 0, len(chunks)
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if j < mid:
            path.append(('L', node_name(mid, hi)))
            hi = mid
        else:
            path.append(('R', node_name(lo, mid)))
            lo = mid
    pf = leaf
    for side, other in reversed(path):
        pf = (f'List.mem_append_left {other} ({pf})' if side == 'L'
              else f'List.mem_append_right {other} ({pf})')
    return pf


C = ['-- GENERATED by scripts/syi/gen_alloc_steps.py; do not edit.',
     'import VsaIris.Vsa.SymRun', '',
     *CFG['CODE_DOC'], '',
     'namespace VsaIris.Sym', '', 'open Vsa.MemRepr Vsa.Sim', '']
for j, c in enumerate(chunks):
    C.append(f'def {P}Chunk{j} : List (Nat × BitVec 8) :=')
    C.append('  [' + ', '.join(f'(0x{a:x}, 0x{b:02x}#8)' for a, b in c) + ']\n')
C += node_defs
C.append(f'/-- {CFG["WHO"]} code bytes: `(address, byte)`. -/')
C.append(f'def {P}Text : List (Nat × BitVec 8) := {ROOT_NODE}\n')
for pc in PCS:
    bs = [BYTE[pc + i] for i in range(4)]
    C.append(f'theorem {P}_at_{pc:08x} {{m : Mem}} (h : TextLoaded {P}Text m) :')
    C.append('    ' + ' ∧\n    '.join(f'm[(0x{pc + i:x} : Nat)]? = some (0x{bs[i]:02x} : BitVec 8)'
                                       for i in range(4)) + ' :=')
    C.append('  ⟨' + ',\n   '.join(f'h _ ({mem_proof(pc + i)})' for i in range(4)) + '⟩\n')
JALS = [pc for pc in PCS if classify(pc)[0] == 'jal' or sltu_kind(pc)]
for pc in JALS:
    bs = [BYTE[pc + i] for i in range(4)]
    code = ', '.join(f'0x{b:02x}#8' for b in bs)
    C.append(f'theorem {P}_code_{pc:08x} : ∀ p ∈ codeFoot 0x{pc:x} [{code}], (p.1, p.2.2) ∈ {P}Text := by')
    C.append('  intro p hp')
    C.append('  simp only [codeFoot, List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil,')
    C.append('    List.mem_cons, List.not_mem_nil, or_false] at hp')
    C.append('  rcases hp with rfl | rfl | rfl | rfl')
    for i in range(4):
        C.append(f'  · exact {mem_proof(pc + i)}')
    C.append('')
a0, ib = IMPURE
C.append('/-- The `_impure_ptr` word. -/')
C.append(f'theorem {P}_impure {{m : Mem}} (h : TextLoaded {P}Text m) :')
C.append(f'    LPins8 m ({lit64(GPV)} + {lit64(a0 - GPV)}).toNat [' + ', '.join(f'0x{b:02x}#8' for b in ib) + '] := by')
C.append(f'  rw [show ({lit64(GPV)} + {lit64(a0 - GPV)}).toNat = 0x{a0:x} by decide]')
C.append('  exact ⟨' + ',\n   '.join(f'by rw [h _ ({mem_proof(a0 + i)})]; rfl' for i in range(8)) + '⟩\n')
C.append('/-- The `gp` the step table computes with is the ELF\'s `__global_pointer$`. -/')
C.append(f'theorem {P}_gp : VsaIris.MallocFast.gpV = {lit64(GPV)} := rfl\n')
C.append('end VsaIris.Sym\n')
OUT = {ROOT / CFG['CODE_OUT']: '\n'.join(C)}

# ---------------------------------------------------------------- the step table


def ks_of(regs):
    return sorted({r for r in regs if r != 0})


def lst(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def hgp(ks):
    return '(fun _ => rfl)' if 3 in ks else '(fun h => absurd h (by decide))'


def hR(ks):
    """Each pinned register's final value, `finReg` on the left."""
    alts = ' | '.join(['rfl'] * len(ks))
    return ('(by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; '
            f'rcases hx with {alts} <;> first | rfl | exact absurd rfl hg)')


def hRo(ks, rd=None):
    if rd is None:
        return '(fun _ _ _ _ => rfl)'
    return f'(fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : {rd} ∈ {lst(ks)}))))'


HDR = """theorem st_{pc:08x} {{live : Nat → Prop}} {{S : Nat → Prop}}
    {{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}} {{R : Nat → BitVec 64}} {{Mt : Mem}}
    (hlive : ∀ p ∈ allocText, live p.1)""".replace('allocText', f'{P}Text')
CF = f'chain_facts hm with "VsaIris.Sym.{P}_at_"'


def step(seg, ks, lds, LD, W, cover, tail, gp, hpc, R, Ro, hk, ind='  '):
    """The `swp_step` application for one segment."""
    t = f'; {tail}' if tail else ''
    return (f'{ind}swp_step {seg} {lst(ks)} {lds} {LD} {W} 0 rfl (by decide) (by decide) (by decide)\n'
            f'{ind}  {cover} hlive\n'
            f'{ind}  (fun m hm hLD => by unfold {seg} ChainFacts; {CF}{t})\n'
            f'{ind}  (by decide) (by decide) {gp} (by decide) {"hLDS" if LD != "[]" else "(fun a h => by cases h)"}\n'
            f'{ind}  {"hS" if W != "[]" else "(fun a h => by cases h)"} {hpc}\n'
            f'{ind}  {R}\n'
            f'{ind}  {Ro} rfl {hk}')


def okfact(thm, kind, pc, prop):
    """A concrete `LdOK`/`StOK` side condition as its own lemma, closed by one
    `decide` at top level (inside the `swp_step` term the same `decide` runs
    past the default recursion depth)."""
    name = f'{kind}_{pc:08x}'
    thm.append(f'theorem {name} : {prop} := by decide')
    return name


def ea_expr(rs1, imm):
    """The effective address, as the segment computes it (`gp`-relative ones
    are closed terms, decided in place)."""
    return f'({src(rs1)} + {sx12(imm)}).toNat', rs1 == 3


def emit(pc):
    if sltu_kind(pc):
        return emit_sltu(pc)
    cls, d = classify(pc)
    w = W[pc]
    bs = [(w >> (8 * i)) & 0xff for i in range(4)]
    nxt = f'0x{pc + 4:x}#64'
    segs, thm = [], []
    if cls == 'unsupported':
        return None, None
    single = f'def ax_{pc:08x} : List BBlock := [{{ body := [mkLine 0x{pc:x}#64 0x{w:08x}#32], term := none }}]'
    tinstr = lambda kind, rs1, rs2, i13, i21: (
        f'⟨0x{pc:x}#64, 0x{w:08x}#32, 0x{bs[0]:02x}#8, 0x{bs[1]:02x}#8, 0x{bs[2]:02x}#8, '
        f'0x{bs[3]:02x}#8, {kind}, {rs1}, {rs2}, 0x{i13 & 0x1fff:x}#13, 0x{i21 & 0x1fffff:x}#21, 0#12⟩')
    tdef = lambda name, kind, rs1, rs2, i13, i21: (
        f'def {name} : List BBlock := [⟨[], some ({tinstr(kind, rs1, rs2, i13, i21)} : TInstr)⟩]')
    NIL = '(fun a _ => trivial)'
    if cls == 'alu':
        segs.append(single)
        ks = ks_of(d['srcs'] + [d['rd']])
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} ({d['val']})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, '[]', '[]', '[]', NIL, '', hgp(ks), 'rfl', hR(ks), hRo(ks, d['rd']), 'hk'))
    elif cls == 'load':
        segs.append(single)
        ea, conc = ea_expr(d['rs1'], d['imm'])
        wd = d['width']
        ks = ks_of([d['rs1'], d['rd']])
        if conc and (GPV + d['imm']) & M64 == IMPURE[0]:
            lds = '[[' + ', '.join(f'0x{b:02x}#8' for b in IMPURE[1]) + ']]'
            val = 'bytesVal .ld [' + ', '.join(f'0x{b:02x}#8' for b in IMPURE[1]) + ']'
            thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} ({val})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, lds, '[]', '[]', NIL,
           f'exact ⟨{okfact(thm, "ldok", pc, f"LdOK {ea} 8")}, {P}_impure hm⟩', hgp(ks), 'rfl', hR(ks),
           hRo(ks, d['rd']), 'hk'))
        else:
            pin = {8: 'lpins8_img hLD', 4: 'lpins4_img hLD', 1: 'lpins1_img hLD', 2: 'lpins2_img hLD'}[wd]
            okh = '' if conc else f'\n    (hea : LdOK {ea} {wd})'
            okp = okfact(thm, 'ldok', pc, f'LdOK {ea} {wd}') if conc else 'hea'
            thm.append(HDR.format(pc=pc) + f"""{okh}
    (hLDS : ∀ b ∈ accAddrs {ea} {wd}, S b)
    (hk : {RUN} live S Q {nxt} (upd R {d['rd']} (ldv .{d['kind']} Mt {ea})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, f'[bytesAt (imgM Mt) {ea} {wd}]', f'(accAddrs {ea} {wd})', '[]', NIL,
           f'exact ⟨{okp}, {pin}⟩', hgp(ks), 'rfl', hR(ks), hRo(ks, d['rd']), 'hk'))
    elif cls == 'store':
        segs.append(single)
        ea, conc = ea_expr(d['rs1'], d['imm'])
        wd = d['width']
        ks = ks_of([d['rs1'], d['rs2']])
        ok = f'StOKb {ea}' if d['kind'] == 'sb' else f'StOK {ea} {wd}'
        okh = '' if conc else f'\n    (hea : {ok})'
        okp = okfact(thm, 'stok', pc, ok) if conc else 'hea'
        thm.append(HDR.format(pc=pc) + f"""{okh}
    (hS : ∀ b ∈ accAddrs {ea} {wd}, S b)
    (hk : {RUN} live S Q {nxt} R (writeLog Mt [({ea}, {wd}, {src(d['rs2'])})])) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', ks, '[]', '[]', f'(accAddrs {ea} {wd})', '(fun a ha => outL_single _ ha)',
           f'exact {okp}', hgp(ks), 'rfl', hR(ks), hRo(ks), 'hk'))
    elif cls == 'br':
        A, B = src(d['rs1']), src(d['rs2'])
        cond = {'BEQ': f'{A} = {B}', 'BNE': f'{A} ≠ {B}', 'BLT': f'{A}.toInt < {B}.toInt',
                'BGE': f'{B}.toInt ≤ {A}.toInt', 'BLTU': f'{A}.toNat < {B}.toNat',
                'BGEU': f'{B}.toNat ≤ {A}.toNat'}[d['op']]
        gl = {'BEQ': 'guard_beq', 'BNE': 'guard_bne', 'BLT': 'guard_blt', 'BGE': 'guard_bge',
              'BLTU': 'guard_bltu', 'BGEU': 'guard_bgeu'}[d['op']]
        ks = ks_of([d['rs1'], d['rs2']])
        segs.append(tdef(f'axT_{pc:08x}', f'.br bop.{d["op"]} true', d['rs1'], d['rs2'], d['imm'], 0))
        segs.append(tdef(f'axF_{pc:08x}', f'.br bop.{d["op"]} false', d['rs1'], d['rs2'], d['imm'], 0))
        tgt = f'0x{d["tgt"]:x}#64'
        thm.append(HDR.format(pc=pc) + f"""
    (hT : {cond} → {RUN} live S Q {tgt} R Mt) (hF : ¬ ({cond}) → {RUN} live S Q {nxt} R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt := by
  by_cases hc : {cond}
  · exact
""" + step(f'axT_{pc:08x}', ks, '[]', '[]', '[]', NIL, f'exact ({gl} _ _).2 hc', hgp(ks), 'rfl',
           hR(ks), hRo(ks), '(hT hc)', '    ') + """
  · exact
""" + step(f'axF_{pc:08x}', ks, '[]', '[]', '[]', NIL, f'exact (guard_false ({gl} _ _)).2 hc', hgp(ks),
           'rfl', hR(ks), hRo(ks), '(hF hc)', '    '))
    elif cls == 'j':
        segs.append(tdef(f'ax_{pc:08x}', '.j', 0, 0, 0, d['imm']))
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q 0x{d['tgt']:x}#64 R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', [], '[]', '[]', '[]', NIL, '', '(fun h => nomatch h)', 'rfl',
           '(fun _ h => nomatch h)', hRo([]), 'hk'))
    elif cls == 'ret':
        segs.append(tdef(f'ax_{pc:08x}', '.jr', 1, 0, 0, 0))
        thm.append(HDR.format(pc=pc) + f"""
    (hal : (R 1).toNat % 4 = 0) (hk : {RUN} live S Q (R 1) R Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
""" + step(f'ax_{pc:08x}', [1], '[]', '[]', '[]', NIL,
           'show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; '
           'rw [ret_tgt _ hal]; exact hal', hgp([1]), '(ret_tgt _ hal)', hR([1]), hRo([1]), 'hk'))
    elif cls == 'jal':
        code = ', '.join(f'0x{b:02x}#8' for b in bs)
        hb = '\n'.join(f'  have hb{i} := hb (0x{pc + i:x}, .discard, 0x{bs[i]:02x}#8) (by simp [codeFoot])'
                       for i in range(4))
        imm = d['imm'] & 0x1fffff
        tgt = d['tgt']
        thm.append(f"""open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in
/-- `jal` at `0x{pc:x}` to `0x{tgt:x}`. -/
theorem jalx_{pc:08x} (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x{pc:x} [{code}], live p.1) :
    JalExec (vsaModel live) 0x{pc:x} [{code}] 0x{tgt:x}#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
{hb}
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x{pc:x}#64) vm (0x{w:08x}#32) (0x{imm:06x}#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x{pc:x}#64) 4)
      {' '.join(f'(0x{b:02x}#8)' for b in bs)}
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.decodeW (w := 0x{w:08x}#32) (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x{pc:x}#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x{tgt:x}#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x{pc:x}#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x{pc:x} + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h
""")
        thm.append(HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q 0x{tgt:x}#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x{pc:x} + 4))) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
  swp_jal 0x{pc:x} [{code}] 0x{tgt:x}#64
    (jalx_{pc:08x} live fun p hp => hlive _ ({P}_code_{pc:08x} p hp)) {P}_code_{pc:08x}
    (by decide) (by decide) rfl hk""")
    return segs, thm


def extra_imports(pc):
    return {'VsaIris.Vsa.AllocSltu'} if sltu_kind(pc) else set()


def emit_sltu(pc):
    """The `st_<pc>` of an `sltu`: VSA's observational ALU step (`stepObs_alu`,
    decoded by `decodeW`) as one `SWP` step (`swp_aluRR`), from
    `AllocSltu.sltuAluStepAt`, which covers `_realloc_r`'s `sltu a4,a5,a4` at
    any address. Any other shape is reported as unsupported."""
    kind, rd, rs1, x = sltu_kind(pc)
    if (kind, rd, rs1, x) != ('sltu', 14, 15, 14):
        return None, None
    val = 'zero_extend (m := 64) (bool_to_bit (zopz0zI_u (R 15) (R 14)))'
    thm = HDR.format(pc=pc) + f"""
    (hk : {RUN} live S Q 0x{pc + 4:x}#64 (upd R 14 ({val})) Mt) :
    {RUN} live S Q 0x{pc:x}#64 R Mt :=
  swp_aluRR 0x{pc:x} _ _ 14 _
    (sltuAluStepAt hlive 0x{pc:x} {P}_code_{pc:08x} (by decide) (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (R 14) (R 15))
    {P}_code_{pc:08x}
    (fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact ⟨by dsimp only; decide, by dsimp only; decide, rfl⟩)
    (by decide) (by decide) rfl hk"""
    return [], [thm]


unsupported = []
parts = []
cur_segs, cur_thms, cur_mods, cur_pcs = [], [], set(), []
for pc in PCS:
    segs, thms = emit(pc)
    if segs is None:
        unsupported.append(pc)
        continue
    cur_segs += segs
    cur_thms += thms
    cur_mods |= extra_imports(pc)
    cur_pcs.append(pc)
    if len(cur_pcs) >= PER_FILE:
        parts.append((cur_segs, cur_thms, cur_mods, cur_pcs))
        cur_segs, cur_thms, cur_mods, cur_pcs = [], [], set(), []
if cur_pcs:
    parts.append((cur_segs, cur_thms, cur_mods, cur_pcs))

outdir = ROOT / CFG['STEPS_DIR']
for k, (segs, thms, mods, pcs) in enumerate(parts):
    L = ['-- GENERATED by scripts/syi/gen_alloc_steps.py; do not edit.',
         f'import {CFG["RUN_MOD"]}', 'import Vsa.Sim.DecodeNF'] + \
        [f'import {m}' for m in sorted(mods)] + ['',
         f'/-! {CFG["WHO"]} step table, `0x{pcs[0]:x}` to `0x{pcs[-1]:x}` (one lemma `st_<pc>` per',
         'instruction; see `scripts/syi/gen_alloc_steps.py`). -/', '',
         'open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail', '',
         'namespace Vsa.Sim', ''] + segs + ['', 'end Vsa.Sim', '',
         'namespace VsaIris.Sym', '', 'open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast', ''] + \
        [t + '\n' for t in thms] + ['end VsaIris.Sym', '']
    OUT[outdir / f'Part{k:02d}.lean'] = '\n'.join(L)
agg = ['-- GENERATED by scripts/syi/gen_alloc_steps.py; do not edit.'] + \
      [f'import {CFG["STEPS_MOD"]}.Part{k:02d}' for k in range(len(parts))] + ['']
OUT[ROOT / (CFG['STEPS_DIR'] + '.lean')] = '\n'.join(agg)
if unsupported:
    sys.exit('unsupported: ' + ', '.join(f'0x{pc:x} {MN[pc]}' for pc in unsupported))
if '--check' in sys.argv:
    bad = [p for p, t in OUT.items() if not p.exists() or p.read_text() != t]
    bad += [p for p in outdir.glob('Part*.lean') if p not in OUT]
    for p in bad:
        print(f'drift: {p.relative_to(ROOT)}', file=sys.stderr)
    sys.exit(1 if bad else 0)
outdir.mkdir(exist_ok=True)
for old in outdir.glob('Part*.lean'):
    if old not in OUT:
        old.unlink()
for p, t in OUT.items():
    p.write_text(t)
print(f'{len(PCS)} instructions, {len(text)} bytes, {len(chunks)} chunks, {len(parts)} parts')

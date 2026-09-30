#!/usr/bin/env python3
"""Boot traces of the Lua ELF up to `luaV_execute`'s entry (PHASES A0.6).

Retargets ship-your-interpreter's `scripts/gen_boot_witness.py`
(`scripts/syi/gen_boot_witness.py`) from `interp_run` to `luaV_execute`.

For each program (`PROGRAMS`):

1. build its ELF by writing its `luac -s` chunk into the committed ELF's
   `.lua_chunk` region (`_chunk_size` dword, the chunk, a NUL, zeros: exactly
   what `c/src/chunk.S` assembles; link.ld fixes every other byte, and the
   committed ELF, built from `while.lua`, is checked to be reproduced
   byte for byte);
2. trace it with the Lean emulator (`--trace-all`) up to the first step at
   `luaV_execute`;
3. reconstruct the entry memory: the PT_LOAD segment's `p_filesz` bytes (the
   loader), then every traced store in program order (the binary is rv64i:
   stores are its only memory writes);
4. evaluate natively every field of `VmEntryData` (Lua/Vm/Repr.lean), of
   `luaRuntimeReady` (Lua/Vm/Runtime.lean) and of `MachineAt.regs`
   (`RegsOk`: every GPR present, the HTIF mailbox idle) at that memory and the
   entry registers, and fail on the first false one;
5. check that the boot-invariant values are the same for every program.

It writes (all GENERATED, drift-checked by `--check`):

* `Lua/Vm/RuntimeData.lean`: the boot-invariant constants `luaRuntimeReady`
  pins (entry `sp`/`ra`, the `jmp_buf`, the caller frames' bytes, the return
  chain);
* `Lua/Vm/Boot/ImageData.lean`: the loaded bytes after `.rodata` (`.tohost`,
  `.data`, `.init_array`) up to `.bss`;
* `Lua/Vm/Boot/Gen/<Prog>.lean`: the program's chunk region, packed store log
  (`PackedLog`), final byte map (`RunTree`), entry registers, and the witness
  pointers (`EntryPtrs`, `RtPtrs`), as data. `Lua/Vm/Boot/Image.lean`'s
  `bootMem_get` says `bootView chunk runs` is the entry memory's byte view
  under a `LogOk log runs`.

    python3 scripts/gen_lua_boot_witness.py [--work DIR] [--check]

`--work` keeps the patched ELFs and traces (default: a temporary directory).
Each trace takes about 12 s.
"""
from __future__ import annotations

import argparse
import os
import re
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ELF = ROOT / "c" / "lua-riscv-htif.elf"
EMU = ROOT / "riscv-lean" / "lean_emulator" / ".lake" / "build" / "bin" / "lean_riscv_emulator"
OUT_DATA = ROOT / "Lua" / "Vm" / "RuntimeData.lean"
OUT_IMAGE = ROOT / "Lua" / "Vm" / "Boot" / "ImageData.lean"
GEN_DIR = ROOT / "Lua" / "Vm" / "Boot" / "Gen"
MAX_STEPS = 400000

# (file stem, chunk, Lean name, Proto constant, module)
PROGRAMS = [
    ("while", "c/tests/while.luac", "While", "Lua.Programs.whileProto", "Lua.Programs.While"),
    ("f1_ops", "c/tests/f1_ops.luac", "F1Ops", "Lua.Programs.f1OpsProto", "Lua.Programs.F1Ops"),
]

PAGE = 256
LOG_PAGE = 64
RUN_MAX = 64

sys.path.insert(0, str(ROOT / "scripts"))
import gen_lua_layout as GL  # noqa: E402


# ------------------------------------------------------------------ layout
def layout():
    """Every offset/symbol the checks use, from the cross compiler and nm
    (the same values Lua/Vm/Layout.lean and LayoutRt.lean hold)."""
    lay = dict(GL.probe())
    lay.update(GL.probe_rt())
    syms = GL.elf_syms()
    lay.update(syms)
    for n, (a, sz) in GL.elf_syms_sized().items():
        lay[n] = a
        if sz is not None:
            lay[n + "Size"] = sz
    nm = subprocess.run([GL.CC[:-3] + "nm", str(ELF)], capture_output=True, text=True,
                        check=True).stdout
    tab = {}
    for line in nm.splitlines():
        f = line.split()
        if len(f) == 3:
            tab[f[2]] = int(f[0], 16)
    lay["__bss_start"] = tab["__bss_start"]
    lay["__chunk_region"] = tab["__chunk_region"]
    lay["_chunk_size"] = tab["_chunk_size"]
    lay["_chunk_start"] = tab["_chunk_start"]
    return lay


def text_word(raw, seg, a):
    vaddr, off, _ = seg
    return struct.unpack_from("<I", raw, off + a - vaddr)[0]


def pt_load(raw):
    phoff = struct.unpack_from("<Q", raw, 0x20)[0]
    phentsize, phnum = struct.unpack_from("<HH", raw, 0x36)
    loads = []
    for i in range(phnum):
        (p_type, _, p_off, p_vaddr, _, p_filesz, _, _) = struct.unpack_from(
            "<IIQQQQQQ", raw, phoff + i * phentsize)
        if p_type == 1:
            loads.append((p_vaddr, p_off, p_filesz))
    assert len(loads) == 1, loads
    return loads[0]


# ------------------------------------------------------------------ ELFs
def chunk_region(lay, chunk):
    region = lay["__chunk_region"]
    assert lay["_chunk_size"] == region and lay["_chunk_start"] == region + 8
    blob = struct.pack("<Q", len(chunk)) + chunk + b"\0"
    assert len(blob) <= lay["symEnd"] - region
    return blob


def patched_elf(lay, chunk):
    raw = bytearray(ELF.read_bytes())
    vaddr, off, filesz = pt_load(raw)
    region = lay["__chunk_region"]
    size = lay["symEnd"] - region
    assert vaddr + filesz == lay["symEnd"], "the chunk region ends the loaded segment"
    blob = chunk_region(lay, chunk)
    fo = off + region - vaddr
    raw[fo:fo + size] = blob + b"\0" * (size - len(blob))
    return bytes(raw)


def trace(elf_path, entry_pc):
    """(store log, entry row, active return chain) up to the first step at
    `entry_pc`. The chain is the calls still open at the entry, outermost
    first, each as `(slot, return address)`: a call is a step whose successor
    has `ra = pc + 4` and a jump; it closes when control reaches its return
    address; its slot is the first stack store of the return address after
    the call (the callee's prologue `sd ra`)."""
    proc = subprocess.Popen([str(EMU), str(elf_path), "--trace-all", "--max-steps", str(MAX_STEPS)],
                            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True)
    log, entry, prev, calls = [], None, None, []
    for line in proc.stderr:
        p = line.rstrip("\n").split("\t")
        if p[0] != "T":
            continue
        pc = int(p[2], 16)
        if prev is not None:
            ppc, pnpc = int(prev[2], 16), int(prev[3], 16)
            if pnpc != ppc + 4 and int(p[4], 16) == ppc + 4 and int(prev[4], 16) != ppc + 4:
                calls.append([ppc + 4, int(prev[5], 16), None])
            elif calls and pc == calls[-1][0]:
                calls.pop()
        if pc == entry_pc:
            entry = p
            break
        if len(p) > 35 and p[35][:1] == "S":
            a, w, v = int(p[36], 16), int(p[35][1:]), int(p[38], 16)
            log.append((a, w, v))
            for c in calls:
                if c[2] is None and w == 8 and v == c[0] and c[1] - 1024 <= a < c[1]:
                    c[2] = a
        elif len(p) > 35 and p[35][:1] not in ("L", "O"):
            raise SystemExit(f"{elf_path}: unexpected memory operand {p[35]}")
        prev = p
    proc.kill()
    proc.wait()
    if entry is None:
        raise SystemExit(f"{elf_path}: the trace does not reach luaV_execute")
    return log, entry, calls


def entry_memory(raw, log):
    vaddr, off, filesz = pt_load(raw)
    mem = {vaddr + i: raw[off + i] for i in range(filesz)}
    for a, w, v in log:
        assert w in (1, 2, 4, 8) and a + w <= 1 << 32
        for j in range(w):
            mem[a + j] = (v >> (8 * j)) & 0xFF
    return mem


# ------------------------------------------------------------------ checks
class Fail(Exception):
    pass


class Mem:
    def __init__(self, mem):
        self.m = mem

    def rd(self, a, n):
        x = 0
        for i in range(n):
            b = self.m.get(a + i)
            if b is None:
                raise Fail(f"absent byte at {a + i:#x}")
            x |= b << (8 * i)
        return x

    def present(self, a, n):
        return all((a + i) in self.m for i in range(n))


def need(cond, what):
    if not cond:
        raise Fail(what)


def evaluate(lay, M, regs, proto):
    """Natively evaluate VmEntryData and luaRuntimeReady at the entry; return
    the witnesses (`e`, `w`, the print slot) and the boot-invariant values."""
    L, ci = regs[10], regs[11]
    rd = M.rd
    # ---- VmEntryData
    e = {}
    need(rd(L + lay["stateCiOff"], 8) == ci, "ci_eq")
    e["func"] = rd(ci + lay["ciFuncOff"], 8)
    need(rd(e["func"] + lay["tvalueTagOff"], 1) == lay["vLcl"], "func_tag")
    e["cl"] = rd(e["func"] + lay["tvalueValOff"], 8)
    e["pa"] = rd(e["cl"] + lay["lclosureProtoOff"], 8)
    check_proto(lay, M, e["pa"], proto)
    e["code"] = rd(e["pa"] + lay["protoCodeOff"], 8)
    need(rd(ci + lay["ciSavedpcOff"], 8) == e["code"], "savedpc")
    e["uv"] = rd(e["cl"] + lay["lclosureUpvalsOff"], 8)
    e["envv"] = rd(e["uv"] + lay["upvalVOff"], 8)
    need(rd(e["envv"] + lay["tvalueTagOff"], 1) == lay["vTable"], "env_tag")
    e["env"] = rd(e["envv"] + lay["tvalueValOff"], 8)
    slot = find_print(lay, M, e["env"])
    e["g"] = rd(L + lay["stateGOff"], 8)
    need(rd(e["g"] + lay["gGcstpOff"], 1) == lay["gcstpUsr"], "gc_stopped")
    e["stackLast"] = rd(L + lay["stateStackLastOff"], 8)
    need(e["func"] + lay["stackValueSize"] * (1 + proto[2]) <= e["stackLast"], "frame_fits")
    # ---- CStackAt
    inv = {}
    inv["spEntry"], inv["retCcall"] = regs[2], regs[1]
    need(regs[3] == lay["symGlobalPointer"], "gp")
    stack_top = lay["symStackTop"]
    segs, run = [], None
    for a in range(regs[2], stack_top):
        if a in M.m:
            if run and run[0] + len(run[1]) == a:
                run[1].append(M.m[a])
            else:
                run = [a, [M.m[a]]]
                segs.append(run)
    inv["callerFrames"] = [(a, bs) for a, bs in segs]
    # ---- ErrorJmpAt
    lj = rd(L + lay["stateErrorJmpOff"], 8)
    inv["ljAddr"] = lj
    need(regs[2] <= lj < stack_top, "lj on the caller stack")
    need(rd(lj + lay["ljPreviousOff"], 8) == 0, "lj previous")
    b = lj + lay["ljBOff"]
    inv["setjmpRet"] = rd(b + 8 * lay["jbRa"], 8)
    inv["rawrunSp"] = rd(b + 8 * lay["jbSp"], 8)
    for i in range(12):
        need(M.present(b + 8 * (lay["jbS0"] + i), 8), "jmp_buf s-register slots")
    # ---- StdioBoot
    need(rd(lay["symStdioExitHandler"], 8) == 0, "__stdio_exit_handler")
    need(rd(lay["symImpurePtr"], 8) == lay["symImpureData"], "_impure_ptr")
    imp, sf, fs = lay["symImpureData"], lay["symSf"], lay["fileSize"]
    need(rd(imp + lay["reentStdinOff"], 8) == sf, "stdin")
    need(rd(imp + lay["reentStdoutOff"], 8) == sf + fs, "stdout")
    need(rd(imp + lay["reentStderrOff"], 8) == sf + 2 * fs, "stderr")
    need(rd(lay["symSglue"] + lay["glueNextOff"], 8) == 0, "glue next")
    need(rd(lay["symSglue"] + lay["glueNiobsOff"], 4) == 3, "glue niobs")
    need(rd(lay["symSglue"] + lay["glueIobsOff"], 8) == sf, "glue iobs")
    need(lay["symSfSize"] == 3 * fs, "__sf is three FILEs")
    need(all(rd(sf + i, 1) == 0 for i in range(lay["symSfSize"])), "__sf zero")
    # ---- MemfsBoot
    need(rd(lay["symFsReady"], 4) == 0, "fs_ready")
    need(all(rd(lay["symFds"] + i, 1) == 0 for i in range(lay["symFdsSize"])), "fds zero")
    need(all(rd(lay["symFiles"] + i, 1) == 0 for i in range(lay["symFilesSize"])), "files zero")
    # ---- HeapAt
    heap = heap_walk(lay, M)
    # ---- LuaStateAt
    w = dict(func=e["func"], stackLast=e["stackLast"], g=e["g"])
    need(rd(L + lay["stateHookmaskOff"], 4) == 0, "hookmask")
    need(rd(ci + lay["ciTrapOff"], 4) == 0, "trap")
    need(rd(L + lay["stateErrfuncOff"], 8) == 0, "errfunc")
    inv["nCcallsEntry"] = rd(L + lay["stateNCcallsOff"], 4)
    need(rd(L + lay["stateOpenupvalOff"], 8) == 0, "openupval")
    w["stack"] = rd(L + lay["stateStackOff"], 8)
    need(rd(L + lay["stateTbclistOff"], 8) == w["stack"], "tbclist")
    need(w["stack"] <= w["func"], "stack_le")
    need(rd(L + lay["stateTopOff"], 8) == w["func"] + lay["stackValueSize"], "top")
    w["ciTop"] = rd(ci + lay["ciTopOff"], 8)
    need(w["ciTop"] <= w["stackLast"], "ci_top_le")
    need(rd(ci + lay["ciCallstatusOff"], 2) == lay["cistFresh"], "callstatus")
    need(rd(ci + lay["ciNresultsOff"], 2) == 0, "nresults")
    need(rd(ci + lay["ciPreviousOff"], 8) == L + lay["stateBaseCiOff"], "previous")
    need(rd(ci + lay["ciNextOff"], 8) == 0, "next")
    g = w["g"]
    for t in ("luaTnil", "luaTboolean", "luaTnumber"):
        need(rd(g + lay["gMtOff"] + 8 * lay[t], 8) == 0, f"mt[{t}]")
    w["strtHash"] = rd(g + lay["gStrtHashOff"], 8)
    w["strtSize"] = rd(g + lay["gStrtSizeOff"], 4)
    w["strtNuse"] = rd(g + lay["gStrtNuseOff"], 4)
    size = w["strtSize"]
    need(w["strtNuse"] <= size and size > 0 and size & (size - 1) == 0, "strt size")
    heads, count = [], 0
    for i in range(size):
        ts = rd(w["strtHash"] + 8 * i, 8)
        heads.append(ts)
        while ts:
            need(rd(ts + lay["gcTtOff"], 1) == lay["gcShrStr"], "strt chain tag")
            need(rd(ts + lay["tstringHashOff"], 4) % size == i, "strt chain bucket")
            ts = rd(ts + lay["tstringLnglenOff"], 8)
            count += 1
    need(count == w["strtNuse"], "strt nuse counts the chained strings")
    w["strtHeads"] = heads
    cache = []
    for i in range(lay["strcacheN"] * lay["strcacheM"]):
        ts = rd(g + lay["gStrcacheOff"] + 8 * i, 8)
        need(rd(ts + lay["gcTtOff"], 1) in (lay["gcShrStr"], lay["gcLngStr"]), "strcache tag")
        cache.append(ts)
    w["strcache"] = cache
    w.update(heap)
    # ---- VmRegionsAt
    lo, hi = lay["symEnd"], lay["symHeapEnd"]
    need(lo <= L and L + lay["stateSize"] <= hi, "L in the heap")
    need(lo <= ci and ci + lay["ciSize"] <= hi, "ci in the heap")
    need(lo <= w["stack"] and w["stackLast"] <= hi, "the Lua stack in the heap")
    need(w["func"] % 8 == 0, "func_al")
    need(ci + lay["ciSize"] <= w["stack"] or w["stackLast"] <= ci, "ci apart from the Lua stack")
    w["cl"] = rd(w["func"] + lay["tvalueValOff"], 8)
    need(lo <= w["cl"] and w["cl"] + lay["lclosureUpvalsOff"] <= hi, "the closure in the heap")
    w["proto"] = rd(w["cl"] + lay["lclosureProtoOff"], 8)
    need(lo <= w["proto"] and w["proto"] + lay["protoCodeOff"] + 8 <= hi, "the Proto in the heap")
    w["code"] = rd(w["proto"] + lay["protoCodeOff"], 8)
    w["sizecode"] = rd(w["proto"] + lay["protoSizecodeOff"], 4)
    code_end = w["code"] + 4 * w["sizecode"]
    need(lo <= w["code"] and code_end <= hi, "the code array in the heap")
    need(code_end <= w["stack"] or w["stackLast"] <= w["code"], "the code array apart from the Lua stack")
    w["k"] = rd(w["proto"] + lay["protoKOff"], 8)
    w["sizek"] = rd(w["proto"] + lay["protoSizekOff"], 4)
    k_end = w["k"] + lay["tvalueSize"] * w["sizek"]
    need(lo <= w["k"] and k_end <= hi, "the constant array in the heap")
    need(w["k"] % 8 == 0, "k_al")
    need(k_end <= w["stack"] or w["stackLast"] <= w["k"], "the constant array apart from the Lua stack")
    L_end, ci_end = L + lay["stateSize"], ci + lay["ciSize"]
    need(L_end <= ci or ci_end <= L, "L_sep_ci")
    need(code_end <= L or L_end <= w["code"], "code_sep_L")
    need(code_end <= ci or ci_end <= w["code"], "code_sep_ci")
    need(k_end <= L or L_end <= w["k"], "k_sep_L")
    need(k_end <= ci or ci_end <= w["k"], "k_sep_ci")
    need(L_end <= w["stack"] or w["stackLast"] <= L, "L_sep_stack")
    # ---- KInterned: short constants with equal bytes are one TString
    interned = {}
    for i in range(w["sizek"]):
        a = w["k"] + lay["tvalueSize"] * i
        if rd(a + lay["tvalueTagOff"], 1) != lay["vShrStr"]:
            continue
        ts = rd(a + lay["tvalueValOff"], 8)
        n = rd(ts + lay["tstringShrlenOff"], 1)
        s = bytes(rd(ts + lay["tstringContentsOff"] + j, 1) for j in range(n))
        need(interned.setdefault(s, ts) == ts, "KInterned")
    return e, w, slot, inv


def plat_insns_per_tick():
    """The Sail model's `plat_insns_per_tick` (`Vsa.stepOnce`'s tick period)."""
    src = (ROOT / "riscv-lean" / "Lean_RV64D_executable" / "LeanRV64DExecutable"
           / "PlatformConfig.lean").read_text()
    return int(re.search(r"def plat_insns_per_tick : nat1 := (\d+)", src).group(1))


def check_harness(lay, log):
    """`HarnessAt`: the tick counter (`Config.tick`, reset to 0 every
    `plat_insns_per_tick` steps from 0) stays below 2, and no boot store
    touched `tohost` (the HTIF console is empty)."""
    need(plat_insns_per_tick() <= 2, "tick < 2")
    t = lay["symTohost"]
    need(all(a + wd <= t or t + 8 <= a for a, wd, _ in log), "no console output before the entry")


def check_regs(lay, entry, log):
    """`MachineAt.regs` (`RegsOk`): every GPR `x1 … x31` holds a value at the
    entry (the traced row has all 31), and the HTIF mailbox is idle:
    `htif_payload_writes` starts at the model's `undefined_bitvector 4`, which
    the machine's choice source (`trivialChoiceSource`, lean-sail) makes 0,
    and only a store to the `tohost` word changes it; no boot store touches
    it."""
    need(len(entry) >= 35 and all(re.fullmatch(r"[0-9a-fA-F]{1,16}", x) for x in entry[4:35]),
         "every GPR present at the entry")
    src = (ROOT / "riscv-lean" / "lean-sail" / "Sail" / "ConcurrencyInterfaceV1.lean").read_text()
    need(re.search(r"def trivialChoiceSource[\s\S]*?\| \.bitvector _ => 0\n", src) is not None,
         "the choice source's undefined bit vectors are 0")
    t = lay["symTohost"]
    need(all(a + wd <= t or t + 8 <= a for a, wd, _ in log), "the HTIF mailbox is idle at the entry")


def check_tstring(lay, M, ts, s):
    rd = M.rd
    n = len(s)
    if n <= lay["maxShortLen"]:
        need(rd(ts + lay["gcTtOff"], 1) == lay["gcShrStr"], "short string tag")
        need(rd(ts + lay["tstringShrlenOff"], 1) == n, "shrlen")
    else:
        need(rd(ts + lay["gcTtOff"], 1) == lay["gcLngStr"], "long string tag")
        need(rd(ts + lay["tstringLnglenOff"], 8) == n, "lnglen")
    c = ts + lay["tstringContentsOff"]
    need(all(rd(c + i, 1) == s[i] for i in range(n)) and rd(c + n, 1) == 0, "string bytes")


def check_proto(lay, M, pa, proto):
    rd = M.rd
    numparams, vararg, maxstack, code, k, ups, protos = proto
    need(rd(pa + lay["gcTtOff"], 1) == 10, "proto tag")
    need(rd(pa + lay["protoNumparamsOff"], 1) == numparams, "numparams")
    need(rd(pa + lay["protoIsVarargOff"], 1) == vararg, "is_vararg")
    need(rd(pa + lay["protoMaxstacksizeOff"], 1) == maxstack, "maxstacksize")
    need(rd(pa + lay["protoSizecodeOff"], 4) == len(code), "sizecode")
    ca = rd(pa + lay["protoCodeOff"], 8)
    need(all(rd(ca + 4 * i, 4) == wd for i, wd in enumerate(code)), "code words")
    need(rd(pa + lay["protoSizekOff"], 4) == len(k), "sizek")
    ka = rd(pa + lay["protoKOff"], 8)
    for i, c in enumerate(k):
        a = ka + lay["tvalueSize"] * i
        tag = rd(a + lay["tvalueTagOff"], 1)
        kind, val = c
        if kind == "nil":
            need(tag == lay["vNil"], "k nil")
        elif kind == "bool":
            need(tag == (lay["vTrue"] if val else lay["vFalse"]), "k bool")
        elif kind == "int":
            need(tag == lay["vNumInt"] and rd(a + lay["tvalueValOff"], 8) == val, "k int")
        elif kind == "float":
            need(tag == lay["vNumFlt"] and rd(a + lay["tvalueValOff"], 8) == val, "k float")
        else:
            need(tag == (lay["vShrStr"] if len(val) <= lay["maxShortLen"] else lay["vLngStr"]),
                 "k str tag (strTag: the variant follows the length)")
            check_tstring(lay, M, rd(a + lay["tvalueValOff"], 8), val)
    need(rd(pa + lay["protoSizeupvaluesOff"], 4) == len(ups), "sizeupvalues")
    ua = rd(pa + lay["protoUpvaluesOff"], 8)
    for i, (instack, idx, kind) in enumerate(ups):
        a = ua + lay["upvaldescSize"] * i
        need((rd(a + lay["upvaldescInstackOff"], 1), rd(a + lay["upvaldescIdxOff"], 1),
              rd(a + lay["upvaldescKindOff"], 1)) == (instack, idx, kind), "upvaldesc")
    need(rd(pa + lay["protoSizepOff"], 4) == len(protos) == 0, "no nested protos (F1)")
    need(M.present(pa + lay["protoPOff"], 8), "proto p field")


def find_print(lay, M, t):
    rd = M.rd
    lsz = rd(t + lay["tableLsizenodeOff"], 1)
    node = rd(t + lay["tableNodeOff"], 8)
    for i in range(1 << lsz):
        n = node + lay["nodeSize"] * i
        if rd(n + lay["nodeKeyTtOff"], 1) != lay["vShrStr"]:
            continue
        ts = rd(n + lay["nodeKeyValOff"], 8)
        s = bytes(rd(ts + lay["tstringContentsOff"] + j, 1) for j in range(rd(ts + lay["tstringShrlenOff"], 1)))
        if s == b"print":
            check_tstring(lay, M, ts, list(b"print"))
            need(rd(n + lay["tvalueTagOff"], 1) == lay["vLcf"], "print tag")
            need(rd(n + lay["tvalueValOff"], 8) == lay["symLuaBPrint"], "print is luaB_print")
            return dict(lsz=lsz, node=node, i=i, ts=ts)
    raise Fail("_ENV has no \"print\"")


def heap_walk(lay, M):
    rd = M.rd
    av = lay["symMallocAv"]
    start, end = lay["symEnd"], lay["symHeapEnd"]
    top, brkv = rd(av + 16, 8), rd(lay["symBrk"], 8)
    need(rd(lay["symMallocSbrkBase"], 8) == start, "sbrk_base")
    need(top <= brkv <= end and (brkv - top) % 16 == 0, "top/brk")
    need(rd(top + 8, 8) == brkv - top + 1, "top header")
    need(rd(lay["symMallocTopPad"], 8) == 0, "top_pad")
    need(M.present(lay["symMallocMaxSbrked"], 8) and M.present(lay["symMallocMallinfo"], 8), "mallinfo")
    need(rd(start + 8, 8) % 2 == 1, "first prev_inuse")
    p, chunks = start, []
    while p != top:
        h = rd(p + 8, 8)
        sz = h // 4 * 4
        need(h % 4 < 2 and sz >= 32 and sz % 16 == 0, f"chunk header at {p:#x}")
        chunks.append((p, sz, rd(p + sz + 8, 8) % 2 == 1))
        p += sz
        need(p <= top, "walk overshoots top")
    for c, d in zip(chunks, chunks[1:]):
        need(c[2] or d[2], "coalesced")
    for a, sz, inuse in chunks:
        if not inuse:
            need(rd(a + sz, 8) == sz, "free footer")
    bins = []
    for i in range(128):
        b = av + 16 * i
        q, qs, prev = rd(b + 16, 8), [], b
        while i > 0 and q != b:
            need(rd(q + 24, 8) == prev, "bin bk")
            qs.append(q)
            prev, q = q, rd(q + 16, 8)
        if i > 0:
            need(rd(b + 24, 8) == prev, "bin close")
        bins.append(qs)
    free = {a for a, _, u in chunks if not u}
    binned = [q for qs in bins for q in qs]
    need(sorted(binned) == sorted(free), "every free chunk is on exactly one bin")
    need(len(bins[1]) <= 1, "last remainder")
    while bins and not bins[-1]:
        bins.pop()
    return dict(top=top, brkv=brkv, chunks=chunks, bins=bins)


# ------------------------------------------------------------------ Lean
def pack(items, bits):
    n = 0
    for i, x in enumerate(items):
        assert 0 <= x < (1 << bits), (x, bits)
        n |= x << (bits * i)
    return n


def if_tree(var, n, leaf):
    def go(lo, hi):
        if hi - lo == 1:
            return leaf(lo)
        mid = (lo + hi) // 2
        return f"(if {var} < {mid} then {go(lo, mid)} else {go(mid, hi)})"
    return go(0, n)


def byte_pages(name, data, doc):
    pages = [data[i:i + PAGE] for i in range(0, len(data), PAGE)]
    out = [f"private def {name}Page{i} : Nat := {hex(pack(pg, 8))}" for i, pg in enumerate(pages)]
    out += ["", f"private def {name}Page (page : Nat) : Nat :=\n  "
            + if_tree("page", len(pages), lambda k: f"{name}Page{k}"), "",
            f"/-- {doc} -/",
            f"def {name} (offset : Nat) : BitVec 8 :=\n"
            f"  BitVec.ofNat 8 (Nat.shiftRight ({name}Page (offset / {PAGE})) (8 * (offset % {PAGE})))"]
    return out


def final_runs(log):
    fin = {}
    for i, (a, w, v) in enumerate(log):
        for j in range(w):
            fin[a + j] = (i, (v >> (8 * j)) & 0xFF)
    runs = []
    for k in sorted(fin):
        if runs and runs[-1][0] + len(runs[-1][1]) == k and len(runs[-1][1]) < RUN_MAX:
            runs[-1][1].append(fin[k])
        else:
            runs.append([k, [fin[k]]])
    return runs


def run_tree(runs):
    def go(lo, hi):
        if hi - lo == 1:
            b, cells = runs[lo]
            return f"(.leaf ⟨{b:#x}, {len(cells)}, {hex(pack([i | (x << 24) for i, x in cells], 32))}⟩)"
        mid = (lo + hi) // 2
        return f"(.node {runs[mid][0]:#x}\n    {go(lo, mid)}\n    {go(mid, hi)})"
    return go(0, len(runs))


def lean_bytes(bs):
    return "[" + ", ".join(str(b) for b in bs) + "]"


def lean_list(xs, fmt=hex):
    return "[" + ", ".join(fmt(x) for x in xs) + "]"


def render_data(lay, inv, names):
    segs = ",\n   ".join(f"({a:#x}, {lean_bytes(bs)})" for a, bs in inv["callerFrames"])
    chain = ",\n   ".join(f"({s:#x}, {r:#x})" for s, r in inv["returnChain"])
    return "\n".join([
        "/-! GENERATED by scripts/gen_lua_boot_witness.py -- do not edit.",
        "",
        "The boot-invariant values `luaRuntimeReady` (Lua/Vm/Runtime.lean) pins, read",
        f"from the boot traces of {', '.join(names)} at `luaV_execute`'s entry; the",
        "generator fails unless every traced program agrees on each of them. -/",
        "",
        "namespace Lua.Vm.RuntimeData",
        "",
        "/-- `sp` at the entry: `_start` → `main` → `lua_pcallk` → `luaD_pcall` →",
        "`luaD_rawrunprotected` → `f_call` → `luaD_callnoyield` (`ccall`). -/",
        f"def spEntry : Nat := {inv['spEntry']:#x}",
        "/-- `ra` at the entry: after `ccall`'s `jal luaV_execute`. -/",
        f"def retCcall : Nat := {inv['retCcall']:#x}",
        "/-- `L->errorJmp`: `luaD_rawrunprotected`'s local `struct lua_longjmp lj`. -/",
        f"def ljAddr : Nat := {inv['ljAddr']:#x}",
        "/-- The `jmp_buf`'s `ra`: after `luaD_rawrunprotected`'s `jal setjmp`. -/",
        f"def setjmpRet : Nat := {inv['setjmpRet']:#x}",
        "/-- The `jmp_buf`'s `sp`: `luaD_rawrunprotected`'s frame. -/",
        f"def rawrunSp : Nat := {inv['rawrunSp']:#x}",
        "/-- newlib's riscv `setjmp` slots (dwords of the `jmp_buf`), read from its",
        "`sd` instructions: `ra`, then `s0 … s11`, then `sp`. -/",
        f"def jbRa : Nat := {lay['jbRa']}",
        f"def jbS0 : Nat := {lay['jbS0']}",
        f"def jbSp : Nat := {lay['jbSp']}",
        "/-- `L->nCcalls` at the entry (two non-yieldable C calls, one C level). -/",
        f"def nCcallsEntry : Nat := {inv['nCcallsEntry']:#x}",
        "",
        "/-- The present bytes of the caller frames `[spEntry, __stack_top)`, as",
        "maximal runs. -/",
        "def callerFrames : List (Nat × List UInt8) :=",
        f"  [{segs}]",
        "",
        "/-- The saved return addresses of the caller chain `(slot, return address)`,",
        "outermost first (each stored by its callee's prologue `sd ra`). -/",
        "def returnChain : List (Nat × Nat) :=",
        f"  [{chain}]",
        "",
        "end Lua.Vm.RuntimeData",
        ""])


def render_image(lay, raw):
    vaddr, off, filesz = pt_load(raw)
    base = lay["dataBase"]
    data = [raw[off + a - vaddr] for a in range(base, lay["__bss_start"])]
    out = ["/-! GENERATED by scripts/gen_lua_boot_witness.py -- do not edit.",
           "",
           "The loaded bytes of `c/lua-riscv-htif.elf` between `.rodata` and `.bss`",
           "(`.tohost`, `.data`, `.init_array`), and the loaded segment's geometry.",
           "Packed data only. -/",
           "",
           "namespace Lua.Vm.Boot",
           "",
           "/-- The PT_LOAD segment: `p_vaddr`, `p_filesz` (the loader inserts these bytes). -/",
           f"def segBase : Nat := {vaddr:#x}",
           f"def segSize : Nat := {filesz:#x}",
           "/-- The end of `.rodata`, where the data bytes start. -/",
           f"def dataBase : Nat := {base:#x}",
           "/-- `__bss_start`: `.bss` and the chunk region's padding load as zeros. -/",
           f"def bssStart : Nat := {lay['__bss_start']:#x}",
           "/-- `__chunk_region`: `_chunk_size`, then the chunk (`c/src/chunk.S`). -/",
           f"def chunkRegion : Nat := {lay['__chunk_region']:#x}",
           ""]
    out += byte_pages("dataByte", data, f"Loaded bytes `[{base:#x}, {lay['__bss_start']:#x})`, by offset.")
    out += ["", "end Lua.Vm.Boot", ""]
    return "\n".join(out)


def render_program(lay, name, lean, proto_const, module, chunk, log, entry, e, w, slot):
    runs = final_runs(log)
    enc = [a | (wd << 32) | (v << 36) for a, wd, v in log]
    pages = [enc[i:i + LOG_PAGE] for i in range(0, len(enc), LOG_PAGE)]
    regs = [int(x, 16) for x in entry[4:35]]
    blob = chunk_region(lay, chunk)
    out = [
        "import Lua.Vm.Boot.Image",
        "import Lua.Vm.Runtime",
        f"import {module}",
        "",
        "/-!",
        f"# Boot trace of `c/tests/{name}.lua` (GENERATED by scripts/gen_lua_boot_witness.py -- do not edit)",
        "",
        f"The entry state at `luaV_execute` (emulator step {int(entry[1])}): the chunk region",
        f"(`chunk`), {len(log)} stores from `_start` (`log`), their final bytes (`runs`,",
        f"{len(runs)} runs), the entry registers (`gprs`), and the witness pointers",
        f"(`e` for `VmEntryData`, `w` for `luaRuntimeReady`, `printSlot` for `_ENV.print`).",
        "Every field of `VmEntryData … e` and `RuntimeReadyAt … w` holds at this memory",
        "(evaluated natively by the generator); the kernel witness is open (PHASES A0.6).",
        "-/",
        "",
        f"namespace Lua.Vm.Boot.Gen.{lean}",
        "",
        "open Lua.Vm Lua.Vm.Boot",
        "",
        f"/-- The `.lua_chunk` region's bytes (`_chunk_size`, the chunk, a NUL), little-endian. -/",
        f"def chunk : Nat := {hex(pack(list(blob), 8))}",
        "",
    ]
    for i, pg in enumerate(pages):
        out.append(f"private def logPage{i} : Nat := {hex(pack(pg, 128))}")
    out += ["", "private def logPage (i : Nat) : Nat :=\n  " + if_tree("i", len(pages), lambda k: f"logPage{k}"),
            "",
            "/-- The stores from `_start` to the entry, in program order. -/",
            f"def log : PackedLog := ⟨logPage, {len(log)}⟩",
            "",
            "/-- The final byte of every stored address, with its last writer. -/",
            f"def runs : RunTree :=\n  {run_tree(runs)}",
            "",
            "/-- The entry memory's byte view (`bootMem_get`). -/",
            "def view : View := bootView chunk runs",
            "",
            "/-- `x1 … x31` at the entry. -/",
            "def gprs : List (Nat × BitVec 64) :=",
            "  [" + ",\n   ".join(f"({r + 1}, {v:#x}#64)" for r, v in enumerate(regs)) + "]",
            "",
            "/-- Architectural steps from `_start` to the entry. -/",
            f"def entrySteps : Nat := {int(entry[1])}",
            "",
            f"/-- `L` and `ci`: `a0`, `a1`. -/",
            f"def L : Nat := {regs[9]:#x}",
            f"def ci : Nat := {regs[10]:#x}",
            "",
            "/-- The pointers `VmEntryData` names. -/",
            "def e : EntryPtrs where",
            ] + [f"  {k} := {e[k]:#x}" for k in ("func", "cl", "pa", "code", "uv", "envv", "env", "g", "stackLast")] + [
            "",
            "/-- `_ENV.print`'s node: `(lsizenode, node array, index, key string)`. -/",
            f"def printSlot : Nat × Nat × Nat × Nat := ({slot['lsz']}, {slot['node']:#x}, {slot['i']}, {slot['ts']:#x})",
            "",
            "/-- The program-dependent pointers and heap shape of `luaRuntimeReady`. -/",
            "def w : RtPtrs where",
            ] + [f"  {k} := {w[k]:#x}" for k in ("func", "stack", "stackLast", "ciTop", "g", "strtHash")] + [
            f"  strtSize := {w['strtSize']}",
            f"  strtNuse := {w['strtNuse']}",
            f"  strtHeads := {lean_list(w['strtHeads'])}",
            f"  strcache := {lean_list(w['strcache'])}",
            f"  top := {w['top']:#x}",
            f"  brkv := {w['brkv']:#x}",
            "  chunks :=",
            "    [" + ",\n     ".join(f"⟨{a:#x}, {sz:#x}, {'true' if u else 'false'}⟩" for a, sz, u in w["chunks"]) + "]",
            f"  bins := {'[' + ', '.join(lean_list(qs) for qs in w['bins']) + ']'}",
            ] + [f"  {k} := {w[k]:#x}" for k in ("cl", "proto", "code")] + [
            f"  sizecode := {w['sizecode']}",
            f"  k := {w['k']:#x}",
            f"  sizek := {w['sizek']}",
            "",
            f"/-- The program at the entry: `{proto_const}` (`scripts/gen_proto.py` on the same chunk). -/",
            f"abbrev proto : Lua.Bytecode.Proto := {proto_const}",
            "",
            f"end Lua.Vm.Boot.Gen.{lean}",
            ""]
    return "\n".join(out)


# ------------------------------------------------------------------ driver
def setjmp_slots(lay, raw, seg):
    """`sd rs2, imm(a0)` of newlib's riscv setjmp: dword slot per register."""
    slots, a = {}, lay["symSetjmp"]
    for k in range(14):
        wd = text_word(raw, seg, a + 4 * k)
        need(wd & 0x7F == 0x23 and (wd >> 12) & 7 == 3 and (wd >> 15) & 31 == 10, "setjmp sd a0")
        imm = ((wd >> 25) << 5) | ((wd >> 7) & 31)
        slots[(wd >> 20) & 31] = imm // 8
    sregs = [8, 9] + list(range(18, 28))
    s0 = slots[8]
    need([slots[r] for r in sregs] == list(range(s0, s0 + 12)), "setjmp s-register slots")
    return slots[1], s0, slots[2]


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--work")
    ap.add_argument("--check", action="store_true")
    args = ap.parse_args()
    lay = layout()
    raw = ELF.read_bytes()
    seg = pt_load(raw)
    lay["dataBase"] = section_end(raw, ".rodata")
    lay["textEnd"] = section_end(raw, ".text")
    lay["jbRa"], lay["jbS0"], lay["jbSp"] = setjmp_slots(lay, raw, seg)
    work = Path(args.work) if args.work else Path(tempfile.mkdtemp(prefix="lua-boot-"))
    work.mkdir(parents=True, exist_ok=True)
    outputs, invs, names = {}, [], []
    for name, chunk_path, lean, proto_const, module in PROGRAMS:
        chunk = (ROOT / chunk_path).read_bytes()
        elf = patched_elf(lay, chunk)
        if name == "while":
            need(elf == raw, "the committed ELF embeds c/tests/while.luac")
        elf_path = work / f"{name}.elf"
        elf_path.write_bytes(elf)
        log, entry, calls = trace(elf_path, lay["symLuaVExecute"])
        regs = [0] + [int(x, 16) for x in entry[4:35]]
        M = Mem(entry_memory(elf, log))
        proto = undump(chunk)
        try:
            e, w, slot, inv = evaluate(lay, M, regs, proto)
            check_harness(lay, log)
            check_regs(lay, entry, log)
        except Fail as ex:
            raise SystemExit(f"{name}: the entry state fails {ex}")
        need(calls[-1][0] == regs[1] and calls[-1][2] is None, "the innermost call is ccall's, in ra")
        need(all(c[2] is not None for c in calls[:-1]), "every open caller saved its ra")
        inv["returnChain"] = [(c[2], c[0]) for c in calls[:-1]]
        for _, r in inv["returnChain"]:
            wd = text_word(raw, seg, r - 4)
            need(wd & 0x7F in (0x6F, 0x67) and (wd >> 7) & 31 == 1, "a call precedes each return address")
        print(f"{name}: entry at step {entry[1]}, {len(log)} stores, "
              f"{len(w['chunks'])} heap chunks, {w['strtNuse']} interned strings: all fields hold")
        invs.append(inv)
        names.append(f"`{name}.lua`")
        outputs[GEN_DIR / f"{lean}.lean"] = render_program(
            lay, name, lean, proto_const, module, chunk, log, entry, e, w, slot)
    for k in invs[0]:
        for inv in invs[1:]:
            need(inv[k] == invs[0][k], f"boot-invariant value {k} differs between programs")
    outputs[OUT_DATA] = render_data(lay, invs[0], names)
    outputs[OUT_IMAGE] = render_image(lay, raw)
    if args.check:
        bad = [p for p, t in outputs.items() if not p.exists() or p.read_text() != t]
        for p in bad:
            print(f"boot witness: DRIFT in {p.relative_to(ROOT)} (rerun scripts/gen_lua_boot_witness.py)")
        print("boot witness: ok" if not bad else "")
        sys.exit(1 if bad else 0)
    for p, t in outputs.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(t)
        print("wrote", p.relative_to(ROOT))


def section_end(raw, want):
    shoff = struct.unpack_from("<Q", raw, 0x28)[0]
    shentsize, shnum, shstrndx = struct.unpack_from("<HHH", raw, 0x3A)
    def sh(i):
        return struct.unpack_from("<IIQQQQIIQQ", raw, shoff + i * shentsize)
    stroff = sh(shstrndx)[4]
    for i in range(shnum):
        s = sh(i)
        nm = raw[stroff + s[0]:raw.index(b"\0", stroff + s[0])].decode()
        if nm == want:
            return s[3] + s[5]
    raise SystemExit(f"no section {want}")


def undump(chunk):
    """The chunk's main function, by gen_proto.py's own undumper (its
    definitions only: the module runs `main()` at import)."""
    import ast
    import types
    src = (ROOT / "scripts" / "gen_proto.py").read_text()
    tree = ast.parse(src)
    tree.body = [n for n in tree.body if isinstance(n, (ast.Import, ast.ImportFrom, ast.ClassDef, ast.FunctionDef))]
    GP = types.ModuleType("gen_proto_defs")
    exec(compile(tree, "gen_proto.py", "exec"), GP.__dict__)
    r = GP.R(chunk)
    GP.header(r)
    numparams, vararg, maxstack, code, k, ups, protos = GP.function(r)
    kk = []
    for c in k:
        if c == ".nil":
            kk.append(("nil", None))
        elif c.startswith(".bool"):
            kk.append(("bool", c.endswith("true")))
        elif c.startswith(".int"):
            kk.append(("int", int(c.split()[1].split("#")[0])))
        elif c.startswith(".float"):
            kk.append(("float", int(c.split()[1].split("#")[0], 16)))
        else:
            kk.append(("str", [int(x) for x in re.findall(r"\d+", c)]))
    return (numparams, vararg, maxstack, code, kk, ups, protos)


if __name__ == "__main__":
    main()

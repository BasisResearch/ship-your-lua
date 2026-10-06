#!/usr/bin/env python3
"""Per-function code pins for the Lua ELF, derived from `Lua/Vm/Image.lean`.

ship-your-interpreter's pair, retargeted:
  * `experiments/gen_code_lemmas.py` (copied as experiments/syi/) emits, per
    function F, `<f>Chunk<i>` (the byte facts of 16 instructions), `<F>Loaded`
    (their conjunction), chunk projections and one fetch lemma
    `<f>_at_<addr>` per instruction (the four byte facts the step lemmas
    consume);
  * `scripts/gen_fixed_image.py --projection F` emits
    `FixedImage_<F>.lean`: per chunk, `h off (by decide)` for each byte, so
    the kernel checks every pinned byte against the packed image; then
    `<F>Loaded` from the whole-image hypothesis.
Here the image hypothesis is `Vsa.Sim.Code.FixedBytesLoaded Image.textBase
Image.textSize Image.textByte mem`, the `text` field of `VmLoaded`
(`Lua/Vm/Loaded.lean`), and the bytes are read from the ELF and checked
against `Lua/Vm/Image.lean`'s packed pages before emission.

One change of shape: a function of more than `PART_CHUNKS` chunks
(luaV_execute has 252) is split into parts `<F>/P<k>.lean`, each exactly the
syi shape (`<F>_p<k>Loaded` over at most 16 chunks, site lemmas from it), and
`<F>Loaded` is the conjunction of the parts. Projection depth stays bounded
(16 parts x 16 chunks x 64 bytes) and every module stays small.

Functions: luaV_execute and its F1 callees, read from
experiments/census/luaV_execute_arms.tsv (the F1 arms' callees, minus the
soft-float/libm routines that the integers-only `Supported` prunes, which
are A6), plus `EXTRA`: the callees reached below them on F1 paths (the
`print` chain and the error helpers).

    python3 scripts/gen_lua_code.py [--check] [--list]
"""
import csv
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ELF = ROOT / "c/lua-riscv-htif.elf"
IMAGE = ROOT / "Lua/Vm/Image.lean"
OUT = ROOT / "Lua/Vm/Code"
ARMS_TSV = ROOT / "experiments/census/luaV_execute_arms.tsv"
ARMS_JSON = ROOT / "experiments/census/luaV_execute_arms.json"
sys.path.insert(0, str(ROOT / "scripts"))
from gen_lua_decode_check import OBJDUMP  # noqa: E402

CHUNK = 16          # instructions per chunk (64 byte conjuncts), as syi
PART_CHUNKS = 16    # chunks per module before a function is split into parts
# `Lua/Fragment.lean` classifies VARARGPREP as F1 (every main chunk opens
# with it); the census summary's F1 list predates that.
F1_EXTRA_OPS = {"OP_VARARGPREP"}
# Soft-float and libm callees of the F1 arms: float paths, pruned by the
# integers-only `Supported` (PHASES.md A1, A6).
FLOAT = re.compile(r"df|^floor$|^fmod$|^pow$")
# Callees below the arms on F1 paths: CALL print -> luaD_precall ->
# luaB_print -> luaL_tolstring, lua_writestring = fwrite (lauxlib.h:260);
# the error helper luaG_opinterror. (`__udivdi3` is an alias of
# `__hidden___udivdi3`, the label objdump prints, so it is pinned as that;
# `__umoddi3` holds `__divdi3`'s sign fix-ups, `0x8002f78c`, `0x8002f79c`.)
EXTRA = ["luaB_print", "luaL_tolstring", "fwrite", "luaG_opinterror", "__umoddi3",
         # axis S: the string callees of EQ (long strings) and LT/LE
         "luaS_eqlngstr", "memcmp", "strcoll", "strcmp", "strlen",
         # lane F1-2: OP_LEN on a string (`luaV_objlen`)
         "luaV_objlen",
         # lane F1-4: the return chain of `OP_RETURN*` (`FinalSim`): `luaF_close`'s
         # callee, then `ccall` -> ... -> `main` -> `_start` -> `exit` -> `_exit`
         "luaF_closeupval", "luaD_callnoyield", "luaD_rawrunprotected", "luaD_pcall",
         "lua_pcallk", "main", "_start", "exit", "__call_exitprocs",
         "__retarget_lock_acquire_recursive", "__retarget_lock_release_recursive", "_exit",
         # lane F1-6: htif.c's console write, the bottom of `print`'s stdio chain
         "_write", "_write_r", "__swrite", "__sflush_r",
         # lane F1-8: the stdio calls above it (the callee-context route)
         "fflush", "memmove", "_fflush_r", "memchr", "__sfvwrite_r"]

FUNC_RE = re.compile(r"^([0-9a-f]{16}) <(.+)>:$")
INST_RE = re.compile(r"^\s+([0-9a-f]+):\s+([0-9a-f]{8})\s")
ALLOW = ("  -- discipline: allow(R6-anon-projection-tower) generated "
         "code-pin projections (bounded, chunked)\n")


def functions() -> list[str]:
    f1 = set(json.load(open(ARMS_JSON))["summary"]["F1_ops"]) | F1_EXTRA_OPS
    names = {"luaV_execute"}
    for row in csv.DictReader(open(ARMS_TSV), delimiter="\t"):
        if row["op"] in f1:
            for c in filter(None, row["callees"].split(",")):
                c = re.sub(r"x\d+$", "", c)       # `floorx2`: called twice
                if not FLOAT.search(c):
                    names.add(c)
    return ["luaV_execute"] + sorted(names - {"luaV_execute"}) + \
        [f for f in EXTRA if f not in names]


def disasm() -> dict:
    out = subprocess.run([OBJDUMP, "-d", str(ELF)], capture_output=True,
                         text=True, check=True).stdout
    funcs, cur = {}, None
    for line in out.splitlines():
        m = FUNC_RE.match(line)
        if m:
            cur = m.group(2)
            if cur in funcs:        # two local symbols of one name: unusable
                cur = f"{cur}@dup{len(funcs)}"
                funcs[m.group(2)] = None
            funcs[cur] = []
            continue
        m = INST_RE.match(line)
        if m and cur is not None and funcs[cur] is not None:
            funcs[cur].append((int(m.group(1), 16), int(m.group(2), 16)))
    return funcs


def image_text() -> tuple[int, bytes]:
    """.text as packed in Lua/Vm/Image.lean (independent of the ELF read)."""
    src = IMAGE.read_text()
    base = int(re.search(r"^def textBase : Nat := 0x([0-9a-f]+)", src, re.M)[1], 16)
    size = int(re.search(r"^def textSize : Nat := (\d+)", src, re.M)[1])
    pages = {int(n): int(v, 16) for n, v in
             re.findall(r"^private def textPage(\d+) : Nat := 0x([0-9a-f]+)", src, re.M)}
    data = b"".join(pages[p].to_bytes(256, "little") for p in range(len(pages)))
    return base, data[:size]


def ident(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_]", "_", name)


def byte_facts(addr, word):
    return [(addr + k, (word >> (8 * k)) & 0xFF) for k in range(4)]


def pin(a, b):
    return f"mem[(0x{a:x} : Nat)]? = some (0x{b:02x} : BitVec 8)"


def proj(n, i, var="h"):
    """The i-th conjunct (0-based) of an n-fold right-nested conjunction."""
    if n == 1:
        return var
    return var + ".2" * i + (".1" if i < n - 1 else "")


def pins_module(name, f, pred, insts, chunk_base, mod_doc, top_doc):
    """syi's gen_code_lemmas.emit body for one predicate `pred` over `insts`."""
    chunks = [insts[i:i + CHUNK] for i in range(0, len(insts), CHUNK)]
    L = [top_doc, "open Std (ExtHashMap)\n", "namespace Lua.Vm.Code\n"]
    for ci, ch in enumerate(chunks, chunk_base):
        conj = " ∧\n  ".join(pin(a, b) for addr, w in ch for a, b in byte_facts(addr, w))
        L.append(f"def {f}Chunk{ci} (mem : ExtHashMap Nat (BitVec 8)) : Prop :=\n  {conj}\n")
    top = " ∧ ".join(f"{f}Chunk{ci} mem" for ci in range(chunk_base, chunk_base + len(chunks)))
    L.append(f"/-- {mod_doc} -/\ndef {pred} (mem : ExtHashMap Nat (BitVec 8)) : Prop :=\n  {top}\n")
    for k in range(len(chunks)):
        ci = chunk_base + k
        allow = ALLOW if k >= 3 else ""
        L.append(f"theorem {f}_chunk{ci} {{mem : ExtHashMap Nat (BitVec 8)}}\n"
                 f"    (h : {pred} mem) : {f}Chunk{ci} mem :=\n{allow}  {proj(len(chunks), k)}\n")
    for k, ch in enumerate(chunks):
        ci = chunk_base + k
        for ii, (addr, word) in enumerate(ch):
            concl = " ∧\n      ".join(pin(a, b) for a, b in byte_facts(addr, word))
            parts = ", ".join(proj(4 * len(ch), 4 * ii + j, "hc") for j in range(4))
            allow = ALLOW if ii >= 1 else ""
            L.append(f"theorem {f}_at_{addr:x} {{mem : ExtHashMap Nat (BitVec 8)}}\n"
                     f"    (h : {pred} mem) :\n      {concl} :=\n"
                     f"  have hc := {f}_chunk{ci} h\n{allow}  ⟨{parts}⟩\n")
    L.append("end Lua.Vm.Code\n")
    return "\n".join(L), chunks


TEXT_HYP = ("(h : Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize "
            "Image.textByte mem)")


def fixed_module(imp, f, pred, chunks, chunk_base, base, total_name):
    """syi's gen_fixed_image.projection_module body."""
    L = [f"import {imp}", "import Lua.Vm.Image", "import Vsa.Sim.Code.FixedImage", "",
         "/-! GENERATED by scripts/gen_lua_code.py -- do not edit.", "",
         f"`{pred}` from the packed `.text` of `Lua/Vm/Image.lean`: each pinned",
         "byte is `h offset (by decide)`, checked by the kernel against the image. -/", "",
         "namespace Lua.Vm.Code", ""]
    names = []
    for k, ch in enumerate(chunks):
        ci = chunk_base + k
        thm = f"textLoaded_{f}Chunk{ci}"
        names.append(thm)
        pins = [ab for addr, w in ch for ab in byte_facts(addr, w)]
        terms = ",\n    ".join(f"h {a - base} (by decide)" for a, _ in pins)
        L += [f"theorem {thm} {{mem : Std.ExtHashMap Nat (BitVec 8)}}",
              f"    {TEXT_HYP} : {f}Chunk{ci} mem := by",
              f"  exact ⟨{terms}⟩", ""]
    value = ", ".join(f"{n} h" for n in names)
    value = value if len(names) == 1 else f"⟨{value}⟩"
    L += [f"theorem {total_name} {{mem : Std.ExtHashMap Nat (BitVec 8)}}",
          f"    {TEXT_HYP} : {pred} mem :=", f"  {value}", "",
          f"#print axioms {total_name}", "", "end Lua.Vm.Code", ""]
    return "\n".join(L)


def emit(name, insts, base, text) -> dict:
    for addr, word in insts:     # the ELF's words are the image's bytes
        if not base <= addr < base + len(text) - 3 or \
                int.from_bytes(text[addr - base:addr - base + 4], "little") != word:
            raise ValueError(f"{name}: 0x{addr:x} differs from Lua/Vm/Image.lean")
    f = ident(name)
    F = f[0].upper() + f[1:]
    rng = f"{len(insts)} instructions at [0x{insts[0][0]:x}, 0x{insts[-1][0] + 4:x})"
    per_part = CHUNK * PART_CHUNKS
    files = {}
    if len(insts) <= per_part:
        doc = (f"/-! GENERATED by scripts/gen_lua_code.py -- do not edit.\n\n"
               f"Code-region predicate and fetch lemmas for `{name}`: {rng}. -/\n")
        body, chunks = pins_module(name, f, f"{F}Loaded", insts, 0,
                                   f"The whole `{name}` code region is loaded.", doc)
        files[f"{F}.lean"] = "import Std.Data.ExtHashMap.Basic\n\n" + body
        files[f"FixedImage_{F}.lean"] = fixed_module(
            f"Lua.Vm.Code.{F}", f, f"{F}Loaded", chunks, 0, base, f"textLoaded_{F}Loaded")
        return files
    parts = [insts[i:i + per_part] for i in range(0, len(insts), per_part)]
    preds, fixed_names = [], []
    for k, pi in enumerate(parts):
        pred = f"{F}_p{k:02d}Loaded"
        preds.append(pred)
        cb = k * PART_CHUNKS
        doc = (f"/-! GENERATED by scripts/gen_lua_code.py -- do not edit.\n\n"
               f"Part {k} of `{name}`'s code pins ({rng}): {len(pi)} instructions at "
               f"[0x{pi[0][0]:x}, 0x{pi[-1][0] + 4:x}). -/\n")
        body, chunks = pins_module(name, f, pred, pi, cb,
                                   f"Part {k} of the `{name}` code region is loaded.", doc)
        files[f"{F}/P{k:02d}.lean"] = "import Std.Data.ExtHashMap.Basic\n\n" + body
        tn = f"textLoaded_{pred}"
        fixed_names.append(tn)
        files[f"FixedImage_{F}/P{k:02d}.lean"] = fixed_module(
            f"Lua.Vm.Code.{F}.P{k:02d}", f, pred, chunks, cb, base, tn)
    L = [f"import Lua.Vm.Code.{F}.P{k:02d}" for k in range(len(parts))]
    L += ["", f"/-! GENERATED by scripts/gen_lua_code.py -- do not edit.", "",
          f"Code-region predicate for `{name}`: {rng}, the conjunction of",
          f"{len(parts)} parts (`{F}/P*.lean`; fetch lemmas `{f}_at_<addr>` there). -/", "",
          "open Std (ExtHashMap)", "", "namespace Lua.Vm.Code", "",
          f"/-- The whole `{name}` code region is loaded. -/",
          f"def {F}Loaded (mem : ExtHashMap Nat (BitVec 8)) : Prop :=",
          "  " + " ∧ ".join(f"{p} mem" for p in preds), ""]
    for k, p in enumerate(preds):
        L += [f"theorem {f}_part{k:02d} {{mem : ExtHashMap Nat (BitVec 8)}}",
              f"    (h : {F}Loaded mem) : {p} mem :="]
        if k >= 3:
            L.append(ALLOW.rstrip("\n"))
        L += [f"  {proj(len(preds), k)}", ""]
    L += ["end Lua.Vm.Code", ""]
    files[f"{F}.lean"] = "\n".join(L)
    total = f"textLoaded_{F}Loaded"
    L = [f"import Lua.Vm.Code.FixedImage_{F}.P{k:02d}" for k in range(len(parts))]
    L += [f"import Lua.Vm.Code.{F}", "",
          "/-! GENERATED by scripts/gen_lua_code.py -- do not edit.", "",
          f"`{F}Loaded` from the packed `.text` of `Lua/Vm/Image.lean`. -/", "",
          "namespace Lua.Vm.Code", "",
          f"theorem {total} {{mem : Std.ExtHashMap Nat (BitVec 8)}}",
          f"    {TEXT_HYP} : {F}Loaded mem :=",
          "  ⟨" + ", ".join(f"{n} h" for n in fixed_names) + "⟩", "",
          f"#print axioms {total}", "", "end Lua.Vm.Code", ""]
    files[f"FixedImage_{F}.lean"] = "\n".join(L)
    return files


def render() -> dict:
    funcs = disasm()
    base, text = image_text()
    names = functions()
    files = {}
    for n in names:
        if not funcs.get(n):
            raise ValueError(f"function {n!r} not (uniquely) in the disassembly")
        files.update(emit(n, funcs[n], base, text))
    idx = [f"import Lua.Vm.Code.FixedImage_{ident(n)[0].upper() + ident(n)[1:]}" for n in names]
    idx += ["", "/-! GENERATED by scripts/gen_lua_code.py -- do not edit.", "",
            "Code pins for `luaV_execute` and its F1 callees, each derived from",
            "`Lua/Vm/Image.lean` (`textLoaded_<F>Loaded`):", ""]
    idx += [f"* `{n}` ({len(funcs[n])} instructions)" for n in names]
    idx += ["-/", ""]
    files["../Code.lean"] = "\n".join(idx)
    return {(OUT / p).resolve(): t for p, t in files.items()}


def main():
    if "--list" in sys.argv:
        funcs = disasm()
        for n in functions():
            print(n, len(funcs.get(n) or []))
        return
    files = render()
    if "--check" in sys.argv:
        stale = [p for p, t in files.items() if not p.exists() or p.read_text() != t]
        stale += [p for p in OUT.rglob("*.lean") if p.resolve() not in files]
        if stale:
            print("code pins: DRIFT", *[str(p.relative_to(ROOT)) for p in stale[:10]])
            sys.exit(1)
        print(f"code pins: ok ({len(files)} files)")
        return
    for p, t in files.items():
        p.parent.mkdir(parents=True, exist_ok=True)
        if not p.exists() or p.read_text() != t:
            p.write_text(t)
    for p in OUT.rglob("*.lean"):
        if p.resolve() not in files:
            p.unlink()
    print(f"wrote {len(files)} files")


if __name__ == "__main__":
    main()

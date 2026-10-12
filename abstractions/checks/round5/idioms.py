#!/usr/bin/env python3
"""Round 5 census: two inlined call patterns of `luaV_execute`'s float paths.

1. The comparison idioms: the instruction after each `jal __{le,ge,eq}df2`
   (how the 4-valued answer becomes a branch or a 0/1), with their counts.
   `Kit/FltVal.lean` has one hand lemma per idiom met so far (5).
2. The inlined `luaV_flttointeger` chains: from each `jal floor`, the calls
   and branches up to `__fixdfdi` (layout variants of one C function).

    python3 abstractions/checks/round5/idioms.py > abstractions/checks/round5/idioms.out
"""
import collections
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OBJDUMP = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump"
ELF = ROOT / "c/lua-riscv-htif.elf"


def main():
    out = subprocess.run([str(OBJDUMP), "-d", "--disassemble=luaV_execute", str(ELF)],
                         capture_output=True, text=True).stdout
    L = [line.split("\t", 2)[2].replace("\t", " ").strip() for line in out.splitlines()
         if re.match(r"\s+[0-9a-f]+:\s", line) and line.count("\t") >= 2]
    c = collections.Counter()
    for i, l in enumerate(L):
        m = re.match(r"jal\s+\S+ <(__(?:le|ge|eq)df2)>", l)
        if not m:
            continue
        nxt = L[i + 1].split()
        mn, ops = nxt[0], (nxt[1] if len(nxt) > 1 else "")
        if mn.startswith("b"):
            key = f"{mn} (branch)"
        elif mn == "not":
            nx2 = L[i + 2].split()
            key = f"not; {nx2[0]} {nx2[1].split(',')[-1]}"
        elif mn in ("slti", "sltiu", "srli"):
            key = f"{mn} {ops.split(',')[-1]}"
        else:
            key = mn
        c[(m.group(1), key)] += 1
    print("comparison idioms (routine, idiom): sites")
    for k, v in sorted(c.items()):
        print(f"  {v:3d} {k[0]:8s} {k[1]}")
    print(f"  {len(c)} idioms, {sum(c.values())} sites")
    sites = [i for i, l in enumerate(L) if re.match(r"jal\s+\S+ <floor>", l)]
    ch = collections.Counter()
    for i in sites:
        seq = []
        for l in L[i:i + 40]:
            mn = l.split()[0]
            if mn == "jal":
                seq.append(re.search(r"<([^>+]+)", l).group(1))
            elif mn.startswith("b") or mn == "j":
                seq.append(mn)
            if "__fixdfdi" in seq:
                break
        ch[" ".join(seq[:12])] += 1
    print(f"\ninlined flttointeger chains from `jal floor`: {len(sites)} sites")
    for k, v in ch.most_common():
        print(f"  {v:3d} {k}")


if __name__ == "__main__":
    main()

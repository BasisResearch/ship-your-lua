#!/usr/bin/env python3
"""Round 5, law L5-stage on the ELF: how often each soft-fp stage macro is
inlined in each libgcc routine the Lua ELF links.

Stages (libgcc `soft-fp/op-common.h`, `op-1.h`, `double.h`, RV64 `_FP_W_TYPE`
= 64 bits, `_FP_WORKBITS` = 3), recognised as instruction idioms with
registers abstracted:

* `round`  `_FP_ROUND_NEAREST`: `andi x,y,7` then `andi x,y,15` within 6 instructions (then `+4`
           unless the low nibble is 4);
* `sticky` `_FP_FRAC_SRS` by a variable count: `sll`/`snez`/`srl`/`or` within 6 instructions;
* `clz`    `__FP_CLZ` (a `jal __clzdi2`);
* `pack`   `_FP_PACK_RAW`: `slli x,e,52` … `slli y,s,63` … `or`;
* `cls`    `_FP_UNPACK_RAW`/semiraw class tests on the exponent: `li x,2047` or `andi x,y,2046`
           compares (exponent all ones / zero / normal).

    python3 abstractions/checks/round5/stage_sites.py > abstractions/checks/round5/stage_sites.out
"""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
OBJDUMP = Path.home() / "toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf-objdump"
ELF = ROOT / "c/lua-riscv-htif.elf"
FNS = ["__adddf3", "__subdf3", "__muldf3", "__divdf3", "__floatsidf", "__floatdidf", "__fixdfdi",
       "__eqdf2", "__ledf2", "__gedf2"]


def insns(fn):
    out = subprocess.run([str(OBJDUMP), "-d", f"--disassemble={fn}", str(ELF)],
                         capture_output=True, text=True).stdout
    rows = []
    for line in out.splitlines():
        m = re.match(r"\s*([0-9a-f]+):\s+[0-9a-f]+\s+(\S+)\s*(.*)", line)
        if m:
            rows.append((int(m.group(1), 16), m.group(2), m.group(3)))
    return rows


def count(rows):
    c = {"insns": len(rows), "round": 0, "sticky": 0, "clz": 0, "pack": 0, "cls": 0}
    for i, (_, mn, ops) in enumerate(rows):
        w = rows[i:i + 6]
        mns = [x[1] for x in w]
        if mn == "andi" and ops.endswith(",7") and any(
                x[1] == "andi" and x[2].endswith(",15") for x in w[1:]):
            c["round"] += 1
        if mn == "sll" and "snez" in mns and "srl" in mns and "or" in mns:
            c["sticky"] += 1
        if mn == "jal" and "__clzdi2" in ops:
            c["clz"] += 1
        if mn == "slli" and ops.endswith(",0x34") and any(
                x[1] == "slli" and x[2].endswith(",0x3f") for x in rows[i:i + 5]):
            c["pack"] += 1
        if (mn == "li" and ops.endswith(",2047")) or (mn == "andi" and ops.endswith(",2046")):
            c["cls"] += 1
    return c


def main():
    print("routine\tinsns\tround\tsticky\tclz\tpack\tcls")
    for fn in FNS:
        c = count(insns(fn))
        print(f"{fn}\t{c['insns']}\t{c['round']}\t{c['sticky']}\t{c['clz']}\t{c['pack']}\t{c['cls']}")


if __name__ == "__main__":
    main()

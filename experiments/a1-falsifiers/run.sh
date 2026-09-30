#!/bin/bash
# Re-run all three falsifiers (read-only over the repo; ELFs are built into
# $OUT, default a fresh temp dir).  Needs python3, gawk, the xPack toolchain,
# host ./c/luac and the lean_riscv_emulator.  No lake.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../.." && pwd)
OUT=${OUT:-$(mktemp -d)}; mkdir -p "$OUT/elf" "$OUT/probe"
cd "$HERE"
python3 selftest.py
python3 f1_orbits.py | tee f1_orbits.out
python3 f2_exits.py > f2_exits.out
# F3 inputs: every difftest chunk + the four validation chunks
for f in "$REPO"/c/tests/difftest/*.lua "$REPO"/c/tests/{while,f1_ops,f1b_bits,f4_strlite}.lua; do
  n=$(basename "$f" .lua)
  make -s -C "$REPO/c" riscv-htif CHUNK_SRC="$f" CHUNK="$OUT/elf/$n.luac" ELF="$OUT/elf/$n.elf" >/dev/null
done
TMPDIR=$OUT ./f3_stack.sh "$OUT"/elf/*.elf | sort > f3_stack.out
# F3 probe: N locals then print(aN)  (an F1 program; finds the growth threshold)
for N in 8 12 14 15 16 17 18 20 24 30 40; do
  python3 -c "N=$N; print('local ' + ', '.join(f'a{i}' for i in range(1,N+1)) + ' = ' + ', '.join(map(str, range(1,N+1)))); print(f'print(a{N})')" > "$OUT/probe/locals$N.lua"
  make -s -C "$REPO/c" riscv-htif CHUNK_SRC="$OUT/probe/locals$N.lua" CHUNK="$OUT/probe/locals$N.luac" ELF="$OUT/probe/locals$N.elf" >/dev/null
done
TMPDIR=$OUT ./f3_stack.sh $(ls "$OUT"/probe/*.elf | sort -V) | sort -V > f3_probe.out

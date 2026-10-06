#!/bin/bash
# Differential tests of Lua/Num/Decimal.lean (`tostringbuff`/`%.14g`,
# `str2number`/`l_str2int`/`l_str2d`) against the bare-metal ELF on the Sail
# Lean emulator. Vectors: gen.py (split into fmt_*.lua/parse_*.lua to fit the
# ELF's 64 KiB chunk region). The Lean side: scripts/test_decimal.lean.
# The host `lua` (glibc) is reported for information only: it differs on the
# NaN sign and on newlib gethex's rounding.
# A program that exceeds TIMEOUT seconds on Sail is reported as TIMEOUT.
#   EMU=path/to/lean_riscv_emulator  JOBS=4  TIMEOUT=3600  c/tests/float/run.sh
set -u
cd "$(dirname "$0")/../.."          # c/
EMU=${EMU:-$(pwd)/../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
JOBS=${JOBS:-4}
TIMEOUT=${TIMEOUT:-3600}
OUT=build/float
mkdir -p $OUT
python3 tests/float/gen.py
make -s host >/dev/null
progs=$(cd tests/float && ls fmt_*.lua parse_*.lua | sed 's/\.lua$//' | sort -V)
for n in $progs; do
  ./luac -s -o $OUT/$n.luac tests/float/$n.lua
  ./lua $OUT/$n.luac > $OUT/$n.host 2>&1
  make -s riscv-htif CHUNK_SRC=tests/float/$n.lua CHUNK=$OUT/$n.luac ELF=$OUT/$n.elf >/dev/null 2>&1 || { echo "$n BUILD-FAIL"; exit 1; }
done
run1() {
  /usr/bin/time -f "%e s" -o $OUT/$1.time timeout $TIMEOUT $EMU $OUT/$1.elf 2>/dev/null \
    | grep -vE '^(TODO: cancel_reservation|PC = 0x|htif_tohost = 0x|SUCCESS$|FAILURE|lua: )' > $OUT/$1.emu
}
export -f run1; export OUT EMU TIMEOUT
echo $progs | tr ' ' '\n' | xargs -P $JOBS -I{} bash -c 'run1 {}'
(cd .. && lake env lean scripts/test_decimal.lean)
fail=0
for k in fmt parse; do
  cat $(for n in $progs; do case $n in ${k}_*) echo $OUT/$n.emu;; esac; done) > $OUT/$k.emu
  cat $(for n in $progs; do case $n in ${k}_*) echo $OUT/$n.host;; esac; done) > $OUT/$k.host
  total=$(wc -l < $OUT/$k.lean)
  if cmp -s $OUT/$k.lean $OUT/$k.emu; then echo "$k: PASS ($total vectors, Lean = ELF)"
  else echo "$k: FAIL (Lean vs ELF)"; diff $OUT/$k.lean $OUT/$k.emu | head -20; fail=1; fi
  hd=$(diff $OUT/$k.emu $OUT/$k.host | grep -c '^<')
  echo "$k: host lua differs from the ELF on $hd of $total lines"
done
for n in $progs; do
  grep -q "exited with non-zero status 124" $OUT/$n.time && echo "$n: TIMEOUT after ${TIMEOUT} s"
  echo "$n: Sail $(tail -1 $OUT/$n.time)"
done
exit $fail

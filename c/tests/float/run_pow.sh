#!/bin/bash
# Differential test of Lua/Num/Pow.lean (`Lua.Num.numpow`: `luai_numpow` over
# newlib's fdlibm `pow`) against the bare-metal ELF on the Sail Lean emulator.
# Vectors: gen_pow.py (pow.vec, split into pow_*.lua). The Lean side:
# scripts/test_pow.lean (writes build/float/pow.lean). Lines are the bits of
# `x ^ y` as signed integers, compared bit for bit (NaN sign included).
# pow_snan.lua (signalling-NaN operands, outside Float.Model) is run and
# printed for information. The host `lua` (glibc pow) is reported for
# information only.
#   EMU=path/to/lean_riscv_emulator  JOBS=4  TIMEOUT=3600  LEAN='lake env lean'  c/tests/float/run_pow.sh
set -u
cd "$(dirname "$0")/../.."          # c/
EMU=${EMU:-$(pwd)/../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
JOBS=${JOBS:-4}
TIMEOUT=${TIMEOUT:-3600}
LEAN=${LEAN:-lake env lean}
OUT=build/float
mkdir -p $OUT
python3 tests/float/gen_pow.py
make -s host >/dev/null
progs="$(cd tests/float && ls pow_[0-9]*.lua | sed 's/\.lua$//' | sort -V) pow_snan"
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
(cd .. && $LEAN scripts/test_pow.lean)
main=$(echo $progs | tr ' ' '\n' | grep -v snan)
cat $(for n in $main; do echo $OUT/$n.emu; done) > $OUT/pow.emu
cat $(for n in $main; do echo $OUT/$n.host; done) > $OUT/pow.host
fail=0
total=$(wc -l < $OUT/pow.lean)
if cmp -s $OUT/pow.lean $OUT/pow.emu; then echo "pow: PASS ($total vectors, Lean = ELF)"
else echo "pow: FAIL (Lean vs ELF)"; diff $OUT/pow.lean $OUT/pow.emu | head -20; fail=1; fi
hd=$(diff $OUT/pow.emu $OUT/pow.host | grep -c '^<')
echo "pow: host lua differs from the ELF on $hd of $total lines"
echo "snan (ELF, information): $(tr '\n' ' ' < $OUT/pow_snan.emu)"
echo "snan (Lean, operands canonicalised): $(tr '\n' ' ' < $OUT/snan.lean)"
for n in $progs; do
  grep -q "exited with non-zero status 124" $OUT/$n.time && echo "$n: TIMEOUT after ${TIMEOUT} s"
  echo "$n: Sail $(tail -1 $OUT/$n.time)"
done
exit $fail

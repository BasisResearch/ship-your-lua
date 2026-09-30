#!/bin/bash
# Differential test: host `lua` (same vendored source, same baremetal.h) vs
# the bare-metal ELF on the Sail Lean emulator. Both run the SAME stripped
# luac chunk; the host runs with the collector stopped, like the ELF, in an
# empty environment with TZ=UTC0 (the ELF's newlib has no environment, so
# its local time is UTC) and in a scratch directory (io/os difftests create
# and remove files there; the ELF's are in htif.c's in-image file system).
# Compares stdout and the exit status (0 vs nonzero). Reports Sail steps.
#   EMU=path/to/lean_riscv_emulator  JOBS=8  tests/difftest.sh [files...]
set -u
cd "$(dirname "$0")/.."
EMU=${EMU:-$(pwd)/../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
JOBS=${JOBS:-8}
NM=${NM:-$(ls -d $HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin | head -1)/riscv-none-elf-nm}
OUT=build/difftest
mkdir -p $OUT
files=("$@"); [ ${#files[@]} -eq 0 ] && files=(tests/difftest/*.lua)
for f in "${files[@]}"; do
  n=$(basename $f .lua)
  make -s riscv-htif CHUNK_SRC=$f CHUNK=$OUT/$n.luac ELF=$OUT/$n.elf >/dev/null 2>&1 || { echo "$n BUILD-FAIL"; continue; }
  mkdir -p $OUT/cwd
  (cd $OUT/cwd && env -i TZ=UTC0 ../../../lua -e "collectgarbage('stop')" ../$n.luac > ../$n.host 2>/dev/null; echo $? > ../$n.host.rc)
done
run1() {
  n=$1
  pc=$($NM $OUT/$n.elf 2>/dev/null | awk '$3=="_exit"{print $1}')
  # the `sd` to tohost is _exit's 5th instruction (see src/htif.c)
  printf '0x%x\n' $(( 0x$pc + 16 )) > $OUT/$n.pcs
  $EMU $OUT/$n.elf --trace-pcs $OUT/$n.pcs > $OUT/$n.raw 2> $OUT/$n.trace; echo $? > $OUT/$n.emu.rc
  # stderr shares the HTIF console: main.c's "lua: <msg>" line is dropped
  # here (the host prints it to stderr, which is not compared)
  grep -vE '^(TODO: cancel_reservation|PC = 0x|htif_tohost = 0x|SUCCESS$|FAILURE|lua: )' $OUT/$n.raw > $OUT/$n.emu
}
export -f run1; export OUT EMU NM
[ -n "${NORUN:-}" ] || for f in "${files[@]}"; do basename $f .lua; done | xargs -P $JOBS -I{} bash -c 'run1 {}'
pass=0; fail=0
printf '%-16s %-6s %-8s %-8s %s\n' test result host-rc emu-rc sail-steps
for f in "${files[@]}"; do
  n=$(basename $f .lua)
  hr=$(cat $OUT/$n.host.rc); er=$(cat $OUT/$n.emu.rc)
  steps=$(awk -F'\t' '$1=="T"{print $2+1}' $OUT/$n.trace | tail -1)
  if cmp -s $OUT/$n.host $OUT/$n.emu && [ $(( hr == 0 )) = $(( er == 0 )) ]; then
    r=PASS; pass=$((pass+1)); else r=FAIL; fail=$((fail+1)); fi
  printf '%-16s %-6s %-8s %-8s %s\n' $n $r $hr $er "${steps:-?}"
done
echo "pass=$pass fail=$fail"
[ $fail = 0 ]

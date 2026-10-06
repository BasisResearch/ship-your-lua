#!/bin/bash
# End-to-end differential test of the bytecode semantics
# (Lua/Bytecode/Semantics.lean: floats, `δ`, `fastArith`, `forprepK`/`forloopK`,
# `Value.show`, string coercion) against the bare-metal ELF on the Sail Lean
# emulator. Programs: gen_sem.py (sem_*.lua; sem_err_*.lua raise an error after
# one line). For each program: `luac -s`, the ELF with that chunk on Sail
# (expected output), `scripts/gen_proto.py` to a `Proto`, and
# `Lua.Bytecode.run Lua.Vm.binaryHost` in `lake env lean` (Lean output; on
# `none`, `stuckRun` reports the stuck pc and instruction). Outputs are
# compared byte for byte. An error program passes when the ELF exits nonzero
# with a `lua: ` line, Lean is stuck (not out of fuel), and the output before
# the error agrees. Generated Lean files live in build/float/sem/
# (gitignored). The host `lua` is reported for information only (it differs
# from the ELF on the NaN sign and on pow).
#   EMU=path/to/lean_riscv_emulator  JOBS=4  LJOBS=2  TIMEOUT=3600  FUEL=1000000  c/tests/float/run_sem.sh [prog ...]
set -u
cd "$(dirname "$0")/../.."          # c/
EMU=${EMU:-$(pwd)/../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
JOBS=${JOBS:-4}
LJOBS=${LJOBS:-2}
TIMEOUT=${TIMEOUT:-3600}
FUEL=${FUEL:-1000000}
LEAN=${LEAN:-systemd-run --user --scope -p MemoryMax=12G -q lake env lean}
OUT=build/float/sem
mkdir -p $OUT
python3 tests/float/gen_sem.py
make -s host >/dev/null
if [ $# -gt 0 ]; then progs="$*"
else progs=$(cd tests/float && ls sem_*.lua | sed 's/\.lua$//' | sort -V); fi

# 1. chunks, ELFs, host runs, Lean files
for n in $progs; do
  ./luac -s -o $OUT/$n.luac tests/float/$n.lua || { echo "$n LUAC-FAIL"; exit 1; }
  timeout 60 ./lua $OUT/$n.luac 2>/dev/null | head -c 4000000 > $OUT/$n.host
  [ -f $OUT/$n.elf ] && [ $OUT/$n.elf -nt tests/float/$n.lua ] && [ $OUT/$n.elf -nt lua-riscv-htif.elf ] || \
    make -s riscv-htif CHUNK_SRC=tests/float/$n.lua CHUNK=$OUT/$n.luac ELF=$OUT/$n.elf >/dev/null 2>&1 \
    || { echo "$n BUILD-FAIL"; exit 1; }
  id=$(echo $n | tr -c 'a-zA-Z0-9\n' '_')
  (cd .. && python3 scripts/gen_proto.py c/$OUT/$n.luac --name $id -o c/$OUT/P_$id.lean --luac c/luac >/dev/null)
  {
    echo 'import Lua.Bytecode.Exec'; echo 'import Lua.Vm.Host'; echo 'import Lua.Fragment'
    echo 'import Lua.StuckCases'
    grep -v '^import' $OUT/P_$id.lean
    cat <<EOF
open Lua.Bytecode Lua.Programs in
#eval show IO Unit from do
  let p := $id
  let dir := "c/$OUT/"
  let sup := decide (Supported p)
  match run Lua.Vm.binaryHost p $FUEL State.init with
  | some s =>
    IO.FS.writeFile (dir ++ "$n.lean") s.out
    IO.FS.writeFile (dir ++ "$n.status") s!"OK supported={sup}\n"
  | none =>
    match stuckRun Lua.Vm.binaryHost p $FUEL State.init with
    | some s =>
      IO.FS.writeFile (dir ++ "$n.lean") s.out
      let w := p.fetch s.pc
      IO.FS.writeFile (dir ++ "$n.status")
        s!"STUCK supported={sup} pc={s.pc} op={repr (w.bind (·.op?))} word={repr w}\n"
    | none =>
      IO.FS.writeFile (dir ++ "$n.lean") ""
      IO.FS.writeFile (dir ++ "$n.status") s!"FUEL supported={sup}\n"
EOF
  } > $OUT/T_$id.lean
done

# 2. Sail, in parallel; the Lean side, in parallel (memory-capped)
run1() {
  /usr/bin/time -f "%e s" -o $OUT/$1.time timeout $TIMEOUT $EMU $OUT/$1.elf 2>/dev/null | head -c 4000000 > $OUT/$1.raw
  echo ${PIPESTATUS[0]} > $OUT/$1.rc
  grep -vE '^(TODO: cancel_reservation|PC = 0x|htif_tohost = 0x|SUCCESS$|FAILURE|lua: )' $OUT/$1.raw > $OUT/$1.emu
}
lean1() {
  id=$(echo $1 | tr -c 'a-zA-Z0-9\n' '_')
  while [ "$(grep 'Mem:' ~/syi-mem.log 2>/dev/null | tail -1 | awk '{print $NF}')" != "" ] && \
        [ "$(grep 'Mem:' ~/syi-mem.log | tail -1 | awk '{print $NF}')" -lt 25 ]; do sleep 30; done
  (cd .. && /usr/bin/time -f "%e s" -o c/$OUT/$1.ltime $LEAN c/$OUT/T_$id.lean > c/$OUT/$1.leanlog 2>&1)
}
export -f run1 lean1; export OUT EMU TIMEOUT LEAN
start=$(date +%s)
echo $progs | tr ' ' '\n' | xargs -P $JOBS -I{} bash -c 'run1 {}' &
sail=$!
echo $progs | tr ' ' '\n' | xargs -P $LJOBS -I{} bash -c 'lean1 {}'
wait $sail
end=$(date +%s)

# 3. compare
fail=0; lines=0; nprog=0; sailsum=0
for n in $progs; do
  nprog=$((nprog + 1))
  st=$(cat $OUT/$n.status 2>/dev/null || echo "NO-STATUS $(head -c 300 $OUT/$n.leanlog)")
  rc=$(cat $OUT/$n.rc)
  t=$(tail -1 $OUT/$n.time | cut -d' ' -f1); sailsum=$(echo "$sailsum + $t" | bc)
  hd=$(diff $OUT/$n.emu $OUT/$n.host | grep -c '^<')
  case $n in
    sem_err_*)
      msg=$(grep '^lua: ' $OUT/$n.raw | head -1)
      if [ "$rc" != 0 ] && [ -n "$msg" ] && [[ $st == STUCK* ]] && cmp -s $OUT/$n.lean $OUT/$n.emu; then
        echo "$n: PASS (ELF rc=$rc '$msg'; Lean $st)"
      else
        echo "$n: FAIL (ELF rc=$rc '$msg'; Lean $st)"; diff $OUT/$n.lean $OUT/$n.emu | head -5; fail=1
      fi ;;
    *)
      k=$(wc -l < $OUT/$n.emu); lines=$((lines + k))
      if [ "$rc" = 0 ] && [[ $st == OK* ]] && cmp -s $OUT/$n.lean $OUT/$n.emu; then
        echo "$n: PASS ($k lines; host differs on $hd; Sail ${t}s)"
      else
        echo "$n: FAIL (ELF rc=$rc; Lean $st; $k ELF lines; host differs on $hd)"
        diff $OUT/$n.lean $OUT/$n.emu | head -20; fail=1
      fi ;;
  esac
done
echo "programs: $nprog; lines compared (non-error programs): $lines; Sail CPU ${sailsum}s, wall $((end - start))s"
exit $fail

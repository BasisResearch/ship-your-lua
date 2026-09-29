#!/usr/bin/env bash
# check.sh — the gate for ship-your-lua.
#
#   scripts/check.sh [--static-only]
#
# (1) generator drift: every generated Lean file matches its inputs
#     (opcodes <- lopcodes.h, layout <- the cross compiler + ELF symbols,
#     image <- the ELF, programs <- the committed .luac chunks);
# (2) the committed ELF's sha256 matches c/lua-riscv-htif.elf.sha256, and it
#     contains no `ecall`;
# (3) forbidden tokens outside comments in Lua/, Vsa/, VsaIris/: sorry,
#     axiom declarations, native_decide, bv_decide, ofReduceBool,
#     trustCompiler, and raised maxHeartbeats/maxRecDepth in Lua/;
# (3b) proof discipline (scripts/check_discipline.py, scripts/discipline_rules.tsv);
# (4) the copied machine layer imports nothing WHILE-specific
#     (experiments/port/port_census.py --copyset; needs a syi checkout,
#     skipped if absent);
# (5) lake build Lua Vsa VsaIris   (skipped with --static-only);
# (6) #print axioms of the key theorems ⊆ {propext, Classical.choice, Quot.sound}.
set -uo pipefail
cd "$(dirname "$0")/.." || exit 2
fail() { echo "check: FAIL: $*"; exit 1; }

echo "== (1) generator drift"
# gen_proto.py embeds the host luac's listing: build lua/luac if absent
[ -x c/luac ] || make -s -C c host >/dev/null || fail "host luac build"
python3 scripts/gen_opcodes.py --check || fail "opcodes drift"
python3 scripts/gen_lua_layout.py --check || fail "layout drift"
python3 scripts/gen_lua_image.py --check || fail "image drift"
while read -r chunk name out; do
  python3 scripts/gen_proto.py "$chunk" --name "$name" -o "$out" --check || fail "$out drift"
done <<'LIST'
c/tests/while.luac whileProto Lua/Programs/While.lean
c/tests/print_print.luac printPrintProto Lua/Programs/PrintPrint.lean
c/tests/f1_ops.luac f1OpsProto Lua/Programs/F1Ops.lean
LIST

echo "== (2) ELF hash"
(cd c && sha256sum -c lua-riscv-htif.elf.sha256) || fail "ELF hash"
# no `ecall`: on the bare Sail machine it traps with no handler and hangs
# (newlib's libgloss _gettimeofday/_times use it; htif.c must provide them)
OBJDUMP=${OBJDUMP:-$(ls -d $HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-*/bin | head -1)/riscv-none-elf-objdump}
n=$("$OBJDUMP" -d c/lua-riscv-htif.elf | grep -cw ecall)
[ "$n" = 0 ] || fail "$n ecall instruction(s) in the ELF"
echo "no ecall"

echo "== (3) forbidden tokens"
python3 - <<'PY' || fail "forbidden tokens"
import os, re, sys
bad = []
pat = re.compile(r"\bsorry\b|^\s*axiom\b|native_decide|bv_decide|ofReduceBool|trustCompiler")
lim = re.compile(r"maxHeartbeats|maxRecDepth")
def strip(src):
    src = re.sub(r"/-.*?-/", "", src, flags=re.S)
    src = re.sub(r"--[^\n]*", "", src)
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', src)
for d in ["Lua", "Vsa", "VsaIris"]:
    for dp, _, fs in os.walk(d):
        for f in fs:
            if not f.endswith(".lean"): continue
            p = os.path.join(dp, f); s = strip(open(p).read())
            for i, line in enumerate(s.splitlines(), 1):
                if pat.search(line) or (d == "Lua" and lim.search(line)):
                    bad.append(f"{p}:{i}: {line.strip()}")
for b in bad: print(b)
sys.exit(1 if bad else 0)
PY
echo "ok"

echo "== (3b) proof discipline"
python3 scripts/check_discipline.py || fail "discipline"

echo "== (4) copied layer is WHILE-free"
if [ -d "${SYI:-$HOME/Documents/code/syi}" ]; then
  python3 experiments/port/port_census.py --syi "${SYI:-$HOME/Documents/code/syi}" --copyset || fail "taint"
else echo "skipped (no syi checkout)"; fi

[ "${1:-}" = "--static-only" ] && { echo "check: static stages OK (build and axioms not run)"; exit 0; }

echo "== (5) build"
lake build Lua Vsa VsaIris 2>&1 | tail -1 | grep -q "Build completed successfully" || fail "lake build"
echo "ok"

echo "== (6) axioms"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Lua
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.DeriveCase
import VsaIris.Vsa.AllocStepsTohost
import VsaIris.Vsa.AllocSteps.Part01
#print axioms Lua.vm_refinement_of_sim
#print axioms Lua.compile_refinement_of_tv
#print axioms Lua.endToEnd_of_layers
#print axioms Lua.endToEnd_of_obligations
#print axioms Lua.Refine.refinement
#print axioms Lua.Bytecode.step?_sound
#print axioms Lua.Bytecode.bcSem_of_run
#print axioms Lua.Bytecode.ledger_exact
#print axioms Lua.Programs.while_bcSem
#print axioms Lua.Programs.f1Ops_bcSem
#print axioms Lua.Programs.printPrint_bcSem
#print axioms Lua.Programs.while_supported
#print axioms Lua.Programs.f1Ops_supported
#print axioms Lua.Programs.readsStale_unsupported
#print axioms Lua.Vm.tohostAddr_eq_symTohost
#print axioms Vsa.Sim.segToTripleFramed
#print axioms Vsa.Sim.segRowFramed
#print axioms Vsa.Sim.bridgeOfSeg
#print axioms Vsa.Sim.jalStep_of_obs
#print axioms Vsa.Sim.bridgeOfSegFull
#print axioms Vsa.Sim.abiFrame_of_wrChain
#print axioms Vsa.Sim.memFrame_of_chain
#print axioms VsaIris.Sym.swp_seg
#print axioms VsaIris.Sym.swp_jal
#print axioms VsaIris.Sym.swp_step
#print axioms VsaIris.Sym.st_80004908
#print axioms VsaIris.Sym.allocSteps_whileGlobals_not_stOK
LEAN
lake env lean "$tmp/Axioms.lean" > "$tmp/out.txt" 2>&1 || { cat "$tmp/out.txt"; fail "axioms file"; }
cat "$tmp/out.txt"
n=$(grep -cE "depends on axioms|does not depend on any axioms" "$tmp/out.txt")
[ "$n" = 27 ] || fail "expected 27 axiom reports, got $n"
if grep "depends on axioms" "$tmp/out.txt" | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/ //g' \
   | grep -vxE 'propext|Classical.choice|Quot.sound' | grep -q .; then fail "non-standard axiom"; fi
echo "check: all stages OK"

#!/usr/bin/env bash
# check.sh — the gate for ship-your-lua.
#
#   scripts/check.sh [--static-only]
#
# (1) generator drift: every generated Lean file matches its inputs
#     (opcodes <- lopcodes.h, layout <- the cross compiler + ELF symbols,
#     image <- the ELF, programs <- the committed .luac chunks, code pins
#     <- the ELF + Lua/Vm/Image.lean, decodeW coverage check <- the ELF +
#     its committed AST dump, boot traces <- the ELF + the emulator);
# (2) the committed ELF's sha256 matches c/lua-riscv-htif.elf.sha256, and it
#     contains no `ecall`;
# (3) forbidden tokens outside comments in Lua/, Vsa/, VsaIris/, tcb/: sorry,
#     axiom declarations, native_decide, bv_decide, ofReduceBool,
#     trustCompiler, and raised maxHeartbeats/maxRecDepth in Lua/;
# (3b) proof discipline (scripts/check_discipline.py, scripts/discipline_rules.tsv);
# (3c) the abstraction gate (abstractions/gate.py, abstractions/clusters.tsv);
# (4) the copied machine layer imports nothing WHILE-specific
#     (experiments/port/port_census.py --copyset; needs a syi checkout,
#     skipped if absent);
# (5) lake build Lua Vsa VsaIris   (skipped with --static-only);
# (5b) the OS-spec trace validation, quick subset (skipped with --static-only);
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
python3 scripts/gen_lua_code.py --check || fail "code pins drift"
python3 scripts/gen_lua_decode_check.py --check || fail "decode check drift"
python3 scripts/gen_lua_arms.py --check || fail "F1 arm segments drift"
python3 scripts/gen_lua_arm.py --check || fail "A1 arm simulation lemmas drift"
python3 scripts/syi/gen_alloc_steps.py --check || fail "allocator step table drift"
python3 scripts/draft_f1_arms.py | tail -1 | grep -q "; 0 steps need" || fail "F1 arm steps without a site class"
# boot traces to luaV_execute (re-traced on the emulator, ~25 s): the runtime
# constants, the loaded data bytes and the per-program entry data; also
# evaluates every VmEntryData/luaRuntimeReady field at the traced entries
python3 scripts/gen_lua_boot_witness.py --check || fail "boot witness drift"
while read -r chunk name out; do
  python3 scripts/gen_proto.py "$chunk" --name "$name" -o "$out" --check || fail "$out drift"
done <<'LIST'
c/tests/while.luac whileProto Lua/Programs/While.lean
c/tests/print_print.luac printPrintProto Lua/Programs/PrintPrint.lean
c/tests/f1_ops.luac f1OpsProto Lua/Programs/F1Ops.lean
c/tests/f1b_bits.luac f1bProto Lua/Programs/F1bBits.lean
c/tests/f1_src.luac f1SrcProto Lua/Programs/F1Src.lean
c/tests/f4_strlite.luac f4StrliteProto Lua/Programs/F4Strlite.lean
LIST
# source ASTs (Layer B translation validation) <- the .lua files, parsed by
# gen_ast.py (all of Lua 5.4); the committed .luac chunks <- the host luac on
# the same files; the parser round-trips every .lua file in the repo through
# the host luac (identical `luac -l -l` listings)
python3 scripts/gen_ast.py --roundtrip $(find c -name '*.lua' | sort) > /dev/null \
  || fail "gen_ast.py round-trip against luac"
while read -r src name out; do
  python3 scripts/gen_ast.py "$src" --name "$name" -o "$out" --check || fail "$out drift"
done <<'LIST'
c/tests/f1_ops.lua f1OpsAst Lua/Programs/F1OpsAst.lean
c/tests/f1_src.lua f1SrcAst Lua/Programs/F1SrcAst.lean
c/tests/while.lua whileAst Lua/Programs/WhileAst.lean
c/tests/f1b_bits.lua f1bAst Lua/Programs/F1bBitsAst.lean
c/tests/f4_strlite.lua f4StrliteAst Lua/Programs/F4StrliteAst.lean
LIST
for f in f1_ops f1_src while f1b_bits f4_strlite; do
  ./c/luac -s -o - "c/tests/$f.lua" | cmp -s - "c/tests/$f.luac" || fail "c/tests/$f.luac is not luac -s of $f.lua"
done

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
for d in ["Lua", "Vsa", "VsaIris", "tcb"]:
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

echo "== (3c) abstraction gate"
# a cluster of 8+ hand proofs whose per-case cost is not falling by a
# third fails here with "run /abstraction-discovery" (abstractions/gate.py)
python3 abstractions/gate.py || fail "abstraction gate (run /abstraction-discovery; see abstractions/)"

echo "== (4) copied layer is WHILE-free"
if [ -d "${SYI:-$HOME/Documents/code/syi}" ]; then
  python3 experiments/port/port_census.py --syi "${SYI:-$HOME/Documents/code/syi}" --copyset || fail "taint"
else echo "skipped (no syi checkout)"; fi

[ "${1:-}" = "--static-only" ] && { echo "check: static stages OK (build and axioms not run)"; exit 0; }

echo "== (5) build"
lake build Lua Vsa VsaIris 2>&1 | tail -1 | grep -q "Build completed successfully" || fail "lake build"
echo "ok"

echo "== (5b) OS-spec traces (tcb/, experiments/os/run.sh --quick)"
experiments/os/run.sh --quick > /dev/null 2>&1 || fail "OS trace run"
grep -q " rejected 0 " experiments/os/out-quick/linux.summary || fail "Linux traces rejected by TCB.Os.next"
cat experiments/os/out-quick/linux.summary
# htif.c's in-image file system: no trace rejected, and its verdicts are
# pinned (a change means experiments/os/RESULTS.md is stale)
grep -q "accepted 264 rejected 0 special 4 unsupported 61" experiments/os/out-quick/htif.summary \
  || fail "htif.c generated-script verdicts changed (update experiments/os/RESULTS.md)"
cat experiments/os/out-quick/htif.summary
grep -q "accepted 25 rejected 0 special 1 " experiments/os/out-quick/console-htif.summary \
  || fail "htif.c console verdicts changed (update experiments/os/RESULTS.md)"
cat experiments/os/out-quick/console-htif.summary

echo "== (6) axioms"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Lua
import Vsa.Sim.SegToTripleFramed
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.DeriveCase
import VsaIris.Vsa.AllocSteps
import VsaIris.Vsa.AllocSltu
import VsaIris.Vsa.SymRunO
import VsaIris.Vsa.SymJalr
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
#print axioms Vsa.Sim.decodeW
#print axioms Lua.Vm.Code.textLoaded_LuaV_executeLoaded
#print axioms Lua.Vm.Code.textLoaded_LuaD_precallLoaded
#print axioms Lua.Vm.Code.textLoaded_LuaB_printLoaded
#print axioms Lua.Vm.Sim.dispatch
#print axioms Lua.Vm.Sim.vmRel_entry
#print axioms Lua.Vm.Arms.seg_8001bf68_8001bfb0
#print axioms Lua.Vm.Arms.seg_8001bfb0_8001bfe4
#print axioms Lua.Vm.Sim.sim_MOVE
#print axioms Lua.Vm.Sim.sim_LOADI
#print axioms Lua.Vm.Sim.sim_JMP
#print axioms Lua.Vm.Sim.sim_ADD
#print axioms Lua.Vm.Sim.Kit.sim_ADD
#print axioms Lua.Vm.Sim.Kit.sim_MUL
#print axioms Lua.Vm.Sim.Kit.sim_MOD
#print axioms Lua.Vm.Sim.Kit.eq_short
#print axioms Lua.Vm.Sim.Kit.sim_EQ_of_long
#print axioms Lua.Vm.Sim.Kit.muldi3_sum
#print axioms Lua.Vm.Sim.Kit.udivdi3_sum
#print axioms Lua.Vm.Sim.Kit.moddi3_sum
#print axioms Lua.Vm.Sim.Kit.equalobj_sum
#print axioms Lua.Vm.Sim.Kit.imodC_eq
#print axioms Lua.Vm.Sim.Kit.sim_LOADNIL
#print axioms Lua.Vm.Sim.Kit.loadnil_loop
#print axioms Lua.Vm.Sim.Kit.lt_int
#print axioms Lua.Vm.Sim.Kit.lt_stuck
#print axioms Lua.Vm.Sim.Kit.sim_LT_of_str
#print axioms Lua.Vm.Sim.Kit.le_int
#print axioms Lua.Vm.Sim.Kit.le_stuck
#print axioms Lua.Vm.Sim.Kit.sim_LE_of_str
#print axioms Lua.Vm.Sim.Kit.eqk_short
#print axioms Lua.Vm.Sim.Kit.sim_EQK_of_long
#print axioms Lua.Vm.Sim.Kit.toint_sum
#print axioms Lua.Vm.Sim.sim_order
#print axioms Lua.Vm.Sim.Core.bleachF
#print axioms Lua.Vm.Sim.Core.stack_of
#print axioms Lua.Vm.Sim.sim_EQI
#print axioms Lua.Vm.Sim.sim_FORLOOP
#print axioms Lua.Vm.Sim.sim_SUB
#print axioms Lua.Vm.Sim.sim_ADDI
#print axioms Lua.Vm.Sim.sim_ADDK
#print axioms Lua.Vm.Sim.sim_SUBK
#print axioms Lua.Vm.Sim.sim_BAND
#print axioms Lua.Vm.Sim.sim_BOR
#print axioms Lua.Vm.Sim.sim_BXOR
#print axioms Lua.Vm.Sim.sim_LTI
#print axioms Lua.Vm.Sim.sim_GTI
#print axioms Lua.Vm.Sim.sim_LEI
#print axioms Lua.Vm.Sim.sim_GEI
#print axioms Lua.Vm.Sim.sim_LOADTRUE
#print axioms Lua.Vm.Sim.sim_LOADFALSE
#print axioms Lua.Vm.Sim.sim_LFALSESKIP
#print axioms Lua.Vm.Sim.sim_LOADK
#print axioms Lua.Vm.Sim.sim_BNOT
#print axioms Lua.Vm.Sim.sim_NOT
#print axioms Lua.Vm.Sim.sim_TEST
#print axioms Lua.Vm.Sim.sim_TESTSET
#print axioms Lua.Vm.Sim.Core.update
#print axioms Lua.Vm.Sim.Ranges.of_regions
#print axioms Lua.Vm.TStringRepr.inj
#print axioms Lua.Vm.ProtoRepr.kArr
#print axioms Lua.Vm.Sim.exists_intern
#print axioms Lua.Vm.Sim.Core.forloop
#print axioms Lua.Vm.Sim.Core.write
#print axioms Lua.Vm.Sim.Core.jump
#print axioms Lua.Vm.RegsOk.of_step
#print axioms Lua.Vm.RegsOk.alu
#print axioms Lua.Vm.RegsOk.store
#print axioms Lua.Programs.f1b_bcSem
#print axioms Lua.Programs.f1b_supported
#print axioms Lua.Programs.f4Strlite_bcSem
#print axioms Lua.Programs.f4Strlite_supported
#print axioms Lua.Bytecode.step?_complete
#print axioms Lua.Bytecode.Step.deterministic
#print axioms Lua.Bytecode.BcSem.deterministic
#print axioms Lua.Bytecode.Supported.defInit
#print axioms Lua.Bytecode.DefInit.step
#print axioms Lua.Bytecode.bcSemFrom_iff
#print axioms Lua.Bytecode.cbcSem_iff
#print axioms Lua.Bytecode.reachable_defInit
#print axioms Lua.Bytecode.kstep_iff
#print axioms Lua.Bytecode.footprint
#print axioms Lua.Bytecode.certain_answers
#print axioms Lua.Bytecode.DefInit.cert
#print axioms Lua.Ast.luaRun_sound
#print axioms Lua.Ast.LuaSem.deterministic
#print axioms Lua.Bytecode.Final.not_step
#print axioms Lua.Compile.agree_of_outputs
#print axioms Lua.Compile.f1Ops_tv
#print axioms Lua.Compile.f1Src_tv
#print axioms Lua.Compile.while_tv
#print axioms Lua.Compile.f1b_tv
#print axioms Lua.Rulebook.sem_iff_solve
#print axioms Lua.Vm.Boot.vmLoaded_of_checks
#print axioms Lua.Vm.Boot.Witness.While.vmLoaded_while_entry
#print axioms Lua.Vm.Boot.Witness.While.runtimeReady_while_entry
#print axioms Lua.Vm.Boot.Witness.F1Ops.vmLoaded_f1Ops_entry
#print axioms Lua.Vm.Boot.Witness.F1Ops.runtimeReady_f1Ops_entry
#print axioms Lua.Rulebook.Sem.det
#print axioms Lua.Ast.luaSem_iff_run
#print axioms Lua.Programs.f4Strlite_astSupported
#print axioms Lua.Programs.f4Strlite_luaSem
#print axioms Lua.Compile.corpus_compileTV
#print axioms Lua.Compile.compile_refinement_corpus
#print axioms TCB.Os.allowed_sound
#print axioms TCB.Os.allowed_complete
#print axioms TCB.Os.checkTrace_sound
#print axioms Lua.Os.HtifTraces.accepts_write_stdout
#print axioms Lua.Os.HtifTraces.rejects_write_unknown_fd
#print axioms Lua.Os.HtifTraces.rejects_fstat_stdout_nlink0
#print axioms Lua.Os.HtifTraces.accepts_fstat_stdout
#print axioms Lua.Os.HtifTraces.accepts_write_unknown_fd_ebadf
#print axioms Lua.Os.HtifTraces.accepts_clock_frozen
#print axioms Lua.Vm.tohostAddr_eq_symTohost
#print axioms Lua.Vm.retCcall_after_call
#print axioms Lua.Vm.setjmpRet_after_call
#print axioms Lua.Vm.cstack_room
#print axioms Lua.Vm.PartialView.rdLE
#print axioms Lua.Vm.Boot.writeLog_view
#print axioms Lua.Vm.Boot.bootMem_get
#print axioms Lua.Vm.Boot.heapAt_of_check
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
#print axioms VsaIris.Sym.st_8002fa34
#print axioms VsaIris.Sym.st_80030360
#print axioms VsaIris.Sym.sltuAluStepAt
#print axioms Lua.Vm.Arms.TextLoaded.writeMap8
#print axioms Lua.Vm.Arms.seg_8001d3ec_8001d400
#print axioms Lua.Vm.Arms.seg_8001d00c_8001d034
#print axioms Lua.Vm.Arms.seg_8001d3bc_8001d3ec
#print axioms Lua.Vm.Arms.seg_8001c6e4_8001c708
#print axioms VsaIris.Sym.swpo_run
#print axioms VsaIris.Inst.putc_runFact
#print axioms VsaIris.Inst.exit_haltFact
#print axioms VsaIris.Inst.vsa_adequacy_exit
#print axioms VsaIris.Inst.whileSites_not_tohost
#print axioms Vsa.Sim.stepObs_tohost_putchar
#print axioms Vsa.Sim.stepOnce_tohost_G
LEAN
lake env lean "$tmp/Axioms.lean" > "$tmp/out.txt" 2>&1 || { cat "$tmp/out.txt"; fail "axioms file"; }
cat "$tmp/out.txt"
n=$(grep -cE "depends on axioms|does not depend on any axioms" "$tmp/out.txt")
[ "$n" = "$(grep -c "^#print axioms" "$tmp/Axioms.lean")" ] || fail "expected one axiom report per #print axioms line, got $n"
if grep "depends on axioms" "$tmp/out.txt" | sed 's/.*\[//; s/\]//' | tr ',' '\n' | sed 's/ //g' \
   | grep -vxE 'propext|Classical.choice|Quot.sound' | grep -q .; then fail "non-standard axiom"; fi
echo "check: all stages OK"

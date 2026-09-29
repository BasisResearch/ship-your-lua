#!/usr/bin/env bash
# abs_inventory.sh — list the abstractions available in this repository, to
# reuse by name before any proof work (CLAUDE.md). Adapted from
# ship-your-interpreter's scripts/abs_inventory.sh (see scripts/syi/).
cd "$(dirname "$0")/.." || exit 2
echo "### AVAILABLE ABSTRACTIONS (HEAD $(git rev-parse --short HEAD 2>/dev/null || echo none))"
echo "# Lua development (Lua/): top-level declarations"
grep -rhoE '^(theorem|def|abbrev|structure|inductive) [^ :({]+' Lua --include=*.lean \
  | grep -v '^def \(textPage\|rodataPage\)' | sort -u | sed 's/^/#   /'
echo "# copied machine layer (Vsa/, VsaIris/): tool-table modules present"
for m in Vsa/Sim/FnSummary Vsa/Sim/DeriveCallSeg Vsa/Sim/DeriveLoop Vsa/Sim/TripleCat \
         Vsa/Sim/StepObs Vsa/Sim/Decode Vsa/Sim/RamReadPolicy Vsa/Sim/RamReadScalar \
         Vsa/Sim/RamReadVirtual Vsa/Sim/RamReadLoad Vsa/Sim/RamReadValue Vsa/Sim/Muldi3Spec \
         Vsa/Sim/DivSpec Vsa/Sim/MemcpySpec Vsa/Densify VsaIris/MachWP VsaIris/LocalRun \
         VsaIris/DlHeap VsaIris/MallocRun; do
  [ -e "$m.lean" ] && echo "#   $m.lean"
done
echo "# not yet ported (PHASES.md A0; experiments/port/CUTS.txt): SegToTripleFramed, BridgeSeg*,"
echo "#   FrameMeta, DeriveCase, SeparationLogic, AllocLedger, VsaIris/Vsa/{SymRun,AllocSteps,Stdout,Fprintf,ExitH}"
echo "# generators: scripts/gen_*.py (Lua), scripts/syi/*.py (copied; retarget their defaults)"

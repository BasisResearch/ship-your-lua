#!/bin/bash
# F3: does the Lua stack (and so `base`) move under a running luaV_execute
# activation?
#   f3_stack.sh ELF...     (summary lines per ELF on stdout; no trace stored)
# Traced pcs (--trace-pcs; stderr streamed through gawk, never written):
#   luaV_execute entry (a new C frame), `startfunc` (the target of CALL's
#   `goto startfunc`: a new Lua activation in the same C frame), the dispatch
#   `jr` (every opcode dispatch passes it), luaD_reallocstack and
#   luaD_growstack entries.
# Activations: per C frame (sp), a stack of CallInfo pointers (s7).  At
# startfunc: ci not on the stack -> push (call); ci == top -> new activation
# in place (tail call).  At a dispatch whose ci is below the top -> pop to it
# (return).  At each dispatch, base = s9.  A base change between two
# consecutive dispatches of one activation is "within" if no other
# activation dispatched in between, else "across" (a call ran in between).
# Each change is attributed to the opcode whose arm ran just before it
# (a4 = i & 0x7f at the previous jr of that activation), and flagged if a
# luaD_reallocstack ran in between.
set -u
REPO=$(cd "$(dirname "$0")/../.." && pwd)
EMU=${EMU:-$REPO/riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
TC=${TC:-$HOME/toolchains/xpack-riscv-none-elf-gcc-15.2.0-1/bin/riscv-none-elf}
TMP=${TMPDIR:-/tmp}
one() {
  elf=$1
  n=$(basename "$elf" .elf)
  sym() { $TC-nm "$elf" | awk -v s="$1" '$3==s{sub(/^0+/,"",$1); print $1}'; }
  VX=$(sym luaV_execute); RA=$(sym luaD_reallocstack); GR=$(sym luaD_growstack)
  # the one `jr`, and startfunc = the lowest in-function jump target
  read JR SF < <($TC-objdump -d "$elf" --start-address=0x$VX --stop-address=$(printf '0x%x' $((0x$VX + 0x4000))) \
      | gawk -v vx=$VX '/>:$/ {h++; if (h>1) exit}
          $3=="jr"{jr=$1; sub(":","",jr)}
          $3=="j" || $3 ~ /^b/ { t=$4; sub(/.*,/,"",t); if (strtonum("0x" t) > strtonum("0x" vx) && (sf=="" || strtonum("0x" t) < strtonum("0x" sf))) sf=t }
          END{print jr, sf}')
  pcs=$(mktemp "$TMP/f3pcs.XXXX")
  printf '0x%s\n' $VX $RA $GR $JR $SF > "$pcs"
  $EMU "$elf" --trace-pcs "$pcs" 2>&1 >/dev/null | gawk -v n="$n" -v VX=$VX -v RA=$RA -v GR=$GR -v JR=$JR -v SF=$SF '
    function frame() { return $6 }                     # sp inside luaV_execute
    function push(f, c) { d = ++depth[f]; sci[f, d] = c; sid[f, d] = ++nact; calls++ }
    $1!="T" {next}
    $3==VX { vx++; if (!first) first=$2
             f = sprintf("%x", strtonum("0x" $6) - 176); depth[f] = 0; next }
    $3==RA || $3==GR {
      w = ($3==RA) ? "realloc" : "grow"
      if (first) { after[w]++; if (w=="realloc") nre++
                   if (ev < 8) evs = evs sprintf(" %s@%s(ra=%s,n=%d)", w, $2, $5, strtonum("0x" $15)); ev++ }
      else before[w]++
      next }
    $3==SF { f = frame(); c = $27
             if (depth[f] > 0 && sci[f, depth[f]] == c) { sid[f, depth[f]] = ++nact; tails++ }
             else push(f, c)
             next }
    $3==JR {
      disp++; f = frame(); c = $27; b = $29
      if (depth[f] == 0 || sci[f, depth[f]] != c) {
        for (k = depth[f]; k > 0 && sci[f, k] != c; k--) ;
        if (k > 0) { depth[f] = k; rets++ } else { push(f, c); orphan++ } }
      a = sid[f, depth[f]]
      if (a in lastb && lastb[a] != b) {
        op = sprintf("op%d", lastop[a]); rr = (lastre[a] != nre) ? "+realloc" : ""
        if (lastact == a) { within++; wop[op rr]++ } else { across++; aop[op rr]++ } }
      lastb[a] = b; lastop[a] = strtonum("0x" $18); lastre[a] = nre; lastact = a
      next }
    END {
      printf "%-14s dispatches=%d vx_entries=%d activations=%d (calls=%d tailcalls=%d returns=%d unmatched=%d) realloc/grow before first luaV_execute=%d/%d after=%d/%d base_change_within=%d across=%d%s\n",
        n, disp, vx, nact, calls, tails, rets, orphan, before["realloc"], before["grow"], after["realloc"], after["grow"], within+0, across+0, evs
      for (c in wop) printf "%-14s   within-activation base change after %s x%d\n", n, c, wop[c]
      for (c in aop) printf "%-14s   across-call base change after %s x%d\n", n, c, aop[c] }'
  rm -f "$pcs"
}
export -f one; export EMU TC TMP
printf '%s\n' "$@" | xargs -P ${JOBS:-8} -I{} bash -c 'one {}'

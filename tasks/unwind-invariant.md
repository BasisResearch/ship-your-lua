Binding rules: read CLAUDE.md and relevant PHASES.md/ledger before work.
Save scripts/abs_inventory.sh output to /tmp; query relevant entries, never dump it.
No sorry, new axioms, native_decide, bv_decide, or raised Lean budgets.
Generated files change through their generators; obey R-rules and abstraction gate.
Work only in your assigned worktree; preserve existing work and caches.
No subagents or extra codex workers. The manager owns the two worker slots.
Run every Lean command via the MAIN repo's scripts/lean-capped.sh (12 GB scope).
One build at a time per worktree; check free -g; wait if available <25 GB.
Do not modify shared dependency caches; use your private .lake/build.
Read abstractions/DEAD-ENDS.md; do not repeat recorded dead ends unchanged.
Prove real obligations; do not weaken semantics or use vacuous specifications.
Commit validated work on your branch; if Git is read-only, hand files to manager.
Never merge/push main; read-only Git must not stop proof work or validation.
Update lane ledger and relevant PHASES/check.sh axiom entries when ready.
Report tests and exact remaining premises. Manager reviews and lands through check.sh.
Final line: RESULT: landed <worker-branch-commit> OR RESULT: stuck <exact obstacle>.

Target: establish the complete missing runtime invariant for error unwind:
base CallInfo, owned terminal successor, and stderr representation, with no new premise.
Files: Runtime/EntryData/Boot checks, Sim/Rel/StdioState, Kit/CallOpen/ExtendCI/
CallPrint/CallClose/Errno/Sinit/StdoutSetup/StdoutEmpty/Unwind, boot generator and gate.
Read f1-unwind-plan.md and tasks/base-ci-invariant.md, cinext-owned.md,
stderr-invariant.md for the audited subcontracts; preserve CiNext.next=NULL.
BaseCI: kernel-check func=stack, top=stack+21*16, previous=0, next=current Lua ci,
status=CIST_C at boot/VARARGPREP; freeze its footprint and preserve through CALL.
Successor: retain MallocPost.block and16-alignment in heap-indexed NciApart,
through allocation/reuse, PrintPost.kept and close; expose FreeRHeap owned-block input.
Do not infer allocation base from interior payload liveness; initial NULL needs no premise.
Stderr: move pure FileStd/ErrStd below execution imports, strengthen StdioRest and
RestFoot/congrT with full stderr and _REENT pointer; establish from real sinit.
Account for ErrStd.tail through176 versus old SinitPost through168: lock init is
an actual ret, whose preservation must be proved. Keep the compatible StdQuiet API.
Expose all-phase stderr pointer and nonboot ErrStd accessors for FprintfPre.
Factor shared footprint/heap transports; no per-arm proof duplication or import cycles.
Build narrow targets while developing; freeze all final proof sources before one
combined Entry/CallPrint/PrintIO/Unwind consumer build and public axiom audit.
Done: capped builds, standard-only axioms, generators/discipline/abstraction PASS;
update ledger/PHASES/gate and state remaining machine runs. Full gate is lead's.

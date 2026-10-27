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

Target: carry the proved stderr console write through _write_r and __swrite,
so FprintfErr's unbuffered __sfvwrite_r path has a proved write-hook summary.
Files: Lua/Vm/Sim/Kit/Swrite.lean or a factored sibling; generators only if
needed; relevant lane ledger, CLAUDE availability, PHASES/check.sh audits.
First inspect write_r_sum/swrite_sum and the new write_console_sum. Generalize
shared reasoning by descriptor/file parameters where it avoids duplicate runs;
retain existing stdout APIs as corollaries so current callers still build.
State honest FILE facts for stderr (fd=2, no __SAPP, initialized descriptor),
errno and buffer/frame separation. Prove the actual finite Sail execution,
return n, exact output bytes, ABI preservation and byte/presence memory frame.
Use the existing generated Hwrite_r/Hswrite segments and shared frame helpers.
Keep one byte loop: do not copy write_sum or introduce an opaque callee premise.
The summary must cover arbitrary n within the existing address bounds, incl 0.
Done: capped new module and stdout-consumer builds; standard-only axiom audit;
relevant discipline/abstraction/generator checks and accurate remaining ledger.
Do not claim FprintfErr or global HtifPrint closed: unbuffered sfvwrite,
formatting and persistent OS representation remain distinct obligations.
Run targeted static checks; leave full check.sh (including static-only) to the lead.
Poll long builds at 45-second intervals; do not dump replay warnings or inventories.

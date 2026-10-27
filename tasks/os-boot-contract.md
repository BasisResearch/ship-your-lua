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

Target: diagnose and repair the OS boot-output contract, without claiming
HtifPrint/HtifFs or adding an arbitrary boot-only representation.
Files: Lua/Os/Htif.lean, a small diagnostic module if needed, PHASES,
abstractions/ledger/os-stdout.md, check.sh public axiom registration.
First inspect BootAt, HtifRepr.init/console, GoodState and Machine.output.
Prove a generic diagnostic: changing only sailOutput preserves the old
image/register boot facts, but nonempty output contradicts representation
of OsState.init. Do not rely on an unproved concrete boot existence claim.
Make the necessary empty-output initial condition explicit in BootAt;
retain the old image/control facts under a reusable named predicate if
needed for the diagnostic. Show exact construction from those facts plus
empty output. Document this specification repair and why it is necessary.
Do not weaken ConsoleAt, OS behavior, or claim this supplies the persistent
representation/frame, resource bounds, read/fstat runs or global premises.
Done: capped affected module/consumer builds and standard-only axiom audit,
targeted discipline/abstraction checks, accurate ledger and remaining work.
Leave full check.sh (including static-only) to the lead. Poll at 45 seconds.

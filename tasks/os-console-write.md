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

Target: bridge the existing stdout machine summary to the TCB OS relation.
Files: Lua/Os/ConsoleWrite.lean (preserved draft), Os/Htif.lean,
Os/HtifFs.lean, Vm/Sim/Kit/Write.lean and tcb/Os; PHASES OS.
First: inspect and compile the draft using the capped wrapper; repair proof errors.
Done: stdout write has actual machine Steps, ABI call/return, OsStep and console
agreement using write_sum; axiom checks and imports registered, ledger, commit.
Do not claim HtifPrint/HtifFs globally: boot-only R vacuity, other calls, persistent
representation/frame and filesystem resource bounds remain separate obligations.
Earlier build failed in dependency StdioState on thread creation, not this proof.
Main repo is /data/home/kirancodes/Documents/code/ship-your-lua.
The manager fixed scope access: the launcher now inherits a 12 GB scope.
If Git metadata is read-only, report ready files; manager will commit after review.

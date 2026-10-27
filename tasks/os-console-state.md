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

Target: retain the standard console descriptor invariant across all three local boundaries.
Files: new Lua/Os/ConsoleState.lean, existing Console{Read,Write,Stat}/Kit summaries,
PHASES/CLAUDE, check.sh audits and abstractions/ledger/os-console-state.md.
Reuse Agree.b4 and wrBootMem_facts; do not duplicate any instruction path.
Define a named ready state for fs_ready and all three descriptor kinds, with
its exact four-word footprint and one generic agreement transport theorem.
Define the lazy-or-ready input; derive initialization and ready preservation
from the actual prefix memory. Preserve it through read/write, and fstat's
zeroed/output memory using an explicit output/descriptor separation fact.
Use the local machine result's actual post-memory, not an assumed final state.
Keep abstract stream lookup/live/empty-input and machine frame requirements
explicit. Do not claim boot framing, arbitrary callers or HtifPrint from a
boot-only relation; resource/reachability/global representation remain open.
Done: reusable state facts tied to actual read/write/fstat summaries, target
build and standard-only audit, gate registration in executable/heredoc bodies,
accurate ledger. Record any failed abstraction choice before retrying.

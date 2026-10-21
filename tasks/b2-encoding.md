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

Target: finish B2 checked instruction encoding and jump-patching foundations.
Files: Lua/Compile/Encode.lean (preserved draft), Bytecode/Syntax.lean,
vendor/lua-5.4.7/src/lopcodes.h and lcode.c; PHASES B2, ledger b-s3.
First: inspect the unvalidated draft; prove generic field roundtrips under bounds.
Then implement checked signed jump construction/patching and prove its target law.
Done: useful generic laws build and use standard axioms only; register checks,
write a short lane ledger, commit. Do not claim CompileTV or B3 is solved.
The draft's earlier build failed on thread creation before checking this file.
Main repo is /data/home/kirancodes/Documents/code/ship-your-lua.
The manager fixed scope access: the launcher now inherits a 12 GB scope.
If Git metadata is read-only, report ready files; manager will commit after review.

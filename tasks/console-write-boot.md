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

Target: prove _write(fd=1 or 2) through its lazy fs_init path, reusing the
landed initialized-console summary/loop, with exact stores and full frame.
Files: Kit/Write.lean or WriteBoot.lean; gen_lua_arms.py/gen_lua_at.py as
needed; Setup/FsGlobal only for shared facts; ledger/PHASES/check.sh audits.
First inspect ELF 0x80000ae8 through the fs_ready=0 branch at 0x80000b04.
An error before any print takes unbuffered __smakebuf_r at 0x80049a38,
which returns without _fstat. Do not assume fs_ready was initialized there.
Refactor one shared join/suffix if needed; never copy the byte loop or add
an opaque initialization premise. The stores initialize fs_ready, root
used/dir and the three standard descriptor kinds; establish FdsStd explicitly.
Use generated segments/callee-context runs, preserving existing generated
names and stdout APIs. Prefer standalone new helper imports where feasible.
State honest buffer/frame separation from the initialization stores, bounds
and ABI facts. Cover arbitrary byte counts including zero. Prove actual
finite Sail steps, n returned, exact console append and optional-byte frame.
Done: capped target/stdout-consumer builds, standard-only public axiom audit,
relevant generator/discipline/abstraction checks and accurate remaining ledger.
Keep FprintfErr/global HtifPrint open. The lead runs the complete gate.
Poll long builds at 45-second intervals with concise output.

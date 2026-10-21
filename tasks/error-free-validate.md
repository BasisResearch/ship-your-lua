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

Target: finish and validate the existing FreeRHeap_Statement draft; no new lane.
Files: Kit/{Malloc,AllocHeap,AllocProof}.lean, VsaIris/Vsa/FreeRunAll.lean,
abstractions/ledger/f1-lane-26.md, PHASES.md and scripts/check.sh.
The manager stopped your old worker scope, releasing the orphan build lock,
and restored missing PRIVATE cache files from main. No build is running here.
Read /tmp/syi-free-review-build.log: Malloc compiled; AllocHeap fails in
freeSurvivors_ledger because simp unfolds the goal beyond the induction hypothesis.
Fix that proof, then remaining genuine type errors. Do not use lake build while
shared dependency symlinks are installed: run /tmp/sol1-validate-free.sh, which
uses the capped wrapper and lake env lean with explicit private output paths.
Keep the resulting heap, surviving allocation base/capacity, exact payload and
ABI/console frames; old freeR_proved must remain a corollary. Do not weaken them.
Do not cancel a build and then retry against its held lock. Await every process.
If a missing cached module is reported, record its exact name for the manager.
Done: all four changed modules and the ten-name axiom audit pass, only standard
axioms, discipline/abstraction/diff checks pass, ledger reports actual evidence.
Keep the pending unwind premises explicit; do not claim ErrorSimRest is closed.
If Git is read-only, return the validated files for the manager to commit.

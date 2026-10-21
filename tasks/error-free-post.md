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

Target: expose _free_r resulting heap and live-payload frame for error unwind.
Files: Kit/AllocProof.lean, Kit/AllocHeap.lean, Kit/Malloc.lean,
VsaIris/Vsa/FreeRunAll.lean and its FRet; Kit/Unwind.lean, F1-26 ledger.
First: read existing FQ/freeR_proved; identify which FRet fields it discards.
Done: strengthened named post and proved summary retains HeapAt and other
live payloads, old FreeR_Statement obtained as a corollary, standard axioms.
Reuse free_body and LocalRun.reach; no new allocator instruction proof.
Do not promise the freed block is still in use; preserve surviving ledger entries.
If entry/post fields in Unwind are changed, use named structures (R6/R7).
Record exact pcall shrink/realloc and fprintf premises still open.
Main repo is /data/home/kirancodes/Documents/code/ship-your-lua.
The pending Unwind file is in main/.claude/worktrees/lane-f1-26; read it there.

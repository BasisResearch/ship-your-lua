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

Target: prove newlib _Bfree at 0x8003d700 (9 instructions), for float formatting.
Files: Vm/EntryData.lean (ReentMp/BigChain), Kit/BigHeap.lean, generators
scripts/gen_lua_{code,arms,at}.py, new Kit/Bfree.lean and generated AtF file.
First: reuse callee-context generation for null and non-null branches.
Non-null: read class at b+8, freelist at _REENT+104, push b into slot fl+8*k.
Done: generated run plus precise ABI/memory-frame summary for both branches,
with bounded/aligned pointers and class; standard axioms; generator/gate checks.
Use a named-field input/post structure; do not claim heap unchanged on allocation.
If feasible derive the ReentMp free-list update with an apart owned block.
Do not claim FloatToStr is closed; this supplies its first bignum primitive.
Update ledger, CLAUDE availability and check.sh axioms; leave other generators intact.
Main repo is /data/home/kirancodes/Documents/code/ship-your-lua.
F1-25 BigHeap is pending on main; consult the main workspace copy if absent here.
Generate new helper/code pins as standalone imports, keeping aggregate indexes stable.

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

Target: retain that the successor print CallInfo is an allocation base,
so its eventual free has an owned-block input, without a new open premise.
Files: Sim/Rel, Kit/CallOpen,ExtendCI,CallPrint,CallClose,Errno;
relevant ledger/PHASES/check.sh; preserve the terminal successor fact.
First read f1-unwind-plan.md: NciApart.kept is only payload liveness.
Use a named owned-block fact carrying an in-use chunk at nci-16 with
capacity at least ciSize; retain the allocator-derived 16-byte alignment.
Keep heap-dependent ownership in NciApart/CallInvAt, not memory-only CiNext.
ExtPost should retain MallocPost.block from the real allocation.
Thread it through allocated/reused joins, PrintPost.kept, and call_close.
The initial successor is NULL; do not demand a new initial hypothesis.
Frame-only transports such as Errno must preserve this fact too.
Expose an accessor with the owned-block input of FreeRHeap_Statement.
Done: affected capped CallPrint/CallArm/Entry builds, standard-only public
axioms, generator/discipline/abstraction checks, clear remaining shrinkCI run.
Leave full check.sh to lead; poll long builds every 45 seconds.

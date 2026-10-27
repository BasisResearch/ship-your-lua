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

Target: retain and prove the terminal successor CallInfo fact nci->next=NULL
through the VM relation, needed by luaE_shrinkCI on the error-unwind path.
Files: Sim/Rel.lean (CiNext), Kit/CallOpen,ExtendCI,CallPrint,CallClose,
related relation constructors, ledger/PHASES/CLAUDE/check.sh as needed.
First inspect CiNext.previous, ExtPost, JoinIn and CloseIn: the ELF's
luaE_extendCI writes next=NULL, but the current contracts discard that fact.
Add the named field to CiNext and carry it through generated allocation
stores, reused/allocated join paths, the print run and call_close.
Establish it from the existing machine writes, never as a new open premise.
Initial LuaStateAt.rel has ci->next=NULL, so no new boot premise is needed;
prove all relation constructors still satisfy the strengthened invariant.
Factor a reusable successor-field preservation lemma if the two joins need it.
Do not add the whole unwind or base_ci/stderr facts in this lane.
Done: affected capped builds including CallPrint/CallArm/Fold, standard-only
public axiom audit, targeted discipline/abstraction/generator checks, and
ledger locating the field available to the future luaE_shrinkCI summary.
Leave full check.sh to lead; poll long builds every 45 seconds.

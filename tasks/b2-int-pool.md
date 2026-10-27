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

Target: model integer constant interning and discharge IntEmit's supplied
constant-reference premise in a checked integer-emission pipeline.
Files: Compile/IntPool.lean (or focused companion), IntEmit integration/checks,
ledger b-s3/PHASES/CLAUDE/check.sh and only necessary shared lemmas.
First inspect lcode.c:addk/luaK_intK/luaK_int, IntEmit and DEAD-ENDS' cache probe.
Model the mutable cache explicitly; an integer key's cached index can be stale
or point to a different tag/value. Validate index and exact integer value;
on miss append and overwrite that key. Preserve all existing pool entries.
Keep the scalar cache abstract enough to admit scanner/nested-function changes;
do not claim a complete parser/hash-table/float interner refinement.
Respect max constant-index and operand bounds with checked failure, not truncation.
LOADI must bypass interning; LOADK should receive a proved ConstantRef from the
updated pool. Prove generic one-step register/pc/output semantics for the
composed pipeline, rather than assuming the post pool or an execution result.
Do not silently support LOADKX: retain its explicit current unsupported boundary.
Done: capped target builds, standard-only public axioms, meaningful stale-cache,
wrong-tag and repeated-integer boundary checks; ledger precise about B2/B3 gaps.
Leave full check.sh to lead; poll long builds every 45 seconds.

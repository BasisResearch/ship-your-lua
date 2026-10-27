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

Target: prove _Balloc's cached-block path, from its actual entry to ABI return,
including its ReentMp/BigRun ownership effect (zero heap growth).
Files: generators gen_lua_{code,arms,at}.py, new Kit/Balloc.lean and BallocHeap.lean
if useful; EntryData/BigHeap only for reusable facts; ledger/PHASES/check audits.
Start from the ELF at 0x8003d654 and nonzero freelist[k]. It pops that head,
zeros _sign/_wds at returned block+16, and returns the block at 0x8003d690.
Use standalone helper imports and generated callee-context runs, as Bfree does.
Reuse BfreeHeap's bounded cache-value transport and ownership ledger machinery;
factor shared ownership changes instead of copying the entire Bfree proof.
Expose honest named pre/post records: initialized nonempty class list, heap,
stack separation, ABI frame; the returned block apart from remaining owners,
class/capacity retained, sign/wds zero, other block bytes preserved.
The resulting BigRun must follow from real stores and the unchanged heap,
not assume a desired post. Keep array-allocation and fresh-block paths named
as remaining work; do not claim a full Balloc or FloatToStr summary.
Done: capped affected-module build and standard-only public axiom audit;
relevant generator/discipline/abstraction checks; accurate lane ledger.
Run targeted static checks; leave full check.sh (including static-only) to the lead.
Poll long builds at 45-second intervals; do not dump replay warnings or inventories.

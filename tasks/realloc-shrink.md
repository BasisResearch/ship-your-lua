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

Target: port the allocator's nonzero in-place shrink path for PcallErr;
prove a named Lua-facing ReallocShrink contract with actual Sail steps.
Files: relocated VsaIris/Vsa/Realloc{Ctx,Pro,Dec,Tail} and minimal imports,
Kit/AllocProof (or a focused companion), ledger/PHASES/audits/attribution.
First inspect upstream syi ReallocCtx.RHeap.grow and ReallocTail.old_le.
The public growth entry requires nOld<new; it does not prove stack shrink.
Reuse the tail's retained-prefix <=new contract, the generated allocator
SWP steps and free_body. Relocate with experiments/port/alloc/reloc.py;
never retype allocator instruction proofs or count an unresolved PC map.
Input: a live allocation base/capacity and positive smaller request with
actual heap/stack/ABI bounds. Post: same nonzero base, requested prefix
bytes, resulting HeapAt/ledger, every other live allocation and payload
preserved, honest written-region frame and console/ABI return.
Cover both unsplit and split/free-tail shrink paths. Do not promise the
truncated suffix survives or claim full realloc/PcallErr is discharged.
Done: capped affected builds, standard-only public axiom audit, targeted
generator/discipline/abstraction checks, exact remaining premises recorded.
Leave full check.sh to the lead; poll long builds every 45 seconds.

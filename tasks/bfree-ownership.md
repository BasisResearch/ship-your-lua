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

Target: lift the proved _Bfree exact-store/chain primitive to the reusable
ReentMp/BigRun ownership contract needed by float formatting and strtod.
Files: Kit/Bfree.lean, new Kit/BfreeHeap.lean, Kit/BigHeap.lean and
Vm/EntryData.lean only if a missing reusable fact demands it; ledger/check.sh.
Start from bfree_sum, bfree_chain, BigChain.congr and BigRun. No new run proof.
For an active block b of class k, separately owned and apart from every
bigBlocks entry, push it into freelist[k], preserving the other chains,
result and power-five cache, with updated heads/lists and honest byte frames.
Keep the heap ledger unchanged only because these stores are in live payloads;
prove that from HeapAt and ownership. Keep the bignum region within old B.
Expose a named precondition, not opaque assumptions of the desired post.
Audit p5v/bigVal footprint: ReentMpAt alone does not bound _wds by capacity.
Strengthen ReentMpAt with a justified cache-capacity fact if needed, and
prove it at boot (ReentBoot.mp) and preserve it; never assume the desired post.
Done: machine summary supplies BigRun with zero heap growth under the named
ownership precondition; ReentMp and its Frozen fact are proved for the new memory.
Capped target builds, axiom audit and applicable static checks must pass.
Keep FloatToStr/FpStrFlt open. Private caches permit normal lake build.
Resume: WIP 7ce52ee preserves the draft; repair rather than restart it.
Read /tmp/sol-2-build.log for concrete failures; static gate already passed.
Do not increase proof budgets; factor difficult framing/ownership arguments.
For long builds, poll at 45-second intervals with concise output.

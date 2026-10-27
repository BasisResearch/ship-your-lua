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

Target: prove the successful positive-request _calloc_r machine summary from
entry 0x8004a35c through ABI return, composing proved malloc and zeroing.
Files: generators/standalone Callee at-runs, Kit/Calloc.lean, shared heap laws,
ledger/f1-calloc-plan.md, PHASES/check.sh. Read that ledger and Kit/MemsetZero.
Use __muldi3 summary and AllocProof.mallocR_proved, never assumed runs/posts.
Scope inputs: _REENT, 1<=nmemb,size<2^32, product n and malloc room bounds;
these select actual low32 fast path and rule out NULL/overflow from proved bounds.
Read actual allocated header p-8: cap=chunk.size-8, not requested product.
Derive full-capacity freshness from AllocHeap.walkV, ChunkWalk.chunk_sep/bounds,
MallocPost.kept/fresh (positive n); no new chunk-walk induction or freshness premise.
Use memsetZero_sum for cap>72; generated inline paths cover cap24/40/56/72.
Post: retained HeapAt, live block at p-16, cap>=n, all cap bytes present zero,
old live payloads unchanged, honest global/arena/stack frame, ABI/console kept.
Account for outer32-byte frame plus malloc's1024 below sp-32; never claim only1024.
Factor zeroing heap/frame transport once; use HeapAt.congrU and ZeroOut laws.
Keep code/arms standalone and generated; every path/run via generator layer.
Done: capped target/affected builds, all public standard-only axiom checks,
generator/discipline/abstraction passes; register explicit build target and audits.
Record exact scope and remaining fresh Balloc/FloatToStr work; full gate is lead's.

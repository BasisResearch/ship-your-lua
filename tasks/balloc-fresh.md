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

Target: prove fresh _Balloc success paths from actual entry0x8003d654 through
ABI return, composing the proved calloc summary, then lift to BigRun ownership.
Files: generators/standalone Balloc roots, Kit/BallocFresh*.lean and shared
heap/ledger laws, PHASES/check.sh; read f1-balloc-fresh-plan.md first.
Cover initialized-array empty-head and NULL-array first-use (calloc8*65 then
calloc1*bigSize k). Keep the already proved cached path and its API reusable.
Derive k<31 from explicit mathematical allocation-room bounds; k<=64 alone
cannot justify the machine sllw/sign extension. Use existing generated sllw rule.
Post: real ABI return, resulting HeapAt, array installed/zero heads as needed,
returned owned block with cls=k,maxwds=2^k,sign=wds=0, zero next/digits;
old live payloads and ledger preserved outside actual effects, BigRun with cost.
Retain physical base/capacity separately from logical bigSize; active block is
not a freelist member. Extend B only by proved fresh in-use regions.
Factor ReentMp array installation and new active ownership once; compose
malloc/zero frames and frozen ledger laws, never assume the desired heap/post.
Budget both successful calloc calls, stack frames and break growth explicitly.
Done: capped target builds, public standard-only axiom audit, generated drift,
discipline/abstraction checks; explicit build/audit registrations. Full gate lead's.
Record scope and remaining dtoa/strtod/FloatToStr obligations without claiming them.

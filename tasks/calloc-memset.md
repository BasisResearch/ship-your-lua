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

Target: prove the memset zero-fill path used by newlib calloc: 16-aligned
pointer p, n>=24 and n%16=8, actual entry 0x8003b56c through ABI return.
Files: existing at/code/arms generators, standalone AtF/MemsetZero modules,
Kit/MemsetZero.lean, shared memory-range laws, ledger/PHASES/check.sh.
First inspect _calloc_r 0x8004a3a8: memset length is physical chunk size-8,
not the requested size. Heap chunk sizes are 16-aligned; this gives remainder8.
Inventory existing ZeroAt/writeLog/frame abstractions and seg_loop before work.
Generate the actual 16-byte loop at 0x8003b590 and computed eight-byte tail;
use one loop invariant with named frame/zero-prefix facts, not unrolled runs.
Post: every byte of [p,p+n) is present zero; exact optional-byte equality
outside it; return p, ABI/console preserved. Require honest RAM/MMIO bounds.
Do not assume original bytes are zero, a run/post, or a calloc conclusion.
Keep pins and helper segments standalone; no aggregate regeneration churn.
Done: symbolic arbitrary-length proof with capped affected build, standard-only
public axiom audit, targeted generators/discipline/abstraction checks.
Record how calloc derives alignment/remainder and which malloc/calloc/Balloc
composition remains. Leave full check.sh to lead; poll builds every 45 seconds.

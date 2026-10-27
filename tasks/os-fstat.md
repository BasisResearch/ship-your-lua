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

Target: prove actual initialized/lazy _fstat for console fds 0,1,2 and
its TCB stream-stat refinement, with arbitrary safe 8-aligned output buffer.
Files: existing code/arms/at generators, Kit/FstatConsole.lean,
Os/ConsoleStat.lean, os-fstat-plan.md/PHASES/check.sh. Read that plan first.
Reuse Setup.fstat_sum's generated shape; it is at _fstat_r, not this entry.
ELF entry 0x80000e9c; memset(0,104), mode=S_IFCHR, nlink=1, size=0.
Cover both buffer residues 0 and 8 mod16; newlib's actual caller uses 8.
Use generated fixed-size paths/one shared tail, no hand unrolled proof.
Name entry/post contracts: actual SegSt, initialized matching kind or
ready=0, aligned safe stack/RA, writable RAM output apart from saved RA,
with exact conditional init/output/frame stores and preserved ABI/console.
Use generated Layout offsets; preserve optional bytes off the exact writes.
Prove StatAt with present mode/nlink/size reads, ReturnsTo, HtifRetAt stats,
OsStep for a live abstract stream descriptor, and ConsoleAt.
No assumed run/post, boot-only R, or full OS-implementation claim.
Done: capped target builds, all public standard-only axioms, targeted
generator/discipline/abstraction checks; record persistent/resource seams.
Leave full check.sh to lead; freeze sources before validation, poll at 45s.

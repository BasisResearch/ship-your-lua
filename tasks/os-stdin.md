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

Target: prove the actual _read(0,buf,n) EOF boundary, both initialized and
lazy-fs-init paths, and its TCB OS refinement for an empty stdin stream.
Files: standalone generated code/arms/AtF via existing generators,
Kit/ReadStdin.lean, Os/ConsoleRead.lean, ledger/PHASES/check.sh.
First inspect c/src/htif.c and ELF 0x80000984; fd0-kind1 returns zero via
0x80000a94 without reading or writing buf. Mirror ConsoleWrite's honest bridge.
Use one common return/tail summary; lazy init writes files[0]'s halfword,
fs_ready and fds[0..2].kind, plus saved RA. Reuse pure init/frame laws where
applicable, but generate this routine's actual instruction run.
Named entry/post: aligned safe stack/RA, initialized fd0 or fs_ready=0,
actual SegSt, finite Sail Steps, return0, ABI/console preserved and exact frame.
Do not demand arbitrary input buffer validity: this EOF path never accesses it.
For the OS bridge, use a live abstract process/fd0 bound to stdin with empty
input, decoded length, ReturnsTo, HtifRetAt bytes[], OsStep and ConsoleAt.
State caller facts explicitly, with no assumed run/post or boot-only R.
Done: both paths built, all new public axioms standard-only, targeted generator,
discipline/abstraction checks, clear remaining fstat/persistence/resource seams.
Leave full check.sh to lead; poll long builds every 45 seconds.

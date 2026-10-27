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

Target: prove the real _write(2, buf, n) console run needed by FprintfErr,
and connect it to the OS stderr write relation beside the stdout bridge.
Files: Kit/Write.lean, new Kit/WriteStderr.lean if useful, Os/ConsoleWrite.lean,
scripts/gen_lua_{arms,at}.py only as needed, lane ledger/check.sh/PHASES.
Reuse write_loop, write_putc, wrMem/wrRet and osStep_write_full. Factor any
common prefix/frame reasoning; do not duplicate the byte loop or console seam.
Use generated segments/callee-context rows for the fd=2 prefix; retain the
existing write_sum API and semantics. A common console descriptor summary is
welcome when it simplifies both fd=1 and fd=2, without weakening preconditions.
State honest initialized descriptor-table, buffer/frame and ABI preconditions.
Done: finite Sail Steps for arbitrary n including zero, exact console append,
return n, ABI and memory frames; matching HtifCallAt/HtifRetAt/OsStep bridge;
capped target builds and new standard-only axiom checks, relevant static checks.
Do not claim FprintfErr or global HtifPrint is closed by this boundary result.
Private dependency caches are now seeded by the launcher, so lake build is safe.
Await builds completely; keep logs outside source and report exact commands.
Resume: draft is preserved in WIP 908aa37; finish it, do not restart.
Prior build /tmp/sol-1-write-build.log has kit_run failures at Write:317/323.
Static gate already passed; fix guards, finish builds and axiom checks.
For long builds, poll at 45-second intervals with concise output.

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

Target: retain FprintfPre's stderr state and pointer across stdout print.
Files: Sim/StdioState, Kit/Sinit,StdoutSetup,StdoutEmpty,Unwind and transport
consumers; lane ledger/PHASES/check.sh. Read f1-unwind-plan.md first.
Move pure FileStd/ErrStd below execution modules; avoid Unwind import cycles.
StdioBoot already supplies stderr's pointer and zeroed FILE region.
Strengthen StdioRest with the unchanged stderr FileStd/tail and _REENT pointer;
extend RestFoot and congrT, and establish them from the real sinit run.
ErrStd.tail is [88,176); current SinitPost.tail stops at 168. The actual
lock-init helper is ret; prove the extra preservation without weakening ErrStd.
Use the existing StdoutIn fresh/up and frame transports across prints.
Expose StdoutIn accessors giving stderr_ptr for all phases and ErrStd for
non-boot phases, usable by FprintfPre; no new CallOpen/ErrorSim premise.
Keep StdQuiet's exit API as a consequence or retained compatible field.
Done: affected capped Sinit/StdoutSetup/PrintIO/CallPrint/Unwind builds,
standard-only public axioms and generator/discipline/abstraction checks.
Full fprintf execution and pcall remain open; leave full check.sh to lead.
Poll long builds every 45 seconds.

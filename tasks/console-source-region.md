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

Target: let the proved console-write stack consume .rodata fragments as
well as heap buffers, so fprintf's literal pieces meet real preconditions.
Files: Kit/Write.lean, WriteBoot.lean, Swrite.lean and shared frame modules;
generators only if required; ledger/PHASES/check.sh audits.
First inspect WrFrame.buf_lo and WrrCtx.buf_lo: they exclude .rodata below
tohost/errno. Reuse the scan summaries' below-or-above-MMIO source separation
and the existing range/Agree abstractions; do not special-case one literal.
Generalize the common source contract to RAM bytes apart from MMIO, the
saved frames, errno, FILE flags and lazy-init stores, wherever actually needed.
Retain old stdout APIs as corollaries. Cover both console fds, both ready/lazy
paths, and every count within address bounds, including zero.
Prove output reads the entry bytes and retain exact/presence/ABI frames.
Use one loop and the existing generated paths; do not duplicate summaries
or solve the issue by assuming a whole formatted-output conclusion.
Done: capped affected builds plus stdout consumers, standard-only public
axiom audit and targeted static checks. Include a checked instantiation for
a .rodata literal's region, not an execution-only regression test.
Keep the complete FprintfErr/global OS statements open. Leave full check.sh
(including static-only) to the lead. Poll long builds at 45-second intervals.

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

Target: prove _dtoa_r's complete result-release prefix, entry 0x8004a760
to 0x8004a7d0, including NULL and non-NULL prior results.
Files: gen_lua_{code,arms,at}.py, generated DtoaRelease modules, a Kit
summary/ownership lift, EntryData only for reusable laws, ledger/check.sh.
First inspect the ELF prefix and Bfree/BfreeHeap; reuse their machine run,
ledger permutations, bounded-cache transport and zero-fill helpers.
The real sequence restores result _k/_maxwds at 0x8004a7c0/4, calls
_Bfree at 0x8004a7c8, then clears _result at 0x8004a7cc. ReentMp cannot
hold between push and clear. Prove the ownership transfer across the
whole prefix from the actual input ledger; no assumed output invariant.
Generate paths/runs, preserve live caller registers and exact stack stores,
and expose the join context for later dtoa paths. Prove zero-growth BigRun
with result removed and pushed into its class, cache/other owners preserved.
Respect sllw's 32-bit shift: ReentMpAt.res_k <=64 alone does not justify
2^rk. Derive rk<32 from physical ownership bounds if possible, or name
that honest input bound explicitly and record the remaining reachability fact.
Done: both machine paths and ownership, capped target builds, standard-only
axioms, targeted generator/discipline/abstraction checks, accurate ledger.
No claim of full dtoa or FloatToStr. Leave full check.sh to the lead.
Poll long builds at 45 seconds; do not dump whole inventories or replay logs.

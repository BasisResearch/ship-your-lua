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

Target: establish the actual string __unm lookup boundary from the boot
invariant through luaT_gettmbyobj's ABI return; full UnmStr remains open.
Files: Env/Getshortstr shared lookup, EntryData/Boot checks/StatFacts,
gen_lua_boot_witness.py, generated helper/at-runs, ledger/PHASES/check.sh.
Read f1-unm-lookup-plan.md. Existing StrMtMiss proves __tostring absence,
not the __unm function. Observed boot addresses are inputs to kernel checks.
Factor direct table/key success context and summary from getshortstr_sum;
reuse shrWalk/gs_loop, retaining the old Env API as a corollary, no copied walk.
Prove generated string prefix at0x8001917c and compose its tail to getshortstr;
return actual node with vLcf payload arith_unm from a named checked invariant.
Freeze the g->mt[4], tmname[18], key/hash and lookup-node footprint in the
relation; establish boot/VARARGPREP and preserve across CALL with existing frames.
No fake closure, hard-coded two-node machine walk, assumed run, or new open premise.
Coordinate after other invariant edits land; preserve their fields and accessors.
Done: affected capped builds including old lookup/boot/CallPrint consumers,
all public standard-only axioms, generator drift/discipline/abstraction checks;
register explicit standalone target/audits. Leave full check.sh to lead.
Record remaining metamethod C-call, integer/float conversion and result-copy work.

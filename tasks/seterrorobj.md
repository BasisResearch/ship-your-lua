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

Target: prove luaD_seterrorobj's LUA_ERRRUN (status 2) machine summary,
a concrete PcallErr helper, from actual entry 0x80009984 through ret 0x800099bc.
Files: gen_lua_at/code/arms generators, standalone generated helper modules,
Kit/SetErrorObj.lean, focused ledger, PHASES/CLAUDE/check.sh as appropriate.
First inspect vendor/lua-5.4.7/src/ldo.c and ELF disassembly; inventory existing
TValue copies/memory-frame helpers and reuse them. Generate instruction proofs.
The helper copies payload+tag from L->top-16 to oldtop, then sets L->top=oldtop+16.
Give named entry/post structures, exact stores/frame, actual finite Sail steps,
ABI/console preservation and a semantic TValue/string-message preservation lemma.
Allow oldtop equal to the source slot (normal alias case), and distinct aligned
stack slots; require honest separation from L's top field, RAM and MMIO bounds.
Do not assume a run/post, add a Core premise, or claim full PcallErr discharged.
Keep code pins/arms standalone to avoid an unrelated aggregate rebuild.
If a reusable copy-frame abstraction is missing, factor it once, not per branch.
Done: affected capped builds, standard-only audit of public theorems, targeted
generator/discipline/abstraction checks; exact remaining unwind premises recorded.
Leave full check.sh to lead. Poll long builds every 45 seconds.

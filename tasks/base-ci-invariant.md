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

Target: establish and preserve the base CallInfo fields needed by PcallErr,
using a named BaseCiAt-style region invariant and the existing boot checks.
Files: Vm/Runtime,EntryData,Boot/Check, Sim/Rel,Entry, Kit/CallClose,
gen_lua_boot_witness.py and related constructors; ledger/PHASES/check.sh.
First inspect experiments/unwind/boot-ci.py and f1-unwind-plan.md; observations
are not proofs. Check stack_init and relstack/correctstack in the C source.
Fields at L+stateBaseCiOff: func=rt.stack, top=rt.stack+21*stackValueSize,
previous=0, next=current Lua ci, callstatus=CIST_C (use layout constants).
Prove the fields at boot and after VARARGPREP through kernel boot witnesses;
keep them in StatFacts' frozen region, included in luaStaticWords/footprint.
Transport through CALL using its existing frame; do not introduce a new
open premise or assume BaseCiAt at PcallErr. A companion StatFacts field
can carry ci without expanding the LuaStatic parameter list unnecessarily.
Keep exact ownership/separation and current Loaded/semantic scope honest.
Done: affected capped builds including boot witnesses, Entry and CallPrint,
standard-only public axioms, generator drift/discipline/abstraction checks.
Do not claim reallocstack or full PcallErr; record the new invariant's accessor.
Leave full check.sh to lead; poll long builds every 45 seconds.

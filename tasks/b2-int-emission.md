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

Target: implement and prove the semantic integer-literal emitter for B2,
matching vendored lcode.c luaK_int's LOADI versus LOADK selection.
Files: new Lua/Compile/IntEmit.lean (and a small boundary-check module if
needed), Encode.lean only for shared signed-Bx laws, Lua.lean, PHASES/ledger/audits.
First read lcode.c fitsBx/luaK_int and the existing Encode checked constructors.
Use the exact signed-Bx range [-65535,65536], full BitVec64 integer inputs,
and a supplied constant index for the fallback. Reject encoded overflow;
LOADKX is outside the current bytecode semantics, so keep its branch explicit
as remaining work rather than pretending a one-word emitter covers it.
Prove generic decoding and opKernel/step laws: the emitted instruction loads
the intended integer, advances pc correctly, and preserves other registers
and output under honest fetch/register/constant-reference preconditions.
No premise may assume the desired execution or just validate a finite corpus.
Factor shared signed-Bx/constant-load reasoning; reuse the kernel abstraction.
Cross-check selector/boundary vectors against the vendored host luac listing.
Done: capped affected builds, standard-only public axiom audit, targeted
static checks, root build registration, and accurate B2 ledger. CompileTV,
constant interning/register allocation, the full compiler and B3 stay open.
Leave full check.sh (including static-only) to the lead. Poll long builds at
45-second intervals; do not dump replay warnings or whole inventories.

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

Target: prove the actual luaK_codeABx wrapper computes Encode.abx and
tail-jumps to luaK_code with that word, a first local B3 refinement.
Files: Compile/Machine/CodeABx.lean, established code/segment/at generators,
ledger b3-codegen-plan.md, PHASES/check.sh. Read that plan first.
ELF entry 0x80005d44, five instructions, tail destination 0x80005b20.
Use generated segments/rows (no hand site proof or copied expression walk).
Quantify over Opcode, A<256, Bx<131072 and the actual SegSt entry; preserve
fs/a0, ra, sp, gp, all callee-saved regs, memory and console exactly.
The output a1 is SIGN extension of the 32-bit instruction (slliw),
not zero extension: include upper-half Bx and maximum-boundary validation.
Relate it to existing Encode.abx/field lemmas, not a new competing encoding.
Name the tail boundary explicitly; no assumed callee run or whole compiler claim.
Done: capped target build, all public standard-only axioms, targeted generator,
discipline/abstraction checks and ledger stating luaK_code/B2/B3 still open.
Leave full check.sh to lead; poll long builds every 45 seconds.

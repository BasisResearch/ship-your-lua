# ship-your-lua status

Resumed 2026-10-27. Target: discharge the premises of `endToEnd_lua`
without new axioms, admitted proofs, or weakened semantics.

## Integration

`origin/main` is at `7211f98`. F1-25 is already published and fully gated.
Two full gates run on frozen proof sources and private caches:

| Batch | Checkout / proof head | State |
|---|---|---|
| Main | root / `7893933` | Full Lean build passed; OS harness descriptor fix passes focused traces; full gate retry pending |
| Next | `.claude/worktrees/lane-f1-26` / `17b2fea` | Static stages pass; full build running before OS traces and axiom audit |
| Queue | `.claude/worktrees/agent-a5c594d418908fc64` / `8575872` | Reviewed checkpoints combined; merged targeted generator checks pass; full gate not started |

Main's batch includes F1-26's exit-after-error proof and import-cycle repair,
checked B2 encoding/jump patching, stdout/stderr OS write bridges,
heap-preserving free, and the Bfree machine/ownership summaries.
Later commits include documentation, tasks, probes and a host trace-driver
descriptor isolation fix. Proof sources remain at the checked revision.
The first gate stopped at OS traces because the driver inherited fd 8
from the build lock; the fixed focused suite has zero rejections. Publish
after the full retry, including the axiom audit, passes.

Next's batch adds lazy console initialization, cached Balloc ownership,
the explicit empty-output OS boot contract, dtoa result release and
stderr hooks. Target builds and standard-only axiom audits pass for each.
Publish after its full gate and integration into main.

Queue's reviewed checkpoints:

| Original commit | Result | Focused validation |
|---|---|---|
| `fb3a27a` | Checked integer LOADI/LOADK emission and semantics | Target builds; 16 axiom reports |
| `e23fff3` | Actual realloc shrink, resulting heap and surviving payloads | 1258-job target build; 12 axiom reports |
| `ed43110` | Status-2 error-object copy and semantic TValue transport | 509-job target build; 95 axiom reports |
| `d6df854` | Console source regions and shared write frames | Final targets: 511 jobs; 93 axiom reports |
| `133c511` | Ready/lazy stdin EOF machine run and OS bridge | 506-job target build; 194 axiom reports |
| `ddd2f95` | ELF luaK_codeABx wrapper refines bitfield encoding | 481-job target build; 19 axiom reports |
| `ecff107` | Arbitrary calloc-capacity memset and exact byte frame | 539-job affected build; 27 axiom reports |

All listed axiom sets are standard-only. Applicable generator, discipline
and abstraction checks pass. The console source change's final broad
consumer check is consolidated into the queue gate; an earlier consumer
pass preceded final shared-helper edits. No queued checkpoint has passed
its combined full gate yet.

## Active lanes

| Lane | Checkout | Current target |
|---|---|---|
| Lead | main, next, queue | Review, full gates, integration and publication |
| Sol slot 1 | `.claude/worktrees/sol-1` | Actual successful `_calloc_r`, including full physical-capacity zeroing and old-allocation frames |
| Sol slot 2 | `.claude/worktrees/sol-2` | Preserve successor CallInfo's terminal NULL link through allocation, reuse and call_close |

Ready follow-ups cover base CallInfo invariants, successor allocation
ownership, stderr state, fresh Balloc, mutable integer constant pools,
and console fstat. Each has a scoped task and supporting ledger audit.
Do not reassign completed or recorded dead ends unchanged.

Workers are external `codex exec -m gpt-6.1-sol` processes at high reasoning,
at most two. Each Lean run is capped at 12 GB, one build per worktree;
project and dependency build caches are private. `codexwork.sh` and
`MANAGER.md` define the workflow. Read-only worker Git metadata is handled
by the lead after review and does not require a user decision.

Old worktrees have been audited. Preserved handoff branches correspond to
integrated snapshots. The obsolete A-TREE experiment remains unmerged
because A-JOIN was adopted; its report is already on main. Untracked
scratch directories are preserved.

## Remaining obligations

- Layer A: `CallOpen.floatToStr`, `ErrorSimRest`, `UnmStr_Statement`,
  `FpStrFlt_Statement` (the remaining FORPREP coercion premise), `MMBIN`,
  `MMBINI`, `MMBINK`, `CONCAT`, and `CALL_heap`. F1-25 derives list-level
  PrintFlt/PrintFn from float formatting; formatting remains open.
- Layer B: `CompileTV` for a Lean compiler, then the ELF parser/code
  generator refining it. Corpus translation validation is proved.
- OS: `HtifPrint_Statement` and resource-bounded, framed `HtifFs_Statement`.
  Local syscall summaries do not discharge the global relation premises.

## Needs user

None.

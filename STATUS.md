# ship-your-lua status

Lead takeover: 2026-10-21; resumed 2026-10-27. Goal: discharge the premises of `endToEnd_lua`
without new axioms, admitted proofs, or weakened semantics.

## Integration

- F1-25 is merged and pushed as `d09b792`. Full `scripts/check.sh` passed
  under a 12 GB scope: generators, ELF/no-ecall, discipline, abstraction,
  WHILE exclusion, build, OS traces and standard-only axiom audit.
- F1-26 is reviewed through `17c714e`: the exit-after-error proof passes
  targeted builds and axiom checks, with its import cycle repaired and
  named witnesses added. It is integrated locally with the B2 encoding
  and stdout bridge checkpoints. The thread-limit failure is repaired: all
  four aborted modules build with explicit `-j1` frontend scheduling.
  The combined full gate now runs on `7893933`, including the stronger
  free summary, stderr bridge and Bfree ownership lift, before publication.
- Other existing worktrees are merged ancestors, except the old A-TREE
  bake-off branch. Its report is already on main (`b2d98dd`); A-JOIN was
  adopted instead, so the obsolete implementation will not be merged.
  Untracked scratch directories are preserved.

## Active lanes

| Lane | Worktree | Work |
|---|---|---|
| Lead / integration | main and `.claude/worktrees/lane-f1-26` | Run both full gates on isolated sources and private caches |
| Sol slot 1 / console source regions | `.claude/worktrees/sol-1` | Allow initialized/lazy console writes from read-only data and factor pure imports |
| Sol slot 2 / successor CallInfo invariant | `.claude/worktrees/sol-2` | Retain nci->next = NULL through allocation, reuse and call_close |

Reviewed checkpoints:

- `e5fbe8c`: `_Bfree` machine run, exact stores and owned-chain push;
  target build, full static gate and nine axiom checks pass. Integrated locally; combined full gate pending.
- `405ff77`: stronger free summary, resulting heap and surviving payload
  frame; four modules and ten axiom checks pass. Integrated locally; combined full gate pending.
- `0e5af27`: checked B2 instruction emission and signed jump patching;
  exact semantic jump target, unchanged code length and other instructions.
  C-macro boundary vectors and all 21 public axiom checks pass.
- `11fdb6d`: the actual stdout `_write` run refines a full TCB write,
  with ABI return and console agreement. Three axiom checks and both
  affected OS modules pass; global OS premises remain open.
- `17c714e` (over `38da244`): F1-26 import-cycle fix, named error-boundary
  witnesses, complete lane ledger. `Unwind`/`StuckErr` build; all eleven new
  axiom checks pass. Pcall and fprintf are still named premises.

Preserved handoff branches `codex-layer-b` (`43441ae`) and `codex-os`
(`190aeb2`) correspond to integrated snapshots `8ee5368` and `7893933`.
Their WIP history is not additional unmerged proof work.

Workers run as separate `codex exec -m gpt-6.1-sol` processes, high reasoning
effort, at most two. The initial built-in subagents have stopped; their drafts
are preserved for the Sol workers. `codexwork.sh` and `MANAGER.md` document
the workflow; `abstractions/DEAD-ENDS.md` records failed approaches.

Every Lean run is capped at 12 GB. Each worktree has at most one Lake build.
Generated files are changed through their generators. Landing requires the
applicable generator, discipline, abstraction, build, and axiom checks.

Latest local proof commits: `8ee5368` (stderr), `7893933` (Bfree ownership).
Both worker static gates passed. Bignum consumer validation is consolidated
into the main full gate; its redundant worker build was stopped.
The lazy console write is reviewed at `c5758e7`: target/consumer builds,
generator and discipline checks, and all 27 axiom reports pass. It awaits
the next integration. Stderr hooks are reviewed at `5717060`: all stdout
and formatter consumer builds, targeted static checks and 36 standard-only
axiom reports pass. Slot 1 completed integer emission at `fb3a27a` and now widens console source regions. Cached Balloc is
reviewed at `5ac09e4`: generated machine run, ownership transfer, affected
builds, targeted static checks and all 26 axiom reports pass. It also awaits
integration (rebased equivalent `9e40987`). The OS boot-output repair
`d425afd` is also reviewed: affected builds, 19 OS axiom reports and targeted
static checks pass. It explicitly requires empty initial output and proves
the old contract mismatch; global OS premises remain open. Slot 2 now
has completed dtoa result release at `098f68c`: both generated machine
paths, restored ownership, derived class bound, and zero-growth BigRun pass
the target build, all 22 axiom reports, and static/full at-generator checks.
It is prepared in `integration-next`. Slot 2 completed realloc shrink at
`e23fff3`: both shrink paths, actual Sail steps, retained requested prefix,
resulting heap and other live payloads pass affected builds, twelve standard-only
axiom reports and targeted static checks. The allocator seam awaits integration;
PcallErr composition remains open. The error-object helper is also reviewed at `ed43110`: status-2 machine
run, exact payload/tag/top stores, alias case, semantic TValue transport,
target builds and all 95 standard-only public axiom reports pass.
Slot 2 now retains the terminal successor CallInfo fact in the relation.
Integer emission `fb3a27a` likewise awaits a later integration gate: checked
LOADI/LOADK selection and generic load semantics pass target builds, sixteen
standard-only axiom reports and targeted checks. LOADKX and the full compiler
remain open.

The idle F1-26 checkout now holds `integration-next`, with the reviewed
lazy-write, cached-Balloc, boot-contract, dtoa-release and stderr-hook
checkpoints merged. Its full gate runs on `17b2fea` under a separate 12 GB
scope, using CPUs 9/10; main continues on its unchanged proof sources
using CPUs 17/25. Both checkouts have private caches. No new checkout/cache
copy was needed. Publication waits for the applicable complete gate.

`integration-queue` in the idle `.claude/worktrees/agent-a5c594d418908fc64`
checkout combines the next batch with reviewed integer emission and realloc
shrink. Only discipline-table entries and build/audit lists conflicted;
the resolution retains both lanes. No build runs there yet. The status-2 error-object
helper is now combined at `50b4d86`; all standalone generator registrations
were retained, and the merged code/target-arm/target-at checks pass.
Console source regions will join after review. The queue's project and
three local dependency caches are separate from main.

## Remaining obligations

- Layer A: `CallOpen.floatToStr`; `ErrorSimRest`; string coercion
  (`UnmStr_Statement`, `FpStrFlt_Statement`, the latter supplying the
  remaining `FORPREP` premise); `MMBIN`, `MMBINI`, `MMBINK`, `CONCAT`, and
  `CALL_heap` (table resizing and emergency GC beyond allocation room).
  F1-25 derives both list-level print statements from float formatting;
  they are not independent discharged formatting proofs.
- Layer B: `CompileTV` for a Lean compiler and the ELF parser/code generator
  refining that compiler. Corpus translation validation is already proved.
- OS: `HtifPrint_Statement` and resource-bounded, framed `HtifFs_Statement`.

## Needs user

None.

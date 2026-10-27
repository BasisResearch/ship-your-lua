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
| Lead / integration | main and `.claude/worktrees/lane-f1-26` | Gate current main; prepare `integration-next` independently |
| Sol slot 1 / stderr hooks | `.claude/worktrees/sol-1` | Lift both initialized and lazy writes through `_write_r` and `__swrite` |
| Sol slot 2 / realloc shrink | `.claude/worktrees/sol-2` | Port in-place shrink with retained prefix and surviving heap payloads |

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
the next integration; slot 1 now handles stderr hooks. Cached Balloc is
reviewed at `5ac09e4`: generated machine run, ownership transfer, affected
builds, targeted static checks and all 26 axiom reports pass. It also awaits
integration (rebased equivalent `9e40987`). The OS boot-output repair
`d425afd` is also reviewed: affected builds, 19 OS axiom reports and targeted
static checks pass. It explicitly requires empty initial output and proves
the old contract mismatch; global OS premises remain open. Slot 2 now
has completed dtoa result release at `098f68c`: both generated machine
paths, restored ownership, derived class bound, and zero-growth BigRun pass
the target build, all 22 axiom reports, and static/full at-generator checks.
It is prepared in `integration-next`; slot 2 now handles realloc shrink.

The idle F1-26 checkout now holds `integration-next`, with the reviewed
lazy-write, cached-Balloc, boot-contract and dtoa-release checkpoints merged. Its gate
has not started; stderr hooks will join after worker validation. The main
gate continues on unchanged proof sources. No new worktree/cache copy was needed.

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

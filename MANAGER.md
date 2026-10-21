# Manager workflow

The lead plans, reviews, and lands. Proof workers run as separate
`codex exec -m gpt-6.1-sol` processes at high reasoning effort; built-in
subagents are not used for proofs. At most two workers run for this project.

Launch `./codexwork.sh 1 tasks/<task>.md > /tmp/syi-sol-launch-1.log 2>&1 & wait`
in a persistent execution session (or slot 2). The launcher checks memory, locks the slot, preserves dirty
work, rebases its worktree on main, seeds private project/dependency caches, and records `logs/sol-<slot>-<time>.log`.
Tasks start with `tasks/RULES.txt` verbatim and stay below 40 lines: one
target, its files, first step, and explicit completion criteria.

Every Lean run uses `scripts/lean-capped.sh`: a 12 GB systemd scope,
single CPU affinity to avoid shared-host thread exhaustion, and one run
per worktree. The launcher establishes a 12 GB scope before entering the
worker sandbox; the wrapper verifies inherited scope membership because
`workspace-write` cannot contact the user systemd bus. The lead checks
`free -g` before launching each worker.

A worker's `RESULT: landed <commit>` means committed on its branch, awaiting
review. This host's sandbox protects Git metadata even with `--add-dir`;
workers can hand validated files to the lead for the branch commit. This
does not block proof work or require a broader sandbox. Await running builds;
if a worker exits with children still holding its build lock, the manager
stops that worker’s named systemd scope before resuming validation. Only the lead merges
and pushes `origin/main`, after the repository
gate; never force-push. Record failed approaches in `abstractions/DEAD-ENDS.md`
before issuing another task. Keep `STATUS.md`, including `## Needs user`, current.

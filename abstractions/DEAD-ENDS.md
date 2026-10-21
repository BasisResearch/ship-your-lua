# Approaches not to repeat unchanged

- 2026-10-21: worker Git metadata is intentionally read-only under the
  requested sandbox. Finish proof validation and hand ready files to the
  manager for commits; do not stop the lane merely because `git add` fails.

- 2026-10-21: `systemd-run --user` inside `workspace-write` cannot contact
  the user bus. Establish the 12 GB scope in `codexwork.sh` before entering
  the sandbox; `lean-capped.sh` verifies inherited scope membership.

- 2026-10-21: uncapped CPU discovery in Lean caused `failed to create thread`
  on this shared host (~4,900 threads). `LEAN_NUM_THREADS=2` alone did not
  avoid it. Use `scripts/lean-capped.sh` with CPU affinity and 12 GB systemd cap.
- F1-26 audit: importing `Kit.Unwind` in the `Kit` index creates
  `Kit -> Unwind -> ErrTail -> Fold -> Kit`. Import it only at `StuckErr`.
- Round 5: A-TREE was not adopted; main already contains its report via
  `b2d98dd`. Use adopted A-JOIN/B-SFREF, not a wholesale merge of `588eaa8`.
- F1-F9/F1-25: a `strtod`/`_dtoa_r` summary claiming the heap is unchanged
  is false. Bignum calls must carry `BigRun` and `_REENT` free-list ownership.
- B-S3: unrestricted host-folded constant `^` disagrees with ELF newlib
  `pow`; preserve `powOk` and the checked `powFold_counterexample`.

- 2026-10-21: cancelling a sandboxed build wrapper can leave Lake children
  in the worker's outer systemd scope, invisible from later sandbox PID
  namespaces. Do not start a second build or loop on its lock. Preserve the
  diagnostic and have the manager stop the completed worker's own scope.
  A partial cache may then need missing artifacts restored before validation.

- 2026-10-21: sharing writable dependency-cache symlinks lets Lake rebuild
  another worktree's inputs. The launcher now seeds private dependency
  caches as well as private project output before each new worker starts.

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

- Bignum ownership: `ReentMpAt.p5v` describes values but does not bound a
  cache node's `_wds` by its capacity. `BigChain` only pins class/maxwds.
  Do not derive a digit-read footprint from those fields alone; establish
  a bounded shape/footprint fact before transporting the power-five cache.

- `_dtoa_r` result release is a multi-instruction ownership boundary:
  the pinned ELF restores `_k`/`_maxwds` at 0x8004a7c0/0x8004a7c4, calls
  `_Bfree` at 0x8004a7c8, then clears `_result` at 0x8004a7cc. A full
  `ReentMp` cannot hold between that call and the clear: the same block
  is still the result and is now on the freelist. Use the exact-store
  primitive across the whole release prefix; the active-block `_Bfree`
  ownership lemma assumes the returned block is apart from existing owners.

- 2026-10-27: CPU affinity and `LEAN_NUM_THREADS=1` alone still let the
  Lean frontend hit a scope task cap (128 tasks, `pids.events: max 3`).
  Use package `weakLeanArgs = ["-j1"]` to bound elaborator threads too;
  changing scheduling must not change proof budgets or trust settings.

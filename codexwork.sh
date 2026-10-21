#!/usr/bin/env bash
# One Sol worker per slot; the lead reviews and merges worker commits.
set -euo pipefail
repo=$(cd "$(dirname "$0")" && pwd)
slot=${1:?usage: codexwork.sh SLOT TASKFILE}
[[ $slot == 1 || $slot == 2 ]] || { echo 'Only slots 1 and 2 are allowed'; exit 2; }
task=$(realpath "${2:?task file required}")
[[ $(wc -l < "$task") -lt 40 ]] || { echo 'Task must be under 40 lines'; exit 2; }
rules="$repo/tasks/RULES.txt"
head -n "$(wc -l < "$rules")" "$task" | cmp -s "$rules" - || {
  echo 'Task must start with tasks/RULES.txt verbatim'; exit 2;
}
mkdir -p "$repo/logs"
exec 9>"$repo/logs/slot-$slot.lock"
flock -n 9 || { echo "Slot $slot already running"; exit 2; }
log="$repo/logs/sol-$slot-$(date -u +%Y%m%d-%H%M%S)-$$.log"
wt="$repo/.claude/worktrees/sol-$slot"
echo "$log"
exec > >(tee -a "$log") 2>&1
trap 'rc=$?; if (( rc != 0 )); then echo "RESULT: stuck launcher exit $rc (see log)"; fi' EXIT
free -g
available=$(free -g | awk '/^Mem:/ {print $7}')
(( available >= 25 )) || { echo 'RESULT: stuck available memory below 25 GB'; exit 1; }
if [[ ! -d $wt ]]; then
  git -C "$repo" worktree add -b "sol-$slot" "$wt" main
fi
[[ -z $(git -C "$wt" ls-files -u) ]] || { echo 'RESULT: stuck unresolved conflicts'; exit 1; }
git -C "$wt" diff --quiet && git -C "$wt" diff --cached --quiet || {
  echo 'RESULT: stuck tracked edits need manager review before rebase'; exit 1;
}
git -C "$wt" rebase main || { echo 'RESULT: stuck rebase (work preserved)'; exit 1; }
# Private project and dependency outputs prevent a worktree's Lake rebuild
# from changing the inputs of another build. Replace only old cache symlinks.
seed_private() {
  local src=$1 dst=$2
  if [[ -L $dst ]]; then unlink "$dst"; fi
  if [[ ! -e $dst ]]; then
    mkdir -p "$(dirname "$dst")"
    cp -a --reflink=auto "$src" "$dst"
  fi
}
seed_private "$repo/.lake/packages" "$wt/.lake/packages"
seed_private "$repo/.lake/build" "$wt/.lake/build"
seed_private "$repo/riscv-lean/lean_emulator/.lake" "$wt/riscv-lean/lean_emulator/.lake"
printf 'Task: %s\nWorktree: %s\nStart: %s\n' "$task" "$wt" "$(date -u --iso-8601=seconds)"
codex_bin=${CODEX:-$HOME/.local/share/codex-0.162.0/node_modules/@openai/codex-linux-x64/vendor/x86_64-unknown-linux-musl/bin/codex}
rc=0
scope="syi-sol-$slot-$$"
systemd-run --user --scope --unit="$scope" -p MemoryMax=12G -p TasksMax=256 \
  env LUA_WORKER_SCOPE="$scope" "$codex_bin" exec -m gpt-6.1-sol -c 'model_reasoning_effort="high"' \
  -s workspace-write --add-dir "$repo" -C "$wt" "$(cat "$task")" || rc=$?
printf 'Worker exit: %s\nEnd: %s\n' "$rc" "$(date -u --iso-8601=seconds)"
# The worker's RESULT is authoritative; never infer success from exit status.
result=$(grep -E '^RESULT: (landed |stuck )' "$log" | tail -1 || true)
echo "${result:-RESULT: stuck worker supplied no result; inspect log}"

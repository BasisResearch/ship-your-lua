#!/usr/bin/env bash
# Invoke from the target worktree: /absolute/path/scripts/lean-capped.sh lake build Module
set -euo pipefail
root=$(git rev-parse --show-toplevel)
mkdir -p "$root/.lake"
exec 8>"$root/.lake/lean-run.lock"
flock -n 8 || { echo 'Another capped Lean run owns this worktree'; exit 2; }
free -g
available=$(free -g | awk '/^Mem:/ {print $7}')
(( available >= 25 )) || { echo 'Available memory below 25 GB; retry later'; exit 2; }
cpu=$(awk '/Cpus_allowed_list/ {split($2,a,/[-,]/); print a[1]}' /proc/self/status)
# Give the two worker slots separate CPUs when this host permits it.
case ${LUA_WORKER_SCOPE:-} in
  syi-sol-1-*) candidate=1 ;;
  syi-sol-2-*) candidate=2 ;;
  *) candidate=$cpu ;;
esac
if taskset -c "$candidate" true 2>/dev/null; then cpu=$candidate; fi
# workspace-write cannot create scopes through the user bus. The launcher
# already placed this worker and all descendants in a 12 GB systemd scope.
if [[ -n ${LUA_WORKER_SCOPE:-} ]] && grep -Fq "/${LUA_WORKER_SCOPE}.scope" /proc/self/cgroup; then
  exec taskset -c "$cpu" env LEAN_NUM_THREADS=1 "$@"
fi
exec systemd-run --user --scope -p MemoryMax=12G -p TasksMax=128 \
  taskset -c "$cpu" env LEAN_NUM_THREADS=1 "$@"

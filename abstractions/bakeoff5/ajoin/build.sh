#!/usr/bin/env bash
# Round 5 bake-off, A-JOIN: the one full build (`lake build Lua Vsa VsaIris`)
# under a 12 GB cap. Lake builds independent modules in parallel, which
# exceeds 12 GB when a kit file the at-route imports changed; so the stale
# modules are first built one at a time in import order (each `lake build`
# then compiles one module), then the full build confirms.
#   bash abstractions/bakeoff5/ajoin/build.sh > abstractions/bakeoff5/ajoin/build.out 2>&1
here="$(cd "$(dirname "$0")" && pwd)"
cd "$here/../../.."
wait_mem() { until [ "$(grep 'Mem:' ~/syi-mem.log | tail -1 | awk '{print $NF}')" -ge 25 ]; do sleep 10; done; }
date
start=$(date +%s)
python3 - <<'PY' > "$here/.order"
import re, pathlib
mods = {}
for f in pathlib.Path("Lua").rglob("*.lean"):
    m = ".".join(f.with_suffix("").parts)
    mods[m] = [i for i in re.findall(r"^import (\S+)", f.read_text(), re.M) if i.startswith("Lua.")]
seen, order = set(), []
def visit(m):
    if m in seen or m not in mods:
        return
    seen.add(m)
    for d in mods[m]:
        visit(d)
    order.append(m)
import sys
sys.setrecursionlimit(100000)
for m in sorted(mods):
    visit(m)
print("\n".join(order))
PY
n=0
while read -r m; do
  case "$m" in Lua.Vm.Sim.Kit*|Lua.Vm.At.*|Lua.Vm.AtF.*|Lua.Vm.Sim.*|Lua.Vm.Arms.Segs.*|Lua.Vm.Fn.*) ;; *) continue;; esac
  wait_mem
  out=$(systemd-run --user --scope -p MemoryMax=12G -q lake build "$m" 2>&1)
  if ! echo "$out" | tail -1 | grep -q "Build completed successfully"; then
    echo "FAILED: $m"; echo "$out" | grep -A20 "error" | head -40; n=$((n+1))
  fi
done < "$here/.order"
wait_mem
/usr/bin/time -f "full build: USER %U s  WALL %e s  PEAK %M KB" \
  systemd-run --user --scope -p MemoryMax=12G -q lake build Lua Vsa VsaIris > "$here/.full" 2>&1
tail -1 "$here/.full"
grep "full build" "$here/.full"
echo "module failures: $n; wall $(( $(date +%s) - start )) s"
date

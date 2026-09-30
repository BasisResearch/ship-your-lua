import Lean
open Lean

/-- usage: RevDeps.lean <out> <targetsFile> <mod>... : every constant of the
given modules that transitively depends on one of the target constants
(one per line in targetsFile). Output `module\tconst`. -/
partial def main (args : List String) : IO Unit := do
  let out := args[0]!
  let targets : Std.HashSet Name := ((← IO.FS.readFile args[1]!).splitOn "\n"
    |>.filter (· ≠ "") |>.map String.toName).foldl (·.insert ·) {}
  let ms := (args.drop 2).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (ms.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let modOf (c : Name) : Name := match env.getModuleIdxFor? c with
    | some j => modNames[j.toNat]!
    | none => .anonymous
  let msSet : Std.HashSet Name := ms.foldl (·.insert ·) {}
  let memo ← IO.mkRef (∅ : Std.HashMap Name Bool)
  let rec dep (c : Name) (fuel : Nat) : IO Bool := do
    if targets.contains c then return true
    if let some b := (← memo.get)[c]? then return b
    if fuel == 0 then return false
    unless msSet.contains (modOf c) do return false
    memo.modify (·.insert c false)
    let some ci := env.find? c | return false
    let used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    let mut r := false
    for u in used do
      if ← dep u (fuel - 1) then r := true; break
    memo.modify (·.insert c r)
    return r
  let h ← IO.FS.Handle.mk out .write
  for m in ms do
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      if ← dep c 100000 then h.putStrLn s!"{m}\t{c}"
  h.flush

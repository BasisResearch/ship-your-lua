import Lean
open Lean

/-- usage: lean --run Closure.lean <outfile> <taintedListFile> <targetMod>...
  Seeds: all constants defined in the target modules. Transitive closure
  over directly-used constants, not descending into modules outside the
  tainted list (those are clean). Prints `Module\tconst` for every
  reached constant that lives in a tainted-list module or a WHILE root, plus
  for each such constant one referrer (`via`). -/
def isRoot (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Vsa.While." || s == "Vsa.MemRepr" || s == "Vsa.MemReprReadArrays" ||
  s == "Vsa.MemReprReadChildren" || s == "Vsa.MemReprReadFields" || s == "Vsa.MemReprWithin" ||
  s == "Vsa.RuntimeRepr" || s == "Vsa.ElfBytes"

def main (args : List String) : IO Unit := do
  let out := args[0]!
  let tl ← IO.FS.readFile args[1]!
  let tset : Std.HashSet Name := (tl.splitOn " " |>.map (·.trimAscii.toString) |>.filter (· ≠ "") |>.map String.toName) |>.foldl (·.insert ·) {}
  let ms := ((args.drop 2).filter (fun a => !a.startsWith "c:")).map String.toName
  let extra := ((args.drop 2).filter (fun a => a.startsWith "c:")).map (fun a => (a.drop 2).toString.toName)
  initSearchPath (← findSysroot)
  let env ← importModules (ms.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let modOf (c : Name) : Name := match env.getModuleIdxFor? c with
    | some j => modNames[j.toNat]!
    | none => .anonymous
  let mut seen : Std.HashMap Name Name := {}
  let mut stack : Array Name := #[]
  for m in ms do
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      seen := seen.insert c m; stack := stack.push c
  for c in extra do
    if env.contains c && !seen.contains c then
      seen := seen.insert c `SOURCE; stack := stack.push c
  while h : stack.size > 0 do
    let c := stack.back
    stack := stack.pop
    let mc := modOf c
    unless tset.contains mc || ms.contains mc do continue
    let some ci := env.find? c | continue
    let used0 := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    -- the enclosing declaration of an auxiliary constant (`foo._auto_1`, `S.mk`)
    -- is kept whole, so its own dependencies are needed too
    let mut used := used0
    -- a kept inductive/structure keeps its constructors (their field types)
    if let .inductInfo iv := ci then
      for k in iv.ctors do used := used.push k
    let mut p := c.getPrefix
    while !p.isAnonymous do
      if env.contains p && modOf p == mc then used := used.push p
      p := p.getPrefix
    for u in used do
      unless seen.contains u do
        seen := seen.insert u c
        stack := stack.push u
  let h ← IO.FS.Handle.mk out .write
  for (c, via) in seen.toList do
    let mc := modOf c
    if (tset.contains mc || isRoot mc) && !ms.contains mc then
      h.putStrLn s!"{mc}\t{c}\t{via}"
  h.flush

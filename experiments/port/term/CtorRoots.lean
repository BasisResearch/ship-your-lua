import Lean
open Lean

def isRoot (m : Name) : Bool :=
  let s := m.toString
  s.startsWith "Vsa.While." || s == "Vsa.MemRepr" || s == "Vsa.MemReprReadArrays" ||
  s == "Vsa.MemReprReadChildren" || s == "Vsa.MemReprReadFields" || s == "Vsa.MemReprWithin" ||
  s == "Vsa.RuntimeRepr" || s == "Vsa.ElfBytes"

/-- usage: CtorRoots.lean <out> <constsFile> <mod>... : for each inductive in
constsFile, one root-module constant its constructors reach (through any
non-root module of the imported environment), or nothing. -/
partial def main (args : List String) : IO Unit := do
  let out := args[0]!
  let cs := ((← IO.FS.readFile args[1]!).splitOn "\n").filter (· ≠ "") |>.map String.toName
  let ms := (args.drop 2).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (ms.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let modNames := env.header.moduleNames
  let modOf (c : Name) : Name := match env.getModuleIdxFor? c with
    | some j => modNames[j.toNat]!
    | none => .anonymous
  let memo ← IO.mkRef (∅ : Std.HashMap Name (Option Name))
  let rec hit (c : Name) : IO (Option Name) := do
    let ok := [`Vsa.MemRepr.Mem, `Vsa.MemRepr.readLE, `Vsa.MemRepr.read64, `Vsa.MemRepr.read32,
      `Vsa.While.wrap64, `Vsa.While.wrap64_toInt, `Vsa.While.natDigits, `Vsa.While.natToString,
      `Vsa.While.intToString]
    if ok.any (fun o => o.isPrefixOf c) then return none
    if isRoot (modOf c) then return some c
    if let some r := (← memo.get)[c]? then return r
    let mc := modOf c
    unless mc.toString.startsWith "Vsa" do return none
    memo.modify (·.insert c none)
    let some ci := env.find? c | return none
    let mut used := ci.type.getUsedConstants ++ ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[])
    if let .inductInfo iv := ci then used := used ++ iv.ctors.toArray
    let mut r := none
    for u in used do
      if let some x ← hit u then r := some x; break
    memo.modify (·.insert c r)
    return r
  let h ← IO.FS.Handle.mk out .write
  for c in cs do
    let some (.inductInfo iv) := env.find? c | continue
    for k in iv.ctors do
      if let some x ← hit k then h.putStrLn s!"{c}\t{x}"; break
  h.flush

import Lean
open Lean

/-- usage: Meta.lean <out> <mod>... : constants of the modules that are
metaprograms (syntax, macros, elaborators, parser descriptors, attribute
registrations): their type mentions a `Lean.` meta type. Also every
constant carrying a declaration range whose type lives in `Lean.*`. -/
def isMetaTy (n : Name) : Bool :=
  -- any type from the `Lean` metaprogramming namespace (Syntax, Expr, MetaM, …)
  (`Lean).isPrefixOf n || n == `IO || n == `EIO

def main (args : List String) : IO Unit := do
  let out := args[0]!
  let ms := (args.drop 1).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (ms.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let h ← IO.FS.Handle.mk out .write
  for m in ms do
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      let some ci := env.find? c | continue
      if ci.type.getUsedConstants.any isMetaTy then
        h.putStrLn s!"{m}\t{c}"
  h.flush

import Lean
open Lean

/-- usage: Ranges.lean <out> <mod>... : for every constant defined in each
module, `mod\tconst\tstartLine\tendLine` of its declaration range (aux
constants without their own range are omitted). -/
def main (args : List String) : IO Unit := do
  let out := args[0]!
  let ms := (args.drop 1).map String.toName
  initSearchPath (← findSysroot)
  let env ← importModules (ms.toArray.map fun m => { module := m }) {} (trustLevel := 1024)
  let h ← IO.FS.Handle.mk out .write
  for m in ms do
    let some idx := env.getModuleIdx? m | continue
    for c in env.header.moduleData[idx.toNat]!.constNames do
      match declRangeExt.find? env c with
      | some r => h.putStrLn s!"{m}\t{c}\t{r.range.pos.line}\t{r.range.endPos.line}"
      | none => pure ()
  h.flush

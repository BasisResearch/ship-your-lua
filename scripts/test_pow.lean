import Lua.Num.Pow
/-!
The Lean side of the differential test of `Lua/Num/Pow.lean`
(`c/tests/float/run_pow.sh`). From the repository root,
`lake env lean scripts/test_pow.lean` reads `c/tests/float/{pow,snan}.vec`
(pairs of 64-bit patterns in hex) and writes the lines the ELF should print,
the bits of `x ^ y` (`Lua.Num.numpow`) as signed integers, to
`c/build/float/{pow,snan}.lean`.
-/
open Lua.Num

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87

def ofHex (s : String) : Float.Model :=
  .ofBits (UInt64.ofNat (s.toList.foldl (fun a c => a * 16 + hexVal c) 0))

def line (l : String) : String :=
  match l.splitOn " " with
  | [x, y] => s!"{(BitVec.ofNat 64 (numpow (ofHex x) (ofHex y)).toBits.toNat).toInt}"
  | _ => "bad vector"

#eval show IO Unit from do
  IO.FS.createDirAll "c/build/float"
  for n in ["pow", "snan"] do
    let v ← IO.FS.lines s!"c/tests/float/{n}.vec"
    IO.FS.writeFile s!"c/build/float/{n}.lean"
      (String.intercalate "\n" (v.toList.map line) ++ "\n")
    IO.println s!"{n}: {v.size} lines"

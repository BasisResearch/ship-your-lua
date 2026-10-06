import Lua.Num.Decimal
/-!
The Lean side of the differential tests of `Lua/Num/Decimal.lean`
(`c/tests/float/run.sh`). From the repository root,
`lake env lean scripts/test_decimal.lean` reads `c/tests/float/{fmt,parse}.vec`
and writes the lines the ELF should print to `c/build/float/{fmt,parse}.lean`.
-/
open Lua.Num

def bytesToString (l : List UInt8) : String := String.ofList (l.map fun b => Char.ofNat b.toNat)

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - 48 else c.toLower.toNat - 87

def unhex : List Char → List UInt8
  | a :: b :: r => (hexVal a * 16 + hexVal b).toUInt8 :: unhex r
  | _ => []

def bitsOfHex (s : String) : BitVec 64 :=
  BitVec.ofNat 64 (s.toList.foldl (fun a c => a * 16 + hexVal c) 0)

def showNumeral : Option Numeral → String
  | none => "nil"
  | some (.int i) => s!"I {i.toInt}"
  | some (.flt x) =>
    s!"F {bytesToString (tostringbuff false x)} {(BitVec.ofNat 64 x.toBits.toNat).toInt}"

#eval show IO Unit from do
  IO.FS.createDirAll "c/build/float"
  let fmt ← IO.FS.lines "c/tests/float/fmt.vec"
  let out := fmt.toList.map fun l => bytesToString (tostringbuffBits (bitsOfHex l))
  IO.FS.writeFile "c/build/float/fmt.lean" (String.intercalate "\n" out ++ "\n")
  let parse ← IO.FS.lines "c/tests/float/parse.vec"
  let out := parse.toList.map fun l => showNumeral (str2number (unhex l.toList))
  IO.FS.writeFile "c/build/float/parse.lean" (String.intercalate "\n" out ++ "\n")
  IO.println s!"fmt: {fmt.size} lines, parse: {parse.size} lines"

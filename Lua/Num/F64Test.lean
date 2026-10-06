import Lua.Num.F64
import Lua.Num.Arith

/-!
# `F64` and `Lua.Num.Arith` against host `Float` and against the ELF on Sail

Not imported by `Lua`: run with `lake env lean Lua/Num/F64Test.lean`.

* **Host oracle.** Lean's `Float` runs on the host's IEEE hardware and is
  equal to `Float.Model` by `Float.toModel`; each `#eval` compares `F64`'s
  bits with `Float`'s on edge vectors (±0, subnormal boundaries, ties,
  overflow, ∞, NaN) and on pseudo-random vectors. A NaN result is compared
  by class only (x86 returns a negative default NaN).
* **ELF oracle.** `sailVectors` are the results of `c/tests/float/vectors.lua`
  run on the ELF under the Sail emulator (`c/tests/float/run_sail.sh`); they
  are compared bit for bit, NaN sign included.
-/

open Lua.Num

namespace Lua.Num.F64Test

def toF (x : F64) : Float := Float.ofBits x.toNat.toUInt64
def ofF (f : Float) : F64 := BitVec.ofNat 64 f.toBits.toNat

/-- Same bits, or both NaN. -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)

/-- Edge values: zeros, subnormal boundaries, normal boundaries, ±1 and its
neighbours, ties at 2^53, max finite, ∞, NaNs with payload and sign. -/
def edges : List F64 :=
  let pos : List Nat := [0, 1, 2, 3, 0x000fffffffffffff, 0x0010000000000000, 0x0010000000000001,
    0x001fffffffffffff, 0x3fe0000000000000, 0x3fefffffffffffff, 0x3ff0000000000000,
    0x3ff0000000000001, 0x3ff8000000000000, 0x4000000000000000, 0x4008000000000000,
    0x4330000000000000, 0x4330000000000001, 0x4340000000000000, 0x4340000000000001,
    0x43e0000000000000, 0x7fefffffffffffff, 0x7fe0000000000000, 0x7ff0000000000000,
    0x7ff8000000000000, 0x7ff0000000000001, 0x3fb999999999999a, 0x3fd5555555555555,
    0x0000000000000800, 0x3c90000000000000, 0x3ca0000000000000, 0x4024000000000000]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

/-- A 64-bit LCG (Knuth's MMIX constants). -/
def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- `n` pseudo-random pairs; one in four pairs shares its exponent field
(cancellation in `add`/`sub`), one in four has small exponents (subnormal results). -/
def randPairs (n : Nat) (seed : UInt64) : List (F64 × F64) := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s; let a := s
    s := lcg s; let b := s
    let x : F64 := BitVec.ofNat 64 a.toNat
    let y : F64 := match i % 4 with
      | 0 => BitVec.ofNat 64 ((x.toNat / 2 ^ 52) * 2 ^ 52 + b.toNat % 2 ^ 52)
      | 1 => BitVec.ofNat 64 (b.toNat % 2 ^ 59 + (b.toNat / 2 ^ 63) * 2 ^ 63)
      | 2 => BitVec.ofNat 64 ((x.toNat / 2 ^ 52 + b.toNat % 64 - 32) % 2 ^ 12 * 2 ^ 52 + b.toNat % 2 ^ 52)
      | _ => BitVec.ofNat 64 b.toNat
    let x := if i % 4 = 1 then BitVec.ofNat 64 (a.toNat % 2 ^ 59 + (a.toNat / 2 ^ 63) * 2 ^ 63) else x
    out := (x, y) :: out
  return out

def pairs : List (F64 × F64) :=
  (edges.flatMap fun x => edges.map fun y => (x, y)) ++ randPairs 100000 0x5eed

/-- Mismatches of a binary operation against the host. -/
def checkBin (f : F64 → F64 → F64) (g : Float → Float → Float) : List (F64 × F64) :=
  (pairs.filter fun (x, y) => !agree (f x y) (ofF (g (toF x) (toF y)))).take 5

def checkUn (f : F64 → F64) (g : Float → Float) : List F64 :=
  ((pairs.map (·.1)).filter fun x => !agree (f x) (ofF (g (toF x)))).take 5

/-! ## Host-oracle runs (each prints `[]` when all vectors agree) -/

#eval checkBin F64.add (· + ·)
#eval checkBin F64.sub (· - ·)
#eval checkBin F64.mul (· * ·)
#eval checkBin F64.div (· / ·)
#eval checkUn F64.sqrt Float.sqrt
#eval checkUn (F64.neg) (fun f => -f)
#eval ((pairs.filter fun (x, y) =>
    F64.lt x y != (toF x < toF y) || F64.le x y != (toF x ≤ toF y) ||
    F64.eq x y != (toF x == toF y)).take 5)
#eval ((pairs.map (·.1)).filter fun i =>
    F64.ofInt i != ofF (Float.ofInt i.toInt)).take 5
-- Negative control: the harness does see a wrong operation (expect a non-empty list).
#eval (checkBin F64.add (· - ·)).length

/-! ## `Lua.Num.Arith` against host `Float` -/

def toM (x : F64) : Float.Model := F64.toModel x
def parseF (s : String) : Option F64 := s.toInt?.map (BitVec.ofInt 64)
def mBits (m : Float.Model) : F64 := m.toBits.toBitVec

-- `floor`: against `Float.floor` (C `floor`).
#eval ((pairs.map (·.1)).filter fun x =>
    !agree (mBits (Lua.Num.floor (toM x))) (ofF (Float.floor (toF x)))).take 5

/-- The F2I modes against `Float.floor`/`Float.ceil` and the C range guard. -/
def f2iOracle (x : Float) (m : F2Imod) : Option (BitVec 64) :=
  let f := match m with | .eq => x.floor | .floor => x.floor | .ceil => x.ceil
  if m == .eq && f != x then none
  else if -9223372036854775808.0 ≤ f && f < 9223372036854775808.0 then
    some (BitVec.ofInt 64 (if f < 0 then -((-f).toUInt64.toNat : Int) else (f.toUInt64.toNat : Int)))
  else none

#eval ((pairs.map (·.1)).filter fun x =>
    [F2Imod.eq, .floor, .ceil].any fun m => flttointeger (toM x) m != f2iOracle (toF x) m).take 5

/-! ## `fmod` against host `lua`'s `math.fmod` (glibc `fmod`, exact; NaN by class)

Host `lua` agrees with the ELF except on the NaN sign, so NaN results are
compared by class. Needs `c/lua` (`make -C c host`). -/

def fmodPairs : List (F64 × F64) :=
  (edges.flatMap fun x => edges.map fun y => (x, y)) ++ randPairs 3000 0xf00d

def hostFmod : IO (List (Option F64)) := do
  let lit (x : F64) : String := toString x.toInt
  let body := fmodPairs.map fun (x, y) => "P(" ++ lit x ++ "," ++ lit y ++ ")"
  let script := "local function B(x) return (string.unpack('<i8', string.pack('<d', x))) end\n" ++
    "local function F(i) return (string.unpack('<d', string.pack('<i8', i))) end\n" ++
    "local function P(x, y) print(B(math.fmod(F(x), F(y)))) end\n" ++
    String.intercalate "\n" body ++ "\n"
  IO.FS.createDirAll "c/build/float"
  IO.FS.writeFile "c/build/float/fmod_host.lua" script
  let out ← IO.Process.output { cmd := "c/lua", args := #["c/build/float/fmod_host.lua"] }
  return ((out.stdout.splitOn "\n").filter (· ≠ "")).map parseF

-- Prints the number of vectors and the mismatches (expect `[]`).
#eval do
  let host ← hostFmod
  let bad := (fmodPairs.zip host).filter fun ((x, y), h) =>
    match h with
    | some h => !agree (mBits (Lua.Num.fmod (toM x) (toM y))) h
    | none => true
  return (host.length, (bad.take 5).map fun (p : (F64 × F64) × Option F64) =>
    (p.1.1.toInt, p.1.2.toInt, p.2.map BitVec.toInt))

/-! ## The ELF on Sail (`c/tests/float/vectors.sail.out`)

Each line is `x y x+y x-y x*y x/y x%y x//y x<y x<=y x==y x|0` (floats as the
signed integer of their bits), then `i i+0.0` lines. Every field is compared
bit for bit, NaN sign included. -/

def sailLines : IO (List (List String)) := do
  let txt ← IO.FS.readFile "c/tests/float/vectors.sail.out"
  return (txt.splitOn "\n").filter (· ≠ "") |>.map (·.splitOn "\t")

def bstr (b : Bool) : String := if b then "true" else "false"

/-- The fields of one vector line that disagree with `F64`/`Arith`. -/
def checkLine (l : List String) : List String :=
  match l with
  | [xs, ys, a, s, m, d, md, id, lt, le, eq, fi] =>
    match parseF xs, parseF ys with
    | some x, some y =>
      let chk (nm : String) (got : F64) (want : String) : List String :=
        if parseF want == some got then [] else [s!"{nm} {xs} {ys}: F64 {got.toInt} ELF {want}"]
      let chkB (nm : String) (got : Bool) (want : String) : List String :=
        if bstr got == want then [] else [s!"{nm} {xs} {ys}"]
      let fiGot := match flttointeger (toM x) .eq with
        | some i => toString i.toInt | none => "e"
      chk "add" (F64.add x y) a ++ chk "sub" (F64.sub x y) s ++ chk "mul" (F64.mul x y) m ++
      chk "div" (F64.div x y) d ++ chk "mod" (mBits (nummod (toM x) (toM y))) md ++
      chk "idiv" (mBits (numidiv (toM x) (toM y))) id ++
      chkB "lt" (F64.lt x y) lt ++ chkB "le" (F64.le x y) le ++ chkB "eq" (F64.eq x y) eq ++
      (if fiGot == fi then [] else [s!"f2i {xs}: {fiGot} ELF {fi}"])
    | _, _ => ["parse " ++ xs]
  | [is, r] =>
    match is.toInt? with
    | some i => if parseF r == some (F64.ofInt (BitVec.ofInt 64 i)) then [] else [s!"ofInt {is}"]
    | none => ["parse " ++ is]
  | _ => ["bad line"]

-- Prints the number of lines and the mismatches (expect `428` and `[]`).
#eval do
  let ls ← sailLines
  return (ls.length, (ls.flatMap checkLine).take 10)

end Lua.Num.F64Test

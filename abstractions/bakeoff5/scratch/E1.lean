import Lua.Vm.Fn.Spec
import Lua.Num.SfRef

open Lua.Num
namespace Lua.Vm.Fn.SpecTest

/-- Edge operands. -/
def edges : List (BitVec 64) :=
  [0x0, 0x8000000000000000, 0x1, 0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000,
   0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
   0x4340000000000000, 0x4340000000000001, 0x433fffffffffffff, 0xc3e0000000000000,
   0x43e0000000000000, 0x43dfffffffffffff, 0x41dfffffffc00000, 0xc1e0000000000000,
   0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000,
   0x7ff8000000000000, 0xfff8000000000000, 0x7ff0000000000001, 0x4000000000000000,
   0x3fe0000000000000, 0x3cb0000000000000, 0x0008000000000000, 0x4059000000000000]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Pseudo-random operands: raw bits, and small integers' doubles (where
cancellation and rounding happen in `__adddf3`). -/
def rands (n : Nat) (seed : UInt64) : List (BitVec 64) := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let v := if i % 3 == 0 then (s >>> 11).toBitVec ||| 0x3ff0000000000000
      else s.toBitVec
    out := v :: out
  return out

def ops : List (BitVec 64) := edges ++ rands 300 20261006
def pairs : List (BitVec 64 × BitVec 64) :=
  (edges.flatMap fun a => edges.map fun b => (a, b)) ++ (rands 2000 7).zip (rands 2000 11)

/-- The stack the framed routines run on: any `FnSp` pointer. -/
def sp : Nat := 0x80100000
def m0 : Mem := ∅
def ra : BitVec 64 := 0x8001ca88

def bad2 (f g : BitVec 64 → BitVec 64 → BitVec 64) : List (BitVec 64 × BitVec 64) :=
  pairs.filter fun (a, b) => f a b != g a b

end Lua.Vm.Fn.SpecTest
open Lua.Vm.Fn.SpecTest

def morePairs : List (BitVec 64 × BitVec 64) :=
  let es : List Nat := [0, 1, 2, 3, 50, 52, 53, 54, 55, 56, 57, 58, 60, 1000, 1022, 1023, 1024, 2045, 2046]
  let fs : List Nat := [0, 1, 2, 3, 4, 7, 2^51, 2^52 - 1, 2^52 - 2, 2^51 + 1, 12345678901]
  let mk (s : Bool) (e f : Nat) : BitVec 64 := F64.bits s e f
  (es.flatMap fun e1 => es.flatMap fun e2 => fs.flatMap fun f1 => [true, false].flatMap fun s2 =>
    [(mk false e1 f1, mk s2 e2 (2^52 - 1 - f1 % 2^52)), (mk false e1 f1, mk s2 e2 f1), (mk false e1 f1, mk s2 e2 1)])

def bad (f g : BitVec 64 → BitVec 64 → BitVec 64) (ps : List (BitVec 64 × BitVec 64)) :=
  (ps.filter fun (a, b) => f a b != g a b).take 5

#eval morePairs.length
#eval bad SfRef.add F64.add pairs
#eval bad SfRef.add F64.add morePairs
#eval bad SfRef.sub F64.sub pairs
#eval bad SfRef.sub F64.sub morePairs
#eval bad SfRef.add (Lua.Vm.Fn.Adddf3.F m0 sp ra) pairs
#eval bad SfRef.add (Lua.Vm.Fn.Adddf3.F m0 sp ra) morePairs
#eval bad SfRef.sub (Lua.Vm.Fn.Subdf3.F m0 sp ra) morePairs

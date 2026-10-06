import Lua.Vm.Fn.Spec

/-!
# The soft-float summaries against their specifications, by evaluation

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/SpecTest.lean`.

Evidence for the fields of `SoftFloatSpec` (`Lua/Vm/Fn/Spec.lean`), not a
proof: each `#eval` runs a routine's lifted function `F` (generated from the
ELF's instructions by `scripts/gen_lua_fn.py`; the level-(a) theorem `sum`
says the machine computes it) and its specification `S` (`F64`, equal to
`Float.Model` by lane float-s0a) on edge operands (zeros, subnormal and
normal boundaries, ±1, ties, max finite, ∞, NaNs) and pseudo-random ones,
and lists the disagreements: every line must print `[]`.
-/

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

#eval (pairs.length, ops.length)
#eval bad2 Eqdf2.F Eqdf2.S
#eval bad2 Ledf2.F Ledf2.S
#eval bad2 Gedf2.F Gedf2.S
#eval ops.filter fun x => Fixdfdi.F x != Fixdfdi.S x
-- `__floatsidf` on canonical arguments only (`SoftFloatSpec.floatsidf`'s
-- hypothesis): a sign-extended low word.
def canon (x : BitVec 64) : BitVec 64 := (x.setWidth 32).signExtend 64
#eval (ops ++ (List.range 600).map (fun i => BitVec.ofInt 64 ((i : Int) - 300))).filter
  fun x => Floatsidf.F m0 sp ra (canon x) != Floatsidf.S (canon x)
-- Off canonical arguments the routine differs (`0.5` for a zero low word
-- under a nonzero upper word): why the field has its hypothesis. Prints `true`.
#eval Floatsidf.F m0 sp ra 0x8000000000000000 != Floatsidf.S 0x8000000000000000
#eval (ops ++ (List.range 600).map (fun i => BitVec.ofInt 64 ((i : Int) - 300))).filter
  fun x => Floatdidf.F m0 sp ra x != Floatdidf.S x
#eval bad2 (Adddf3.F m0 sp ra) Adddf3.S
#eval bad2 (Subdf3.F m0 sp ra) Subdf3.S

end Lua.Vm.Fn.SpecTest

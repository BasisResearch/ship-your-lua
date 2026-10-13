import Lua.Vm.Fn.Ieee754Fmod
import Lua.Num.Arith

/-!
# `fmod` by evaluation (lane float-sf5)

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/FmodTest.lean`.

Evidence beside the proofs: the ELF's `__ieee754_fmod` (its lifted function
`Ieee754Fmod.F`, generated from the instructions; `Ieee754Fmod.sum` says the
machine computes it when its termination function `T` holds), the model's
`Lua.Num.fmod` (`Lua/Num/Arith.lean`, itself tested against the host's
`math.fmod` in `Lua/Num/F64Test.lean`) on edge and pseudo-random operand
pairs. Every disagreement line must print `[]`.
-/

open Lua.Num

namespace Lua.Vm.Fn.FmodTest

/-- Same bits, or both NaN. -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)

def edges : List F64 :=
  let pos : List Nat := [0, 1, 2, 3, 0x000fffffffffffff, 0x0008000000000000, 0x0000000100000000,
    0x00000000ffffffff, 0x0010000000000000, 0x0010000000000001, 0x3fe0000000000000,
    0x3ff0000000000000, 0x3ff0000000000001, 0x3ff8000000000000, 0x4000000000000000,
    0x4008000000000000, 0x400c000000000000, 0x4024000000000000, 0x412e848000000000,
    0x41e0000000000000, 0x4330000000000000, 0x4340000000000000, 0x43e0000000000000,
    0x7fe0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000, 0x7ff8000000000000,
    0x7ff0000000000001, 0x3fb999999999999a, 0x400921fb54442d18]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Random pairs: raw bits, and pairs with nearby or subnormal exponents. -/
def rands (n : Nat) (seed : UInt64) : List (F64 × F64) := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let a := s
    s := lcg s
    let b := s
    let x : UInt64 := match i % 4 with
      | 0 => a
      | 1 => (a &&& (0x800fffffffffffff : UInt64)) ||| (((1000 : UInt64) + (a >>> (50 : UInt64)) % (48 : UInt64)) <<< (52 : UInt64))
      | 2 => a &&& (0x800fffffffffffff : UInt64)
      | _ => (a &&& (0x800fffffffffffff : UInt64)) ||| (((a >>> (52 : UInt64)) % (2046 : UInt64) + 1) <<< (52 : UInt64))
    let y : UInt64 := match i % 4 with
      | 0 => b
      | 1 => (b &&& (0x800fffffffffffff : UInt64)) ||| (((1000 : UInt64) + (b >>> (50 : UInt64)) % (40 : UInt64)) <<< (52 : UInt64))
      | 2 => (b &&& (0x800000000fffffff : UInt64))
      | _ => (b &&& (0x800fffffffffffff : UInt64)) ||| (((b >>> (52 : UInt64)) % (60 : UInt64) + 1) <<< (52 : UInt64))
    out := (x.toBitVec, y.toBitVec) :: out
  return out

def pairs : List (F64 × F64) :=
  (edges.flatMap fun x => edges.map fun y => (x, y)) ++ rands 4000 20261013

/-- `.rodata`'s `Zero` (`0x80054030`: `+0.0`, `-0.0`) in an otherwise empty memory. -/
def mRod : Mem := Id.run do
  let mut m : Mem := ∅
  for j in [0:16] do
    m := m.insert (0x80054030 + j) (if j = 15 then 0x80 else 0)
  return m
def sp : Nat := 0x80100000
def ra : BitVec 64 := 0x8002b984

def model (x y : F64) : F64 := (Lua.Num.fmod (F64.toModel x) (F64.toModel y)).toBits.toBitVec

#eval pairs.length
-- the machine's `__ieee754_fmod` terminates (within `fnFuel`, its side conditions hold)
#eval (pairs.filter fun (x, y) => !Ieee754Fmod.T mRod sp ra x y).take 5
-- the machine's `__ieee754_fmod` against the model's `Lua.Num.fmod`
#eval (pairs.filter fun (x, y) => !agree (Ieee754Fmod.F mRod sp ra x y) (model x y)).take 5

end Lua.Vm.Fn.FmodTest

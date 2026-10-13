import Lua.Vm.Fn.FloorFn
import Lua.Num.SfRefFloor
import Lua.Num.Arith

/-!
# `floor` by evaluation (lane float-sf3)

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/FloorTest.lean`.

Evidence beside the proofs of `Lua/Vm/Fn/SfRefFloorSpec.lean`: the ELF's
`floor` (its lifted function `FloorFn.F`, generated from the instructions;
`FloorFn.sum` says the machine computes it), the reference `SfRef.floor`
(new: `s_floor.c` over the fields), the model's `Lua.Num.floor` and the
host's C `floor` (`Float.floor`) on edge and pseudo-random operands. Every
line lists disagreements and must print `[]`.
-/

open Lua.Num

namespace Lua.Vm.Fn.FloorTest

def toF (x : F64) : Float := Float.ofBits x.toNat.toUInt64
def ofF (f : Float) : F64 := BitVec.ofNat 64 f.toBits.toNat
/-- Same bits, or both NaN (x86's default NaN is negative). -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)

def edges : List F64 :=
  let pos : List Nat := [0, 1, 0x000fffffffffffff, 0x0010000000000000, 0x3fe0000000000000,
    0x3fefffffffffffff, 0x3ff0000000000000, 0x3ff0000000000001, 0x3ff8000000000000,
    0x4000000000000000, 0x400c000000000000, 0x412e848000000000, 0x41dfffffffc00000,
    0x41e0000000000000, 0x41f0000000000001, 0x4320000000000001, 0x432fffffffffffff,
    0x4330000000000000, 0x4330000000000001, 0x433fffffffffffff, 0x4340000000000000,
    0x7fefffffffffffff, 0x7ff0000000000000, 0x7ff8000000000000, 0x7ff0000000000001,
    0x3fb999999999999a, 0x4059000000000000, 0x4093480000000000, 0x41d0000000000001]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Raw bits, and operands with exponents in `floor`'s mask range. -/
def rands (n : Nat) (seed : UInt64) : List F64 := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let e : UInt64 := (1013 : UInt64) + (s >>> (40 : UInt64)) % (72 : UInt64)
    let v := if i % 2 == 0 then ((s &&& (0x800fffffffffffff : UInt64)) ||| (e <<< (52 : UInt64))).toBitVec
      else s.toBitVec
    out := v :: out
  return out

def ops : List F64 := edges ++ rands 3000 20261013

/-- `.rodata`'s `huge` (`0x8005c4b0`) in an otherwise empty memory. -/
def mRod : Mem := Id.run do
  let mut m : Mem := ∅
  for j in [0:8] do
    m := m.insert (0x8005c4b0 + j) (BitVec.ofNat 8 (0x7e37e43c8800759c / 2 ^ (8 * j) % 256))
  return m
def sp : Nat := 0x80100000
def ra : BitVec 64 := 0x8001ca88

#eval ops.length
-- the machine's `floor` against the reference
#eval (ops.filter fun x => FloorFn.F mRod sp ra x != SfRef.floor x).take 5
-- the reference against the model's `Lua.Num.floor`
#eval (ops.filter fun x => SfRef.floor x != (Lua.Num.floor (F64.toModel x)).toBits.toBitVec).take 5
-- the reference against the host's C `floor`
#eval (ops.filter fun x => !agree (SfRef.floor x) (ofF (Float.floor (toF x)))).take 5
-- negative control: `huge` absent, the machine's `floor` of a negative
-- fraction differs (expect a non-empty list)
#eval ((ops.filter fun x => FloorFn.F ∅ sp ra x != SfRef.floor x).take 1).length

end Lua.Vm.Fn.FloorTest

import Lua.Vm.Fn.Ieee754Sqrt

/-!
# `__ieee754_sqrt` by evaluation (lane float-sf6)

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/SqrtTest.lean`.

Evidence beside the proofs: the ELF's `__ieee754_sqrt` (its lifted function
`Ieee754Sqrt.F`, generated from the instructions; `Ieee754Sqrt.sum` says the
machine computes it when its termination function `T` holds) against
`F64.sqrt` (proved equal to `Float.Model.sqrt`, `F64.sqrt_eq_model`) and the
host's `Float.sqrt`, on edge and pseudo-random operands. Every disagreement
line must print `[]`.
-/

open Lua.Num Lua.Vm.Sim

namespace Lua.Vm.Fn.SqrtTest

def toF (x : F64) : Float := Float.ofBits x.toNat.toUInt64
def ofF (f : Float) : F64 := BitVec.ofNat 64 f.toBits.toNat
/-- Same bits, or both NaN (x86's default NaN is negative). -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)

def edges : List F64 :=
  let pos : List Nat := [0, 1, 2, 3, 0x000fffffffffffff, 0x0008000000000000, 0x0000000100000000,
    0x00000000ffffffff, 0x0000000000100000, 0x0010000000000000, 0x0010000000000001,
    0x3fe0000000000000, 0x3ff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
    0x4000000000000000, 0x4008000000000000, 0x4010000000000000, 0x4024000000000000,
    0x7fe0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000, 0x7ff8000000000000,
    0x7ff0000000000001, 0x3fb999999999999a, 0x400921fb54442d18, 0x43e0000000000000]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Raw bits, positive normals, positive subnormals, perfect squares. -/
def rands (n : Nat) (seed : UInt64) : List F64 := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let v : UInt64 := match i % 4 with
      | 0 => s
      | 1 => s &&& (0x7fffffffffffffff : UInt64)
      | 2 => s &&& (0x000fffffffffffff : UInt64) >>> ((s >>> (58 : UInt64)) % (52 : UInt64))
      | _ => (ofF (let f := Float.ofNat ((s >>> (38 : UInt64)).toNat); f * f)).toNat.toUInt64
    out := v.toBitVec :: out
  return out

def ops : List F64 := edges ++ rands 4000 20261014

/-- `.rodata`'s `tiny` (`0x8005c690`, `1e-300`) and `one` (`0x8005c698`). -/
def mRod : Mem := Id.run do
  let mut m : Mem := ∅
  for j in [0:8] do
    m := m.insert (0x8005c690 + j) (BitVec.ofNat 8 (0x01a56e1fc2f8f359 / 2 ^ (8 * j) % 256))
    m := m.insert (0x8005c698 + j) (BitVec.ofNat 8 (0x3ff0000000000000 / 2 ^ (8 * j) % 256))
  return m
def sp : Nat := 0x80100000
def ra : BitVec 64 := 0x8001ca88
def g : SFrame := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12⟩

#eval ops.length
-- termination: `T` holds on every operand
#eval (ops.filter fun x => !Ieee754Sqrt.T mRod sp ra g x).take 5
-- machine = `F64.sqrt`
#eval (ops.filter fun x => Ieee754Sqrt.F mRod sp ra g x != F64.sqrt x).take 5
-- `F64.sqrt` = host `Float.sqrt` (NaN by class)
#eval (ops.filter fun x => !agree (F64.sqrt x) (ofF (Float.sqrt (toF x)))).take 5

end Lua.Vm.Fn.SqrtTest

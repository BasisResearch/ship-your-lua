import Lua.Vm.Fn.Pow
import Lua.Num.Pow

/-!
# libm `pow` by evaluation (lane float-sf6)

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/PowTest.lean`.

Evidence beside the level (a) summaries: the ELF's `__ieee754_pow` and `pow`
(their lifted functions `Ieee754Pow.F`, `Pow.F`, generated from the
instructions; `Ieee754Pow.sum`, `Pow.sum` say the machine computes them)
against `Lua.Num.Pow.ieee754Pow` and `Lua.Num.pow`, the transcriptions of
`e_pow.c`/`w_pow.c` over `Float.Model`, and `scalbn` against
`Lua.Num.Pow.scalbn`, on edge and pseudo-random operands. The memory holds
`.rodata` (`Image.rodataByte`) around the routines' constants. Signalling-NaN
inputs are outside `Float.Model` (`Lua/Num/Pow.lean`'s header) and are left
out of the pairs; their disagreement is checked on its own (lane F1-21). Every
disagreement line must print `[]`.
-/

open Lua.Num Lua.Vm.Sim

namespace Lua.Vm.Fn.PowTest

/-- Same bits, or both NaN. -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)
def isSNaN (x : F64) : Bool := F64.isNaN x && (x.toNat / 2 ^ 51) % 2 == 0

def edges : List F64 :=
  let pos : List Nat := [0, 1, 0x000fffffffffffff, 0x0008000000000000, 0x0010000000000000,
    0x3fe0000000000000, 0x3ff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
    0x3feffffffffffff0, 0x3ff0000000000010, 0x3ff8000000000000,
    0x4000000000000000, 0x4008000000000000, 0x4010000000000000, 0x4024000000000000,
    0x4059000000000000, 0x408f400000000000, 0x4090000000000000, 0x4330000000000000,
    0x4340000000000000, 0x4350000000000000, 0x43e0000000000000, 0x41e0000000000000,
    0x3e50000000000000, 0x3c90000000000000, 0x7fe0000000000000, 0x7fefffffffffffff,
    0x7ff0000000000000, 0x7ff8000000000000, 0x3fd0000000000000, 0x3fb999999999999a,
    0x400921fb54442d18, 0x4005bf0a8b145769, 0x40862e42fefa39ef]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Pseudo-random operands: raw bits, moderate magnitudes, near one, integers. -/
def rands (n : Nat) (seed : UInt64) : List F64 := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let v : UInt64 := match i % 4 with
      | 0 => s
      | 1 => (s &&& (0x800fffffffffffff : UInt64)) ||| ((0x3c0 + (s >>> (52 : UInt64)) % 0x80) <<< 52)
      | 2 => (s &&& (0x800fffffffffffff : UInt64) >>> ((s >>> (58 : UInt64)) % (40 : UInt64))) ||| 0x3ff0000000000000
      | _ => (F64.ofInt (((s >>> (40 : UInt64)).toNat % 41 : Nat) - 20 : Int)).toNat.toUInt64
    out := v.toBitVec :: out
  return out

def ops : List F64 := (edges ++ rands 60 20261019).filter (!isSNaN ·)
def pairs : List (F64 × F64) := ops.flatMap fun x => ops.map (x, ·)

/-- `.rodata` from `0x8005c000` to the HTIF mailbox (the routines' constants). -/
def mRod : Mem := Id.run do
  let mut m : Mem := ∅
  for a in [0x8005c000:0x8005c6c0] do
    m := m.insert a (Image.rodataByte (a - Image.rodataBase))
  return m
def sp : Nat := 0x80100000
def ra : BitVec 64 := 0x8001ca88
def g : SFrame := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12⟩

def ref (x y : F64) : F64 := (Lua.Num.Pow.ieee754Pow (F64.toModel x) (F64.toModel y)).toBits.toBitVec
def refW (x y : F64) : F64 := (Lua.Num.pow (F64.toModel x) (F64.toModel y)).toBits.toBitVec

#eval pairs.length
-- machine `__ieee754_pow` = `e_pow.c`'s transcription
#eval (pairs.filter fun (x, y) => !agree (Ieee754Pow.F mRod sp ra g x y) (ref x y)).take 5
-- machine `pow` = `w_pow.c`'s transcription
#eval (pairs.filter fun (x, y) => !agree (Lua.Vm.Fn.Pow.F mRod sp ra g x y) (refW x y)).take 5
-- lane F1-21: the bits exactly (`PowR.Ieee754PowSpec_Statement`'s form: every NaN
-- result the canonical datum), for `__ieee754_pow` and for `pow`
#eval (pairs.filter fun (x, y) => Ieee754Pow.F mRod sp ra g x y != ref x y).take 5
#eval (pairs.filter fun (x, y) => Lua.Vm.Fn.Pow.F mRod sp ra g x y != refW x y).take 5
-- lane F1-21: signalling-NaN operands (outside `Float.Model`): `pow(sNaN, ±0)` and
-- `pow(1, sNaN)` are the NaN on the ELF, `1.0` on the model (prints `true`)
#eval [(0x7ff0000000000001#64, 0#64), (0x7ff0000000000001#64, 0x8000000000000000#64),
    (0xfff4000000000000#64, 0#64), (0x3ff0000000000000#64, 0x7ff0000000000001#64)].all
  fun (x, y) => Lua.Vm.Fn.Pow.F mRod sp ra g x y == F64.qnan && refW x y == 0x3ff0000000000000#64
-- machine `scalbn` = `s_scalbn.c`'s transcription, `n` over `[-1100, 1100]`
#eval ((ops.flatMap fun x => [-1100, -1075, -1074, -1023, -54, -1, 0, 1, 53, 1023, 1024, 1100].map (x, ·)).filter
    fun (x, n) => !agree (Scalbn.F mRod sp ra x (BitVec.ofInt 64 n))
      (Lua.Num.Pow.scalbn (F64.toModel x) (Int32.ofInt n)).toBits.toBitVec).take 5

end Lua.Vm.Fn.PowTest

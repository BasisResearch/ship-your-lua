import Lua.Vm.Fn.Divdf3
import Lua.Num.SfRefDiv

/-!
# `__divdf3` by evaluation (lane float-sf4)

Not imported by `Lua`: run with `lake env lean Lua/Vm/Fn/DivTest.lean`.

Evidence beside the proofs: the ELF's `__divdf3` (its lifted function
`Divdf3.F`, generated from the instructions, its `udiv_qrnnd` by the
`__udivdi3`/`__umoddi3`/`__muldi3` summaries' values and its class switch by
the two jump tables; `Divdf3.sum` says the machine computes it), the
reference `SfRef.div` (soft-fp's `_FP_DIV` with Knuth's algorithm D over the
fields), the specification `F64.div` and the host's IEEE division on edge
and pseudo-random operand pairs. Every line lists disagreements and must
print `[]`.

`Divdf3.F` reads no memory: the jump tables' targets are the generator's
reading of `.rodata`, checked against the image in each entry's node lemma
(`fn_jt_tgt`), so the class switch is a case on the index.
-/

open Lua.Num

namespace Lua.Vm.Fn.DivTest

def toF (x : F64) : Float := Float.ofBits x.toNat.toUInt64
def ofF (f : Float) : F64 := BitVec.ofNat 64 f.toBits.toNat
/-- Same bits, or both NaN (x86's default NaN is negative). -/
def agree (x y : F64) : Bool := x == y || (F64.isNaN x && F64.isNaN y)

def edges : List F64 :=
  let pos : List Nat := [0, 1, 2, 3, 0x000fffffffffffff, 0x0008000000000000, 0x0010000000000000,
    0x0010000000000001, 0x001fffffffffffff, 0x3fe0000000000000, 0x3fefffffffffffff,
    0x3ff0000000000000, 0x3ff0000000000001, 0x3ff8000000000000, 0x4000000000000000,
    0x3cb0000000000000, 0x3ca0000000000000, 0x2000000000000000, 0x1ff0000000000000,
    0x7fe0000000000000, 0x7fefffffffffffff, 0x7ff0000000000000, 0x7ff8000000000000,
    0x7ff0000000000001, 0x3fb999999999999a, 0x4059000000000000, 0x5fe0000000000000,
    0x6000000000000000, 0x2010000000000000, 0x1ca0000000000000, 0x4008000000000000,
    0x3fd5555555555555, 0x400921fb54442d18]
  pos.map (BitVec.ofNat 64 ·) ++ pos.map (fun n => BitVec.ofNat 64 (n + 2 ^ 63))

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

/-- Raw bits, and operands whose quotient lands near the subnormal and
overflow boundaries. -/
def rands (n : Nat) (seed : UInt64) (hi : Bool) : List F64 := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let e : UInt64 := if i % 3 == 0 then (s >>> (40 : UInt64)) % (64 : UInt64)
      else if i % 3 == 1 then (if hi then (1960 : UInt64) else (0 : UInt64)) + (s >>> (40 : UInt64)) % (88 : UInt64)
      else (s >>> (52 : UInt64)) % (2048 : UInt64)
    out := ((s &&& (0x800fffffffffffff : UInt64)) ||| (e <<< (52 : UInt64))).toBitVec :: out
  return out

def pairs : List (F64 × F64) :=
  (edges.flatMap fun a => edges.map fun b => (a, b)) ++ (rands 4000 7 false).zip (rands 4000 11 true) ++
    (rands 2000 13 true).zip (rands 2000 17 false)

def sp : Nat := 0x80100000
def ra : BitVec 64 := 0x8001ca88

#eval pairs.length
-- the machine's `__divdf3` against the reference
#eval (pairs.filter fun (a, b) => Divdf3.F ∅ sp ra a b != SfRef.div a b).take 5
-- the reference against the specification
#eval (pairs.filter fun (a, b) => SfRef.div a b != F64.div a b).take 5
-- the reference against the host's division
#eval (pairs.filter fun (a, b) => !agree (SfRef.div a b) (ofF (toF a / toF b))).take 5

end Lua.Vm.Fn.DivTest

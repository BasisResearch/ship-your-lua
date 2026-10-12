import Lua.Vm.Fn.Spec

/-!
# Round 5, §2: the candidate laws checked by evaluation on the artefact

Not imported by `Lua`. Every `#eval` runs the generated lifted functions
(`Lua.Vm.Fn.<R>.F`/`N_<pc>`, read off the ELF by `scripts/gen_lua_fn.py`,
equal to the machine by the level-(a) theorems) or the bytecode kernels
(`Lua.Bytecode.opArith`, `forloopK`, `δ`), never a model restating a law.

    abstractions/checks/round5/run_lean.sh abstractions/checks/round5/LawChecks.lean abstractions/checks/round5/LawChecks.out
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Lua.Num Lua.Bytecode Lua.Vm.Fn Lua.Vm.Sim

namespace Round5

/-! ## Test vectors (`Lua/Vm/Fn/SpecTest.lean`'s) -/

def edges : List (BitVec 64) :=
  [0x0, 0x8000000000000000, 0x1, 0x8000000000000001, 0x000fffffffffffff, 0x0010000000000000,
   0x3ff0000000000000, 0xbff0000000000000, 0x3ff0000000000001, 0x3fefffffffffffff,
   0x4340000000000000, 0x4340000000000001, 0x433fffffffffffff, 0xc3e0000000000000,
   0x43e0000000000000, 0x43dfffffffffffff, 0x41dfffffffc00000, 0xc1e0000000000000,
   0x7fefffffffffffff, 0xffefffffffffffff, 0x7ff0000000000000, 0xfff0000000000000,
   0x7ff8000000000000, 0xfff8000000000000, 0x7ff0000000000001, 0x4000000000000000,
   0x3fe0000000000000, 0x3cb0000000000000, 0x0008000000000000, 0x4059000000000000]

def lcg (s : UInt64) : UInt64 := s * 6364136223846793005 + 1442695040888963407

def rands (n : Nat) (seed : UInt64) : List (BitVec 64) := Id.run do
  let mut s := seed
  let mut out := []
  for i in [0:n] do
    s := lcg s
    let v := if i % 3 == 0 then (s >>> 11).toBitVec ||| 0x3ff0000000000000 else s.toBitVec
    out := v :: out
  return out

def pairs : List (BitVec 64 × BitVec 64) :=
  (edges.flatMap fun a => edges.map fun b => (a, b)) ++ (rands 2000 7).zip (rands 2000 11)

def sp : Nat := 0x80100000
def m0 : Std.ExtHashMap Nat (BitVec 8) := ∅
def ra : BitVec 64 := 0x8001ca88

def count (l : List Bool) : Nat × Nat := (l.length, (l.filter id).length)

/-! ## L5-comm: operand order of the soft-float calls

`(cases, holding)`: a law holds when both numbers agree. -/

-- `__adddf3` commutes, bit for bit (NaN payloads included).
#eval count (pairs.map fun (a, b) => Adddf3.F m0 sp ra a b == Adddf3.F m0 sp ra b a)
-- `__eqdf2` is symmetric.
#eval count (pairs.map fun (a, b) => Eqdf2.F a b == Eqdf2.F b a)
-- `__ledf2(a, b) = −__gedf2(b, a)` (unordered: `2` against `−2`).
#eval count (pairs.map fun (a, b) => Ledf2.F a b == -(Gedf2.F b a))
-- `__subdf3(a, b) = __adddf3(a, b ^ signbit)`: level (b) of `__subdf3` is `__adddf3`'s.
#eval count (pairs.map fun (a, b) =>
  Subdf3.F m0 sp ra a b == Adddf3.F m0 sp ra a (b ^^^ 0x8000000000000000#64))
-- The spec side of the same law: `F64.sub a b = F64.add a (b ^ signbit)`.
#eval count (pairs.map fun (a, b) => F64.sub a b == F64.add a (b ^^^ 0x8000000000000000#64))
-- The NaN cases of the last law.
#eval (pairs.filter fun (a, b) =>
  Subdf3.F m0 sp ra a b != Adddf3.F m0 sp ra a (b ^^^ 0x8000000000000000#64)).take 8

/-! ## L5-stage: one round-pack stage across the routines

`packSemiraw s e f` is `_FP_PACK_SEMIRAW_D`'s tail as `soft-fp/op-common.h`
states it: drop the 3 work bits; an all-ones exponent with a nonzero
fraction is the canonical NaN; pack. One Lean function, checked against the
join node of `__adddf3` (`N_8002d92c`, parameters `f e s`) and of
`__subdf3` (`N_8002ea50`, parameters `e s f`). -/

def packSemiraw (s e f : BitVec 64) : BitVec 64 :=
  let f' := f >>> 3
  if e.toNat % 2048 == 2047 && f' != 0 then 0x7ff8000000000000#64
  else ((e &&& 0x7ff#64) <<< 52) ||| (f' &&& 0xfffffffffffff#64) ||| (s <<< 63)

def stageIns : List (BitVec 64 × BitVec 64 × BitVec 64) := Id.run do
  let fs : List (BitVec 64) := (rands 400 3).map (fun (x : BitVec 64) => x >>> 8) ++
    [0#64, 1#64, 7#64, 8#64, 0x80000000000000#64, 0xffffffffffffff#64, 0x7fffffffffffff#64]
  let es : List (BitVec 64) := [0, 1, 2, 1022, 1023, 1024, 2045, 2046, 2047]
  let mut out := []
  for f in fs do
    for e in es do
      for s in [0#64, 1#64] do
        out := (s, e, f) :: out
  return out

#eval count (stageIns.map fun (s, e, f) => Adddf3.N_8002d92c m0 sp ra f e s == packSemiraw s e f)
#eval count (stageIns.map fun (s, e, f) => Subdf3.N_8002ea50 m0 sp ra e s f == packSemiraw s e f)

/-- `_FP_FRAC_SRS` by a variable count `k`, as `__adddf3` computes it
(`N_8002dcd0`: `srl`, `sll` by `64 − k`, `snez`, `or`), against the Nat
statement: the quotient with the dropped bits' disjunction in bit 0. -/
def srsMachine (x k : BitVec 64) : BitVec 64 :=
  (shift_bits_right x (Sail.BitVec.extractLsb k 5 0)) ||| (zero_extend (m := 64) (bool_to_bit
    (zopz0zI_u (0#64) (shift_bits_left x (Sail.BitVec.extractLsb (sign_extend (m := 64)
      ((Sail.BitVec.extractLsb ((0#64) + sign_extend (m := 64) (0x040#12)) 31 0) -
        (Sail.BitVec.extractLsb k 31 0))) 5 0)))))
def srsNat (x k : Nat) : Nat := x / 2 ^ k ||| (if x % 2 ^ k != 0 then 1 else 0)

-- `1 ≤ k ≤ 63`: holds.
#eval count ((rands 300 5).flatMap fun x => (List.range 63).map fun k =>
  (srsMachine x (BitVec.ofNat 64 (k + 1))).toNat == srsNat x.toNat (k + 1))
-- `k = 0`: the `sll` by 64 is a shift by 0, so the sticky bit is `x ≠ 0`, not `0`:
-- the stage's precondition (soft-fp only shifts by `1 ≤ k`).
#eval count ((rands 300 5).map fun x => (srsMachine x 0).toNat == srsNat x.toNat 0)

/-- `_FP_ROUND_NEAREST` with 3 work bits, as the machine does it
(`andi 7; beqz; andi 15; li 4; beq; addi 4`: `N_8002dc60`, `N_8002dc70`). -/
def rne3 (f : Nat) : Nat := if f % 8 != 0 && f % 16 != 4 then f + 4 else f

/-- **The stage law against the spec.** A semiraw result `(s, E, f)`
(`f` with the implicit bit at 55 when `E ≥ 1`, 3 work bits, bit 0 sticky):
`rne3`, the carry out of bit 56 renormalised (`E + 1`, `f / 2` keeping the
sticky bit), the overflow to ∞ at `E = 2047`, then `packSemiraw`, is `F64.round`
of the same value. -/
def roundPack (s : Bool) (E f : Nat) : BitVec 64 :=
  let g := rne3 f
  let (E', g') := if g ≥ 2 ^ 56 then (E + 1, g / 2 ||| g % 2) else (E, g)
  if E' ≥ 2047 then F64.infty s
  else packSemiraw (if s then 1 else 0) (BitVec.ofNat 64 (if g' ≥ 2 ^ 55 then max E' 1 else E'))
    (BitVec.ofNat 64 g')

def specRound (s : Bool) (E f : Nat) : BitVec 64 :=
  F64.round s (f / 8) ((max E 1 : Nat) - 1075) (f / 4 % 2 == 1) (f % 4 != 0)

def roundIns : List (Bool × Nat × Nat) := Id.run do
  let fs := (rands 600 9).map (fun x => x.toNat / 2 ^ 8 ||| 2 ^ 55) ++
    [2 ^ 55, 2 ^ 56 - 1, 2 ^ 56 - 4, 2 ^ 56 - 5, 2 ^ 55 + 4, 2 ^ 55 + 12, 2 ^ 55 + 3]
  let es := [1, 2, 1023, 2045, 2046]
  let mut out := []
  for f in fs do
    for e in es do
      for s in [false, true] do
        out := (s, e, f) :: out
  return out

-- Normal results.
#eval count (roundIns.map fun (s, E, f) => roundPack s E f == specRound s E f)
-- Subnormal results (`E = 0`, no implicit bit; a carry into bit 55 makes the
-- smallest normal).
#eval count (((rands 600 13).map (fun (x : BitVec 64) => x.toNat / 2 ^ 9) ++ [0, 4, 3, 2 ^ 55 - 1, 2 ^ 55 - 4]).flatMap
  fun f => [false, true].map fun s => roundPack s 0 f == specRound s 0 f)

/-! ## L5-read: which non-float cases a kernel's float path refutes

Every combination of operand skeletons under the arm's operand predicate `Q`
(at least one named read a float); each outcome is classed by the kernel's
answer: `none` (the kernel refutes the case: no step), the edge taken, and
the constructors of the values written. -/

def fl (b : BitVec 64) : Value := Value.ofFloat (F64.toModel b)
def skel : List Value :=
  [.nil, .bool true, .int 0, .int 3, fl 0x3ff8000000000000, fl 0, fl 0x7ff8000000000000,
   .str [49], .str [120], .builtin .print]
def isFlt : Value → Bool | .flt .. => true | _ => false
def tag : Value → String
  | .nil => "nil" | .bool _ => "bool" | .int _ => "int" | .flt .. => "flt" | .str _ => "str"
  | .builtin _ => "fn"

def cls (o : Option (Out Value)) : String := match o with
  | none => "none"
  | some o => s!"e{o.edge}:{(o.vals.map tag)}"

def tuples : Nat → List (List Value)
  | 0 => [[]]
  | n + 1 => (tuples n).flatMap fun t => skel.map (· :: t)

/-- The classes of `body` over the tuples of length `n` with a float at one
of `qs`, and per class the read positions' constructor sets. -/
def classes (n : Nat) (qs : List Nat) (body : List Value → Option (Out Value)) :
    List (String × Nat × List (List String)) :=
  let ts := (tuples n).filter fun t => qs.any fun q => isFlt (t.getD q .nil)
  let cs := (ts.map fun t => cls (body t)).eraseDups
  cs.map fun c =>
    let m := ts.filter fun t => cls (body t) == c
    (c, m.length, (List.range n).map fun i => (m.map fun t => tag (t.getD i .nil)).eraseDups)

def w0 : Word := 0#32

-- FORLOOP (`FltStep`: `R[A+2]` a float).
#eval classes 3 [2] (forloopK 10 w0 3).body
-- ADD (`FltBC`).
#eval classes 2 [0, 1] (opArith 10 0 .add [.reg 1, .reg 2]).body
-- DIV (`/`: every number path is float).
#eval classes 2 [0, 1] (opArith 10 0 .div [.reg 1, .reg 2]).body
-- MOD (`FltBC`).
#eval classes 2 [0, 1] (opArith 10 0 .mod [.reg 1, .reg 2]).body
-- BAND (`FltBC`, `tointegerns`).
#eval classes 2 [0, 1] (opArith 10 0 .band [.reg 1, .reg 2]).body
-- LT (`FltAB`): `δ .lt`'s answer.
#eval classes 2 [0, 1] fun vs => (δ .lt vs).map fun v => { edge := 0, vals := [v] }
-- GEI (`FltA`, the immediate an integer).
#eval classes 1 [0] fun vs => (δ .le (.int 3 :: vs)).map fun v => { edge := 0, vals := [v] }
-- UNM (`FltB`).
#eval classes 1 [0] fun vs => (δ .unm vs).map fun v => { edge := 0, vals := [v] }

end Round5

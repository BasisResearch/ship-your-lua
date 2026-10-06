import Lua.Num.Decimal
import Lua.Num.Pow

/-!
# Lua's numeric functions that `Float.Model` lacks

δ's float spec is Lean core's `Float.Model` (`abstractions/FLOAT-DESIGN.md` §1).
The model has `+ − × ÷`, `sqrt`, the comparisons, `ofInt` and truncation; it
has no `floor`, `fmod` or Lua's float→integer modes. This module defines
them exactly, over the model's `unpack`, each a transcription of the cited C:

| Lean | C |
|---|---|
| `floor` | `l_floor` (`vendor/lua-5.4.7/src/luaconf.h:418`) = newlib `floor` (`libm/math/s_floor.c`, fdlibm): exact, `floor(±0) = ±0`, `floor(±∞) = ±∞`, NaN ↦ the canonical NaN (`x+x`) |
| `fmod` | newlib `fmod` (`libm/math/w_fmod.c` over `e_fmod.c`): exact remainder `x − trunc(x/y)·y` with the sign of `x`; NaN for a NaN operand, `x = ±∞` or `y = ±0`; `x` itself for finite `x` and `y = ±∞` |
| `numberToInteger` | `lua_numbertointeger` (`luaconf.h:432`): the range guard `−2^63 ≤ n < 2^63`, then the C cast (`__fixdfdi`, truncation) |
| `F2Imod`, `flttointeger` | `F2Imod` (`lvm.h:43`), `luaV_flttointeger` (`lvm.c:123`) |
| `numidiv` | `luai_numidiv` (`llimits.h:313`) |
| `nummod` | `luai_nummod` (`llimits.h:333`) |

Every NaN the ELF's soft-float produces is the canonical `0x7ff8000000000000`
(`c/tests/float/nan_probe.lua` on Sail), which is `Float.Model.nan`.
-/

namespace Lua.Num

/-- Floats are shown by their bit pattern. -/
instance : Repr Float.Model := ⟨fun x n => reprPrec x.toBits n⟩

open Float.Model (UnpackedFloat)
open Float.Model.UnpackedFloat (Sign)

/-- The model's binary64 format. -/
abbrev b64 : Float.Model.Format := Float.Model.Format.binary64

/-- `l_floor` (`luaconf.h:418`): newlib's fdlibm `floor`. The integral part of
a finite value with a negative exponent is `m / 2^k`; a negative non-integral
value goes one down. -/
def floor (x : Float.Model) : Float.Model :=
  match x.unpack with
  | .notANumber => .nan
  | .infinity _ => x
  | .zero _ => x
  | .finite s m e _ =>
    if 0 ≤ e then x
    else
      let k := (-e).toNat
      match s with
      | .positive => .ofNat (m / 2 ^ k)
      | .negative => .ofInt (-((m / 2 ^ k + (if m % 2 ^ k = 0 then 0 else 1) : Nat) : Int))

/-- newlib `fmod` (`w_fmod.c` over fdlibm `e_fmod.c`): the exact remainder,
with the sign of `x`. -/
def fmod (x y : Float.Model) : Float.Model :=
  match x.unpack, y.unpack with
  | .notANumber, _ => .nan
  | _, .notANumber => .nan
  | .infinity _, _ => .nan
  | _, .zero _ => .nan
  | .zero _, _ => x
  | .finite .., .infinity _ => x
  | .finite s m₁ e₁ _, .finite _ m₂ e₂ _ =>
    let e := min e₁ e₂
    let r := (m₁ <<< (e₁ - e).toNat) % (m₂ <<< (e₂ - e).toNat)
    if r = 0 then .pack (.zero s) else .pack (UnpackedFloat.round b64 s r e)

/-- `(lua_Number)LUA_MININTEGER`, i.e. `−2^63`. -/
def minIntF : Float.Model := .ofInt (-(2 ^ 63))

/-- `lua_numbertointeger` (`luaconf.h:432`): `n >= (double)LUA_MININTEGER &&
n < -(double)LUA_MININTEGER`, then `(lua_Integer)n` (`__fixdfdi`). -/
def numberToInteger (n : Float.Model) : Option (BitVec 64) :=
  if Float.Model.le minIntF n && Float.Model.lt n minIntF.neg then
    some n.toInt64.toBitVec
  else none

/-- `F2Imod` (`lvm.h:43`). -/
inductive F2Imod where
  /-- no rounding; accepts only integral values -/
  | eq
  /-- takes the floor of the number -/
  | floor
  /-- takes the ceil of the number -/
  | ceil
deriving DecidableEq, Repr

/-- `luaV_flttointeger` (`lvm.c:123`). `n != f` is C's `!=`, true when `n`
is NaN; `f += 1` is a float addition. -/
def flttointeger (n : Float.Model) (mode : F2Imod) : Option (BitVec 64) :=
  let f := floor n
  if !(Float.Model.beq n f) then
    match mode with
    | .eq => none
    | .ceil => numberToInteger (Float.Model.add f (.ofNat 1))
    | .floor => numberToInteger f
  else numberToInteger f

/-- `luai_numidiv` (`llimits.h:313`): `floor(a / b)`. -/
def numidiv (a b : Float.Model) : Float.Model := floor (Float.Model.div a b)

/-- `luai_nummod` (`llimits.h:333`): `m = fmod(a,b); if ((m > 0) ? b < 0 :
(m < 0 && b > 0)) m += b`. -/
def nummod (a b : Float.Model) : Float.Model :=
  let z := Float.Model.ofNat 0
  let m := fmod a b
  if (if Float.Model.lt z m then Float.Model.lt b z else Float.Model.lt m z && Float.Model.lt z b)
  then Float.Model.add m b else m

/-! ## Integer operations (`lvm.c`, `lvm.h`) -/

/-- `luaV_idiv` (`lvm.c:725`): floor division; `none` is the division-by-zero
error (`luaG_runerror`). For `n = -1` this is `0 - m` (wrapping), which
`Int.fdiv` + wrap agrees with. -/
def idiv (m n : BitVec 64) : Option (BitVec 64) :=
  if n = 0 then none else some (BitVec.ofInt 64 (Int.fdiv m.toInt n.toInt))

/-- `luaV_mod` (`lvm.c:745`): floor modulo; `none` is the `n%0` error. -/
def imod (m n : BitVec 64) : Option (BitVec 64) :=
  if n = 0 then none else some (BitVec.ofInt 64 (Int.fmod m.toInt n.toInt))

/-- `luaV_shiftl` (`lvm.c:777`): a negative `y` shifts right (logically: `intop`
works on `lua_Unsigned`), and a shift by 64 or more bits in either direction
gives 0. -/
def shiftl (x y : BitVec 64) : BitVec 64 :=
  if y.toInt < 0 then (if y.toInt ≤ -64 then 0 else x >>> (-y.toInt).toNat)
  else (if 64 ≤ y.toInt then 0 else x <<< y.toNat)

/-- `luaV_shiftr(x,y)` is `luaV_shiftl(x, intop(-, 0, y))` (`lvm.h:116`): the
negation wraps, so `y = minint` shifts left by `minint`, giving 0. -/
def shiftr (x y : BitVec 64) : BitVec 64 := shiftl x (0 - y)

/-! ## Mixed integer/float numbers -/

/-- `cast_num` of an integer (`(lua_Number)i`; `__floatdidf` on the ELF). -/
def ofI (i : BitVec 64) : Float.Model := Float.Model.ofInt i.toInt

/-- `nvalue`/`tonumberns` (`lobject.h`, `lvm.h:56`): a number as a float. -/
def Numeral.toFloat : Numeral → Float.Model
  | .int i => ofI i
  | .flt x => x

/-- `luaV_tointegerns` (`lvm.c:138`) on a number. -/
def Numeral.tointegerns (m : F2Imod) : Numeral → Option (BitVec 64)
  | .int i => some i
  | .flt x => flttointeger x m

/-- `l_intfitsf` (`lvm.c:72`, `NBM = 53`): `(MAXINTFITSF + l_castS2U(i)) <=
2 * MAXINTFITSF` in unsigned (wrapping) arithmetic. -/
def intfitsf (i : BitVec 64) : Bool := (BitVec.ofNat 64 (2 ^ 53) + i).toNat ≤ 2 ^ 54

/-- `LTintfloat` (`lvm.c:411`): `i < f`. -/
def ltIntFloat (i : BitVec 64) (f : Float.Model) : Bool :=
  if intfitsf i then Float.Model.lt (ofI i) f
  else match flttointeger f .ceil with
    | some fi => decide (i.toInt < fi.toInt)
    | none => Float.Model.lt zero f

/-- `LEintfloat` (`lvm.c:428`): `i <= f`. -/
def leIntFloat (i : BitVec 64) (f : Float.Model) : Bool :=
  if intfitsf i then Float.Model.le (ofI i) f
  else match flttointeger f .floor with
    | some fi => decide (i.toInt ≤ fi.toInt)
    | none => Float.Model.lt zero f

/-- `LTfloatint` (`lvm.c:445`): `f < i`. -/
def ltFloatInt (f : Float.Model) (i : BitVec 64) : Bool :=
  if intfitsf i then Float.Model.lt f (ofI i)
  else match flttointeger f .floor with
    | some fi => decide (fi.toInt < i.toInt)
    | none => Float.Model.lt f zero

/-- `LEfloatint` (`lvm.c:462`): `f <= i`. -/
def leFloatInt (f : Float.Model) (i : BitVec 64) : Bool :=
  if intfitsf i then Float.Model.le f (ofI i)
  else match flttointeger f .ceil with
    | some fi => decide (fi.toInt ≤ i.toInt)
    | none => Float.Model.lt f zero

/-- `LTnum` (`lvm.c:480`): `l < r` on numbers. -/
def ltNum : Numeral → Numeral → Bool
  | .int a, .int b => decide (a.toInt < b.toInt)
  | .int a, .flt b => ltIntFloat a b
  | .flt a, .flt b => Float.Model.lt a b
  | .flt a, .int b => ltFloatInt a b

/-- `LEnum` (`lvm.c:502`): `l <= r` on numbers. -/
def leNum : Numeral → Numeral → Bool
  | .int a, .int b => decide (a.toInt ≤ b.toInt)
  | .int a, .flt b => leIntFloat a b
  | .flt a, .flt b => Float.Model.le a b
  | .flt a, .int b => leFloatInt a b

/-- `luaV_equalobj` (`lvm.c:569`) on two numbers: the same variant compares
by `==` (`luai_numeq`: `-0 == 0`, NaN unequal to everything); an integer
and a float compare as integers, through `luaV_tointegerns(F2Ieq)` on both
(`lvm.c:573-581`). -/
def eqNum : Numeral → Numeral → Bool
  | .int a, .int b => decide (a = b)
  | .flt a, .flt b => Float.Model.beq a b
  | a, b =>
    match a.tointegerns .eq, b.tointegerns .eq with
    | some i, some j => decide (i = j)
    | _, _ => false

/-! ## `luaO_rawarith` -/

/-- The arithmetic operators of `lua_arith`, in `lua.h`'s order
(`LUA_OPADD` … `LUA_OPBNOT`, lua.h:216-229). -/
inductive Op where
  | add | sub | mul | mod | pow | div | idiv | band | bor | bxor | shl | shr | unm | bnot
  deriving DecidableEq, Repr

/-- `numarith` (`lobject.c:73`); the default arm is `lua_assert(0); return 0`. -/
def numarith : Op → Float.Model → Float.Model → Float.Model
  | .add, a, b => Float.Model.add a b
  | .sub, a, b => Float.Model.sub a b
  | .mul, a, b => Float.Model.mul a b
  | .div, a, b => Float.Model.div a b
  | .pow, a, b => numpow a b      -- `luai_numpow` (`Lua/Num/Pow.lean`)
  | .idiv, a, b => numidiv a b
  | .unm, a, _ => Float.Model.neg a
  | .mod, a, b => nummod a b
  | _, _, _ => zero

/-- `intarith` (`lobject.c:53`); `none` is the error of `luaV_mod`/`luaV_idiv`
by zero. The default arm (`/` and `^`, never called with them) is
`lua_assert(0); return 0`. -/
def intarith : Op → BitVec 64 → BitVec 64 → Option (BitVec 64)
  | .add, a, b => some (a + b)
  | .sub, a, b => some (a - b)
  | .mul, a, b => some (a * b)
  | .mod, a, b => imod a b
  | .idiv, a, b => idiv a b
  | .band, a, b => some (a &&& b)
  | .bor, a, b => some (a ||| b)
  | .bxor, a, b => some (a ^^^ b)
  | .shl, a, b => some (shiftl a b)
  | .shr, a, b => some (shiftr a b)
  | .unm, a, _ => some (0 - a)
  | .bnot, a, _ => some (~~~a)
  | _, _, _ => some 0

/-- What `luaO_rawarith` does: a result, `fail` (it returns 0: the caller
tries a metamethod; `luaV_execute`'s fast paths fall through to `MMBIN*`), or
a Lua error raised inside (`luaV_mod`/`luaV_idiv` by zero). -/
inductive Res where
  | val (n : Numeral)
  | fail
  | err
  deriving DecidableEq

/-- An integer result of `intarith`. -/
def Res.ofInt (r : Option (BitVec 64)) : Res :=
  match r with
  | some i => .val (.int i)
  | none => .err

/-- `luaO_rawarith` (`lobject.c:89`) on two numbers: bitwise operators on
`tointegerns` (`F2Ieq`) of both, `/` and `^` on floats, the others on two
integers or else on floats. It is also `luaV_execute`'s fast path of every
arithmetic and bitwise opcode (`op_arith`, `op_arithK`, `op_arithI`,
`op_arithf`, `op_arithfK`, `op_bitwise`, `op_bitwiseK`, `OP_SHRI`, `OP_SHLI`,
`lvm.c:905-1011, 1440-1459`), whose non-number operands fall through to
`MMBIN*` (`tonumberns` fails). -/
def rawArith (o : Op) (a b : Numeral) : Res :=
  match o with
  | .band | .bor | .bxor | .shl | .shr | .bnot =>
    match a.tointegerns .eq, b.tointegerns .eq with
    | some i, some j => .ofInt (intarith o i j)
    | _, _ => .fail
  | .div | .pow => .val (.flt (numarith o a.toFloat b.toFloat))
  | _ =>
    match a, b with
    | .int i, .int j => .ofInt (intarith o i j)
    | _, _ => .val (.flt (numarith o a.toFloat b.toFloat))

/-- `intarith` fails only in `luaV_mod`/`luaV_idiv`. -/
theorem intarith_none {o : Op} {a b : BitVec 64} (h : intarith o a b = none) :
    o = .mod ∨ o = .idiv := by
  cases o <;> simp_all [intarith]

/-- `luaO_rawarith` raises an error only in `luaV_mod`/`luaV_idiv`. -/
theorem rawArith_err {o : Op} {a b : Numeral} (h : rawArith o a b = .err) :
    o = .mod ∨ o = .idiv := by
  have hi : ∀ r : Option (BitVec 64), Res.ofInt r = .err → r = none := fun r hr => by
    cases r <;> simp_all [Res.ofInt]
  unfold rawArith at h
  split at h
  all_goals first
    | (split at h
       · exact intarith_none (hi _ h)
       · cases h)
    | cases h
    | (split at h
       · exact intarith_none (hi _ h)
       · cases h)

/-- `luaO_rawarith`'s error: two integers, the divisor zero. -/
theorem rawArith_err_int {o : Op} {a b : Numeral} (h : rawArith o a b = .err) :
    ∃ i, a = .int i ∧ b = .int 0 := by
  rcases rawArith_err h with rfl | rfl <;>
  · simp only [rawArith] at h
    split at h
    · rename_i i j
      refine ⟨i, rfl, ?_⟩
      simp only [intarith, Res.ofInt, imod, idiv] at h
      split at h
      · cases h
      · rename_i hj
        by_cases h0 : j = 0
        · rw [h0]
        · simp at hj; exact absurd hj h0
    · cases h

end Lua.Num

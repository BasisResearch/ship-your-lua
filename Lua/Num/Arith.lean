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

end Lua.Num

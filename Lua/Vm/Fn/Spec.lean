import Lua.Vm.Fn.Floatsidf
import Lua.Vm.Fn.Floatdidf
import Lua.Vm.Fn.Fixdfdi
import Lua.Vm.Fn.Eqdf2
import Lua.Vm.Fn.Ledf2
import Lua.Vm.Fn.Gedf2
import Lua.Vm.Fn.Adddf3
import Lua.Vm.Fn.Subdf3
import Lua.Num.F64

/-!
# The soft-float routines' specifications (FLOAT-DESIGN.md §3, level 2)

Level 1 (`scripts/gen_lua_fn.py`, `Lua/Vm/Fn/*`) proves that each routine's
machine code returns its lifted function `F` (the decompiled routine, over
`BitVec 64`). Level 2 is that `F` is the `F64` operation (`Lua/Num/F64.lean`),
and so `Float.Model`'s through the S0a bridges (`F64.add_eq_model`, …). Each
routine's specification is `S` below, in the form the arms consume:

| routine | `S` | libgcc |
|---|---|---|
| `__floatsidf` | `F64.ofInt` of the low word, sign-extended | `soft-fp/floatsidf.c` |
| `__floatdidf` | `F64.ofInt` | `soft-fp/floatdidf.c` |
| `__fixdfdi` | truncation toward zero, saturated by the sign | `soft-fp/fixdfdi.c` |
| `__eqdf2` | `0` if `F64.eq`, else `1` | `soft-fp/eqdf2.c` |
| `__ledf2` (`= __ltdf2`) | `-1`, `0`, `1` by `F64.compare`, `2` unordered | `soft-fp/ledf2.c` |
| `__gedf2` (`= __gtdf2`) | `-1`, `0`, `1` by `F64.compare`, `-2` unordered | `soft-fp/gedf2.c` |
| `__adddf3` | `F64.add` | `soft-fp/adddf3.c` |
| `__subdf3` | `F64.sub` | `soft-fp/subdf3.c` |

**`SoftFloatSpec`** was the named premise of the level-2 equations, one field
per routine; every field has left it, its equation proved on the `SfRef` route
(`Lua.Vm.Fn.<R>.spec_proved`), which the call sites use directly
(`gen_lua_at.py`'s `FPROVED`):

* `__adddf3`, `__subdf3` (round 5, B-SFREF): `Lua/Vm/Fn/SfRef{Add,Sub}.lean`;
* `__eqdf2`, `__ledf2`, `__gedf2` (lane float-sf2): `Lua/Vm/Fn/SfRefCmp.lean`;
* `__fixdfdi`, `__floatdidf`, `__floatsidf` (lane float-sf2):
  `Lua/Vm/Fn/SfRefInt.lean`.

The structure stays, empty, while the arms (`FloatArms.soft`) still name it.
-/

namespace Lua.Vm.Fn
open Lua.Num

open Lua.Vm.Sim

/-- `__floatsidf`'s argument: the `int` in the low word of `a0`. -/
abbrev Floatsidf.S (x : BitVec 64) : BitVec 64 := F64.ofInt ((x.setWidth 32).signExtend 64)
/-- `__floatdidf`. -/
abbrev Floatdidf.S (x : BitVec 64) : BitVec 64 := F64.ofInt x
/-- `__fixdfdi`: truncation toward zero; NaN, ±∞ and the out-of-range values
saturate by the sign bit (`_FP_TO_INT` with `rsigned = 1`). -/
def Fixdfdi.S (x : BitVec 64) : BitVec 64 :=
  match F64.truncInt? x with
  | some i => if -(2 ^ 63 : Int) ≤ i ∧ i < 2 ^ 63 then BitVec.ofInt 64 i
              else if F64.sign x then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1)
  | none => if F64.sign x then BitVec.ofNat 64 (2 ^ 63) else BitVec.ofNat 64 (2 ^ 63 - 1)
/-- `__eqdf2`. -/
def Eqdf2.S (a b : BitVec 64) : BitVec 64 := if F64.eq a b then 0#64 else 1#64
/-- `__ledf2`. -/
def Ledf2.S (a b : BitVec 64) : BitVec 64 :=
  match F64.compare a b with
  | some .lt => -1#64
  | some .eq => 0#64
  | some .gt => 1#64
  | none => 2#64
/-- `__gedf2`. -/
def Gedf2.S (a b : BitVec 64) : BitVec 64 :=
  match F64.compare a b with
  | some .lt => -1#64
  | some .eq => 0#64
  | some .gt => 1#64
  | none => -2#64
/-- `__adddf3`. -/
abbrev Adddf3.S (a b : BitVec 64) : BitVec 64 := F64.add a b
/-- `__subdf3`. -/
abbrev Subdf3.S (a b : BitVec 64) : BitVec 64 := F64.sub a b

end Lua.Vm.Fn

namespace Lua.Vm.Sim
open Lua.Num

open Lua.Vm.Fn

/-- **The level-2 premise**, now empty: every routine's equation is a theorem
(`Lua.Vm.Fn.<R>.spec_proved`). Kept while `FloatArms.soft` names it. -/
structure SoftFloatSpec : Prop

end Lua.Vm.Sim

namespace Lua.Vm.Fn
open Lua.Num

open Lua.Vm.Sim

/-- A sign-extended word is a canonical `int` argument. -/
theorem sext32_canon (y : BitVec 32) :
    ((LeanRV64DExecutable.Functions.sign_extend (m := 64) y).setWidth 32).signExtend 64 =
      LeanRV64DExecutable.Functions.sign_extend (m := 64) y := by
  have e : (LeanRV64DExecutable.Functions.sign_extend (m := 64) y).setWidth 32 = y := by
    simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp [BitVec.getLsbD_signExtend, hi]
    intro; omega
  rw [e]; rfl

end Lua.Vm.Fn

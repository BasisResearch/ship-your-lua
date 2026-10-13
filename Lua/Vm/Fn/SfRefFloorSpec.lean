import Lua.Vm.Fn.SfRefFloorA
import Lua.Vm.Fn.SfRefFloorB
import Lua.Vm.Fn.SfRefFloorC
import Lua.Vm.Fn.SfRefFloorD
import Lua.Vm.Fn.Floor
import Lua.Num.Arith

/-!
# `FloorSpec`, proved (lane float-sf3)

(b1) `F_eq_ref`: `floor`'s lifted function is `SfRef.floor` on every
argument (the chambers of `Lua/Vm/Fn/SfRefFloor{A,B,C,D}.lean` and the cover
`fl_cover`); (b2) `floor_model`: `SfRef.floor` is `Lua.Num.floor` on the
model (`SfRef.floor_cls`, an exact integer is the model's `ofInt`). The named
premise `FloorSpec` (`Lua/Vm/Fn/Floor.lean`) is then `floorSpec_proved`, with
the summary `FloorFn.sum` (level (a), `scripts/gen_lua_fn.py`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Lua.Vm.Fn.SfLens Lua.Vm.Fn.SfCmpLens Lua.Vm.Sim

namespace Lua.Vm.Fn.FloorFn
open Lua.Vm.Fn.FloorLens Lua.Num

set_option linter.unusedSimpArgs false
set_option linter.deprecated false

fl_cover 1023 1075

end Lua.Vm.Fn.FloorFn

namespace Lua.Num.SfRef
open F64 Float.Model

/-- An exact integer's datum is the model's `ofInt`. -/
theorem toModel_normalize (z : Int) : F64.toModel (normalize z 0 false) = Float.Model.ofInt z := by
  have h : normalize z 0 false = (Float.Model.ofInt z).toBits.toBitVec := normalize_eq_model z 0 false
  rw [h, Lua.Vm.Sim.At.toModel_toBits]

theorem toModel_qnan : F64.toModel qnan = Float.Model.nan := by
  show Float.Model.pack (UnpackedFloat.unpack Float.Model.Format.binary64 qnan) = _
  rw [unpack_eq qnan]
  rfl

/-- **(b2) for `floor`, on the model**: `SfRef.floor` is `Lua.Num.floor`
(`l_floor`, `luaconf.h:418`). -/
theorem floor_model (x : F64) : F64.toModel (floor x) = Lua.Num.floor (F64.toModel x) := by
  unfold Lua.Num.floor
  rw [toModel_unpack, floor_cls]
  rcases hc : x.cls with _ | sg | sg | ⟨sg, m, e⟩
  · exact toModel_qnan
  · rfl
  · rfl
  · have hpos := (cls_fin hc).1.pos
    rw [toU_fin hpos]
    simp only []
    by_cases he : 0 ≤ e
    · simp only [he, ite_true]
    · simp only [he, ite_false, toModel_normalize]
      cases sg
      · simp [sgn, sgnApply, Float.Model.ofNat, Float.Model.ofInt, UnpackedFloat.ofNat]
      · simp [sgn, sgnApply]

end Lua.Num.SfRef

namespace Lua.Vm.Fn.Floor
open Lua.Num

/-- `floor`'s summary with the reference as its result: `FloorFn.sum`
rewritten by `F_eq_ref`. -/
theorem sum_ref : Sum (fun _ _ _ x => SfRef.floor x) FloorFn.Fm := by
  intro m o s r g v10 hs hr hrod
  have h := FloorFn.sum m o s r g v10 hs hr hrod
  rwa [FloorFn.F_eq_ref m s r v10 hs hrod] at h

theorem spec_ref : Spec (fun _ _ _ x => SfRef.floor x) :=
  fun _ _ _ x _ => SfRef.floor_model x

end Lua.Vm.Fn.Floor

namespace Lua.Vm.Sim

/-- **`FloorSpec`, proved**: level (a) `FloorFn.sum`, (b1) `F_eq_ref`, (b2)
`floor_model`. -/
theorem floorSpec_proved : FloorSpec :=
  ⟨⟨_, _, Lua.Vm.Fn.Floor.sum_ref, Lua.Vm.Fn.Floor.spec_ref⟩⟩

end Lua.Vm.Sim

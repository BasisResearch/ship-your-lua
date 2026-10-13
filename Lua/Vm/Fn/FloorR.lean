import Lua.Vm.Fn.SfRefFloorSpec
import Lua.Vm.Sim.Kit.FltVal

/-!
# libm's `floor` by its reference, for a stored result (lane F1-F6)

The call node `Floor` of `scripts/gen_lua_at.py` (`FCALLS`, `PREMISE_PROOF`)
gives `floor`'s result through `FloorSpec`'s chosen function, of which only
the model is known (`Floor.Spec`: `toModel (F x) = Lua.Num.floor (toModel x)`).
That is enough for a test of the result (`luaV_flttointeger`), not for a
stored one: `IDIV`'s `luai_numidiv` stores `floor(a/b)`, and a stored float's
bits are the kernel's value's (`Value.ofFloat`: its sign bit too, for a NaN).

`FloorR` is the same routine with its result the reference itself,
`SfRef.floor` (`Floor.sum_ref`: level (a) `FloorFn.sum` rewritten by (b1)
`FloorFn.F_eq_ref`), so the call site's bits are known: `S_bits` is the
canonical datum of `Lua.Num.floor` (`floor_model`, and `SfRef.floor`'s result
is canonical). The arms that store `floor`'s result take this call node
(`gen_lua_at.py` `FCALL_ARM`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Lua.Vm.Sim

namespace Lua.Vm.Fn.FloorR

open Lua.Num

/-- `floor`'s result, the reference's (`FloorFn.F_eq_ref`). -/
def F (_m : Mem) (_s : Nat) (_r : BitVec 64) (x : BitVec 64) : BitVec 64 := SfRef.floor x

/-- `floor`'s frame (`FloorFn.Fm`). -/
def Fm : Mem → Nat → BitVec 64 → BitVec 64 → Mem := FloorFn.Fm

/-- **The summary** with the reference as the result (`Floor.sum_ref`). -/
theorem sum : Floor.Sum F Fm := Floor.sum_ref

/-- The result's specification: the reference. -/
abbrev S (x : BitVec 64) : BitVec 64 := SfRef.floor x

theorem spec_proved (m : Mem) (s : Nat) (r x : BitVec 64) (_hsp : FnSp s 112) : F m s r x = S x := rfl

/-- A datum that is the canonical NaN, not a NaN, or a model datum's bits is
its own model's bits. -/
theorem canon_toModel (y : F64) (h : y = F64.qnan ∨ y.cls ≠ .nan ∨ ∃ m : Float.Model, y = m.toBits.toBitVec) :
    (F64.toModel y).toBits.toBitVec = y := by
  rcases h with rfl | h | ⟨m, rfl⟩
  · decide
  · simp only [F64.toModel, Float.Model.ofBits, Float.Model.pack]
    show Float.Model.UnpackedFloat.pack Float.Model.Format.binary64
      (Float.Model.UnpackedFloat.unpack Float.Model.Format.binary64 y) = y
    rw [F64.unpack_eq]; exact F64.pack_cls y h
  · rw [Lua.Vm.Sim.At.toModel_toBits]

/-- **`floor`'s stored bits**: the canonical datum of `Lua.Num.floor`. -/
theorem S_bits (x : BitVec 64) : S x = (Lua.Num.floor (F64.toModel x)).toBits.toBitVec := by
  show SfRef.floor x = _
  rw [← SfRef.floor_model x]
  refine (canon_toModel _ ?_).symm
  rw [SfRef.floor_cls]
  rcases hc : F64.cls x with _ | sg | sg | ⟨sg, m, e⟩
  · exact .inl rfl
  · exact .inr (.inl (by rw [hc]; simp))
  · exact .inr (.inl (by rw [hc]; simp))
  · simp only []
    split
    · exact .inr (.inl (by rw [hc]; simp))
    · exact .inr (.inr ⟨Float.Model.ofInt _, F64.normalize_eq_model _ 0 false⟩)

end Lua.Vm.Fn.FloorR

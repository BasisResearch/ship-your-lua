import Lua.Num.SfRefFmod
import Lua.Num.Arith
import Lua.Vm.Sim.Kit.FltVal

/-!
# `SfRef.fmod` on the model (lane float-sf5, (b2))

`SfRef.fmod` (`Lua/Num/SfRefFmod.lean`, fdlibm's `e_fmod.c` over the
fields) is `Lua.Num.fmod` (`Lua/Num/Arith.lean`, the exact remainder) on
`Float.Model`: `fmod_cls` puts the reference in the shape of
`Lua.Num.fmod`'s `match`, and the packs are the model's (`roundExact_eq_model`).
-/

namespace Lua.Num.SfRef

open F64 Float.Model

theorem toModel_pack (u : UnpackedFloat) :
    F64.toModel (UnpackedFloat.pack Format.binary64 u) = Float.Model.pack u :=
  Lua.Vm.Sim.At.toModel_toBits (Float.Model.pack u)

theorem toModel_qnan' : F64.toModel qnan = Float.Model.nan := by
  rw [qnan_eq_pack, toModel_pack]; rfl

/-- **(b2) for `fmod`, on the model**: `SfRef.fmod` is `Lua.Num.fmod` (newlib's
`fmod`, `w_fmod.c` over `e_fmod.c`; `Lua/Num/Arith.lean`). -/
theorem fmod_model (x y : F64) :
    F64.toModel (fmod x y) = Lua.Num.fmod (F64.toModel x) (F64.toModel y) := by
  unfold Lua.Num.fmod
  rw [toModel_unpack, toModel_unpack, fmod_cls]
  rcases hx : x.cls with _ | sx | sx | ⟨sx, m₁, e₁⟩ <;>
    rcases hy : y.cls with _ | sy | sy | ⟨sy, m₂, e₂⟩
  all_goals simp only [Cls.toU]
  all_goals (try (have hp1 := (cls_fin hx).1.pos; simp only [hp1, dif_pos]))
  all_goals (try (have hp2 := (cls_fin hy).1.pos; simp only [hp2, dif_pos]))
  all_goals first
    | (exact toModel_qnan')
    | rfl
    | ((try dsimp only)
       split
       · rw [zero_eq_pack, toModel_pack]
       · rw [roundExact_eq_model _ _ _ (by omega), toModel_pack])

end Lua.Num.SfRef

import Lua.Vm.Fn.FmodW
import Lua.Vm.Fn.SfRefCmp
import Lua.Vm.Fn.SfRefFmodModel
import Lua.Vm.Fn.FloorR

/-!
# libm's `fmod` by its reference (lane F1-F7)

`fmod` (`w_fmod.c`, entry `0x8002b964`) is lifted at level (a) by
`scripts/gen_lua_fn.py` (`Lua.Vm.Fn.FmodW`: `__ieee754_fmod`, `__eqdf2`,
`__unorddf2`, `__errno`, `__divdf3` as call nodes; `errno`'s store outside
the frame, `OUTER`). Its value is

  `z := __ieee754_fmod(x, y)`; `y == 0` and `x`, `y` ordered: `errno = EDOM`,
  `0.0 / 0.0`; otherwise `z`.

On `y = ±0` the reference `SfRef.fmod x y` is already the canonical NaN
(`fmod_cls`), which is `F64.div 0 0`, so whichever way `__unorddf2` answers,
`F = SfRef.fmod` (`F_eq`): `fmod` is `__ieee754_fmod`. (b2) is lane
float-sf5's `SfRef.fmod_model`, so `fmod = Lua.Num.fmod` on the model
(`model`), and the stored bits are `Lua.Num.fmod`'s canonical datum
(`S_bits`).

`sum_ref` is the summary with the reference as its result: the call node of
the `MOD`/`MODK` float paths (`gen_lua_at.py` `FCALLS`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.FmodR

open Lua.Num

/-- `F64.eq y 0` holds only of a zero. -/
theorem eq_zero_cls {y : F64} (h : F64.eq y 0#64 = true) : ∃ s, y.cls = .zero s := by
  have h0 : F64.cls (0#64) = .zero false := by decide
  unfold F64.eq F64.compare at h
  rw [h0] at h
  rcases hy : y.cls with _ | a | a | ⟨a, m, e⟩
  all_goals rw [hy] at h
  · cases h
  · cases a <;> cases h
  · exact ⟨a, rfl⟩
  · cases a <;> cases h

/-- **`fmod` is its reference**: on `y = ±0` both answers are the canonical NaN. -/
theorem F_eq (m : Mem) (s : Nat) (r x y : BitVec 64) : FmodW.F m s r x y = SfRef.fmod x y := by
  have z : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  simp only [FmodW.F, FmodW.N_8002b984, FmodW.N_8002b994, FmodW.N_8002b998, FmodW.N_8002b9a4,
    FmodW.N_8002b9a8, FmodW.N_8002b9c4, FmodW.N_8002b9c8, FmodW.N_8002b9dc, z, BitVec.add_zero]
  rw [Eqdf2.spec_proved]
  unfold Eqdf2.S
  by_cases he : F64.eq y 0#64 = true
  · obtain ⟨sy, hy⟩ := eq_zero_cls he
    have hq : SfRef.fmod x y = F64.qnan := by
      rw [SfRef.fmod_cls, hy]; rcases F64.cls x <;> rfl
    have hd : F64.div 0#64 0#64 = F64.qnan := by
      have h0 : F64.cls (0#64) = .zero false := by decide
      unfold F64.div; rw [h0]
    simp only [he, ite_true, hq, hd]
    simp only [ite_self]
  · have h1 : ((1#64 : BitVec 64) != 0#64) = true := by decide
    simp only [he, Bool.false_eq_true, ite_false, h1, ite_true]

/-- The summary's frame (`FmodW.Fm`). -/
def Fm : Mem → Nat → BitVec 64 → SFrame → BitVec 64 → BitVec 64 → Mem := FmodW.Fm

/-- **`fmod`'s summary with the reference as its result**: the frame and the
`errno` word patched from `Fm`, the rest of memory the entry's. -/
theorem sum_ref (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 v11 : BitVec 64)
    (hs : FnSp s 160) (hr : r.toNat % 4 = 0) (hrod : RodataRead m)
    (hgp : g.gp = BitVec.ofNat 64 Lua.Vm.Layout.symGlobalPointer)
    (hsI : Lua.Vm.Layout.symImpurePtr + 8 + 160 ≤ s)
    (himp : bytesT8 m Lua.Vm.Layout.symImpurePtr = BitVec.ofNat 64 Lua.Vm.Layout.symImpureData) :
    Triple (SegSt 0x8002b964#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, SfRef.fmod v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩]
        (ArmPay (memPatch (memPatch m (Fm m s r g v10 v11) (s - 160) 160) (Fm m s r g v10 v11)
          Lua.Vm.Layout.symImpureData 4) o)) := by
  have h := FmodW.sum m o s r g v10 v11 hs hr hrod hgp hsI himp
  rwa [F_eq] at h

/-- The result's specification: the reference. -/
abbrev S (x y : BitVec 64) : BitVec 64 := SfRef.fmod x y

/-- `fmod`'s result, the reference's (`F_eq`): the call node's value. -/
def F (_m : Mem) (_s : Nat) (_r : BitVec 64) (x y : BitVec 64) : BitVec 64 := SfRef.fmod x y

theorem spec_proved (m : Mem) (s : Nat) (r x y : BitVec 64) (_hsp : FnSp s 112) : F m s r x y = S x y := rfl

/-- **The call node's summary** (`gen_lua_at.py` `FCALL_ARM`): `sum_ref` with
the result `F`. -/
theorem sum (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 v11 : BitVec 64)
    (hs : FnSp s 160) (hr : r.toNat % 4 = 0) (hrod : RodataRead m)
    (hgp : g.gp = BitVec.ofNat 64 Lua.Vm.Layout.symGlobalPointer)
    (hsI : Lua.Vm.Layout.symImpurePtr + 8 + 160 ≤ s)
    (himp : bytesT8 m Lua.Vm.Layout.symImpurePtr = BitVec.ofNat 64 Lua.Vm.Layout.symImpureData) :
    Triple (SegSt 0x8002b964#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, F m s r v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩]
        (ArmPay (memPatch (memPatch m (Fm m s r g v10 v11) (s - 160) 160) (Fm m s r g v10 v11)
          Lua.Vm.Layout.symImpureData 4) o)) :=
  sum_ref m o s r g v10 v11 hs hr hrod hgp hsI himp

/-- **(b) on the model**: `fmod` is `Lua.Num.fmod` (lane float-sf5's `fmod_model`). -/
theorem model (m : Mem) (s : Nat) (r x y : BitVec 64) :
    F64.toModel (FmodW.F m s r x y) = Lua.Num.fmod (F64.toModel x) (F64.toModel y) := by
  rw [F_eq, SfRef.fmod_model]

/-- **`fmod`'s stored bits**: the canonical datum of `Lua.Num.fmod`. -/
theorem S_bits (x y : BitVec 64) :
    S x y = (Lua.Num.fmod (F64.toModel x) (F64.toModel y)).toBits.toBitVec := by
  show SfRef.fmod x y = _
  rw [← SfRef.fmod_model x y]
  refine (FloorR.canon_toModel _ ?_).symm
  rw [SfRef.fmod_cls]
  rcases hx : F64.cls x with _ | sx | sx | ⟨sx, m₁, e₁⟩ <;>
    rcases hy : F64.cls y with _ | sy | sy | ⟨sy, m₂, e₂⟩
  all_goals simp only []
  all_goals first
    | exact .inl trivial
    | exact .inl rfl
    | exact .inr (.inl (by rw [hx]; simp))
    | skip
  all_goals
    split
    · exact .inr (.inl (by simp [F64.zero, F64.cls, F64.bexp, F64.frac, F64.bits]; split <;> simp))
    · exact .inr (.inr ⟨Float.Model.pack _, F64.roundExact_eq_model _ _ _ (Nat.pos_of_ne_zero ‹_›)⟩)

end Lua.Vm.Fn.FmodR

import Lua.Vm.Fn.PowR
import Lua.Vm.Sim.Kit.FltVal

/-!
# libm's `pow` as an arm's call node (lane F1-21)

`luai_numpow(L, a, b)` is `b == 2 ? a*a : pow(a, b)` (`llimits.h:339-342`), so
`OP_POW`'s and `OP_POWK`'s paths call `pow` (`0x8002b9fc`) when `b ≠ 2`. The
call node `PowQ` (`scripts/gen_lua_at.py` `FCALL_ARM`) is the level (a)
summary `Lua.Vm.Fn.Pow.sum` (no premise): its value `F` reads the caller's
frame (`FRAME_F`), its frame stores the caller's callee-saved registers
(`FRAME_G`, the row's thirteen), its `errno` stores are the log's second
window (`FOUTER`).

Its level (b) is conditional (`gen_lua_at.py` `FSPEC_HYP`): given
`__ieee754_pow`'s (`PowR.Ieee754PowSpec_Statement`, open) and quiet operands
(`Q`: neither a signalling NaN, outside `Float.Model`), the result is the
canonical datum of `Lua.Num.pow` (`spec`), the bits an arm stores.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.PowQ

open Lua.Num Lua.Vm.Fn.PowR

/-- **A model datum's bits are quiet**: `Float.Model`'s only NaN is the
canonical `0x7ff8000000000000`. -/
theorem notSNaN_toBits (y : Float.Model) : NotSNaN y.toBits.toBitVec :=
  (Lua.Bytecode.isSNaN_eq_false_iff _).1 (Lua.Bytecode.isSNaN_toBits y)

/-- `__floatdidf`'s result is quiet. -/
theorem notSNaN_ofInt (i : BitVec 64) : NotSNaN (F64.ofInt i) := by
  rw [F64.ofInt_eq_model]; exact notSNaN_toBits _

/-- **The model form of the obligation** (`PowR.model`'s premise). -/
theorem powModel_of (hP : Ieee754PowSpec_Statement) : Ieee754PowModel :=
  fun m s r g x y hro hs hx hy => by rw [hP m s r g x y hro hs hx hy, At.toModel_toBits]

/-- `w_pow.c`'s `1.0` is a model datum's bits. -/
theorem oneW_canon : (F64.toModel oneW).toBits.toBitVec = oneW := by decide

/-- **The wrapper's bits**: over `z`, the canonical datum of `__ieee754_pow`'s
transcription, `pow`'s value is the canonical datum of `Lua.Num.pow`. -/
theorem wrap_bits {z x y : F64}
    (hz : z = (Lua.Num.Pow.ieee754Pow (F64.toModel x) (F64.toModel y)).toBits.toBitVec) :
    wrapV z x y = (Lua.Num.pow (F64.toModel x) (F64.toModel y)).toBits.toBitVec := by
  have hm := wrap_model (z := z) (x := x) (y := y) (by rw [hz, At.toModel_toBits])
  have hc : ∃ c : Float.Model, wrapV z x y = c.toBits.toBitVec := by
    unfold wrapV
    split
    · exact ⟨_, hz⟩
    split
    · exact ⟨_, hz⟩
    split
    · exact ⟨_, hz⟩
    · exact ⟨_, oneW_canon.symm⟩
  obtain ⟨c, hc⟩ := hc
  rw [hc] at hm ⊢
  rw [At.toModel_toBits] at hm
  rw [hm]

/-- `pow`'s value (`Pow.F`): the call node's result. -/
def F : Mem → Nat → BitVec 64 → SFrame → BitVec 64 → BitVec 64 → BitVec 64 := Pow.F

/-- `pow`'s frame (`Pow.Fm`). -/
def Fm : Mem → Nat → BitVec 64 → SFrame → BitVec 64 → BitVec 64 → Mem := Pow.Fm

/-- Quiet operands (`Float.Model` has no signalling NaN). -/
def Q (x y : BitVec 64) : Prop := NotSNaN x ∧ NotSNaN y

theorem Q.mk {x y : BitVec 64} (hx : NotSNaN x) (hy : NotSNaN y) : Q x y := ⟨hx, hy⟩

/-- The result's specification: the canonical datum of `Lua.Num.pow`. -/
abbrev S (x y : BitVec 64) : BitVec 64 := (Lua.Num.pow (F64.toModel x) (F64.toModel y)).toBits.toBitVec

/-- **`pow`'s level (b)** on quiet operands, given `__ieee754_pow`'s. -/
theorem spec (hP : Ieee754PowSpec_Statement) (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame)
    (x y : BitVec 64) (hs : FnSp s 320) (hro : RodataRead m) (hq : Q x y) : F m s r g x y = S x y := by
  have z0 : sign_extend (m := 64) (0x000#12) = 0#64 := by decide
  fn_sp_factsW
  fn_imp_facts
  show Pow.F m s r g x y = _
  unfold Pow.F
  rw [n_wrap _ _ _ _ _ _ (by fn_rod_patch4)]
  simp only [z0, BitVec.add_zero]
  exact wrap_bits (hP _ _ _ _ x y (by fn_rod_patch4) (fn_sp_in hs (by decide) (by decide)) hq.1 hq.2)

/-- **The call node's summary** (`gen_lua_at.py` `FCALL_ARM`, `FRAME_G`):
`Pow.sum`. -/
theorem sum (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 v11 : BitVec 64)
    (hs : FnSp s 320) (hr : r.toNat % 4 = 0) (hrod : RodataRead m)
    (hgp : g.gp = BitVec.ofNat 64 Lua.Vm.Layout.symGlobalPointer)
    (hsI : 8 + 320 + Lua.Vm.Layout.symImpurePtr ≤ s)
    (himp : bytesT8 m Lua.Vm.Layout.symImpurePtr = BitVec.ofNat 64 Lua.Vm.Layout.symImpureData) :
    Triple (SegSt 0x8002b9fc#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, F m s r g v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩]
        (ArmPay (memPatch (memPatch m (Fm m s r g v10 v11) (s - 320) 320) (Fm m s r g v10 v11)
          Lua.Vm.Layout.symImpureData 4) o)) :=
  Pow.sum m o s r g v10 v11 hs hr hrod hgp hsI himp

end Lua.Vm.Fn.PowQ

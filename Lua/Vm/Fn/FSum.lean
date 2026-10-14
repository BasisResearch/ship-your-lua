import Lua.Vm.Fn.SfRefAdd
import Lua.Vm.Fn.SfRefSub
import Lua.Vm.Fn.SfRefMul
import Lua.Vm.Fn.SfRefCmp

/-!
# Soft-float summaries with the `F64` operation as their result (lane float-sf6)

`DivSum.lean`'s pattern for the other proved routines: `<R>.sum` (level (a),
`scripts/gen_lua_fn.py`) rewritten by `<R>.spec_proved` (level (b), the
`SfRef` route), so the result register holds `F64.add`/`F64.sub`/`F64.mul`
of the arguments (`__ledf2`: `Ledf2.S`, by `F64.compare`), and the frame
below `sp` is patched with the routine's `Fm` as before.

A routine whose lifted value passes through these calls (`__ieee754_sqrt`'s
`x*x+x` and its rounding-direction test `one-tiny`, `one+tiny`) takes them as
call nodes (`gen_lua_fn.py` `CALLEES_FOR`): its lifted value is then the
`F64` operation of the arguments, computable and independent of the memory
the caller stored before the call.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic
open Lua.Vm.Sim

namespace Lua.Vm.Fn.Adddf3

/-- **`__adddf3`'s summary, result `F64.add`** (`sum`, then `spec_proved`). -/
theorem sum_add (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 48) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002d7a8#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Num.F64.add v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10 v11) (s - 48) 48) o)) := by
  have h := sum m o s r g v10 v11 hs hr hrod
  rwa [spec_proved m s r v10 v11 hs] at h

end Lua.Vm.Fn.Adddf3

namespace Lua.Vm.Fn.Subdf3

/-- **`__subdf3`'s summary, result `F64.sub`** (`sum`, then `spec_proved`). -/
theorem sum_sub (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 48) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002e9d0#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Num.F64.sub v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10 v11) (s - 48) 48) o)) := by
  have h := sum m o s r g v10 v11 hs hr hrod
  rwa [spec_proved m s r v10 v11 hs] at h

end Lua.Vm.Fn.Subdf3

namespace Lua.Vm.Fn.Muldf3

/-- **`__muldf3`'s summary, result `F64.mul`** (`sum`, then `spec_proved`). -/
theorem sum_mul (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 80) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002e504#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Num.F64.mul v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10 v11) (s - 80) 80) o)) := by
  have h := sum m o s r g v10 v11 hs hr hrod
  rwa [spec_proved m s r v10 v11 hs] at h

end Lua.Vm.Fn.Muldf3

namespace Lua.Vm.Fn.Ledf2

/-- **`__ledf2`'s summary, result `Ledf2.S`** (`sum`, then `spec_proved`). -/
theorem sum_le (m : Mem) (o : Array String) (r : BitVec 64) (f : HFrame) (v10 v11 : BitVec 64)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002e460#64 (⟨Register.x10, v10⟩ :: ⟨Register.x11, v11⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, S v10 v11⟩ :: f.pins) (ArmPay m o)) := by
  have h := sum m o r f v10 v11 hr
  rwa [spec_proved v10 v11] at h

end Lua.Vm.Fn.Ledf2

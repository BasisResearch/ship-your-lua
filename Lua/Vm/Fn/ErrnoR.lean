import Lua.Vm.Fn.Errno
import Lua.Vm.Sim.Close

/-!
# `__errno` with `_impure_ptr`'s target as its result (lane F1-F7)

`__errno()` is `ld a0, 1224(gp); ret` (`Lua.Vm.Fn.Errno`, generated): the
value of `_impure_ptr`, `&_impure_data`, whose first word is
`_REENT->_errno`. With `gp` the global pointer and `_impure_ptr` holding its
boot value, the result is the literal `_impure_data`: `fmod`'s call node
(`gen_lua_fn.py` `CALLEES`), so the address of `fmod`'s `errno` store is a
literal (`OUTER`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Sim Vsa.Logic Lua.Vm.Sim

namespace Lua.Vm.Fn.ErrnoR

/-- **`__errno`'s summary** with its result the literal `_impure_data`. -/
theorem sum_imp (m : Mem) (o : Array String) (r : BitVec 64) (f : HFrame)
    (hgp : f.gp = BitVec.ofNat 64 Lua.Vm.Layout.symGlobalPointer)
    (himp : bytesT8 m Lua.Vm.Layout.symImpurePtr = BitVec.ofNat 64 Lua.Vm.Layout.symImpureData)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8003b40c#64 (⟨Register.x1, r⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, BitVec.ofNat 64 Lua.Vm.Layout.symImpureData⟩ :: f.pins) (ArmPay m o)) := by
  have e : Errno.F m f = BitVec.ofNat 64 Lua.Vm.Layout.symImpureData := by
    rw [Errno.F, hgp, sext64_id,
      show (BitVec.ofNat 64 Lua.Vm.Layout.symGlobalPointer + sign_extend (m := 64) (0x4c8#12)).toNat =
        Lua.Vm.Layout.symImpurePtr from by decide, himp]
  have h := Errno.sum m o r f hr hgp
  rwa [e] at h

end Lua.Vm.Fn.ErrnoR

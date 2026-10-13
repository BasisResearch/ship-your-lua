import Lua.Vm.Fn.SfRefDiv

/-!
# `__divdf3`'s summary with `F64.div` as its result

`Divdf3.sum` (level (a), `scripts/gen_lua_fn.py`) rewritten by
`Divdf3.spec_proved` (level (b), the `SfRef` route): the result is
`F64.div v10 v11`, and the 112 bytes below `sp` are patched with
`Divdf3.Fm m s r g v10 v11`. That memory stores the caller's `s0`-`s3`
(lane float-sf4's mid-body saves), so it takes the caller's frame `g`.

A routine that calls `__divdf3` on a path whose value it computes
(`__ieee754_fmod`'s `(x*y)/(x*y)`) uses this summary as a call node
(`gen_lua_fn.py` `CALLEES`). Its lifted value is then `F64.div` of the
arguments, which is computable and memory-free.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic
open Lua.Vm.Sim

namespace Lua.Vm.Fn.Divdf3

/-- **`__divdf3`'s summary, result `F64.div`** (`sum`, then `spec_proved`). -/
theorem sum_div (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 112) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002de30#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, Lua.Num.F64.div v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r g v10 v11) (s - 112) 112) o)) := by
  have h := sum m o s r g v10 v11 hs hr hrod
  rwa [spec_proved m s r v10 v11 hs] at h

end Lua.Vm.Fn.Divdf3

import Lua.Vm.Sim.Kit.Fn
import Lua.Num.F64

/-!
# `__divdf3` as a named premise (lane float-sf5)

libm's `fmod` (`w_fmod.c`) and `__ieee754_fmod` (`e_fmod.c`) call
`__divdf3` (entry `0x8002de30`, a 112-byte frame, leaf callees) on their NaN
paths: `(x*y)/(x*y)` and `0.0/0.0`. `__divdf3`'s level (a) is refused by
`scripts/gen_lua_fn.py` today (`abstractions/ledger/float-sf3.md`, "the
obstructions"); its levels (a) and (b) together are the named premise
`DivSpec` (CLAUDE.md law 2): *some* frame contents `Fm` summarise its run,
with the result `F64.div` of the arguments, in the shape
`scripts/gen_lua_fn.py` gives every framed routine (`Div.Sum`). It is
supplied by `__divdf3`'s generated summary `Divdf3.sum` and its level-(b)
equation `F = F64.div` (the `SfRef` route), and evidenced meanwhile by the
DIV arm's float vectors (`F64.div` against the ELF on Sail).

The callers' lifted functions apply `F64.div` (computable, so their `#eval`
tests run); their memory functions apply `Div.Fm`, chosen from the premise.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic
open Lua.Vm.Sim Lua.Num

namespace Lua.Vm.Fn.Div

/-- `__divdf3`'s run from its entry to its return: the result
`F64.div v10 v11`, the 112 bytes below `sp` patched with `Fm m s r v10 v11`,
the callee-saved registers and `sp` kept. -/
def Sum (Fm : Mem → Nat → BitVec 64 → BitVec 64 → BitVec 64 → Mem) : Prop :=
  ∀ (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 v11 : BitVec 64),
    FnSp s 112 → r.toNat % 4 = 0 → RodataRead m →
    Triple (SegSt 0x8002de30#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, F64.div v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10 v11) (s - 112) 112) o))

end Lua.Vm.Fn.Div

namespace Lua.Vm.Sim

open Lua.Vm.Fn

/-- **`__divdf3`'s named premise**: its run is summarised (`Div.Sum`) with the
result `F64.div`. Supplied by `__divdf3`'s level (a) (`gen_lua_fn.py`, once
its jump tables, path-fact call nodes and mid-body spills are lifted) and
level (b) (`F = F64.div`, the `SfRef` route). -/
structure DivSpec : Prop where
  ex : ∃ Fm, Div.Sum Fm

end Lua.Vm.Sim

namespace Lua.Vm.Fn.Div

open Lua.Vm.Sim

/-- The frame contents `DivSpec` provides (any, if it does not hold). -/
noncomputable def Fm : Mem → Nat → BitVec 64 → BitVec 64 → BitVec 64 → Mem :=
  Classical.epsilon fun Fm => Sum Fm

/-- **The summary**, from the premise, in the argument order of a generated
summary (`Lua.Vm.Fn.<R>.sum`). -/
theorem sum (h : DivSpec) (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame)
    (v10 v11 : BitVec 64) (hs : FnSp s 112) (hr : r.toNat % 4 = 0) (hrod : RodataRead m) :
    Triple (SegSt 0x8002de30#64 [⟨Register.x10, v10⟩, ⟨Register.x11, v11⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, F64.div v10 v11⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10 v11) (s - 112) 112) o)) :=
  Classical.epsilon_spec (p := fun Fm => Sum Fm) h.ex m o s r g v10 v11 hs hr hrod

end Lua.Vm.Fn.Div

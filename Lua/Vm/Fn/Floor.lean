import Lua.Vm.Sim.Kit.Fn
import Lua.Num.F64
import Lua.Num.Arith

/-!
# libm's `floor` as a named premise (round-5 bake-off, A-INC)

`floor` (newlib `s_floor.c`, entry `0x8002bb14`) is called on the float
paths of `LT`/`LE` (`luaV_flttointeger` inlined), the bitwise arms and
`IDIV`. It has a 64-byte frame and calls `__adddf3` (48 bytes) and
`__gedf2`, so its run uses 112 bytes below `sp`. `scripts/gen_lua_fn.py`
folds only routines whose callees keep the memory (`__clzdi2`), so its
level (a) is not generated; its level (a) and level (b) together are the
named premise `FloorSpec` (CLAUDE.md law 2), outside the pilot.

`FloorSpec` states that *some* result function `F` and frame contents `Fm`
summarise the run (`Floor.Sum`), with the result's model `Lua.Num.floor` of
the argument's; `F` and `Fm` below are chosen from it, so the call node of
`scripts/gen_lua_at.py` (`FCALLS`) uses them as it uses a generated
summary's.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic
open Lua.Vm.Sim Lua.Num

namespace Lua.Vm.Fn.Floor

/-- `floor`'s run from its entry to its return: the result `F m s r x`, the
112 bytes below `sp` patched with `Fm m s r x`, the callee-saved registers
and `sp` kept. -/
def Sum (F : Mem → Nat → BitVec 64 → BitVec 64 → BitVec 64)
    (Fm : Mem → Nat → BitVec 64 → BitVec 64 → Mem) : Prop :=
  ∀ (m : Mem) (o : Array String) (s : Nat) (r : BitVec 64) (g : SFrame) (v10 : BitVec 64),
    FnSp s 112 → r.toNat % 4 = 0 → RodataRead m →
    Triple (SegSt 0x8002bb14#64 [⟨Register.x10, v10⟩, ⟨Register.x1, r⟩, ⟨Register.x2, (BitVec.ofNat 64 s)⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay m o))
      (SegSt r [⟨Register.x10, F m s r v10⟩, ⟨Register.x2, BitVec.ofNat 64 s⟩, ⟨Register.x3, g.gp⟩, ⟨Register.x8, g.s0⟩, ⟨Register.x9, g.s1⟩, ⟨Register.x18, g.s2⟩, ⟨Register.x19, g.s3⟩, ⟨Register.x20, g.s4⟩, ⟨Register.x21, g.s5⟩, ⟨Register.x22, g.s6⟩, ⟨Register.x23, g.s7⟩, ⟨Register.x24, g.s8⟩, ⟨Register.x25, g.s9⟩, ⟨Register.x26, g.s10⟩, ⟨Register.x27, g.s11⟩] (ArmPay (memPatch m (Fm m s r v10) (s - 112) 112) o))

/-- The result is `Lua.Num.floor` of the argument, as models. -/
def Spec (F : Mem → Nat → BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  ∀ m s r x, FnSp s 112 → F64.toModel (F m s r x) = Lua.Num.floor (F64.toModel x)

end Lua.Vm.Fn.Floor

namespace Lua.Vm.Sim

open Lua.Vm.Fn Lua.Num

/-- **`floor`'s named premise**: its run is summarised (`Floor.Sum`) by a
result function whose model is `Lua.Num.floor` (`Floor.Spec`). Supplied by
`floor`'s level (a) (a fold over its segments with framed callees) and level
(b) (`s_floor.c`'s exponent masks against `Lua.Num.floor`). -/
structure FloorSpec : Prop where
  ex : ∃ F Fm, Floor.Sum F Fm ∧ Floor.Spec F

end Lua.Vm.Sim

namespace Lua.Vm.Fn.Floor

open Lua.Vm.Sim

/-- The result function `FloorSpec` provides (any, if it does not hold). -/
noncomputable def F : Mem → Nat → BitVec 64 → BitVec 64 → BitVec 64 :=
  Classical.epsilon fun F => ∃ Fm, Sum F Fm ∧ Spec F

/-- The frame contents `FloorSpec` provides for `F`. -/
noncomputable def Fm : Mem → Nat → BitVec 64 → BitVec 64 → Mem :=
  Classical.epsilon fun Fm => Sum F Fm ∧ Spec F

theorem F_spec (h : FloorSpec) : ∃ Fm, Sum F Fm ∧ Spec F :=
  Classical.epsilon_spec (p := fun F => ∃ Fm, Sum F Fm ∧ Spec F) h.ex

theorem Fm_spec (h : FloorSpec) : Sum F Fm ∧ Spec F :=
  Classical.epsilon_spec (p := fun Fm => Sum F Fm ∧ Spec F) (F_spec h)

/-- **The summary**, from the premise. -/
theorem sum (h : FloorSpec) : Sum F Fm := (Fm_spec h).1

/-- **The result's model.** -/
theorem spec (h : FloorSpec) : Spec F := (Fm_spec h).2

end Lua.Vm.Fn.Floor

import Lua.Vm.Sim.Kit.Fn

/-!
# Call nodes to framed callees (lane float-sf3)

`scripts/gen_lua_fn.py` lifts a routine whose callees are routines with
proved summaries (`floor` calls `__adddf3` and `__gedf2`): a call node runs
the callee's summary (`Lua.Vm.Fn.<R>.sum`) and the lifted function applies
the callee's lifted function (`<R>.F`, its value; `<R>.Fm`, a framed
callee's frame). This file holds what such a fold uses beyond `Kit/Fn.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## Framed callees (lane float-sf3: call nodes to proved summaries)

A framed routine (`floor`, `__muldf3`, …) that calls a framed routine
(`__adddf3`) passes it `sp - F` as its `s`: the callee's window
`[s - F - F', s - F)` lies inside the caller's (`FnSp s W`, `F + F' ≤ W`),
so the caller's summary patches `W` bytes and the callee's patch is absorbed
(`memPatch_patch_in`). -/

/-- The callee's stack facts inside the caller's window. -/
theorem fn_sp_in {s W F F' : Nat} (hs : FnSp s W) (h : F + F' ≤ W) (hF : F % 8 = 0) :
    FnSp (s - F) F' :=
  ⟨by have := hs.lo; omega, by have := hs.hi; omega, by have := hs.al; omega⟩

/-- The caller's `sp` inside its frame, `s + sext (-F)`, as the `Nat` `s - F`. -/
theorem fn_sp_nat (s : Nat) (a : BitVec 12) (k : Nat)
    (ha : sign_extend (m := 64) a = BitVec.ofNat 64 (2 ^ 64 - k)) (hk : k ≤ s) (hk2 : k ≤ 2 ^ 64)
    (hs : s < 2 ^ 64) :
    BitVec.ofNat 64 s + sign_extend (m := 64) a = BitVec.ofNat 64 (s - k) := by
  rw [ha, BitVec.ofNat_add_ofNat]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  omega

/-- **A pin put in front** (found first by `pins_of`): the caller's `sp` as
the callee's `BitVec.ofNat 64 (s - F)` at a framed call, and back after it. -/
theorem _root_.Vsa.Sim.SegSt.pin_sp {pc : BitVec 64} {L : List Pin} {P : MState → Prop}
    {c : Config} (h : SegSt pc L P c) {v : BitVec 64}
    (hv : c.σ.regs.get? Register.x2 = some v) : SegSt pc (⟨Register.x2, v⟩ :: L) P c :=
  ⟨h.good, h.pcAt, ⟨hv, h.pins⟩, h.minstret, h.tick, h.extra⟩

/-- A framed callee's patch inside the caller's window is overwritten by it. -/
theorem memPatch_patch_in {m M M' : Mem} {lo n lo' n' : Nat} (h1 : lo ≤ lo') (h2 : lo' + n' ≤ lo + n) :
    memPatch (memPatch m M' lo' n') M lo n = memPatch m M lo n :=
  Std.ExtHashMap.ext_getElem? fun x => by
    rw [getElem?_memPatch (memPatch m M' lo' n') M lo x n, getElem?_memPatch m M lo x n]
    split
    · rfl
    · exact getElem?_memPatch_out (by omega)

/-- The saved `ra` read back through the prologue's stores and the framed
callees' patches below them. -/
macro "fn_ra_patch" : tactic => `(tactic| (
  try simp (disch := kit_disch) only [bytesT8_memPatch_out, bytesT8_wm8_far]
  first
  | (rw [bytesT8_wm8_same (by kit_disch), sdData_id])
  | assumption))

/-- `.rodata` through the prologue's stores and the framed callees' patches
(the stores stripped first: `assumption` against an unstripped memory would
unfold the stores). -/
macro "fn_rod_patch" : tactic => `(tactic| (
  repeat (first
    | (refine RodataRead.wm8 ?_ (by kit_disch))
    | (refine RodataRead.patch ?_ (by kit_disch)))
  assumption))

end Lua.Vm.Sim

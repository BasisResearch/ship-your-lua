import Lua.Vm.Sim.Kit.FnCall

/-!
# A store outside a lifted routine's frame (lane F1-F7)

libm's `fmod` (`w_fmod.c`) sets `errno` on its domain error (`y = ±0`, `x`
not a NaN): `__errno()` returns `&_REENT->_errno`, the first word of
`_impure_data` (`_impure_ptr`'s target), and the wrapper stores `EDOM` there
(`sw a5, 0(a0)`). `scripts/gen_lua_fn.py` (`OUTER`) states such a routine's
memory as two patches of the entry memory, the frame window and the outer
word, both taken from the memory function:

  `memPatch (memPatch m (Fm …) (s - W) W) (Fm …) A 4`

so the memory is the entry memory outside both windows by construction
(`getElem?_memPatch_out`), as for every framed routine.

* `memPatch_wm4_outer`: the outer store is overwritten by the outer patch;
* `bytesT8_wm4_far`: a read past a 4-byte store;
* `fn_imp`: `_impure_ptr` read back through the stores and the callees'
  patches (the routine's `himp` fact at each node);
* `fn_odisch`: the side conditions over the layout's symbols.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa Vsa.Sim

namespace Lua.Vm.Sim

/-- **The outer store is overwritten by the outer patch**, the frame window
apart from it. -/
theorem memPatch_wm4_outer {m M : Mem} {lo n A a : Nat} {d : BitVec (8 * 4)} (ha : a = A)
    (hs : A + 4 ≤ lo ∨ lo + n ≤ A) :
    memPatch (memPatch (writeMap4 m a d) M lo n) M A 4 = memPatch (memPatch m M lo n) M A 4 :=
  Std.ExtHashMap.ext_getElem? fun x => by
    subst ha
    rw [getElem?_memPatch, getElem?_memPatch (memPatch m M lo n)]
    split
    · rfl
    · rw [getElem?_memPatch, getElem?_memPatch]
      split
      · rfl
      · exact getElem?_writeMap4_out m a d x (by omega)

/-- An 8-byte read past a 4-byte store. -/
theorem bytesT8_wm4_far {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 8 ≤ a ∨ a + 4 ≤ x) :
    bytesT8 (writeMap4 m a d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_writeMap4_out m a d (x + i) (by omega)

/-- The layout's symbols a routine with an outer store names, for `omega`. -/
macro "fn_imp_facts" : tactic => `(tactic| (
  have hIP : Lua.Vm.Layout.symImpurePtr = 0x8005d398 := rfl
  have hID : Lua.Vm.Layout.symImpureData = 0x8005d1b8 := rfl))

/-- A side condition over the layout's symbols: `kit_disch` with their values. -/
macro "fn_odisch" : tactic => `(tactic| first
  | kit_disch
  | (simp only [Lua.Vm.Layout.symImpureData, Lua.Vm.Layout.symImpurePtr,
      Lua.Vm.Layout.symGlobalPointer] at *
     kit_disch)
  | decide)

open Lean Elab Tactic Meta in
/-- The head of a `bytesT8 M a = v` goal's memory: `0` an 8-byte store, `1` a
patch, `3` a 4-byte store, `2` anything else. -/
def fnMemHead4 (t : Expr) : MetaM Nat := do
  let t ← instantiateMVars t
  match t.eq? with
  | some (_, l, _) =>
    if l.isAppOfArity ``Vsa.Sim.bytesT8 2 then
      let m := l.getArg! 0
      if m.isAppOfArity ``Vsa.Sim.writeMap8 3 then return 0
      if m.isAppOfArity ``Lua.Vm.Sim.memPatch 4 then return 1
      if m.isAppOfArity ``Vsa.Sim.writeMap4 3 then return 3
    return 2
  | none => return 2

open Lean Elab Tactic Meta in
/-- **`_impure_ptr` read back** through the stores and the callees' patches
(each apart from it), then the hypothesis `himp` that states it. -/
elab "fn_imp" : tactic => withMainContext do
  let mut go := true
  while go do
    match ← fnMemHead4 (← getMainTarget) with
    | 0 => evalTactic (← `(tactic| rw [Lua.Vm.Sim.bytesT8_wm8_far (by fn_odisch)]))
    | 1 => evalTactic (← `(tactic| rw [Lua.Vm.Sim.bytesT8_memPatch_out (by fn_odisch)]))
    | 3 => evalTactic (← `(tactic| rw [Lua.Vm.Sim.bytesT8_wm4_far (by fn_odisch)]))
    | _ => go := false
  evalTactic (← `(tactic| fn_assumption))

/-- `.rodata` survives a 4-byte store above the HTIF mailbox. -/
theorem RodataRead.wm4 {m : Mem} (h : RodataRead m) {a : Nat} {d : BitVec (8 * 4)}
    (ha : tohostAddr ≤ a) : RodataRead (writeMap4 m a d) := fun o ho => by
  have := Lua.Vm.Sim.rodata_below_tohost
  have e := getElem?_writeMap4_out m a d (Image.rodataBase + o) (by omega)
  simp only [bytesT1, e]
  exact h o ho

open Lean Elab Tactic Meta in
/-- The head of a `RodataRead` goal's memory (`fnMemHead4`'s codes). -/
def fnRodHead4 (t : Expr) : MetaM Nat := do
  let t ← instantiateMVars t
  if t.isAppOfArity ``Lua.Vm.Sim.RodataRead 1 then
    let m := t.appArg!
    if m.isAppOfArity ``Vsa.Sim.writeMap8 3 then return 0
    if m.isAppOfArity ``Lua.Vm.Sim.memPatch 4 then return 1
    if m.isAppOfArity ``Vsa.Sim.writeMap4 3 then return 3
  return 2

open Lean Elab Tactic Meta in
/-- `fn_rod_patch` through 4-byte stores too (a routine with an outer store). -/
elab "fn_rod_patch4" : tactic => withMainContext do
  let mut go := true
  while go do
    match ← fnRodHead4 (← getMainTarget) with
    | 0 => evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.wm8 ?_ (by fn_odisch)))
    | 1 => evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.patch ?_ (by fn_odisch)))
    | 3 => evalTactic (← `(tactic| refine Lua.Vm.Sim.RodataRead.wm4 ?_ (by fn_odisch)))
    | _ => go := false
  evalTactic (← `(tactic| fn_assumption))

open Lean Elab Tactic Meta in
/-- `fn_ra_patch` through 4-byte stores too (a routine with an outer store). -/
elab "fn_ra_patch4" : tactic => withMainContext do
  let mut go := true
  while go do
    if (← getUnsolvedGoals).isEmpty then return
    match ← fnMemHead4 (← getMainTarget) with
    | 0 => evalTactic (← `(tactic| simp (disch := fn_odisch) only [Lua.Vm.Sim.bytesT8_wm8_same,
        Lua.Vm.Sim.bytesT8_wm8_far, Lua.Vm.Sim.sdData_id]))
    | 1 => evalTactic (← `(tactic| simp (disch := fn_odisch) only [Lua.Vm.Sim.bytesT8_memPatch_out]))
    | 3 => evalTactic (← `(tactic| rw [Lua.Vm.Sim.bytesT8_wm4_far (by fn_odisch)]))
    | _ =>
      evalTactic (← `(tactic| fn_assumption))
      go := false

end Lua.Vm.Sim

import Lua.Vm.Sim.Kit.AtErrno
import Lua.Vm.Sim.Kit.AtFloat
import Lua.Vm.Fn.FmodR

/-!
# libm's `fmod` as a call node of the arms (lane F1-F7)

`OP_MOD`'s and `OP_MODK`'s float paths call `fmod` (`luai_nummod`): the call
node `FmodR` (`gen_lua_at.py` `FCALL_ARM`, `Lua.Vm.Fn.FmodR.sum`: the
reference `SfRef.fmod` as its result). What its summary needs at the row,
once:

* `at_fnSp'`: the stack facts of its 160-byte window (its own frame and
  `__ieee754_fmod`'s);
* `at_sI`: the stack above `_impure_ptr`;
* `at_gp`: `gp` the global pointer (the row's literal);
* `at_imp`: `_impure_ptr` at the call's memory, `&_impure_data` (the
  complement's `PrintCells.impure`, read through the path's stores, all in
  the heap's chunks or the C stack).

Its store to `errno` is the log's second window (`FOUTER`), whose fin lemma
is `AtFinE` (`Kit/AtErrno.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap

/-- **A frame of up to 4 KiB below `luaV_execute`'s `sp`** (`FnSp`). -/
theorem at_fnSp' {X : Cx} {F : Nat} (hX : X.Ok) (hF : F ≤ 4096 := by decide) : FnSp X.w.sp F := by
  have := hX.core.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry] at this
  exact ⟨by have : tohostAddr = 0x8005c6c0 := rfl; omega, by omega, by omega⟩

/-- The stack lies above `_impure_ptr` with room for `fmod`'s window. -/
theorem at_sI {X : Cx} (hX : X.Ok) : symImpurePtr + 8 + 160 ≤ X.w.sp := by
  have := hX.core.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry, symImpurePtr] at this ⊢
  omega

/-- The `lua_State`, the `CallInfo` and the register slots lie in the heap
(`CallInvAt`'s `L_in`, `ci_in`, `stack_in`). -/
theorem Cx.Ok.heap_ptrs {X : Cx} (hX : X.Ok) :
    0x8006ecd0 ≤ X.w.L ∧ 0x8006ecd0 ≤ X.w.ci ∧ 0x8006ecd0 ≤ X.w.base := by
  obtain ⟨ph, F, FL, ls, hI⟩ := hX.core.comp.call
  have hfit := hI.fits
  have h1 := (hI.L_in X.w.L (Nat.le_refl _) (by simp only [stateSize]; omega)).lo
  have h2 := (hI.ci_in X.w.ci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have h3 := (hI.stack_in X.w.func (Nat.le_refl _) (by simp only [stackValueSize] at hfit; omega)).lo
  simp only [RelPtrs.base, heapStart, symEnd, stackValueSize] at h1 h2 h3 ⊢
  omega

/-- **`_impure_ptr` at the arm's entry** is `&_impure_data` (the complement's
`PrintCells.impure`; the word is outside the window). -/
theorem Cx.Ok.impure_at {X : Cx} (hX : X.Ok) :
    bytesT8 X.c.σ.mem symImpurePtr = BitVec.ofNat 64 symImpureData := by
  have hc := hX.core
  obtain ⟨ph, F, FL, ls, hI⟩ := hc.comp.call
  obtain ⟨hL, hci, hb⟩ := hX.heap_ptrs
  have hsp := hc.ranges.sp_eq
  simp only [execFrame, RuntimeData.spEntry] at hsp
  have e : symImpurePtr = 0x8005d398 := rfl
  rw [e, bytesT8_congrT fun i hi => hc.frame _ fun hw => by
    rcases hw with h | h | h
    · simp only [Slots] at h; omega
    · omega
    · simp only [Scratch, ciSavedpcOff, stateTopOff, RuntimeData.spEntry, cStackBudget] at h; omega]
  rw [hI.cells.impure]; decide

/-- `gp` at a call site: the row's literal. -/
macro "at_gp" : tactic => `(tactic| rfl)

set_option hygiene false in
/-- A store's window apart from `_impure_ptr` (`at_imp`'s discharger). -/
macro "imp_sep" : tactic => `(tactic| (
  unfold Lua.Vm.Sim.At.Sep
  have := hHP.1
  have := hHP.2.1
  have := hHP.2.2
  first
    | omega
    | (simp only [ciSavedpcOff, stateTopOff, RelPtrs.slot, stackValueSize, Word.a, Word.b, Word.c,
        Word.field, Nat.shiftRight_eq_div_pow]; omega)))

set_option hygiene false in
/-- **`_impure_ptr` at a call's memory**: read through the path's stores (the
`CallInfo`, `L->top`, the register slots, the callee frames), each apart from
it, then `Cx.Ok.impure_at`. -/
macro "at_imp" : tactic => `(tactic| (
  have hImp := Cx.Ok.impure_at hX
  have hHP := Cx.Ok.heap_ptrs hX
  have hspI := at_sI hX
  have hIP : symImpurePtr = 0x8005d398 := rfl
  try at_unfold
  try simp (disch := imp_sep) only [ld8_wm8, ld8_ins, ld8_patch]
  exact hImp))

end Lua.Vm.Sim.At

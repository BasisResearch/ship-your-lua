import Lua.Vm.Sim.Entry
import Lua.Vm.Sim.Kit.Run
import Vsa.Sim.RamReadValue
import Vsa.Sim.RamReadLoad

/-!
# The return path's memory (lane F1-4, `FinalSim`)

From the fetch head at a `RETURN*` the machine leaves `luaV_execute`
(`CIST_FRESH`) and returns through `ccall`, `luaD_rawrunprotected`,
`luaD_pcall`, `lua_pcallk` and `main` to `exit`. On the path every store hits
one of a few words, `RetDirty`:

* `ci->func`, `ci->u.l.savedpc`, `ci->u2.nres` (`OP_RETURN`);
* `L->top`, `L->ci` (`OP_RETURN*`, `luaD_poscall`), `L->nCcalls` (`ccall`,
  `luaD_rawrunprotected`), `L->errorJmp` (`luaD_rawrunprotected`),
  `L->errfunc` (`luaD_pcall`);
* the callee frames below `luaV_execute`'s `sp` (`luaF_close`,
  `luaD_poscall`).

So the memory along the path is kept abstract: it agrees with the head
memory off those words (`RAgree`). A store keeps the agreement when it hits
them (`RAgree.wm8`, `wm4`); a load off them reads the head memory
(`RAgree.bytesT8` …), which the relation describes (`Core.mo8` …: outside the
window `Win` it is the complement `w.mo`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **The words the return path writes**, and the callee frames below `sp`. -/
def RetDirty (w : RelPtrs) (x : Nat) : Prop :=
  (w.ci + ciFuncOff ≤ x ∧ x < w.ci + ciFuncOff + 8) ∨
  (w.ci + ciSavedpcOff ≤ x ∧ x < w.ci + ciSavedpcOff + 8) ∨
  (w.ci + ciNresOff ≤ x ∧ x < w.ci + ciNresOff + 4) ∨
  (w.L + stateTopOff ≤ x ∧ x < w.L + stateTopOff + 8) ∨
  (w.L + stateCiOff ≤ x ∧ x < w.L + stateCiOff + 8) ∨
  (w.L + stateErrorJmpOff ≤ x ∧ x < w.L + stateErrorJmpOff + 8) ∨
  (w.L + stateErrfuncOff ≤ x ∧ x < w.L + stateErrfuncOff + 8) ∨
  (w.L + stateNCcallsOff ≤ x ∧ x < w.L + stateNCcallsOff + 4) ∨
  (RuntimeData.spEntry - cStackBudget ≤ x ∧ x < w.sp)

/-- **The memory `m` agrees with the head memory `m0`** off the dirty words. -/
def RAgree (w : RelPtrs) (m0 m : Mem) : Prop := ∀ x, ¬ RetDirty w x → m[x]? = m0[x]?

section
variable {w : RelPtrs} {m0 m : Mem}

theorem RAgree.refl (w : RelPtrs) (m : Mem) : RAgree w m m := fun _ _ => rfl

/-- An 8-byte store to dirty words keeps the agreement. -/
theorem RAgree.wm8 (h : RAgree w m0 m) {a : Nat} (d : BitVec (8 * 8))
    (hd : ∀ i, i < 8 → RetDirty w (a + i)) : RAgree w m0 (writeMap8 m a d) := fun x hx => by
  rw [getElem?_writeMap8_out m a d x (Classical.byContradiction fun hc => hx (by
    have := hd (x - a) (by omega); rwa [Nat.add_sub_cancel' (by omega)] at this))]
  exact h x hx

/-- A 4-byte store to dirty words keeps the agreement. -/
theorem RAgree.wm4 (h : RAgree w m0 m) {a : Nat} (d : BitVec (8 * 4))
    (hd : ∀ i, i < 4 → RetDirty w (a + i)) : RAgree w m0 (writeMap4 m a d) := fun x hx => by
  rw [getElem?_writeMap4_out m a d x (Classical.byContradiction fun hc => hx (by
    have := hd (x - a) (by omega); rwa [Nat.add_sub_cancel' (by omega)] at this))]
  exact h x hx

/-- A load off the dirty words reads the head memory. -/
theorem RAgree.bytesT8 (h : RAgree w m0 m) {a : Nat} (hn : ∀ i, i < 8 → ¬ RetDirty w (a + i)) :
    bytesT8 m a = bytesT8 m0 a := bytesT8_congr fun i hi => h _ (hn i hi)

theorem RAgree.bytesT4 (h : RAgree w m0 m) {a : Nat} (hn : ∀ i, i < 4 → ¬ RetDirty w (a + i)) :
    bytesT4 m a = bytesT4 m0 a := bytesT4_congr fun i hi => h _ (hn i hi)

theorem RAgree.bytesT2 (h : RAgree w m0 m) {a : Nat} (hn : ∀ i, i < 2 → ¬ RetDirty w (a + i)) :
    bytesT2 m a = bytesT2 m0 a := by
  have h0 : m[a]? = m0[a]? := h _ (hn 0 (by omega))
  have h1 := h _ (hn 1 (by omega))
  show ((m[a + 1]?).getD 0).append ((m[a]?).getD 0) = ((m0[a + 1]?).getD 0).append ((m0[a]?).getD 0)
  rw [h0, h1]

theorem RAgree.trans {m1 : Mem} (h : RAgree w m0 m) (h' : RAgree w m m1) : RAgree w m0 m1 :=
  fun x hx => (h' x hx).trans (h x hx)

end

/-- A `ret`'s target: the saved `ra`, aligned. -/
theorem rtgt (r : BitVec 64) (h : r.toNat % 4 = 0) : BitVec.update r 0 0#1 = r := by
  have := Vsa.Sim.ret_tgt r h; rwa [Vsa.Sim.sext_zero, BitVec.add_zero] at this

theorem sext32_zero : sign_extend (m := 64) (0#32 : BitVec (8 * 4)) = (0#64 : BitVec 64) := by decide
theorem sext16_zero : sign_extend (m := 64) (0#16 : BitVec (8 * 2)) = (0#64 : BitVec 64) := by decide

theorem bytesT2_wm8_out' {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 2 ≤ a ∨ a + 8 ≤ x) :
    bytesT2 (writeMap8 m a d) x = bytesT2 m x := by
  have h0 : (writeMap8 m a d)[x]? = m[x]? := getElem?_writeMap8_out m a d x (by omega)
  have h1 := getElem?_writeMap8_out m a d (x + 1) (by omega)
  show (((writeMap8 m a d)[x + 1]?).getD 0).append (((writeMap8 m a d)[x]?).getD 0) =
    ((m[x + 1]?).getD 0).append ((m[x]?).getD 0)
  rw [h0, h1]

theorem bytesT4_wm8_out'' {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 4 ≤ a ∨ a + 8 ≤ x) :
    bytesT4 (writeMap8 m a d) x = bytesT4 m x :=
  bytesT4_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

theorem bytesT8_wm8_out' {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

/-! ## The head memory, through the relation -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

theorem bytesT2_of_rd16 {m : Mem} {a x : Nat} (h : rd16 m a = some x) :
    bytesT2 m a = BitVec.ofNat 16 x := by
  rw [← bytesT_two_eq]; exact (rdLE_spec 2 m a x h).2

/-- Off the window, an 8-byte read of the machine is the complement's. -/
theorem _root_.Lua.Vm.Sim.Core.mo8 (hc : Core p c s w) {a : Nat} (h : ∀ i, i < 8 → ¬ Win p w (a + i)) :
    bytesT8 c.σ.mem a = bytesT8 w.mo a := bytesT8_congrT fun i hi => hc.frame _ (h i hi)

theorem _root_.Lua.Vm.Sim.Core.mo4 (hc : Core p c s w) {a : Nat} (h : ∀ i, i < 4 → ¬ Win p w (a + i)) :
    bytesT4 c.σ.mem a = bytesT4 w.mo a := bytesT4_congrT fun i hi => hc.frame _ (h i hi)

theorem _root_.Lua.Vm.Sim.Core.mo2 (hc : Core p c s w) {a : Nat} (h : ∀ i, i < 2 → ¬ Win p w (a + i)) :
    bytesT2 c.σ.mem a = bytesT2 w.mo a := by
  have h0 : (c.σ.mem[a]?).getD 0 = (w.mo[a]?).getD 0 := hc.frame _ (h 0 (by omega))
  have h1 : (c.σ.mem[a + 1]?).getD 0 = (w.mo[a + 1]?).getD 0 := hc.frame _ (h 1 (by omega))
  show ((c.σ.mem[a + 1]?).getD 0).append ((c.σ.mem[a]?).getD 0) =
    ((w.mo[a + 1]?).getD 0).append ((w.mo[a]?).getD 0)
  rw [h0, h1]

/-- The `lua_State` but its `top` word (`Scratch`) is off the window. -/
theorem _root_.Lua.Vm.Sim.Ranges.L_out (hr : Ranges p w) {a : Nat} (h1 : w.L ≤ a) (h2 : a < w.L + stateSize)
    (h3 : a < w.L + stateTopOff ∨ w.L + stateTopOff + 8 ≤ a) : ¬ Win p w a := by
  have := hr.L_sep; have := hr.L_top; have := hr.L_sep_ci; have := hr.sp_eq
  simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, stateSize, stateTopOff, ciSize,
    ciSavedpcOff, execFrame, cStackBudget, RuntimeData.spEntry] at *
  omega

/-- The `CallInfo` but its `savedpc` word (`Scratch`) is off the window. -/
theorem _root_.Lua.Vm.Sim.Ranges.ci_out' (hr : Ranges p w) {a : Nat} (h1 : w.ci ≤ a) (h2 : a < w.ci + ciSize)
    (h3 : a < w.ci + ciSavedpcOff ∨ w.ci + ciSavedpcOff + 8 ≤ a) : ¬ Win p w a :=
  hr.ci_out a h1 h2 h3

/-- **The head's view of the Lua state**: the words the return path reads. -/
structure HeadReads (m0 : Mem) (w : RelPtrs) : Prop where
  hookmask : bytesT4 m0 (w.L + stateHookmaskOff) = 0
  openupval : bytesT8 m0 (w.L + stateOpenupvalOff) = 0
  tbclist : bytesT8 m0 (w.L + stateTbclistOff) = BitVec.ofNat 64 w.rt.stack
  stack : bytesT8 m0 (w.L + stateStackOff) = BitVec.ofNat 64 w.rt.stack
  trap : bytesT4 m0 (w.ci + ciTrapOff) = 0
  callstatus : bytesT2 m0 (w.ci + ciCallstatusOff) = BitVec.ofNat 16 cistFresh
  nresults : bytesT2 m0 (w.ci + ciNresultsOff) = 0
  ci_top : bytesT8 m0 (w.ci + ciTopOff) = BitVec.ofNat 64 w.rt.ciTop

set_option hygiene false in
/-- The address facts of the relation, for `omega`. -/
macro "ret_facts " hr:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hr).base_lo; have := ($hr).base_hi; have := ($hr).base_al; have := ($hr).ci_lo
  have := ($hr).ci_hi; have := ($hr).code_hi; have := ($hr).code_lo; have := ($hr).L_lo
  have := ($hr).ci_sep; have := ($hr).L_sep; have := ($hr).ci_top; have := ($hr).L_top
  have := ($hr).slots_top; have := ($hr).sp_eq; have := ($hr).L_al; have := ($hr).ci_al
  have := ($hr).L_sep_ci; have := ($hr).frame_sep
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame,
    RelPtrs.base] at *))

theorem _root_.Lua.Vm.Sim.Core.headReads (hc : Core p c s w) : HeadReads c.σ.mem w := by
  have hr := hc.ranges
  have hl := hc.comp.runtime.lua
  have hL : ∀ (o k : Nat), o + k ≤ stateSize → (o + k ≤ stateTopOff ∨ stateTopOff + 8 ≤ o) →
      ∀ i, i < k → ¬ Win p w (w.L + o + i) := fun o k h1 h2 i hi =>
    hr.L_out (by omega) (by omega) (by omega)
  have hC : ∀ (o k : Nat), o + k ≤ ciSize → (o + k ≤ ciSavedpcOff ∨ ciSavedpcOff + 8 ≤ o) →
      ∀ i, i < k → ¬ Win p w (w.ci + o + i) := fun o k h1 h2 i hi =>
    hr.ci_out _ (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, hc.trap, ?_, ?_, ?_⟩
  · rw [hc.mo4 (hL _ _ (by decide) (by decide)), bytesT4_of_rd32 hl.hookmask]; rfl
  · rw [hc.mo8 (hL _ _ (by decide) (by decide)), bytesT8_of_rd64 hl.openupval]; rfl
  · rw [hc.mo8 (hL _ _ (by decide) (by decide)), bytesT8_of_rd64 hl.tbclist]
  · rw [hc.mo8 (hL _ _ (by decide) (by decide)), bytesT8_of_rd64 hl.stack]
  · rw [hc.mo2 (hC _ _ (by decide) (by decide)), bytesT2_of_rd16 hl.callstatus]
  · rw [hc.mo2 (hC _ _ (by decide) (by decide)), bytesT2_of_rd16 hl.nresults]; rfl
  · rw [hc.mo8 (hC _ _ (by decide) (by decide)), bytesT8_of_rd64 hl.ci_top]

end

end Lua.Vm.Sim.Ret

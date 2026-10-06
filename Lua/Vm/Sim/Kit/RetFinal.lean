import Lua.Vm.Sim.Kit.RetChain

/-!
# `FinalSim`: a `RETURN*` at the fetch head halts with code 0 (lane F1-4)

From `VmRel` at a state whose instruction is `RETURN`, `RETURN0` or `RETURN1`
(any operands): dispatch, the arm to the return into `ccall` (`ret_RETURN`,
`ret_RETURN0`, `ret_RETURN1`), the C return chain to `exit(0)` (`ret_chain`),
and `exit(0)` from the relation's complement (`Complement.exit`, `ExitOk`):
the memory at `exit` reads as the complement off `ExitFree`, since the run
wrote only `RetDirty` words and the head memory is the complement off the
window. The machine halts with code 0 and console `s.out`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- Off `ExitFree`, the memory at `exit` reads as the complement. -/
theorem exit_agree {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w)
    {M : Mem} (hM : RAgree w c.σ.mem M) : ∀ a, ¬ ExitFree p w a → bytesT1 M a = bytesT1 w.mo a := by
  intro a ha
  have hr := hc.ranges
  have a1 := hr.ci_top; have a2 := hr.L_top; have a3 := hr.sp_eq
  simp only [ciSize, stateSize, execFrame, cStackBudget, RuntimeData.spEntry] at a1 a2 a3
  have hS : ¬ Slots p w a := fun h => ha (.inr (.inr (.inr h)))
  have hC : ¬ (RuntimeData.spEntry - cStackBudget ≤ a ∧ a < 0x88000000) := fun h => ha (.inl h)
  have hL : ¬ (w.L ≤ a ∧ a < w.L + stateSize) := fun h => ha (.inr (.inl h))
  have hI : ¬ (w.ci ≤ a ∧ a < w.ci + ciSize) := fun h => ha (.inr (.inr (.inl h)))
  simp only [cStackBudget, RuntimeData.spEntry, stateSize, ciSize] at hC hL hI
  have hd : ¬ RetDirty w a := by
    simp only [RetDirty, ciFuncOff, ciSavedpcOff, ciNresOff, stateTopOff, stateCiOff,
      stateErrorJmpOff, stateErrfuncOff, stateNCcallsOff, cStackBudget, RuntimeData.spEntry]
    omega
  have hw : ¬ Win p w a := by
    rintro (h | h | h)
    · exact hS h
    · simp only [execFrame] at h; omega
    · simp only [Scratch, ciSavedpcOff, stateTopOff, cStackBudget, RuntimeData.spEntry] at h
      omega
  simp only [bytesT1, hM a hd]
  exact hc.frame a hw

/-- **The `Final` side of the fold**, for every `RETURN*`: from the fetch head
in the relation, the machine halts with code 0 and console `s.out`. -/
theorem vmRel_final : vmRel_final_Statement := by
  intro p c s _ ⟨w, hR⟩ hf
  cases hf with
  | ret hfe hop ho =>
  have hnum := opNum_of_op? hop
  obtain ⟨c1, hs1, -, hA, -⟩ := dispatchM hR hfe (by
    rw [hnum]; rcases ho with rfl | rfl | rfl <;> decide)
  have hc := hA.core
  have hArm : ∃ c2, Steps c1 c2 ∧ AtCcall w c1.σ.mem c1.σ.sailOutput c2 := by
    rcases ho with rfl | rfl | rfl
    · exact ret_RETURN hA (by rw [hnum]; decide)
    · exact ret_RETURN0 hA (by rw [hnum]; decide)
    · exact ret_RETURN1 hA (by rw [hnum]; decide)
  obtain ⟨c2, hs2, hq2⟩ := hArm
  obtain ⟨c3, hs3, M, q8, q9, q18, q19, q20, q21, q22, q23, q24, q25, q26, q27, hM, h⟩ :=
    ret_chain hc c1.σ.sailOutput c2 hq2
  obtain ⟨c4, σf, hs4, hh, hout⟩ :=
    hc.comp.exit M _ c3 q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 (exit_agree hc hM) h
  refine ⟨c4, σf, hs1.trans (hs2.trans (hs3.trans hs4)), hh, hout.trans ?_⟩
  rw [output_congr h.armOut]
  exact hc.out

end Lua.Vm.Sim.Ret

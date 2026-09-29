import Lua.Bytecode.Exec

/-!
# Determinism of `BcSem`

`Step` is deterministic and `Final` states are stuck, so a run from
`State.init` has at most one output. The proof goes through the executable
stepper: every `Step` is computed by `step?` (`Lua/Bytecode/Exec.lean`),
except `FORLOOP`'s exit, where `Step` (like `lvm.c`) does not read `R[A]`
but `step?` does; that case is pinned down separately (`ForloopExit`).
-/

namespace Lua.Bytecode

variable {H : Host} {p : Proto}

/-- A `FORLOOP` whose count is 0: the loop exits to the next instruction. -/
inductive ForloopExit (p : Proto) (s s' : State) : Prop where
  | intro (w : Word) (fetch : p.fetch s.pc = some w) (op : w.op? = some .FORLOOP)
      (count : s.regs (w.a + 1) = .int 0) (succ : s' = s.goto (s.pc + 1))

/-- The arithmetic opcodes fall through to `arithStep?`. -/
theorem step?_arith {s : State} {w : Word} {o : OpCode} {f}
    (hw : p.fetch s.pc = some w) (ho : w.op? = some o) (hf : intArith o = some f) :
    step? H p s = arithStep? p s w o := by
  unfold step?
  rw [hw]
  simp only [ho]
  cases o <;> first | rfl | simp [intArith] at hf

/-- Every step is `step?`'s, or a `FORLOOP` exit. -/
theorem step?_of_step {s s' : State} (h : Step H p s s') :
    step? H p s = some s' ∨ ForloopExit p s s' := by
  cases h with
  | forloopDone hw ho hn => exact .inr ⟨_, hw, ho, hn, rfl⟩
  | @arith w _ _ sh x y r hw ho hf hsh hx hy hr =>
    left
    rw [step?_arith hw ho hf]
    unfold arithStep?
    rw [hf, hsh]
    simp only [hx]
    cases sh <;> simp_all [arithOperand]
  | cmpRR hw ho hlt hf hx hy ht =>
    left; unfold step?; rw [hw]; simp only [ho]
    rcases hlt with rfl | rfl <;> simp only at hf ⊢ <;> rw [hf, hx, hy] <;> simp [ht]
  | cmpRI hw ho hlt hf hx ht =>
    left; unfold step?; rw [hw]; simp only [ho]
    rcases hlt with rfl | rfl | rfl | rfl <;> simp only at hf ⊢ <;> rw [hf, hx] <;> simp [ht]
  | _ => left; unfold step?; simp_all

/-- The `FORLOOP` exit is the only successor `step?` can compute there. -/
theorem step?_forloopExit {s s₁ s₂ : State} (h : ForloopExit p s s₂)
    (h₁ : step? H p s = some s₁) : s₁ = s₂ := by
  obtain ⟨w, hw, ho, hn, rfl⟩ := h
  unfold step? at h₁
  rw [hw] at h₁
  simp only [ho, hn] at h₁
  split at h₁
  · rename_i n i st hn' _ _
    cases hn'
    simpa using h₁.symm
  · cases h₁

/-- **`Step` is deterministic.** -/
theorem Step.deterministic {s s₁ s₂ : State} (h₁ : Step H p s s₁) (h₂ : Step H p s s₂) :
    s₁ = s₂ := by
  rcases step?_of_step h₁ with e₁ | x₁ <;> rcases step?_of_step h₂ with e₂ | x₂
  · rw [e₁] at e₂; exact Option.some.inj e₂
  · exact step?_forloopExit x₂ e₁
  · exact (step?_forloopExit x₁ e₂).symm
  · obtain ⟨_, _, _, _, rfl⟩ := x₁
    obtain ⟨_, _, _, _, rfl⟩ := x₂
    rfl

/-- `step?` computes nothing at a `RETURN*`. -/
theorem step?_final {s : State} (h : Final p s) : step? H p s = none := by
  obtain ⟨hw, ho, hr⟩ := h
  unfold step?
  rw [hw]
  simp only [ho]
  rcases hr with rfl | rfl | rfl <;> simp [arithStep?, intArith]

/-- **`Final` states are stuck.** -/
theorem Final.stuck {s s' : State} (hf : Final p s) (h : Step H p s s') : False := by
  rcases step?_of_step h with e | x
  · rw [step?_final hf] at e; cases e
  · obtain ⟨hw, ho, hr⟩ := hf
    obtain ⟨_, hw', ho', _, _⟩ := x
    rw [hw'] at hw
    cases hw
    rw [ho'] at ho
    cases ho
    rcases hr with h | h | h <;> cases h

/-- Two runs to `Final` states from the same state end in the same state. -/
theorem Steps.final_unique {a b c : State} (hb : Steps H p a b) (hfb : Final p b)
    (hc : Steps H p a c) (hfc : Final p c) : b = c := by
  induction hb generalizing c with
  | refl =>
    cases hc with
    | refl => rfl
    | head h => exact (hfb.stuck h).elim
  | head h _ ih =>
    cases hc with
    | refl => exact (hfc.stuck h).elim
    | head h' hc' =>
      cases Step.deterministic h h'
      exact ih hfb hc' hfc

/-- **`BcSem` is deterministic.** -/
theorem BcSem.deterministic {o o' : String} (h : BcSem H p o) (h' : BcSem H p o') : o = o' := by
  obtain ⟨s, hs, hf, rfl⟩ := h
  obtain ⟨s', hs', hf', rfl⟩ := h'
  rw [Steps.final_unique hs hf hs' hf']

end Lua.Bytecode

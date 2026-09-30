import Lua.Bytecode.Semantics

/-!
# An executable stepper, sound and complete for `Step`

`step?` is the opcode kernels run in `Option` (`kstep`), and `run` iterates
it to a `Final` state. They are *not* the semantics: `BcSem` is the
relation. They exist so that the kernel can build `BcSem` derivations for
concrete programs (`Lua/Programs/Validation.lean`): `run_sound` turns a
successful run into `Steps` plus `Final`. Soundness and completeness are
the generic law L-B2 (`kstep_iff`), so `Step` is deterministic
(`Step.deterministic`) and `BcSem` a function of the program
(`BcSem.deterministic`).
-/

namespace Lua.Bytecode

/-- One step, computed. -/
def step? (H : Host) (p : Proto) (s : State) : Option State := kstep (printLine H) (kernelAt p) s

/-- Is `s` at a `RETURN*`? -/
def final? (p : Proto) (s : State) : Bool :=
  match p.fetch s.pc with
  | some w =>
    match w.op? with
    | some .RETURN | some .RETURN0 | some .RETURN1 => true
    | _ => false
  | none => false

/-- Run to a `Final` state within `fuel` steps. -/
def run (H : Host) (p : Proto) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    if final? p s then some s
    else
      match step? H p s with
      | some s' => run H p n s'
      | none => none

section Soundness
variable {H : Host} {p : Proto}

/-- `step?` is sound for `Step` (L-B2). -/
theorem step?_sound {s s' : State} (h : step? H p s = some s') : Step H p s s' :=
  (kstep_iff _ _).2 h

/-- `step?` is complete for `Step` (L-B2). -/
theorem step?_complete {s s' : State} (h : Step H p s s') : step? H p s = some s' :=
  (kstep_iff _ _).1 h

theorem final?_sound {s : State} (h : final? p s = true) : Final p s := by
  unfold final? at h
  split at h
  · rename_i w hw
    split at h
    · rename_i ho; exact Final.ret hw ho (Or.inl rfl)
    · rename_i ho; exact Final.ret hw ho (Or.inr (Or.inl rfl))
    · rename_i ho; exact Final.ret hw ho (Or.inr (Or.inr rfl))
    · cases h
  · cases h

/-- A successful run is a `Steps` derivation to a `Final` state. -/
theorem run_sound : ∀ {n : Nat} {s s' : State}, run H p n s = some s' →
    Steps H p s s' ∧ Final p s'
  | 0, _, _, h => by cases h
  | n + 1, s, s', h => by
    unfold run at h
    split at h
    · rename_i hf; cases h; exact ⟨Steps.refl s, final?_sound hf⟩
    · split at h
      · rename_i s₁ h₁
        obtain ⟨hs, hfin⟩ := run_sound h
        exact ⟨Steps.head (step?_sound h₁) hs, hfin⟩
      · cases h

/-- **Validation route**: a run that ends printing `out` is a `BcSem`
derivation. -/
theorem bcSem_of_run {n : Nat} {out : String}
    (h : ((run H p n State.init).map VState.out) = some out) : BcSem H p out := by
  cases hr : run H p n State.init with
  | none => simp [hr] at h
  | some s =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    obtain ⟨hs, hf⟩ := run_sound hr
    exact ⟨s, hs, hf, h⟩

/-! ## Determinism -/

/-- **`Step` is deterministic.** -/
theorem Step.deterministic {s s₁ s₂ : State} (h₁ : Step H p s s₁) (h₂ : Step H p s s₂) :
    s₁ = s₂ :=
  KStep.det _ _ h₁ h₂

/-- A `Final` state does not step: `RETURN*` has no kernel. -/
theorem Final.not_step {s s' : State} (hf : Final p s) : ¬ Step H p s s' := fun h => by
  obtain ⟨hK, -⟩ := h
  cases hf with
  | ret hw ho hor =>
    rcases hor with rfl | rfl | rfl <;> simp [kernelAt, kernel, opKernel, hw, ho] at hK

/-- Two runs from one state to `Final` states end in the same state. -/
theorem Steps.final_unique {s a b : State} (ha : Steps H p s a) (hfa : Final p a)
    (hb : Steps H p s b) (hfb : Final p b) : a = b := by
  induction ha with
  | refl =>
    cases hb with
    | refl => rfl
    | head h _ => exact absurd h hfa.not_step
  | head h₁ _ ih =>
    cases hb with
    | refl => exact absurd h₁ hfb.not_step
    | head h₂ hs₂ => exact ih hfa ((Step.deterministic h₁ h₂) ▸ hs₂)

/-- **`BcSem` is deterministic in the output.** -/
theorem BcSem.deterministic {out₁ out₂ : String} (h₁ : BcSem H p out₁) (h₂ : BcSem H p out₂) :
    out₁ = out₂ := by
  obtain ⟨a, ha, hfa, rfl⟩ := h₁
  obtain ⟨b, hb, hfb, rfl⟩ := h₂
  rw [Steps.final_unique ha hfa hb hfb]

end Soundness

end Lua.Bytecode

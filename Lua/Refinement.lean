import Vsa.Machine

/-!
# The refinement pattern, generic in the specification

ship-your-interpreter's `Vsa/Refinement.lean` (CompCert's composition)
abstracted over the program type, the specification and the loading
relation: forward simulation (`Sim`) plus machine determinism gives the
backward direction and divergence preservation. Everything here is proved;
`Sim` is the obligation each layer discharges.
-/

namespace Lua.Refine

open Vsa.Machine

variable {P : Type} (Spec : P → String → Prop) (Loaded : P → Config → Prop)

/-- **Forward simulation**: every specified output is produced by a clean
halt, and a program with no specified behaviour never halts cleanly. -/
structure Sim : Prop where
  term_sim : ∀ p c out, Loaded p c → Spec p out → Halts c out 0
  stuck_sim : ∀ p c, Loaded p c → (¬ ∃ out, Spec p out) →
    Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

variable {Spec Loaded}

/-- Backward simulation for clean halts, from `Sim` and determinism. -/
theorem halts_spec (H : Sim Spec Loaded) {p : P} {c : Config} (hL : Loaded p c)
    {out : String} (h : Halts c out 0) : Spec p out := by
  by_cases hex : ∃ out', Spec p out'
  · obtain ⟨out', hb⟩ := hex
    obtain ⟨ho, -⟩ := h.deterministic (H.term_sim p c out' hL hb)
    exact ho ▸ hb
  · rcases H.stuck_sim p c hL hex with hd | ⟨out', e, h', he⟩
    · exact (hd.not_halts h).elim
    · obtain ⟨-, hee⟩ := h.deterministic h'
      exact (he hee.symm).elim

/-- Divergence means no specified output. -/
theorem diverges_no_spec (H : Sim Spec Loaded) {p : P} {c : Config} (hL : Loaded p c)
    (hd : Diverges c) : ¬ ∃ out, Spec p out := by
  rintro ⟨out, hb⟩
  exact hd.not_halts (H.term_sim p c out hL hb)

/-- **The refinement theorem**, generic. -/
theorem refinement (H : Sim Spec Loaded) :
    ∀ p c, Loaded p c →
      (∀ out, Spec p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, Spec p out) := by
  intro p c hL
  exact ⟨fun out => ⟨fun hb => H.term_sim p c out hL hb, fun h => halts_spec H hL h⟩,
    fun hd => diverges_no_spec H hL hd⟩

/-- The specification is deterministic on loaded programs (inherited from
the machine). -/
theorem spec_deterministic (H : Sim Spec Loaded) {p : P} {c : Config} (hL : Loaded p c)
    {out out' : String} (h : Spec p out) (h' : Spec p out') : out = out' :=
  ((H.term_sim p c out hL h).deterministic (H.term_sim p c out' hL h')).1

end Lua.Refine

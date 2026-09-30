/-!
# Opcode kernels: one term per opcode, and the metatheory proved once

The abstraction behind `Step` (abstractions/ROUND-1.md, candidates C1+C2).
Each instruction is ONE first-order term, a `Kernel`:

* static **read ports** `reads` (register indices, fixed before any value
  is seen);
* static **edges**, each with a target pc, **def ports** (registers it
  writes a value to) and **kill ports** (a register range it leaves
  undefined, ⊥: `luaV_concat`'s scratch slots, a call's clobbered frame);
* a **body** from the values of the read ports to the chosen edge index,
  the values of that edge's def ports, and what it prints.

Registers hold `Option V`; `none` is ⊥ ("whatever the machine left
there"). Reads are strict: reading ⊥ is stuck.

Everything else is derived from the term, generically in the value type:

* `KStep` has one constructor (run the kernel) and `kstep` is the same term
  run in `Option`; `kstep_iff` (law L-B2) relates them.
* `footprint` (law L-B1, with kills): two states that agree on the read
  ports take the same edge, their successors agree on what survives plus
  the def ports, and nothing outside the def and kill ports changes.
* `Cert.star` / `certain_answers`: under a must-initialised certificate,
  a run in which every kill port holds an arbitrary value (`HStep`, the
  machine's view) is matched by the ⊥-semantics run with the same output.
  This replaces `keepMask` and the CALL special case.
-/

namespace Lua.Bytecode

/-! ## States, edges, kernels -/

/-- A VM state: the instruction index, the register window (`none` = ⊥),
and everything printed so far. -/
structure VState (V : Type) where
  pc : Nat
  regs : Nat → Option V
  out : String

/-- An edge of a kernel: its target, its def ports, and its kill ports
`[killLo, killLo + killN)`. -/
structure KEdge where
  tgt : Nat
  defs : List Nat := []
  killLo : Nat := 0
  killN : Nat := 0
  deriving DecidableEq, Repr

/-- Register `j` is a kill port of `e`. -/
def KEdge.kills (e : KEdge) (j : Nat) : Prop := e.killLo ≤ j ∧ j < e.killLo + e.killN

instance (e : KEdge) (j : Nat) : Decidable (e.kills j) := inferInstanceAs (Decidable (_ ∧ _))

/-- What a kernel's body chooses: the edge, the values of its def ports (in
order), and the values to print, if any. -/
structure Out (V : Type) where
  edge : Nat
  vals : List V := []
  print : Option (List V) := none

/-- **The per-opcode term.** -/
structure Kernel (V : Type) where
  reads : List Nat
  edges : List KEdge
  body : List V → Option (Out V)

/-- Write `vs` to the def ports `ds` (the first port listed wins; a port with
no value becomes ⊥). -/
def writeDefs {V : Type} : List Nat → List V → (Nat → Option V) → Nat → Option V
  | [], _, ρ => ρ
  | d :: ds, vs, ρ => fun j => if j = d then vs.head? else writeDefs ds vs.tail ρ j

/-- Take edge `e` with outcome `o`: kill, write the defs, print, jump. -/
def VState.apply {V : Type} (line : List V → String) (e : KEdge) (o : Out V) (s : VState V) :
    VState V where
  pc := e.tgt
  regs := writeDefs e.defs o.vals fun j => if e.kills j then none else s.regs j
  out := match o.print with
    | none => s.out
    | some vs => s.out ++ line vs

section Generic
variable {V : Type} (line : List V → String) (kern : Nat → Option (Kernel V))

/-- The decision of the kernel at `s.pc`: the edge and the outcome. -/
def decide? (s : VState V) : Option (KEdge × Out V) := do
  let K ← kern s.pc
  let vs ← K.reads.mapM s.regs
  let o ← K.body vs
  let e ← K.edges[o.edge]?
  pure (e, o)

/-- One step, computed: the kernel run in `Option`. -/
def kstep (s : VState V) : Option (VState V) :=
  (decide? kern s).map fun eo => s.apply line eo.1 eo.2

/-- **One step**: fetch the kernel at `pc`, read its ports, run its body,
take the chosen edge. -/
inductive KStep : VState V → VState V → Prop where
  | run {s : VState V} {K : Kernel V} {vs : List V} {o : Out V} {e : KEdge} :
      kern s.pc = some K → K.reads.mapM s.regs = some vs → K.body vs = some o →
      K.edges[o.edge]? = some e → KStep s (s.apply line e o)

theorem decide?_eq_some {s : VState V} {e : KEdge} {o : Out V} :
    decide? kern s = some (e, o) ↔ ∃ K vs, kern s.pc = some K ∧ K.reads.mapM s.regs = some vs ∧
      K.body vs = some o ∧ K.edges[o.edge]? = some e := by
  simp only [decide?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨K, hK, vs, hvs, o', ho, e', he, rfl, rfl⟩; exact ⟨K, vs, hK, hvs, ho, he⟩
  · rintro ⟨K, vs, hK, hvs, ho, he⟩; exact ⟨K, hK, vs, hvs, o, ho, e, he, rfl, rfl⟩

/-- **L-B2**: the relation is the graph of the stepper. -/
theorem kstep_iff {s s' : VState V} : KStep line kern s s' ↔ kstep line kern s = some s' := by
  constructor
  · rintro ⟨hK, hvs, ho, he⟩
    simp only [kstep, Option.map_eq_some_iff]
    exact ⟨_, (decide?_eq_some kern).2 ⟨_, _, hK, hvs, ho, he⟩, rfl⟩
  · intro h
    obtain ⟨⟨e, o⟩, hd, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨K, vs, hK, hvs, ho, he⟩ := (decide?_eq_some kern).1 hd
    exact KStep.run hK hvs ho he

/-- `KStep` is deterministic. -/
theorem KStep.det {s s₁ s₂ : VState V} (h₁ : KStep line kern s s₁) (h₂ : KStep line kern s s₂) :
    s₁ = s₂ :=
  Option.some.inj (((kstep_iff line kern).1 h₁).symm.trans ((kstep_iff line kern).1 h₂))

end Generic

/-! ## Agreement and the footprint law -/

/-- `s₁` and `s₂` are at the same pc, have printed the same, and agree on
the registers in `m`. -/
structure Agree {V : Type} (m : Nat → Prop) (s₁ s₂ : VState V) : Prop where
  pc : s₁.pc = s₂.pc
  out : s₁.out = s₂.out
  regs : ∀ j, m j → s₁.regs j = s₂.regs j

theorem mapM_congr {V : Type} {f g : Nat → Option V} :
    ∀ {l : List Nat}, (∀ r ∈ l, f r = g r) → l.mapM f = l.mapM g
  | [], _ => rfl
  | r :: l, h => by
    simp only [List.mapM_cons, h r List.mem_cons_self,
      mapM_congr fun r' hr' => h r' (List.mem_cons_of_mem _ hr')]

theorem writeDefs_not_mem {V : Type} {j : Nat} :
    ∀ {ds : List Nat} {vs : List V} {ρ : Nat → Option V}, j ∉ ds → writeDefs ds vs ρ j = ρ j
  | [], _, _, _ => rfl
  | d :: ds, vs, ρ, h => by
    simp only [writeDefs, List.mem_cons, not_or] at h ⊢
    simp only [h.1, ↓reduceIte, writeDefs_not_mem h.2]

theorem writeDefs_mem {V : Type} {j : Nat} :
    ∀ {ds : List Nat} {vs : List V} {ρ ρ' : Nat → Option V}, j ∈ ds →
      writeDefs ds vs ρ j = writeDefs ds vs ρ' j
  | [], _, _, _, h => by cases h
  | d :: ds, vs, ρ, ρ', h => by
    simp only [writeDefs]
    split
    · rfl
    · rename_i hj
      exact writeDefs_mem ((List.mem_cons.1 h).resolve_left hj)

section Footprint
variable {V : Type} {line : List V → String} {kern : Nat → Option (Kernel V)}

/-- The kernel's decision depends only on the pc and the read ports. -/
theorem decide?_congr {m : Nat → Prop} {s₁ s₂ : VState V} (hag : Agree m s₁ s₂)
    (hr : ∀ K, kern s₁.pc = some K → ∀ r ∈ K.reads, m r) : decide? kern s₁ = decide? kern s₂ := by
  unfold decide?
  rw [← hag.pc]
  cases hK : kern s₁.pc with
  | none => rfl
  | some K =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [mapM_congr fun r hr' => hag.regs r (hr K hK r hr')]

/-- Taking the same edge from agreeing states: the successors agree on
what survives the kill ports plus the def ports. -/
theorem Agree.apply {m : Nat → Prop} {s₁ s₂ : VState V} (hag : Agree m s₁ s₂) (e : KEdge)
    (o : Out V) :
    Agree (fun j => (m j ∧ ¬ e.kills j) ∨ j ∈ e.defs) (s₁.apply line e o) (s₂.apply line e o) := by
  refine ⟨rfl, ?_, fun j hj => ?_⟩
  · simp only [VState.apply, hag.out]
  · simp only [VState.apply]
    by_cases hd : j ∈ e.defs
    · exact writeDefs_mem hd
    · rw [writeDefs_not_mem hd, writeDefs_not_mem hd]
      obtain ⟨hm, hk⟩ := hj.resolve_right hd
      simp only [hk, ↓reduceIte]
      exact hag.regs j hm

/-- The frame: outside its def and kill ports, a step changes no register;
its kill ports that are not def ports become ⊥. -/
theorem apply_regs_frame (s : VState V) (e : KEdge) (o : Out V) {j : Nat} (hd : j ∉ e.defs) :
    (s.apply line e o).regs j = if e.kills j then none else s.regs j := by
  simp only [VState.apply, writeDefs_not_mem hd]

/-- What the footprint law says about a step `s₁ → s₁'` along the edge `e`
of the kernel at `s₁.pc`, matched by `s₂ → s₂'`. -/
structure StepMatch (kern : Nat → Option (Kernel V)) (m : Nat → Prop) (s₁ s₁' s₂' : VState V)
    (e : KEdge) : Prop where
  /-- `e` is an edge of the kernel at `s₁.pc` -/
  edge : ∀ K, kern s₁.pc = some K → e ∈ K.edges
  tgt : s₁'.pc = e.tgt
  /-- the successors agree on what survives the kill ports plus the def ports -/
  agree : Agree (fun j => (m j ∧ ¬ e.kills j) ∨ j ∈ e.defs) s₁' s₂'
  /-- outside the def and kill ports nothing changed -/
  frame : ∀ j, j ∉ e.defs → ¬ e.kills j → s₁'.regs j = s₁.regs j

/-- **L-B1, the footprint law, with kills.** Two states that agree on pc,
output and the read ports of the kernel at pc are both stuck or both step,
along the same edge of that kernel (`StepMatch`). -/
theorem footprint {m : Nat → Prop} {s₁ s₂ : VState V} (hag : Agree m s₁ s₂)
    (hr : ∀ K, kern s₁.pc = some K → ∀ r ∈ K.reads, m r) :
    (kstep line kern s₁ = none ↔ kstep line kern s₂ = none) ∧
    ∀ {s₁'}, KStep line kern s₁ s₁' →
      ∃ s₂' e, KStep line kern s₂ s₂' ∧ StepMatch kern m s₁ s₁' s₂' e := by
  have hd := decide?_congr hag hr
  refine ⟨by simp only [kstep, Option.map_eq_none_iff, hd], fun h => ?_⟩
  obtain ⟨hK, hvs, ho, he⟩ := h
  rename_i K vs o e
  obtain ⟨K', vs', hK', hvs', ho', he'⟩ :=
    (decide?_eq_some kern).1 (hd ▸ (decide?_eq_some kern).2 ⟨K, vs, hK, hvs, ho, he⟩)
  refine ⟨_, e, KStep.run hK' hvs' ho' he', ⟨fun K'' hK'' => ?_, rfl, hag.apply e o,
    fun j hj hk => ?_⟩⟩
  · cases hK.symm.trans hK''; exact List.mem_of_getElem? he
  · simp only [apply_regs_frame _ _ _ hj, hk, ↓reduceIte]

end Footprint

/-! ## Certain answers: kill ports are unobservable -/

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | head {a b c : α} : R a b → Star R b c → Star R a c

theorem Star.mono {α : Type} {R R' : α → α → Prop} (hR : ∀ a b, R a b → R' a b) {a b : α}
    (h : Star R a b) : Star R' a b := by
  induction h with
  | refl => exact Star.refl _
  | head h _ ih => exact Star.head (hR _ _ h) ih

section Certain
variable {V : Type} (line : List V → String) (kern : Nat → Option (Kernel V))

/-- The machine's view of a step: take the kernel's edge, then every kill
port that is not a def port holds an arbitrary value. -/
inductive HStep : VState V → VState V → Prop where
  | run {s : VState V} {K : Kernel V} {vs : List V} {o : Out V} {e : KEdge}
      (ρ : Nat → Option V) :
      kern s.pc = some K → K.reads.mapM s.regs = some vs → K.body vs = some o →
      K.edges[o.edge]? = some e →
      (∀ j, j ∈ e.defs ∨ ¬ e.kills j → ρ j = (s.apply line e o).regs j) →
      HStep s { s.apply line e o with regs := ρ }

theorem KStep.hstep {s s' : VState V} (h : KStep line kern s s') : HStep line kern s s' := by
  obtain ⟨hK, hvs, ho, he⟩ := h
  exact HStep.run _ hK hvs ho he fun _ _ => rfl

/-- **A must-initialised certificate** `M pc`: every read port is in the
mask at its pc, and along every edge the target's mask is contained in what
survives the kill ports plus the def ports. -/
structure Cert (M : Nat → Nat → Prop) : Prop where
  reads : ∀ pc K, kern pc = some K → ∀ r ∈ K.reads, M pc r
  stable : ∀ pc K, kern pc = some K → ∀ e ∈ K.edges, ∀ j, M e.tgt j →
    (M pc j ∧ ¬ e.kills j) ∨ j ∈ e.defs

variable {line kern}

/-- **The invariant, one step.** A machine step from a state agreeing with
`s₂` on the mask is matched by a `KStep` from `s₂`, ending in agreement on
the successor's mask. -/
theorem Cert.step {M : Nat → Nat → Prop} (hC : Cert kern M) {s₁ s₁' s₂ : VState V}
    (h : HStep line kern s₁ s₁') (hag : Agree (M s₁.pc) s₁ s₂) :
    ∃ s₂', KStep line kern s₂ s₂' ∧ Agree (M s₁'.pc) s₁' s₂' := by
  obtain ⟨ρ, hK, hvs, ho, he, hρ⟩ := h
  rename_i K vs o e
  obtain ⟨K', vs', hK', hvs', ho', he'⟩ := (decide?_eq_some kern).1
    (decide?_congr hag (hC.reads _) ▸ (decide?_eq_some kern).2 ⟨K, vs, hK, hvs, ho, he⟩)
  have hag' := hag.apply (line := line) e o
  refine ⟨_, KStep.run hK' hvs' ho' he', rfl, hag'.out, fun j hj => ?_⟩
  have hs := hC.stable _ _ hK e (List.mem_of_getElem? he) j hj
  rw [← hag'.regs j hs]
  exact hρ j (hs.elim (fun h => Or.inr h.2) Or.inl)

/-- **The invariant along runs.** -/
theorem Cert.star {M : Nat → Nat → Prop} (hC : Cert kern M) {s₁ s₁' s₂ : VState V}
    (h : Star (HStep line kern) s₁ s₁') (hag : Agree (M s₁.pc) s₁ s₂) :
    ∃ s₂', Star (KStep line kern) s₂ s₂' ∧ Agree (M s₁'.pc) s₁' s₂' := by
  induction h generalizing s₂ with
  | refl => exact ⟨s₂, Star.refl _, hag⟩
  | head h _ ih =>
    obtain ⟨s₂', hs, hag'⟩ := hC.step h hag
    obtain ⟨s₃, hs₃, hag₃⟩ := ih hag'
    exact ⟨s₃, Star.head hs hs₃, hag₃⟩

/-- Runs of `R` from `s₀` that reach a final pc (`fin`), having printed `out`. -/
def RunOut {V : Type} (R : VState V → VState V → Prop) (fin : Nat → Prop) (s₀ : VState V)
    (out : String) : Prop :=
  ∃ s, Star R s₀ s ∧ fin s.pc ∧ s.out = out

/-- **Certain answers.** Under a certificate, the outputs of the machine
view (kill ports arbitrary) from `s₁` are outputs of the ⊥-semantics from
any `s₂` that agrees with `s₁` on the entry mask. -/
theorem certain_answers {M : Nat → Nat → Prop} (hC : Cert kern M) {fin : Nat → Prop}
    {s₁ s₂ : VState V} (hag : Agree (M s₁.pc) s₁ s₂) {out : String}
    (h : RunOut (HStep line kern) fin s₁ out) : RunOut (KStep line kern) fin s₂ out := by
  obtain ⟨s, hs, hf, ho⟩ := h
  obtain ⟨s', hs', hag'⟩ := hC.star hs hag
  exact ⟨s', hs', hag'.pc ▸ hf, hag'.out ▸ ho⟩

end Certain

end Lua.Bytecode

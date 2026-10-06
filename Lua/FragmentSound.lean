import Lua.Bytecode.Exec
import Lua.Fragment

/-!
# Soundness of `Supported`'s definite-initialisation analysis

At `luaV_execute`'s entry the frame's registers hold stale stack values,
and a call leaves the frame above its results stale; `BcSem` says ⊥ for
both (the entry state, the kill ports). This file proves that on
`Supported` programs the machine's view (any values there) has exactly
`BcSem`'s outputs. There is no per-opcode argument: the analysis is read
off the kernels' ports, and the proof is the generic certain-answers
theorem of `Lua/Bytecode/Kernel.lean`.

* `Supported.defInit`: the fixpoint that `supportedB` computes is a
  certificate (`DefInit`): the entry mask is empty, every edge's target mask
  is contained in the source mask minus the edge's kill ports plus its def
  ports, and every instruction's read ports are in its mask.
* `DefInit.cert`: that certificate is the generic `Cert` of the kernels.
* `DefInit.step`: two states that agree on the mask at their (common) pc step
  to states that agree on the mask at the successor.
* `bcSemFrom_iff`: `BcSem` from any initial register file equals `BcSem`.
* `cbcSem_iff`: the same with every kill port (a call's clobbered frame)
  holding arbitrary values after each step (`HStep`).
* `reachable_defInit`: the per-state form, with the well-formedness
  consequences (the pc stays in range, reads are in the mask).
-/

namespace Lua.Bytecode

/-! ## Bit masks -/

theorem testBit_rmask (a n j : Nat) :
    (rmask a n).testBit j = decide (a ≤ j ∧ j < a + n) := by
  unfold rmask
  rw [Nat.testBit_mul_two_pow]
  by_cases h : a ≤ j
  · simp only [h, decide_true, Nat.testBit_two_pow_sub_one, Bool.true_and, true_and]
    congr 1; apply propext; omega
  · simp [h]

theorem testBit_listMask (l : List Nat) (j : Nat) : (listMask l).testBit j = decide (j ∈ l) := by
  induction l with
  | nil => simp [listMask]
  | cons r l ih =>
    have : listMask (r :: l) = rmask r 1 ||| listMask l := rfl
    rw [this, Nat.testBit_or, testBit_rmask, ih]
    by_cases h : j = r
    · subst h; simp
    · simp [h]; omega

theorem testBit_mdiff (s t j : Nat) :
    (mdiff s t).testBit j = (s.testBit j && !t.testBit j) := by
  simp only [mdiff, Nat.testBit_xor, Nat.testBit_and]
  cases s.testBit j <;> cases t.testBit j <;> rfl

theorem msub_iff {s t : Nat} : msub s t = true ↔ s &&& t = s := by
  simp [msub]

theorem msub_testBit {s t : Nat} (h : msub s t = true) {j : Nat} (hj : s.testBit j = true) :
    t.testBit j = true := by
  rw [msub_iff] at h
  rw [← h, Nat.testBit_and] at hj
  simp only [Bool.and_eq_true] at hj
  exact hj.2

/-! ## The analysis as a certificate

`sweep` is a Gauss–Seidel pass: each edge update only shrinks one entry
(`LLe`). A pass that changes nothing therefore changed nothing at any edge,
so every edge's constraint holds at the fixpoint (`sweep_stable`). -/

/-- Pointwise mask inclusion of two analysis states. -/
def LLe (a b : List Nat) : Prop := ∀ i, a.getD i 0 &&& b.getD i 0 = a.getD i 0

theorem LLe.refl (a : List Nat) : LLe a a := fun _ => Nat.and_self _

theorem LLe.trans {a b c : List Nat} (h₁ : LLe a b) (h₂ : LLe b c) : LLe a c := fun i => by
  rw [← h₁ i, Nat.and_assoc, h₂ i]

theorem LLe.antisymm {a b : List Nat} (h₁ : LLe a b) (h₂ : LLe b a) (i : Nat) :
    a.getD i 0 = b.getD i 0 := by
  rw [← h₁ i, Nat.and_comm, h₂ i]

section Fold
variable {σ α : Type} {f : σ → α → σ} {R : σ → σ → Prop}

/-- A fold of shrinking steps shrinks. -/
theorem foldl_shrink (htrans : ∀ a b c, R a b → R b c → R a c) (hrefl : ∀ s, R s s)
    (hdec : ∀ s x, R (f s x) s) : ∀ (l : List α) (s : σ), R (l.foldl f s) s
  | [], s => hrefl s
  | x :: l, s => htrans _ _ _ (foldl_shrink htrans hrefl hdec l (f s x)) (hdec s x)

/-- If a fold of shrinking steps did not shrink, every step met a state
equivalent to the start on which it did not shrink. -/
theorem foldl_stable (htrans : ∀ a b c, R a b → R b c → R a c) (hrefl : ∀ s, R s s)
    (hdec : ∀ s x, R (f s x) s) :
    ∀ (l : List α) (s : σ), R s (l.foldl f s) →
      ∀ x ∈ l, ∃ s', R s' s ∧ R s s' ∧ R s' (f s' x)
  | [], _, _, x, hx => by cases hx
  | y :: l, s, h, x, hx => by
    have hfold := foldl_shrink htrans hrefl hdec l (f s y)
    have hup : R s (f s y) := htrans _ _ _ h hfold
    rcases List.mem_cons.1 hx with rfl | hx
    · exact ⟨s, hrefl s, hrefl s, hup⟩
    · obtain ⟨s', h₁, h₂, h₃⟩ :=
        foldl_stable htrans hrefl hdec l (f s y) (htrans _ _ _ (hdec s y) h) x hx
      exact ⟨s', htrans _ _ _ h₁ (hdec s y), htrans _ _ _ hup h₂, h₃⟩

end Fold

theorem getD_set_self {l : List Nat} {t v : Nat} (ht : t < l.length) :
    (l.set t v).getD t 0 = v := by
  simp [List.getD_eq_getElem?_getD, ht]

theorem getD_set_ne {l : List Nat} {t i v : Nat} (h : i ≠ t) :
    (l.set t v).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, Ne.symm h]

theorem getD_set_ge {l : List Nat} {t v : Nat} (ht : l.length ≤ t) :
    (l.set t v).getD t 0 = l.getD t 0 := by
  simp [List.getD_eq_getElem?_getD, Nat.not_lt.2 ht]

/-- An update `st[t] := st[t] ∩ x` shrinks. -/
theorem LLe_set_and (st : List Nat) (t x : Nat) :
    LLe (st.set t (st.getD t 0 &&& x)) st := fun i => by
  by_cases hi : i = t
  · subst hi
    by_cases ht : i < st.length
    · rw [getD_set_self ht, Nat.and_assoc, Nat.and_comm x, ← Nat.and_assoc, Nat.and_self]
    · rw [getD_set_ge (Nat.not_lt.1 ht), Nat.and_self]
  · rw [getD_set_ne hi, Nat.and_self]

/-- The edge update inside `sweep`. -/
def edgeUpd (pc : Nat) (st : List Nat) (e : Edge) : List Nat :=
  if e.1 = 0 then st
  else st.set e.1 (st.getD e.1 0 &&& (mdiff (st.getD pc 0) e.2.2 ||| e.2.1))

theorem edgeUpd_shrink (pc : Nat) (st : List Nat) (e : Edge) : LLe (edgeUpd pc st e) st := by
  unfold edgeUpd; split
  · exact LLe.refl _
  · exact LLe_set_and _ _ _

/-- One `sweep` round's update of the edges out of `pc`. -/
def pcUpd (es : List (List Edge)) (st : List Nat) (pc : Nat) : List Nat :=
  (es.getD pc []).foldl (edgeUpd pc) st

theorem sweep_eq (es : List (List Edge)) (st : List Nat) :
    sweep es st = (List.range es.length).foldl (pcUpd es) st := rfl

theorem pcUpd_shrink (es : List (List Edge)) (st : List Nat) (pc : Nat) :
    LLe (pcUpd es st pc) st :=
  foldl_shrink (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl (edgeUpd_shrink pc) _ st

theorem sweep_shrink (es : List (List Edge)) (st : List Nat) : LLe (sweep es st) st := by
  rw [sweep_eq]
  exact foldl_shrink (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl (pcUpd_shrink es) _ st

/-- **A stable sweep satisfies every edge constraint.** -/
theorem sweep_stable {es : List (List Edge)} {st : List Nat} (h : sweep es st = st)
    {pc : Nat} {e : Edge} (he : e ∈ es.getD pc []) (h0 : e.1 ≠ 0) :
    st.getD e.1 0 &&& (mdiff (st.getD pc 0) e.2.2 ||| e.2.1) = st.getD e.1 0 := by
  have hpc : pc ∈ List.range es.length := by
    rw [List.mem_range]
    refine Classical.byContradiction fun hn => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hn)] at he
    cases he
  have hs : LLe st ((List.range es.length).foldl (pcUpd es) st) := by
    rw [← sweep_eq, h]; exact LLe.refl _
  obtain ⟨s₁, h₁, h₂, h₃⟩ := foldl_stable (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl
    (pcUpd_shrink es) _ st hs pc hpc
  obtain ⟨s₂, h₄, h₅, h₆⟩ := foldl_stable (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl
    (edgeUpd_shrink pc) _ s₁ h₃ e he
  have eq₁ : ∀ i, s₂.getD i 0 = st.getD i 0 := fun i =>
    (LLe.antisymm h₄ h₅ i).trans (LLe.antisymm h₁ h₂ i)
  have h₇ := h₆ e.1
  unfold edgeUpd at h₇
  simp only [h0, ↓reduceIte] at h₇
  by_cases ht : e.1 < s₂.length
  · rw [getD_set_self ht, ← Nat.and_assoc, Nat.and_self, eq₁, eq₁] at h₇
    exact h₇
  · rw [← eq₁, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 ht)]
    simp

theorem fixpoint_spec (es : List (List Edge)) :
    ∀ (fuel : Nat) (st₀ st : List Nat), fixpoint es fuel st₀ = some st →
      sweep es st = st ∧ LLe st st₀
  | 0, _, _, h => by cases h
  | fuel + 1, st₀, st, h => by
    unfold fixpoint at h
    simp only at h
    split at h
    · rename_i heq
      cases h
      exact ⟨beq_iff_eq.1 heq, LLe.refl _⟩
    · obtain ⟨h₁, h₂⟩ := fixpoint_spec es fuel _ _ h
      exact ⟨h₁, h₂.trans (sweep_shrink es st₀)⟩

theorem mapM_range_some {β : Type} {f : Nat → Option β} {d : β} :
    ∀ {n : Nat} {es : List β}, (List.range n).mapM f = some es →
      es.length = n ∧ ∀ i, i < n → f i = some (es.getD i d)
  | 0, es, h => by
    simp only [List.range_zero, List.mapM_nil] at h
    cases h; exact ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1, es, h => by
    rw [List.range_succ, List.mapM_append] at h
    simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.pure_def,
      Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    obtain ⟨x, hx, _, rfl, rfl⟩ := hb
    obtain ⟨hlen, hf⟩ := mapM_range_some ha
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hf i hi, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (hlen ▸ hi)]
    · rw [hx, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
        Nat.sub_self]; rfl

/-! ## `Supported` gives a certificate -/

/-- **The definite-initialisation certificate**: a mask `M pc` of registers
per instruction, with an empty entry mask, closed under every edge (`M t`
is contained in `M pc` minus the edge's kill ports plus its def ports),
containing every instruction's read ports, and with every instruction's
edges well-formed (`edges` succeeds). -/
structure DefInit (p : Proto) (M : Nat → Nat) : Prop where
  /-- the chunk is not empty, so the entry pc is in range -/
  pos : 0 < p.code.length
  /-- nothing is initialised at entry -/
  entry : M 0 = 0
  /-- every instruction has well-formed edges -/
  total : ∀ pc w, p.fetch pc = some w → edges p pc ≠ none
  /-- the masks are closed under the edges -/
  stable : ∀ pc l, edges p pc = some l → ∀ e ∈ l,
    msub (M e.1) (mdiff (M pc) e.2.2 ||| e.2.1) = true
  /-- every register an instruction reads is initialised -/
  reads : ∀ pc w, p.fetch pc = some w → msub (reads p pc w) (M pc) = true

/-- The mask `supportedB` computes at `pc` (0 when the analysis fails). -/
def defMask (p : Proto) (pc : Nat) : Nat :=
  match (List.range p.code.length).mapM (edges p) with
  | none => 0
  | some es =>
    match fixpoint es (2 * p.code.length + 2)
        (0 :: List.replicate (p.code.length - 1) allRegs) with
    | none => 0
    | some st => st.getD pc 0

theorem fetch_lt {p : Proto} {pc : Nat} {w : Word} (h : p.fetch pc = some w) :
    pc < p.code.length :=
  (List.getElem?_eq_some_iff.1 h).1

theorem edges_lt {p : Proto} {pc : Nat} {l : List Edge} (h : edges p pc = some l) :
    pc < p.code.length := by
  unfold edges at h
  split at h
  · cases h
  · exact fetch_lt ‹_›

/-- **Supported yields the certificate** for the mask it computed. -/
theorem Supported.defInit {p : Proto} (h : Supported p) : DefInit p (defMask p) := by
  unfold Supported supportedB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨_, hpos⟩, _⟩, h⟩ := h
  split at h
  · cases h
  · rename_i es hes
    simp only [Bool.and_eq_true] at h
    obtain ⟨_, h⟩ := h
    split at h
    · cases h
    · rename_i st hst
      have hM : ∀ pc, defMask p pc = st.getD pc 0 := fun pc => by
        unfold defMask; rw [hes]; simp only; rw [hst]
      obtain ⟨hfix, hle⟩ := fixpoint_spec es _ _ _ hst
      obtain ⟨_, hedges⟩ := mapM_range_some (d := []) hes
      have h0 : st.getD 0 0 = 0 := by
        have := hle 0
        simp only [List.getD_cons_zero, Nat.and_zero] at this
        exact this.symm
      have hl : ∀ pc l, edges p pc = some l → l = es.getD pc [] := fun pc l he => by
        rw [hedges pc (edges_lt he)] at he
        exact (Option.some.inj he).symm
      refine ⟨hpos, (hM 0).trans h0, ?_, ?_, ?_⟩
      · intro pc w hw
        rw [hedges pc (fetch_lt hw)]; exact Option.some_ne_none _
      · intro pc l he e hel
        rw [hM, hM, msub_iff]
        by_cases he0 : e.1 = 0
        · rw [he0, h0, Nat.zero_and]
        · exact sweep_stable hfix (hl pc l he ▸ hel) he0
      · intro pc w hw
        have := List.all_eq_true.1 h pc (List.mem_range.2 (fetch_lt hw))
        rw [hw] at this
        rw [hM]; exact this

/-! ## The certificate is the kernels' generic `Cert` -/

/-- The edges of an instruction that has a kernel are its kernel's edges,
all in range and none into the entry pc 0. -/
theorem edges_of_kernel_pos {p : Proto} {pc : Nat} {K : Kernel Value}
    (hK : kernelAt p pc = some K) (hne : edges p pc ≠ none) :
    edges p pc = some (K.edges.map KEdge.toEdge) ∧
      ∀ e ∈ K.edges, 0 < e.tgt ∧ e.tgt < p.code.length := by
  obtain ⟨w, hw, hK⟩ := Option.bind_eq_some_iff.1 hK
  unfold edges at hne ⊢
  simp only [hw, hK] at hne ⊢
  split at hne
  · rename_i hall
    exact ⟨by simp only [hall, ↓reduceIte],
      fun e he => of_decide_eq_true (List.all_eq_true.1 hall e he)⟩
  · exact absurd rfl hne

/-- The edges of an instruction that has a kernel are its kernel's edges,
all in range. -/
theorem edges_of_kernel {p : Proto} {pc : Nat} {K : Kernel Value} (hK : kernelAt p pc = some K)
    (hne : edges p pc ≠ none) :
    edges p pc = some (K.edges.map KEdge.toEdge) ∧ ∀ e ∈ K.edges, e.tgt < p.code.length :=
  ⟨(edges_of_kernel_pos hK hne).1, fun e he => ((edges_of_kernel_pos hK hne).2 e he).2⟩

theorem DefInit.total' {p : Proto} {M : Nat → Nat} (hD : DefInit p M) {pc : Nat}
    {K : Kernel Value} (hK : kernelAt p pc = some K) : edges p pc ≠ none :=
  hD.total pc _ (Option.bind_eq_some_iff.1 hK).choose_spec.1

/-- **The analysis certificate is a `Cert` of the kernels.** -/
theorem DefInit.cert {p : Proto} {M : Nat → Nat} (hD : DefInit p M) :
    Cert (kernelAt p) (fun pc j => (M pc).testBit j = true) where
  reads pc K hK r hr := by
    obtain ⟨w, hw, hK'⟩ := Option.bind_eq_some_iff.1 hK
    have hm := hD.reads pc w hw
    simp only [Lua.Bytecode.reads, hK', Option.map_some, Option.getD_some] at hm
    exact msub_testBit hm (by rw [testBit_listMask]; exact decide_eq_true hr)
  stable pc K hK e he j hj := by
    have hs := hD.stable pc _ (edges_of_kernel hK (hD.total' hK)).1 e.toEdge
      (List.mem_map_of_mem he)
    have := msub_testBit hs hj
    simp only [KEdge.toEdge, Nat.testBit_or, testBit_mdiff, testBit_rmask, testBit_listMask,
      Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] at this
    exact this.imp (fun h => ⟨h.1, h.2⟩) id

section Inv
variable {H : Host} {p : Proto} {M : Nat → Nat}

/-- Every step of a supported program lands in range. -/
theorem DefInit.pc_lt (hD : DefInit p M) {s s' : State} (h : Step H p s s') :
    s'.pc < p.code.length := by
  obtain ⟨hK, -, -, he⟩ := h
  exact (edges_of_kernel hK (hD.total' hK)).2 _ (List.mem_of_getElem? he)

/-- Every step of a supported program leaves the entry pc 0 for good: no
edge targets it (`edges`). -/
theorem DefInit.pc_pos (hD : DefInit p M) {s s' : State} (h : Step H p s s') : 0 < s'.pc := by
  obtain ⟨hK, -, -, he⟩ := h
  exact ((edges_of_kernel_pos hK (hD.total' hK)).2 _ (List.mem_of_getElem? he)).1

/-- **The invariant, one step.** Two states at the same pc that agree on
that pc's mask step (in lockstep) to states that agree on the successor's
mask. -/
theorem DefInit.step (hD : DefInit p M) {s₁ s₁' s₂ : State} (h : Step H p s₁ s₁')
    (hag : Agree (fun j => (M s₁.pc).testBit j) s₁ s₂) :
    ∃ s₂', Step H p s₂ s₂' ∧ Agree (fun j => (M s₁'.pc).testBit j) s₁' s₂' :=
  hD.cert.step (KStep.hstep _ _ h) hag

/-- Entry states agree on the (empty) entry mask, whatever their registers. -/
theorem DefInit.entry_agree (hD : DefInit p M) (s₁ s₂ : State) (h₁ : s₁.pc = 0)
    (h₂ : s₂.pc = 0) (ho : s₁.out = s₂.out) : Agree (fun j => (M s₁.pc).testBit j) s₁ s₂ :=
  ⟨h₁.trans h₂.symm, ho, fun j hj => by rw [h₁, hD.entry, Nat.zero_testBit] at hj; cases hj⟩

end Inv

/-! ## Entry registers and kill ports are unobservable -/

theorem Steps.star {H : Host} {p : Proto} {a b : State} (h : Steps H p a b) :
    Star (Step H p) a b := by
  induction h with
  | refl => exact Star.refl _
  | head h _ ih => exact Star.head h ih

theorem Star.steps {H : Host} {p : Proto} {a b : State} (h : Star (Step H p) a b) :
    Steps H p a b := by
  induction h with
  | refl => exact Steps.refl _
  | head h _ ih => exact Steps.head h ih

/-- The entry state of `luaV_execute` with register file `ρ` (the stale
stack contents). -/
def State.initWith (ρ : Nat → Value) : State := ⟨0, fun j => some (ρ j), ""⟩

/-- `pc` is at a `RETURN*`. -/
def FinalPc (p : Proto) (pc : Nat) : Prop := Final p ⟨pc, fun _ => none, ""⟩

theorem final_iff {p : Proto} {s : State} : Final p s ↔ FinalPc p s.pc :=
  ⟨fun ⟨hw, ho, hor⟩ => ⟨hw, ho, hor⟩, fun ⟨hw, ho, hor⟩ => ⟨hw, ho, hor⟩⟩

theorem bcSem_iff_run {H : Host} {p : Proto} {out : String} :
    BcSem H p out ↔ RunOut (Step H p) (FinalPc p) State.init out :=
  ⟨fun ⟨s, hs, hf, ho⟩ => ⟨s, hs.star, final_iff.1 hf, ho⟩,
    fun ⟨s, hs, hf, ho⟩ => ⟨s, hs.steps, final_iff.2 hf, ho⟩⟩

/-- `BcSem` from the register file `ρ` at entry. -/
def BcSemFrom (H : Host) (p : Proto) (ρ : Nat → Value) : String → Prop :=
  RunOut (Step H p) (FinalPc p) (State.initWith ρ)

/-- The machine's view: `BcSem` from the register file `ρ` at entry, with
every kill port (a call's clobbered frame) holding anything after each step. -/
def CBcSem (H : Host) (p : Proto) (ρ : Nat → Value) : String → Prop :=
  RunOut (HStep (printLine H) (kernelAt p)) (FinalPc p) (State.initWith ρ)

theorem RunOut.hstep {H : Host} {p : Proto} {s : State} {out : String}
    (h : RunOut (Step H p) (FinalPc p) s out) :
    RunOut (HStep (printLine H) (kernelAt p)) (FinalPc p) s out :=
  let ⟨s', hs, hf, ho⟩ := h; ⟨s', hs.mono fun _ _ => KStep.hstep _ _, hf, ho⟩

/-- **Independence from the initial registers.** For a supported program,
`BcSem` from any entry register file is `BcSem`: the stale stack values at
`luaV_execute`'s entry are never observed. -/
theorem bcSemFrom_iff {H : Host} {p : Proto} (hS : Supported p) (ρ : Nat → Value)
    (out : String) : BcSemFrom H p ρ out ↔ BcSem H p out := by
  have hD := hS.defInit
  rw [bcSem_iff_run]
  exact ⟨fun h => certain_answers hD.cert (hD.entry_agree (.initWith ρ) .init rfl rfl rfl) h.hstep,
    fun h => certain_answers hD.cert (hD.entry_agree .init (.initWith ρ) rfl rfl rfl) h.hstep⟩

/-- **Independence from the kill ports.** For a supported program, running
from any entry register file with every kill port (a `CALL`'s clobbered
frame) holding arbitrary values after each step gives exactly `BcSem`'s
outputs. -/
theorem cbcSem_iff {H : Host} {p : Proto} (hS : Supported p) (ρ : Nat → Value)
    (out : String) : CBcSem H p ρ out ↔ BcSem H p out := by
  have hD := hS.defInit
  rw [bcSem_iff_run]
  exact ⟨certain_answers hD.cert (hD.entry_agree (.initWith ρ) .init rfl rfl rfl),
    fun h => (certain_answers hD.cert (hD.entry_agree .init (.initWith ρ) rfl rfl rfl)
      h.hstep).hstep⟩

/-- What holds at every state a supported program reaches. -/
structure DefInitAt (H : Host) (p : Proto) (s : State) : Prop where
  /-- the pc is in range: the fetch succeeds -/
  pc_lt : s.pc < p.code.length
  /-- every register the instruction reads is in the mask -/
  reads : ∀ w, p.fetch s.pc = some w → msub (reads p s.pc w) (defMask p s.pc) = true
  /-- the masked registers were written on the path: every run from any
  entry registers reaches a state agreeing with `s` on the mask -/
  path : ∀ ρ, ∃ s', Steps H p (State.initWith ρ) s' ∧
    Agree (fun j => (defMask p s.pc).testBit j) s s'

/-- **The per-state invariant**: along any run of a supported program from
any entry registers, the pc stays in range, the instruction's reads are in
the mask, and the masked registers hold values that do not depend on the
entry registers. -/
theorem reachable_defInit {H : Host} {p : Proto} (hS : Supported p) {ρ₀ : Nat → Value}
    {s : State} (h : Steps H p (State.initWith ρ₀) s) : DefInitAt H p s := by
  have hD := hS.defInit
  have hlt : ∀ {a b : State}, Steps H p a b → a.pc < p.code.length → b.pc < p.code.length :=
    fun h ha => by
      induction h with
      | refl => exact ha
      | head h₁ _ ih => exact ih (hD.pc_lt h₁)
  refine ⟨hlt h hD.pos, fun w hw => hD.reads _ w hw, fun ρ => ?_⟩
  obtain ⟨s', hs', hag⟩ := hD.cert.star (h.star.mono fun _ _ => KStep.hstep _ _)
    (hD.entry_agree _ (.initWith ρ) rfl rfl rfl)
  exact ⟨s', hs'.steps, hag⟩

end Lua.Bytecode

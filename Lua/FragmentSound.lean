import Lua.Bytecode.Exec
import Lua.Fragment

/-!
# Soundness of `Supported`'s definite-initialisation analysis

The part of `Supported` that A1 relies on semantically (PHASES.md, A1
"Definite initialisation"): at `luaV_execute`'s entry the frame's registers
hold stale stack values, and after a C call every register from the call's
base up is clobbered except the results. `BcSem` starts from all-`nil`
registers and keeps them across `print`. This file proves the two agree on
`Supported` programs.

* `Supported.defInit`: the fixpoint that `supportedB` computes is a
  certificate (`DefInit`): the entry mask is empty, every edge's target mask
  is contained in the source mask (restricted by `keepMask`) plus the
  registers written along the edge, and every instruction's `reads` are in
  its mask.
* `DefInit.step`: two states that agree on the mask at their (common) pc step
  to states that agree on the mask at the successor. This is the invariant:
  a register the analysis says is initialised has a value determined by the
  path from entry, not by the initial registers or by what a call left
  above its results.
* `bcSemFrom_iff`: `BcSem` from any initial register file equals `BcSem`
  from all-`nil` (`State.initWith`).
* `cbcSem_iff`: the same with every register at or above a `CALL`'s results
  arbitrarily clobbered after each call (`CStep`).
* `reachable_defInit`: the per-state form, with the well-formedness
  consequences (the pc stays in range, reads are in the mask).
* `condJump_valid`: in a supported program a conditional test's jump target
  exists and is in range.

`Step.deterministic` and `BcSem.deterministic` are here too.
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

section
variable (p : Proto)

/-- The edge update inside `sweep`. -/
def edgeUpd (pc : Nat) (st : List Nat) (e : Edge) : List Nat :=
  if e.1 = 0 then st
  else st.set e.1 (st.getD e.1 0 &&& ((st.getD pc 0 &&& keepMask p pc) ||| e.2))

theorem edgeUpd_shrink (pc : Nat) (st : List Nat) (e : Edge) : LLe (edgeUpd p pc st e) st := by
  unfold edgeUpd; split
  · exact LLe.refl _
  · exact LLe_set_and _ _ _

/-- One `sweep` round's update of the edges out of `pc`. -/
def pcUpd (es : List (List Edge)) (st : List Nat) (pc : Nat) : List Nat :=
  (es.getD pc []).foldl (edgeUpd p pc) st

theorem sweep_eq (es : List (List Edge)) (st : List Nat) :
    sweep p es st = (List.range es.length).foldl (pcUpd p es) st := rfl

theorem pcUpd_shrink (es : List (List Edge)) (st : List Nat) (pc : Nat) :
    LLe (pcUpd p es st pc) st :=
  foldl_shrink (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl (edgeUpd_shrink p pc) _ st

theorem sweep_shrink (es : List (List Edge)) (st : List Nat) : LLe (sweep p es st) st := by
  rw [sweep_eq]
  exact foldl_shrink (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl (pcUpd_shrink p es) _ st

/-- **A stable sweep satisfies every edge constraint.** -/
theorem sweep_stable {es : List (List Edge)} {st : List Nat} (h : sweep p es st = st)
    {pc : Nat} {e : Edge} (he : e ∈ es.getD pc []) (h0 : e.1 ≠ 0) :
    st.getD e.1 0 &&& ((st.getD pc 0 &&& keepMask p pc) ||| e.2) = st.getD e.1 0 := by
  have hpc : pc ∈ List.range es.length := by
    rw [List.mem_range]
    refine Classical.byContradiction fun hn => ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.not_lt.1 hn)] at he
    cases he
  have hs : LLe st ((List.range es.length).foldl (pcUpd p es) st) := by
    rw [← sweep_eq, h]; exact LLe.refl _
  obtain ⟨s₁, h₁, h₂, h₃⟩ := foldl_stable (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl
    (pcUpd_shrink p es) _ st hs pc hpc
  obtain ⟨s₂, h₄, h₅, h₆⟩ := foldl_stable (R := LLe) (fun _ _ _ => LLe.trans) LLe.refl
    (edgeUpd_shrink p pc) _ s₁ h₃ e he
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
    ∀ (fuel : Nat) (st₀ st : List Nat), fixpoint p es fuel st₀ = some st →
      sweep p es st = st ∧ LLe st st₀
  | 0, _, _, h => by cases h
  | fuel + 1, st₀, st, h => by
    unfold fixpoint at h
    simp only at h
    split at h
    · rename_i heq
      cases h
      exact ⟨beq_iff_eq.1 heq, LLe.refl _⟩
    · obtain ⟨h₁, h₂⟩ := fixpoint_spec es fuel _ _ h
      exact ⟨h₁, h₂.trans (sweep_shrink p es st₀)⟩

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

end

/-! ## `Supported` gives a certificate -/

/-- **The definite-initialisation certificate**: a mask `M pc` of registers
per instruction, with an empty entry mask, closed under every edge (`M t`
is contained in what survives `keepMask` of `M pc` plus what the edge
writes), containing every instruction's `reads`, and with every
instruction's edges well-formed (`edges` succeeds). -/
structure DefInit (p : Proto) (M : Nat → Nat) : Prop where
  /-- the chunk is not empty, so the entry pc is in range -/
  pos : 0 < p.code.length
  /-- nothing is initialised at entry -/
  entry : M 0 = 0
  /-- every instruction has well-formed edges -/
  total : ∀ pc w, p.fetch pc = some w → edges p pc ≠ none
  /-- the masks are closed under the edges -/
  stable : ∀ pc l, edges p pc = some l → ∀ e ∈ l,
    msub (M e.1) ((M pc &&& keepMask p pc) ||| e.2) = true
  /-- every register an instruction reads is initialised -/
  reads : ∀ pc w, p.fetch pc = some w → msub (reads w) (M pc) = true

/-- The mask `supportedB` computes at `pc` (0 when the analysis fails). -/
def defMask (p : Proto) (pc : Nat) : Nat :=
  match (List.range p.code.length).mapM (edges p) with
  | none => 0
  | some es =>
    match fixpoint p es (2 * p.code.length + 2)
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

/-- Every edge target of a well-formed instruction is in range. -/
theorem edges_target_lt {p : Proto} {pc : Nat} {l : List Edge} (h : edges p pc = some l)
    {e : Edge} (he : e ∈ l) : e.1 < p.code.length := by
  unfold edges at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i hall; cases h
          exact of_decide_eq_true (List.all_eq_true.1 hall e he)
        · cases h

/-- **`Supported` yields the certificate** for the mask it computed. -/
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
      obtain ⟨hfix, hle⟩ := fixpoint_spec p es _ _ _ hst
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
        · exact sweep_stable p hfix (hl pc l he ▸ hel) he0
      · intro pc w hw
        have := List.all_eq_true.1 h pc (List.mem_range.2 (fetch_lt hw))
        rw [hw] at this
        rw [hM]; exact this

/-! ## Agreement of two states on a register mask -/

/-- `s₁` and `s₂` are at the same pc, have printed the same, and agree on
the registers in `m`. -/
structure Agree (m : Nat) (s₁ s₂ : State) : Prop where
  pc : s₁.pc = s₂.pc
  out : s₁.out = s₂.out
  regs : ∀ j, m.testBit j = true → s₁.regs j = s₂.regs j

namespace Agree
variable {m : Nat} {s₁ s₂ : State}

theorem symm (h : Agree m s₁ s₂) : Agree m s₂ s₁ :=
  ⟨h.pc.symm, h.out.symm, fun j hj => (h.regs j hj).symm⟩

theorem mono {m' : Nat} (h : Agree m s₁ s₂) (hm : ∀ j, m'.testBit j = true → m.testBit j = true) :
    Agree m' s₁ s₂ :=
  ⟨h.pc, h.out, fun j hj => h.regs j (hm j hj)⟩

theorem zero (h : Agree m s₁ s₂) : Agree (m ||| 0) s₁ s₂ := by rw [Nat.or_zero]; exact h

theorem goto {t₁ t₂ : Nat} (h : Agree m s₁ s₂) (ht : t₁ = t₂) : Agree m (s₁.goto t₁) (s₂.goto t₂) :=
  ⟨ht, h.out, h.regs⟩

theorem emit {str : String} (h : Agree m s₁ s₂) : Agree m (s₁.emit str) (s₂.emit str) :=
  ⟨h.pc, by simp [State.emit, h.out], h.regs⟩

theorem set {a : Nat} {v₁ v₂ : Value} (h : Agree m s₁ s₂) (hv : v₁ = v₂) :
    Agree (m ||| rmask a 1) (s₁.set a v₁) (s₂.set a v₂) := by
  refine ⟨h.pc, h.out, fun j hj => ?_⟩
  simp only [State.set]
  split
  · exact hv
  · rename_i hja
    simp only [Nat.testBit_or, testBit_rmask, Bool.or_eq_true, decide_eq_true_eq] at hj
    exact h.regs j (hj.resolve_right (by omega))

theorem setNils {a n : Nat} (h : Agree m s₁ s₂) :
    Agree (m ||| rmask a n) (s₁.setNils a n) (s₂.setNils a n) := by
  refine ⟨h.pc, h.out, fun j hj => ?_⟩
  simp only [State.setNils]
  split
  · rfl
  · rename_i hja
    simp only [Nat.testBit_or, testBit_rmask, Bool.or_eq_true, decide_eq_true_eq] at hj
    exact h.regs j (hj.resolve_right hja)

end Agree

/-! ## One step: agreement on the reads suffices -/

section Sim
variable {H : Host} {p : Proto}

theorem edgesOf_of_edges {pc : Nat} {w : Word} {o : OpCode} {l : List Edge}
    (hl : edges p pc = some l) (hw : p.fetch pc = some w) (ho : w.op? = some o) :
    edgesOf p pc w o = some l := by
  unfold edges at hl
  rw [hw] at hl
  simp only [ho] at hl
  split at hl
  · cases hl
  · split at hl
    · cases hl; assumption
    · cases hl

theorem condJump_mem {pc : Nat} {c k : Bool} {t : Nat} {l : List Edge}
    (hl : condEdges p pc = some l) (ht : condJump p pc c k = some t) : (t, 0) ∈ l := by
  unfold condEdges at hl
  cases hj : nextJump p pc with
  | none => simp [hj] at hl
  | some t' =>
    simp only [hj, Option.map_some, Option.some.injEq] at hl
    subst hl
    unfold condJump at ht
    split at ht
    · cases ht; simp
    · have : nextJump p pc = some t := ht
      rw [hj] at this; cases this; simp

/-- The edge list of an integer binary operation. -/
theorem edgesOf_arith {pc : Nat} {w : Word} {o : OpCode} {f sh} {l : List Edge}
    (hf : intArith o = some f) (hsh : arithShape o = some sh) (hl : edgesOf p pc w o = some l) :
    l = [(pc + 2, rmask w.a 1)] := by
  cases o <;> simp only [intArith, arithShape, reduceCtorEq] at hf hsh <;>
    simp only [edgesOf, Option.some.injEq] at hl <;>
    first
    | exact hl.symm
    | (split at hl <;> first | exact (Option.some.inj hl).symm | cases hl)

/-- The registers an integer binary operation reads. -/
theorem reads_arith {w : Word} {o : OpCode} {sh : ArithShape} (ho : w.op? = some o)
    (hsh : arithShape o = some sh) :
    (reads w).testBit w.b = true ∧ (sh = .rr → (reads w).testBit w.c = true) := by
  cases o <;> simp only [arithShape, reduceCtorEq, Option.some.injEq] at hsh <;> subst hsh <;>
    simp [reads, ho, testBit_rmask]

theorem args_eq {s₁ s₂ : State} {a n : Nat} (h : ∀ j, j < n → s₁.regs (a + j) = s₂.regs (a + j)) :
    s₁.args a n = s₂.args a n := by
  unfold State.args
  exact List.map_congr_left fun j hj => h j (List.mem_range.1 hj)

/-- **One-step simulation.** If `s₁` steps to `s₁'` and `s₂` agrees with
`s₁` on a mask `m` holding the registers the instruction reads, then `s₂`
steps along the same edge, and the successors agree on `m` plus what the
edge writes. -/
theorem Step.sim {s₁ s₁' s₂ : State} {m : Nat} {l : List Edge} (h : Step H p s₁ s₁')
    (hl : edges p s₁.pc = some l) (hag : Agree m s₁ s₂)
    (hr : ∀ w, p.fetch s₁.pc = some w → msub (reads w) m = true) :
    ∃ s₂', Step H p s₂ s₂' ∧ ∃ wr, (s₁'.pc, wr) ∈ l ∧ Agree (m ||| wr) s₁' s₂' := by
  have rd : ∀ {w : Word}, p.fetch s₁.pc = some w → ∀ j, (reads w).testBit j = true →
      s₁.regs j = s₂.regs j := fun hw j hj => hag.regs j (msub_testBit (hr _ hw) hj)
  have hpc := hag.pc
  cases h with
  | @move w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have hb := rd hw w.b (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.move (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set hb).goto (by simp [hpc])⟩
  | @loadi w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.loadi (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @loadk w c v hw ho hc hv =>
    have hl' := edgesOf_of_edges hl hw ho
    dsimp only [edgesOf] at hl'; rw [hc] at hl'
    have hl'' : l = [(s₁.pc + 1, rmask w.a 1)] := by
      cases c <;> simp_all [Const.toValue?]
    subst hl''
    exact ⟨_, Step.loadk (hpc ▸ hw) ho hc hv, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @loadfalse w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.loadfalse (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @lfalseskip w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.lfalseskip (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @loadtrue w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.loadtrue (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @loadnil w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.loadnil (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      hag.setNils.goto (by simp [hpc])⟩
  | @gettabupPrint w hw ho hb hc =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, hb, hc, and_self, ite_true, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.gettabupPrint (hpc ▸ hw) ho hb hc, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @arith w o f sh x y r hw ho hf hsh hx hy hr =>
    have hl' := edgesOf_arith hf hsh (edgesOf_of_edges hl hw ho); subst hl'
    obtain ⟨hrb, hrc⟩ := reads_arith ho hsh
    have hx' : s₂.regs w.b = .int x := (rd hw _ hrb) ▸ hx
    refine ⟨_, Step.arith (hpc ▸ hw) ho hf hsh hx' ?_ hr, _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
    cases sh
    · exact (rd hw _ (hrc rfl)) ▸ hy
    · exact hy
    · exact hy
  | @unm w x hw ho hx =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have hx' := (rd hw w.b (by simp [reads, ho, testBit_rmask])) ▸ hx
    exact ⟨_, Step.unm (hpc ▸ hw) ho hx', _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @bnot w x hw ho hx =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have hx' := (rd hw w.b (by simp [reads, ho, testBit_rmask])) ▸ hx
    exact ⟨_, Step.bnot (hpc ▸ hw) ho hx', _, List.mem_singleton_self _,
      (hag.set rfl).goto (by simp [hpc])⟩
  | @not w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have hb := rd hw w.b (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.not (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.set (by rw [hb])).goto (by simp [hpc])⟩
  | @jmp w t hw ho ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, ht, Option.map_some, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.jmp (hpc ▸ hw) ho (hpc ▸ ht), _, List.mem_singleton_self _,
      (hag.goto rfl).zero⟩
  | @eq w t hw ho ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    have ha := rd hw w.a (by simp [reads, ho, testBit_rmask])
    have hb := rd hw w.b (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.eq (hpc ▸ hw) ho (by rw [← hpc, ← ha, ← hb]; exact ht), _,
      condJump_mem hl' ht, (hag.goto rfl).zero⟩
  | @eqk w c v t hw ho hc hv ht =>
    have hl' := edgesOf_of_edges hl hw ho
    have hl'' : condEdges p s₁.pc = some l := by
      dsimp only [edgesOf] at hl'; rw [hc] at hl'
      cases c <;> simp_all [Const.toValue?]
    have ha := rd hw w.a (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.eqk (hpc ▸ hw) ho hc hv (by rw [← hpc, ← ha]; exact ht), _,
      condJump_mem hl'' ht, (hag.goto rfl).zero⟩
  | @eqi w t hw ho ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    have ha := rd hw w.a (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.eqi (hpc ▸ hw) ho (by rw [← hpc, ← ha]; exact ht), _,
      condJump_mem hl' ht, (hag.goto rfl).zero⟩
  | @cmpRR w o f x y t hw ho hor hf hx hy ht =>
    have hl' := edgesOf_of_edges hl hw ho
    have hl'' : condEdges p s₁.pc = some l := by
      rcases hor with rfl | rfl <;> exact hl'
    have hrd : (reads w).testBit w.a = true ∧ (reads w).testBit w.b = true := by
      rcases hor with rfl | rfl <;> simp [reads, ho, testBit_rmask]
    exact ⟨_, Step.cmpRR (hpc ▸ hw) ho hor hf ((rd hw _ hrd.1) ▸ hx) ((rd hw _ hrd.2) ▸ hy)
      (hpc ▸ ht), _, condJump_mem hl'' ht, (hag.goto rfl).zero⟩
  | @cmpRI w o f x t hw ho hor hf hx ht =>
    have hl' := edgesOf_of_edges hl hw ho
    have hl'' : condEdges p s₁.pc = some l := by
      rcases hor with rfl | rfl | rfl | rfl <;> exact hl'
    have hrd : (reads w).testBit w.a = true := by
      rcases hor with rfl | rfl | rfl | rfl <;> simp [reads, ho, testBit_rmask]
    exact ⟨_, Step.cmpRI (hpc ▸ hw) ho hor hf ((rd hw _ hrd) ▸ hx) (hpc ▸ ht), _,
      condJump_mem hl'' ht, (hag.goto rfl).zero⟩
  | @test w t hw ho ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    have ha := rd hw w.a (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.test (hpc ▸ hw) ho (by rw [← hpc, ← ha]; exact ht), _,
      condJump_mem hl' ht, (hag.goto rfl).zero⟩
  | @testsetSkip w hw ho hk =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.1 hl'
    have hb := rd hw w.b (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.testsetSkip (hpc ▸ hw) ho (hb ▸ hk), _, by simp [State.goto],
      (hag.goto (by rw [hpc])).zero⟩
  | @testsetJump w ni t hw ho hk hni ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.1 hl'
    have htt : t' = t := by
      unfold nextJump at ht'; rw [hni] at ht'; exact Option.some.inj (ht'.symm.trans ht)
    subst htt
    have hb := rd hw w.b (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.testsetJump (hpc ▸ hw) ho (hb ▸ hk) (hpc ▸ hni) (hpc ▸ ht), _,
      by simp [State.goto], (hag.set hb).goto rfl⟩
  | @forprepEnter w i lim st n hw ho hi hlim hst h0 hn =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have r0 := rd hw w.a (by simp [reads, ho, testBit_rmask])
    have r1 := rd hw (w.a + 1) (by simp [reads, ho, testBit_rmask])
    have r2 := rd hw (w.a + 2) (by simp [reads, ho, testBit_rmask])
    refine ⟨_, Step.forprepEnter (hpc ▸ hw) ho (r0 ▸ hi) (r1 ▸ hlim) (r2 ▸ hst) h0 hn,
      rmask (w.a + 1) 1 ||| rmask (w.a + 3) 1, by simp [State.goto], ?_⟩
    exact (((hag.set rfl).set rfl).goto (by simp [hpc])).mono fun j hj => by
      simp only [Nat.testBit_or, testBit_rmask, Bool.or_eq_true, decide_eq_true_eq] at hj ⊢
      by_cases hm : m.testBit j = true
      · simp [hm]
      · simp only [hm, Bool.false_eq_true, false_or] at hj ⊢; omega
  | @forprepSkip w i lim st hw ho hi hlim hst h0 hn =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    have r0 := rd hw w.a (by simp [reads, ho, testBit_rmask])
    have r1 := rd hw (w.a + 1) (by simp [reads, ho, testBit_rmask])
    have r2 := rd hw (w.a + 2) (by simp [reads, ho, testBit_rmask])
    exact ⟨_, Step.forprepSkip (hpc ▸ hw) ho (r0 ▸ hi) (r1 ▸ hlim) (r2 ▸ hst) h0 hn,
      rmask (w.a + 3) 1, by simp [State.goto], (hag.set rfl).goto (by simp [hpc])⟩
  | @forloopAgain w n i st t hw ho hn h0 hi hst ht =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, ht, Option.map_some, Option.some.injEq] at hl'; subst hl'
    have r0 := rd hw w.a (by simp [reads, ho, testBit_rmask])
    have r1 := rd hw (w.a + 1) (by simp [reads, ho, testBit_rmask])
    have r2 := rd hw (w.a + 2) (by simp [reads, ho, testBit_rmask])
    refine ⟨_, Step.forloopAgain (hpc ▸ hw) ho (r1 ▸ hn) h0 (r0 ▸ hi) (r2 ▸ hst) (hpc ▸ ht),
      rmask w.a 2 ||| rmask (w.a + 3) 1, by simp [State.goto], ?_⟩
    exact ((((hag.set rfl).set rfl).set rfl).goto rfl).mono fun j hj => by
      simp only [Nat.testBit_or, testBit_rmask, Bool.or_eq_true, decide_eq_true_eq] at hj ⊢
      by_cases hm : m.testBit j = true
      · simp [hm]
      · simp only [hm, Bool.false_eq_true, false_or] at hj ⊢; omega
  | @forloopDone w hw ho hn hst =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf] at hl'
    obtain ⟨t, _, rfl⟩ := Option.map_eq_some_iff.1 hl'
    have r1 := rd hw (w.a + 1) (by simp [reads, ho, testBit_rmask])
    have r2 := rd hw (w.a + 2) (by simp [reads, ho, testBit_rmask])
    obtain ⟨st, hst⟩ := hst
    exact ⟨_, Step.forloopDone (hpc ▸ hw) ho (r1 ▸ hn) ⟨st, r2 ▸ hst⟩, _, by simp [State.goto],
      (hag.goto (by rw [hpc])).zero⟩
  | @callPrint w hw ho hp hb hc =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, hb, hc, ne_eq, not_false_eq_true, and_self, ite_true,
      Option.some.injEq] at hl'
    subst hl'
    have ra := rd hw w.a (by simp [reads, ho, testBit_rmask]; omega)
    have hargs : s₁.args (w.a + 1) (w.b - 1) = s₂.args (w.a + 1) (w.b - 1) :=
      args_eq fun j hj => rd hw (w.a + 1 + j) (by simp [reads, ho, testBit_rmask]; omega)
    refine ⟨_, Step.callPrint (hpc ▸ hw) ho (ra ▸ hp) hb hc, _, List.mem_singleton_self _, ?_⟩
    rw [hargs]
    exact hag.emit.setNils.goto (by simp [hpc])
  | @varargprep w hw ho =>
    have hl' := edgesOf_of_edges hl hw ho
    simp only [edgesOf, Option.some.injEq] at hl'; subst hl'
    exact ⟨_, Step.varargprep (hpc ▸ hw) ho, _, List.mem_singleton_self _,
      (hag.goto (by rw [hpc])).zero⟩

end Sim

/-! ## The invariant along runs, with calls clobbering their frames -/

/-- Register `j` may hold anything after the instruction at `pc`: it is a
`CALL A B C` and `j ≥ A + C - 1`, i.e. at or above the call's results
(`luaD_precall`/`luaD_poscall` leave the stack above `L->top` stale). -/
def Clobbered (p : Proto) (pc j : Nat) : Prop :=
  match p.fetch pc with
  | some w => w.op? = some .CALL ∧ w.a + (w.c - 1) ≤ j
  | none => False

/-- A step of `BcSem`, after which every register a `CALL` clobbers
(`Clobbered`) holds an arbitrary value. -/
inductive CStep (H : Host) (p : Proto) : State → State → Prop where
  | mk {s s₀ : State} (regs : Nat → Value) : Step H p s s₀ →
      (∀ j, ¬ Clobbered p s.pc j → regs j = s₀.regs j) → CStep H p s { s₀ with regs := regs }

/-- Every `Step` is a `CStep` (clobbering nothing). -/
theorem CStep.of_step {H : Host} {p : Proto} {s s' : State} (h : Step H p s s') : CStep H p s s' :=
  CStep.mk s'.regs h fun _ _ => rfl

/-- Reflexive-transitive closure. -/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | refl (a : α) : Star R a a
  | head {a b c : α} : R a b → Star R b c → Star R a c

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

theorem Star.mono {α : Type} {R R' : α → α → Prop} (hR : ∀ a b, R a b → R' a b) {a b : α}
    (h : Star R a b) : Star R' a b := by
  induction h with
  | refl => exact Star.refl _
  | head h _ ih => exact Star.head (hR _ _ h) ih

/-- The entry state of `luaV_execute` with register file `ρ` (the stale
stack contents). `State.init` is `initWith (fun _ => .nil)`. -/
def State.initWith (ρ : Nat → Value) : State := ⟨0, ρ, ""⟩

theorem State.init_eq : State.init = State.initWith (fun _ => .nil) := rfl

/-- Runs of the step relation `R` from `s₀` that return, having printed `out`. -/
def RunOut (R : State → State → Prop) (p : Proto) (s₀ : State) (out : String) : Prop :=
  ∃ s, Star R s₀ s ∧ Final p s ∧ s.out = out

/-- `BcSem` from the register file `ρ` at entry. -/
def BcSemFrom (H : Host) (p : Proto) (ρ : Nat → Value) : String → Prop :=
  RunOut (Step H p) p (State.initWith ρ)

/-- `BcSem` from the register file `ρ` at entry, with every call clobbering
the registers at and above its results. -/
def CBcSem (H : Host) (p : Proto) (ρ : Nat → Value) : String → Prop :=
  RunOut (CStep H p) p (State.initWith ρ)

theorem bcSem_iff_from {H : Host} {p : Proto} {out : String} :
    BcSem H p out ↔ BcSemFrom H p (fun _ => .nil) out :=
  ⟨fun ⟨s, hs, hf, ho⟩ => ⟨s, hs.star, hf, ho⟩, fun ⟨s, hs, hf, ho⟩ => ⟨s, hs.steps, hf, ho⟩⟩

theorem Final.of_pc {p : Proto} {s₁ s₂ : State} (h : Final p s₁) (hpc : s₁.pc = s₂.pc) :
    Final p s₂ := by
  cases h with
  | ret hw ho hor => exact Final.ret (hpc ▸ hw) ho hor

theorem Step.fetch_ne_none {H : Host} {p : Proto} {s s' : State} (h : Step H p s s') :
    p.fetch s.pc ≠ none := by
  cases h <;> simp_all

section Inv
variable {H : Host} {p : Proto} {M : Nat → Nat}

/-- What `DefInit.step` gives about the successor. -/
structure StepPost (p : Proto) (M : Nat → Nat) (s₁ s₁' s₂' : State) : Prop where
  /-- the successor pc is in range -/
  pc_lt : s₁'.pc < p.code.length
  /-- the successors agree on the successor's mask -/
  agree : Agree (M s₁'.pc) s₁' s₂'
  /-- no register of the successor's mask is clobbered by the step -/
  kept : ∀ j, (M s₁'.pc).testBit j = true → ¬ Clobbered p s₁.pc j

/-- **The invariant, one step.** Two states at the same pc that agree on
that pc's mask step (in lockstep) to states that agree on the successor's
mask, and a `CALL` clobbers nothing in it. -/
theorem DefInit.step (hD : DefInit p M) {s₁ s₁' s₂ : State} (h : Step H p s₁ s₁')
    (hag : Agree (M s₁.pc) s₁ s₂) : ∃ s₂', Step H p s₂ s₂' ∧ StepPost p M s₁ s₁' s₂' := by
  cases hf : p.fetch s₁.pc with
  | none => exact absurd hf h.fetch_ne_none
  | some w =>
  cases hl : edges p s₁.pc with
  | none => exact absurd hl (hD.total _ _ hf)
  | some l =>
  obtain ⟨s₂', hs, wr, hmem, hag'⟩ := h.sim hl hag (fun w hw => hD.reads _ _ hw)
  have hst : ∀ j, (M s₁'.pc).testBit j = true →
      (M s₁.pc &&& keepMask p s₁.pc).testBit j = true ∨ wr.testBit j = true := fun j hj => by
    have := msub_testBit (hD.stable _ _ hl _ hmem) hj
    simpa only [Nat.testBit_or, Bool.or_eq_true] using this
  refine ⟨s₂', hs, edges_target_lt hl hmem, hag'.mono fun j hj => ?_, fun j hj hc => ?_⟩
  · rcases hst j hj with h | h
    · rw [Nat.testBit_and, Bool.and_eq_true] at h
      simp [h.1]
    · simp [h]
  · unfold Clobbered at hc
    rw [hf] at hc
    obtain ⟨ho, hj'⟩ := hc
    have hk : keepMask p s₁.pc = rmask 0 w.a := by
      unfold keepMask; rw [hf]; simp [ho]
    have hl' := edgesOf_of_edges hl hf ho
    simp only [edgesOf] at hl'
    split at hl'
    · cases hl'
      simp only [List.mem_singleton, Prod.mk.injEq] at hmem
      obtain ⟨_, rfl⟩ := hmem
      rcases hst j hj with h | h
      · rw [hk, Nat.testBit_and, testBit_rmask, Bool.and_eq_true, decide_eq_true_eq] at h
        omega
      · rw [testBit_rmask, decide_eq_true_eq] at h
        omega
    · cases hl'

/-- **The invariant along runs.** A run with calls clobbering their frames
(any `Step` run is one) from a state agreeing with `s₂` on its mask is
matched by a `Step` run from `s₂`, ending in agreement on the final mask,
with every pc in range. -/
theorem DefInit.star (hD : DefInit p M) {s₁ s₁' s₂ : State} (h : Star (CStep H p) s₁ s₁')
    (hag : Agree (M s₁.pc) s₁ s₂) (hpc : s₁.pc < p.code.length) :
    ∃ s₂', Steps H p s₂ s₂' ∧ Agree (M s₁'.pc) s₁' s₂' ∧ s₁'.pc < p.code.length := by
  induction h generalizing s₂ with
  | refl => exact ⟨s₂, Steps.refl _, hag, hpc⟩
  | head hc _ ih =>
    cases hc with
    | @mk s₀ regs hs hkeep =>
      obtain ⟨s₂', hs₂, hpost⟩ := hD.step hs hag
      have hag' : Agree (M s₀.pc) { s₀ with regs := regs } s₂' :=
        ⟨hpost.agree.pc, hpost.agree.out, fun j hj =>
          (hkeep j (hpost.kept j hj)).trans (hpost.agree.regs j hj)⟩
      obtain ⟨s₃, hs₃, hag₃, hlt⟩ := ih hag' hpost.pc_lt
      exact ⟨s₃, Steps.head hs₂ hs₃, hag₃, hlt⟩

/-- Entry states agree on the (empty) entry mask, whatever their registers. -/
theorem DefInit.entry_agree (hD : DefInit p M) (ρ₁ ρ₂ : Nat → Value) :
    Agree (M 0) (State.initWith ρ₁) (State.initWith ρ₂) :=
  ⟨rfl, rfl, fun j hj => by rw [hD.entry, Nat.zero_testBit] at hj; cases hj⟩

/-- Clobbering runs from any entry registers give `BcSem`'s outputs. -/
theorem DefInit.cbcSem_imp (hD : DefInit p M) {ρ₁ ρ₂ : Nat → Value} {out : String}
    (h : CBcSem H p ρ₁ out) : BcSemFrom H p ρ₂ out := by
  obtain ⟨s, hs, hf, ho⟩ := h
  obtain ⟨s₂, hs₂, hag, _⟩ := hD.star hs (hD.entry_agree ρ₁ ρ₂) hD.pos
  exact ⟨s₂, hs₂.star, hf.of_pc hag.pc, hag.out ▸ ho⟩

end Inv

/-- **Independence from the initial registers.** For a supported program,
`BcSem` from any entry register file is `BcSem` from all-`nil`: the stale
stack values at `luaV_execute`'s entry are never observed. -/
theorem bcSemFrom_iff {H : Host} {p : Proto} (hS : Supported p) (ρ : Nat → Value)
    (out : String) : BcSemFrom H p ρ out ↔ BcSem H p out := by
  have hD := hS.defInit
  rw [bcSem_iff_from]
  constructor
  · intro ⟨s, hs, hf, ho⟩
    exact hD.cbcSem_imp ⟨s, hs.mono fun _ _ => CStep.of_step, hf, ho⟩
  · intro ⟨s, hs, hf, ho⟩
    exact hD.cbcSem_imp ⟨s, hs.mono fun _ _ => CStep.of_step, hf, ho⟩

/-- **Independence from clobbering by calls.** For a supported program,
running from any entry register file with every `CALL` leaving arbitrary
values at and above its results gives exactly `BcSem`'s outputs. -/
theorem cbcSem_iff {H : Host} {p : Proto} (hS : Supported p) (ρ : Nat → Value)
    (out : String) : CBcSem H p ρ out ↔ BcSem H p out := by
  have hD := hS.defInit
  rw [bcSem_iff_from]
  constructor
  · exact hD.cbcSem_imp
  · intro ⟨s, hs, hf, ho⟩
    obtain ⟨s', hs', hf', ho'⟩ :=
      hD.cbcSem_imp (ρ₂ := ρ) ⟨s, hs.mono fun _ _ => CStep.of_step, hf, ho⟩
    exact ⟨s', hs'.mono fun _ _ => CStep.of_step, hf', ho'⟩

/-- What holds at every state a supported program reaches. -/
structure DefInitAt (H : Host) (p : Proto) (s : State) : Prop where
  /-- the pc is in range: the fetch succeeds -/
  pc_lt : s.pc < p.code.length
  /-- every register the instruction reads is in the mask -/
  reads : ∀ w, p.fetch s.pc = some w → msub (reads w) (defMask p s.pc) = true
  /-- the masked registers were written on the path: every run from any
  entry registers reaches a state agreeing with `s` on the mask -/
  path : ∀ ρ, ∃ s', Steps H p (State.initWith ρ) s' ∧ Agree (defMask p s.pc) s s'

/-- **The per-state invariant**: along any run of a supported program from
any entry registers, the pc stays in range, the instruction's reads are in
the mask, and the masked registers hold values that do not depend on the
entry registers. -/
theorem reachable_defInit {H : Host} {p : Proto} (hS : Supported p) {ρ₀ : Nat → Value}
    {s : State} (h : Steps H p (State.initWith ρ₀) s) : DefInitAt H p s := by
  have hD := hS.defInit
  have hstar := h.star.mono fun _ _ => CStep.of_step
  obtain ⟨_, _, _, hlt⟩ := hD.star hstar (hD.entry_agree ρ₀ ρ₀) hD.pos
  exact ⟨hlt, fun w hw => hD.reads _ w hw, fun ρ =>
    let ⟨s', hs', hag, _⟩ := hD.star hstar (hD.entry_agree ρ₀ ρ) hD.pos
    ⟨s', hs', hag⟩⟩

/-! ## Conditional jumps in supported programs -/

/-- The opcodes whose successor is `condJump`. -/
def isCondOp : OpCode → Bool
  | .EQ | .LT | .LE | .EQK | .EQI | .LTI | .LEI | .GTI | .GEI | .TEST => true
  | _ => false

theorem condEdges_of_cond {p : Proto} {pc : Nat} {w : Word} {o : OpCode} {l : List Edge}
    (hc : isCondOp o = true) (hl : edgesOf p pc w o = some l) : condEdges p pc = some l := by
  cases o <;> simp only [isCondOp, Bool.false_eq_true] at hc
  case EQK =>
    unfold edgesOf at hl
    cases hk : p.const w.b with
    | none => rw [hk] at hl; cases hl
    | some c => rw [hk] at hl; cases c <;> first | cases hl | exact hl
  all_goals exact hl

/-- In a supported program, a conditional test's `condJump` is defined. -/
theorem condJump_ne_none {p : Proto} (hS : Supported p) {pc : Nat} {w : Word} {o : OpCode}
    (hw : p.fetch pc = some w) (ho : w.op? = some o) (hc : isCondOp o = true) (c k : Bool) :
    condJump p pc c k ≠ none := by
  cases hl : edges p pc with
  | none => exact absurd hl (hS.defInit.total _ _ hw)
  | some l =>
    have hce := condEdges_of_cond hc (edgesOf_of_edges hl hw ho)
    unfold condEdges at hce
    unfold condJump
    split
    · exact Option.some_ne_none _
    · intro hn
      have : nextJump p pc = none := hn
      rw [this] at hce; cases hce

/-- In a supported program, a conditional test's `condJump` target is in range. -/
theorem condJump_lt {p : Proto} (hS : Supported p) {pc : Nat} {w : Word} {o : OpCode}
    (hw : p.fetch pc = some w) (ho : w.op? = some o) (hc : isCondOp o = true) {c k : Bool}
    {t : Nat} (ht : condJump p pc c k = some t) : t < p.code.length := by
  cases hl : edges p pc with
  | none => exact absurd hl (hS.defInit.total _ _ hw)
  | some l =>
    exact edges_target_lt hl (condJump_mem (condEdges_of_cond hc (edgesOf_of_edges hl hw ho)) ht)

end Lua.Bytecode

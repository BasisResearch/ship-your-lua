import Lua.Vm.Sim.Kit.Close

/-!
# Loops and read-only scans over segment-state families (round-4 bake-off, S-SCAN)

Three mechanisms of `abstractions/ROUND-4.md` §3, proved once:

* **M-loop** (`seg_loop`): a loop over a family `S a` of segment states with
  a measure `μ`; one pass of the body either re-enters the family at a
  smaller measure or leaves through the exit post `X` (any number of exits,
  bottom, middle or rotated). This is L4-loop′; the kit's
  `| 0 => absurd | n+1 => …` recursion per loop is gone.
* **M-scan** (`scan_loop`, `relay`): a read-only scan over positions
  `[i, n)`, the family indexed by the position and the invariant "no event
  before `i`" (a first-event fold); `relay` hands a scan's exit to another
  scan entered at the exit's position (`memcmp`'s word loop into its byte
  loop, `strcmp`'s and `strlen`'s word scans into their byte scans).
* **Lanes** (`bytesT8_eq_iff`): an 8-byte word compare is the compare of
  its 8 byte lanes.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## M-loop -/

/-- **The loop rule over a family of states** (L4-loop′): if one pass of
the body from `S a` reaches `S a'` with `μ a' < μ a` or the exit `X`, then
every `S a` reaches `X`. -/
theorem seg_loop {α : Type} {S : α → Config → Prop} {X : Config → Prop} (μ : α → Nat)
    (body : ∀ a, Triple (S a) (fun c => (∃ a', μ a' < μ a ∧ S a' c) ∨ X c)) :
    ∀ a, Triple (S a) X := by
  suffices h : ∀ n a, μ a = n → Triple (S a) X from fun a => h _ a rfl
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro a ha c hc
    obtain ⟨c1, hs1, h1⟩ := body a c hc
    rcases h1 with ⟨a', hlt, h'⟩ | hx
    · obtain ⟨c2, hs2, h2⟩ := ih (μ a') (ha ▸ hlt) a' rfl c1 h'
      exact ⟨c2, hs1.trans hs2, h2⟩
    · exact ⟨c1, hs1, hx⟩

/-! ## M-loop: comprehension log entries -/

/-- **A comprehension log entry** ("for all `i < k`, write `b` at `o + s·i`",
stride `s`, `0` allowed), the stores applied in order on `M`: a store loop's
memory after `k` iterations. -/
def compMem (M : Mem) (o s : Nat) (b : BitVec 8) : Nat → Mem
  | 0 => M
  | k + 1 => (compMem M o s b k).insert (o + s * k) b

/-- A read the entry does not cover. -/
theorem compMem_out {M : Mem} {o s x : Nat} {b : BitVec 8} :
    ∀ {k}, (∀ i, i < k → x ≠ o + s * i) → (compMem M o s b k)[x]? = M[x]?
  | 0, _ => rfl
  | k + 1, h => by
    simp only [compMem]
    rw [getElem?_insert_out (h k (by omega)), compMem_out fun i hi => h i (by omega)]

/-- A read the entry covers. -/
theorem compMem_in {M : Mem} {o s : Nat} {b : BitVec 8} :
    ∀ {k i}, i < k → (compMem M o s b k)[o + s * i]? = some b
  | k + 1, i, hi => by
    simp only [compMem]
    by_cases e : o + s * i = o + s * k
    · rw [e]; simp
    · rw [getElem?_insert_out e]; exact compMem_in (by
        rcases Nat.lt_or_ge i k with h | h
        · exact h
        · exact absurd (by rw [show i = k by omega]) e)

/-! ## M-scan -/

/-- **A read-only scan** over positions below `n`: the state family `S i`
at position `i`, the invariant `∀ j < i, ok j` (no event before `i`). One
pass from `i` either moves to a later position `i' < n` with no event
before it, or leaves through `X`. -/
theorem scan_loop {S : Nat → Config → Prop} {X : Config → Prop} (n : Nat) (ok : Nat → Prop)
    (body : ∀ i, i < n → (∀ j, j < i → ok j) → Triple (S i)
      (fun c => (∃ i', i < i' ∧ i' < n ∧ (∀ j, j < i' → ok j) ∧ S i' c) ∨ X c)) :
    ∀ i, i < n → (∀ j, j < i → ok j) → Triple (S i) X := by
  intro i hi hok c hc
  refine seg_loop (S := fun i c => i < n ∧ (∀ j, j < i → ok j) ∧ S i c) (fun i => n - i)
    (fun i c ⟨hi, hok, hc⟩ => ?_) i c ⟨hi, hok, hc⟩
  obtain ⟨c1, hs1, h1⟩ := body i hi hok c hc
  refine ⟨c1, hs1, ?_⟩
  rcases h1 with ⟨i', h1, h2, h3, h4⟩ | hx
  · exact .inl ⟨i', by omega, h2, h3, h4⟩
  · exact .inr hx

/-- **Relay**: a run whose exit enters a family `S i` (under `R i`) is
continued by that family's summary. -/
theorem relay {P Q : Config → Prop} {S : Nat → Config → Prop} {R : Nat → Prop}
    (h1 : Triple P (fun c => (∃ i, R i ∧ S i c) ∨ Q c)) (h2 : ∀ i, R i → Triple (S i) Q) :
    Triple P Q := fun c hc => by
  obtain ⟨c1, hs1, h⟩ := h1 c hc
  rcases h with ⟨i, hr, hs⟩ | hq
  · obtain ⟨c2, hs2, h2⟩ := h2 i hr c1 hs
    exact ⟨c2, hs1.trans hs2, h2⟩
  · exact ⟨c1, hs1, hq⟩

open Lean Elab Tactic Meta in
/-- **A branch guard named by the arm**: a `Bool` equation that is,
syntactically, a fact in context (the polarity chosen by the arm's case
split, no closer search and no unfolding of the guard's arithmetic). -/
elab "guard_assumption" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOfArity ``Eq 3 && (t.getArg! 0).isConstOf ``Bool do
    throwError "guard_assumption: not a guard"
  for ld in ← getLCtx do
    if ld.isImplementationDetail then continue
    if (← instantiateMVars ld.type) == t then
      closeMainGoal `guard_assumption ld.toExpr
      return
  throwError "guard_assumption: no such fact"

open Lean Elab Tactic Meta in
/-- Fails unless the goal is, syntactically, a `Bool` equation (a branch guard). -/
elab "bool_goal" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  unless t.isAppOfArity ``Eq 3 && (t.getArg! 0).isConstOf ``Bool do throwError "bool_goal: not a guard"

open Lean Elab Tactic Meta in
/-- **`kit_seg h acc seg`**: one named segment step (the polarity chosen by
the proof, no search): values `_`, side conditions by `kit_side`. -/
elab "kit_seg " h:ident acc:ident n:ident : tactic => withMainContext do
  let name ← realizeGlobalConstNoOverloadWithInfo n
  let args ← Tactic.runTermElab (segArgs name)
  let seg ← `($(mkIdent name) $args*)
  evalTactic (← `(tactic| obtain ⟨_, $acc, $h⟩ := Vsa.Sim.SegSt.run $acc $h (by pins_of $h) $seg))

/-! ## Lanes -/

/-- `++` is injective. -/
theorem append_inj' {w v : Nat} {x1 x2 : BitVec w} {y1 y2 : BitVec v} (h : x1 ++ y1 = x2 ++ y2) :
    x1 = x2 ∧ y1 = y2 := by
  have h' := congrArg BitVec.toNat h
  simp only [BitVec.toNat_append] at h'
  rw [← Nat.shiftLeft_add_eq_or_of_lt y1.isLt, ← Nat.shiftLeft_add_eq_or_of_lt y2.isLt,
    Nat.shiftLeft_eq, Nat.shiftLeft_eq] at h'
  have hy1 := y1.isLt; have hy2 := y2.isLt
  have hp := Nat.two_pow_pos v
  have e1 : (x1.toNat * 2 ^ v + y1.toNat) / 2 ^ v = x1.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy1, Nat.zero_add]
  have e2 : (x2.toNat * 2 ^ v + y2.toNat) / 2 ^ v = x2.toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hy2, Nat.zero_add]
  have f1 : (x1.toNat * 2 ^ v + y1.toNat) % 2 ^ v = y1.toNat := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy1]
  have f2 : (x2.toNat * 2 ^ v + y2.toNat) % 2 ^ v = y2.toNat := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy2]
  exact ⟨BitVec.eq_of_toNat_eq (by rw [← e1, ← e2, h']),
    BitVec.eq_of_toNat_eq (by rw [← f1, ← f2, h'])⟩

/-- **An 8-byte word compare is the compare of its byte lanes.** -/
theorem bytesT8_eq_iff {m : Mem} {a b : Nat} :
    bytesT8 m a = bytesT8 m b ↔ ∀ k, k < 8 → bytesT1 m (a + k) = bytesT1 m (b + k) := by
  constructor
  · intro h k hk
    simp only [bytesT8] at h
    obtain ⟨h, h0⟩ := append_inj' h
    obtain ⟨h, h1⟩ := append_inj' h
    obtain ⟨h, h2⟩ := append_inj' h
    obtain ⟨h, h3⟩ := append_inj' h
    obtain ⟨h, h4⟩ := append_inj' h
    obtain ⟨h, h5⟩ := append_inj' h
    obtain ⟨h7, h6⟩ := append_inj' h
    simp only [bytesT1]
    rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa
  · intro h
    have h0 := h 0 (by omega)
    simp only [bytesT1, Nat.add_zero] at h0 h
    simp only [bytesT8, h0, h 1 (by omega), h 2 (by omega), h 3 (by omega), h 4 (by omega),
      h 5 (by omega), h 6 (by omega), h 7 (by omega)]

/-- `lbu`'s zero extension is injective. -/
theorem zext8_beq (x y : BitVec 8) :
    (zero_extend (m := 64) (x : BitVec (8 * 1)) == zero_extend (m := 64) (y : BitVec (8 * 1))) =
      decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; apply h
    have := congrArg BitVec.toNat e
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth] at this
    exact BitVec.eq_of_toNat_eq (by rwa [Nat.mod_eq_of_lt (by have := x.isLt; omega),
      Nat.mod_eq_of_lt (by have := y.isLt; omega)] at this)

/-- `subw` of two zero-extended bytes is zero only when they are equal. -/
theorem subw_bytes_ne {x y : BitVec 8} (h : x ≠ y) :
    sign_extend (m := 64) ((Sail.BitVec.extractLsb (zero_extend (m := 64) (x : BitVec (8 * 1))) 31 0) -
      (Sail.BitVec.extractLsb (zero_extend (m := 64) (y : BitVec (8 * 1))) 31 0)) ≠ 0#64 := by
  simp only [sign_extend, Sail.BitVec.signExtend, zero_extend, Sail.BitVec.zeroExtend,
    Sail.BitVec.extractLsb]
  intro e; apply h
  generalize hz : BitVec.extractLsb 31 0 (BitVec.setWidth 64 x) - BitVec.extractLsb 31 0 (BitVec.setWidth 64 y) = z at e
  have hz0 : z = 0#32 := BitVec.eq_of_getLsbD_eq fun i hi => by
    have := congrArg (·.getLsbD i) e
    simp only [BitVec.getLsbD_signExtend, BitVec.getLsbD_zero] at this
    simp only [BitVec.getLsbD_zero]
    simpa [hi, show i < 64 by omega] using this
  subst hz0
  have ex : (BitVec.extractLsb 31 0 (BitVec.setWidth 64 x)).toNat = x.toNat := by simp; omega
  have ey : (BitVec.extractLsb 31 0 (BitVec.setWidth 64 y)).toNat = y.toNat := by simp; omega
  have h2 := congrArg BitVec.toNat hz
  rw [BitVec.toNat_sub, ex, ey] at h2
  apply BitVec.eq_of_toNat_eq
  have := x.isLt; have := y.isLt
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.sub_zero, Nat.reduceAdd, Nat.reducePow] at h2; omega

end Lua.Vm.Sim

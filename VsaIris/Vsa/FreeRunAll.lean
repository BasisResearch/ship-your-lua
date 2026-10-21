import VsaIris.Vsa.FreeTop

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- Named heap witness of `FRet`, retaining its surviving ledger and top bound. -/
structure FRetHeap (H : List (Nat × Nat)) (top0 : Nat) (Mt : Mem) where
  top : Nat
  brk : Nat
  chunks : List Chunk
  bins : Nat → List Nat
  heap : PHeapAt Mt H top brk chunks bins
  top_le : top ≤ top0

/-- Consume the ported return's heap witnesses in one place. -/
theorem FRet.heap_named {C : MCtx} {R : Nat → BitVec 64} {Mt : Mem}
    (h : FRet C R Mt) : Nonempty (FRetHeap C.H C.top0 Mt) := by
  obtain ⟨top, brk, chunks, bins, hh, ht⟩ := h.heap
  exact ⟨⟨top, brk, chunks, bins, hh, ht⟩⟩

abbrev fS (H : List (Nat × Nat)) (q : BitVec 64) (n : Nat) (s : BitVec 64) : Nat → Prop :=
  freeBytes vsaLayoutP H q n s allocHeadroom

abbrev ft0 (m1 : Mem) (q : BitVec 64) (n : Nat) (s : BitVec 64) (mv : Nat → BitVec 8) : Mem :=
  mt0 (stackBase m1 q.toNat n mv) s mv

theorem foot_block {H : List (Nat × Nat)} {e : Nat × Nat} {a : Nat}
    (h : vsaFoot H a) : vsaFoot (e :: H) a ∨ InExt e a := by
  rcases h with hg | ⟨h1, h2, h3⟩
  · exact .inl (.inl hg)
  · by_cases hin : InExt e a
    · exact .inr hin
    · refine .inl (.inr ⟨h1, h2, fun e' he => ?_⟩)
      rcases List.mem_cons.mp he with rfl | he
      · exact hin
      · exact h3 e' he

theorem fS_of_foot {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat} {s : BitVec 64} {a : Nat}
    (h : vsaFoot H a) : fS H q n s a := .inr (foot_block h)

theorem fS_of_win {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat} {s : BitVec 64} (hsp : SpOKA s)
    (a : Nat) (ha : MWin H s a) : fS H q n s a := by
  rcases ha with hf | ha
  · exact fS_of_foot hf
  · rcases mChg_own hsp a (.inr ha) with h | h
    · exact .inl h
    · exact fS_of_foot h

theorem faw_run {live : Nat → Prop} {H : List (Nat × Nat)} {q : BitVec 64} {n : Nat}
    {s pc : BitVec 64} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {rv : Nat → BitVec 64}
    {mv : Nat → BitVec 8} {m1 : Mem}
    (h : AW live (fS H q n s) Q pc rv (ft0 m1 q n s mv)) (hpc : rv VsaIris.PC = pc)
    (him : ImgOn (vsaFoot ((q.toNat, n) :: H)) mv m1) :
    ∃ fuel, LocalRun (vsaModel live) roR allocText aRegs (fS H q n s) Q fuel rv mv := by
  obtain ⟨fuel, hf⟩ := h
  refine ⟨fuel, hf rv mv ⟨hpc, fun _ _ _ => rfl, fun a ha => ?_⟩⟩
  unfold imgM ft0 mt0
  rw [stackBase_get, stackBase_get]
  by_cases h1 : s.toNat - allocHeadroom ≤ a ∧ a < s.toNat - allocHeadroom + allocHeadroom
  · rw [if_pos h1]; rfl
  rw [if_neg h1]
  by_cases h2 : q.toNat ≤ a ∧ a < q.toNat + n
  · rw [if_pos h2]; rfl
  rw [if_neg h2]
  rcases ha with hs | hh | hx
  · exact absurd ⟨hs.1, by unfold stackWin InExt at hs; simp only at hs; omega⟩ h1
  · rw [him a hh]; rfl
  · exact absurd hx h2

theorem fHeap_entry {C : MCtx} {m1 : Mem} {q : BitVec 64} {n : Nat} {s : BitVec 64}
    {mv : Nat → BitVec 8} {brkv : Nat} {chunks : List Chunk} {bins : Nat → List Nat}
    (hs0 : C.s = s) (hMt : C.Mt0 = ft0 m1 q n s mv) (hsp : SpOKA s)
    (him : ImgOn (vsaFoot ((q.toNat, n) :: C.H)) mv m1)
    (hheap : PHeapAt m1 ((q.toNat, n) :: C.H) C.top0 brkv chunks bins)
    (hst : Starts ((q.toNat, n) :: C.H))
    (hdisj : ∀ a, stackWin s allocHeadroom a →
      ¬ (heapFoot vsaLayoutP ((q.toNat, n) :: C.H) a ∨ InExt (q.toNat, n) a)) :
    FHeap C C.Mt0 q.toNat n brkv chunks bins := by
  subst hs0
  have hs : 512 ≤ C.s.toNat := by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at this; omega
  have hwin : ∀ a, C.s.toNat - allocHeadroom ≤ a → a < C.s.toNat - allocHeadroom + allocHeadroom →
      ¬ vsaFoot C.H a := fun a h1 h2 hf => by
    exact hdisj a ⟨h1, by simp only; omega⟩ (foot_block hf)
  have HH := hheap.heap.heap
  obtain ⟨c, hc, _, hca, hcn⟩ := HH.live _ List.mem_cons_self
  have hcb := HH.walk.chunk_bounds c hc
  have hbrk := HH.brk_le; have htle := HH.top_le; have hroom := hheap.heap.top_room
  unfold heapStart at hcb; unfold heapEnd at hbrk
  simp only at hca hcn
  have hag : ∀ a, vsaFoot ((q.toNat, n) :: C.H) a → C.Mt0[a]? = m1[a]? := by
    intro a ha
    rw [hMt]; unfold ft0 mt0
    rw [stackBase_get, stackBase_get,
      ite_eq_right_iff.2 fun h => absurd (.inl ha) (hdisj a ⟨h.1, by simp only; omega⟩)]
    rcases ha with hg | ⟨_, _, h3⟩
    · exact ite_eq_right_iff.2 fun h => by
        have := allocGlobal_off_arena a hg; unfold heapStart heapEnd at this; omega
    · exact ite_eq_right_iff.2 fun h => absurd h (h3 _ List.mem_cons_self)
  refine ⟨hheap.transport_read fun a ha => (hag a ha.1).symm, hst, fun a ha => ?_,
    fun a h1 h2 hf => hwin a ?_ ?_ hf, fun a _ => rfl⟩
  · rw [hMt]; unfold ft0 mt0
    rw [stackBase_get, stackBase_get]
    by_cases h1 : C.s.toNat - allocHeadroom ≤ a ∧ a < C.s.toNat - allocHeadroom + allocHeadroom
    · rw [if_pos h1]; rfl
    rw [if_neg h1]
    by_cases h2 : q.toNat ≤ a ∧ a < q.toNat + n
    · rw [if_pos h2]; rfl
    rw [if_neg h2]
    rcases foot_block (e := (q.toNat, n)) ha with hh | hx
    · rw [him a hh]; rfl
    · exact absurd hx h2
  · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : mHead ≤ allocHeadroom) _) h1
  · rw [Nat.sub_add_cancel (by unfold allocHeadroom; omega)]; exact h2

end VsaIris.VsaHeap

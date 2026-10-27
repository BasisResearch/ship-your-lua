import Lua.Vm.Sim.Kit.Bfree
import Lua.Vm.Sim.Kit.BigHeap

/-! Ownership lift of the exact `_Bfree` stores. Cache digits are bounded by
`ReentMpAt.p5cap`; no allocator or new machine run is used here. -/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit
open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- A value read stays inside the allocated capacity, including `_wds`. -/
theorem bigVal_congr {m m' : Mem} {b k w : Nat}
    (hw : rd32 m (b + 20) = some w) (hc : w ≤ 2 ^ k)
    (hk : ∀ a, b ≤ a → a < b + bigSize k → m'[a]? = m[a]?) :
    bigVal m' b = bigVal m b := by
  have hr : ∀ a, b ≤ a → a + 4 ≤ b + bigSize k → rd32 m' a = rd32 m a :=
    fun a h1 h2 => rdLE_congr fun i hi => hk _ (by omega) (by omega)
  unfold bigVal
  rw [hr (b + 20) (by omega) (by simp [bigSize]; omega), hw]
  have fold : ∀ l : List Nat, (∀ i ∈ l, i < w) →
      l.foldr (fun i acc => (rd32 m' (b + 24 + 4 * i)).bind
        fun x => acc.map fun r => x + 2 ^ 32 * r) (some 0) =
      l.foldr (fun i acc => (rd32 m (b + 24 + 4 * i)).bind
        fun x => acc.map fun r => x + 2 ^ 32 * r) (some 0) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons i l ih =>
      have hi := hl i (List.mem_cons_self ..)
      simp only [List.foldr_cons]
      rw [hr (b + 24 + 4 * i) (by omega) (by simp [bigSize]; omega),
        ih (fun j hj => hl j (List.mem_cons_of_mem _ hj))]
  exact fold (List.range w) (fun i hi => List.mem_range.mp hi)

/-- Push into exactly one list, retaining the order of every other list. -/
def bfreeLists (b k : Nat) (ls : List (List (Nat × Nat))) : List (List (Nat × Nat)) :=
  ls.modify k ((b, k) :: ·)

/-- The flattened ownership ledger gains exactly the returned block. -/
theorem bfreeLists_perm (b k : Nat) (ls : List (List (Nat × Nat))) (hk : k < ls.length) :
    (bfreeLists b k ls).flatten.Perm ((b, k) :: ls.flatten) := by
  suffices ∀ (i : Nat) (ls : List (List (Nat × Nat))), i < ls.length →
      (ls.modify i ((b, k) :: ·)).flatten.Perm ((b, k) :: ls.flatten) from this k ls hk
  intro i ls
  induction ls generalizing i with
  | nil => simp
  | cons l ls ih =>
    cases i with
    | zero => simp
    | succ i =>
      intro hi
      simp only [List.modify_succ_cons, List.flatten_cons]
      exact ((ih i (by simpa using hi)).append_left l).trans List.perm_middle

/-- The concrete ownership list after a push is the old list plus one block. -/
theorem bfreeBlocks_perm (b k fl res rk : Nat) (ls : List (List (Nat × Nat)))
    (ps : List (Nat × Nat)) (hk : k < ls.length) :
    (bigBlocks fl res rk (bfreeLists b k ls) ps).Perm
      ((b, bigSize k) :: bigBlocks fl res rk ls ps) := by
  unfold bigBlocks
  have hp := ((bfreeLists_perm b k ls hk).append_right ps).map
    (fun x : Nat × Nat => (x.1, bigSize x.2))
  simp only [List.cons_append, List.map_cons] at hp
  exact (hp.append_left ((if fl = 0 then [] else [(fl, 8 * 65)]) ++
    (if res = 0 then [] else [(res, bigSize rk)]))).trans List.perm_middle

/-- Every free/cache node contributes its entire allocation to the ledger. -/
theorem bigBlocks_node {fl res rk : Nat} {ls : List (List (Nat × Nat))}
    {ps : List (Nat × Nat)} {x : Nat × Nat} (hx : x ∈ ls.flatten ∨ x ∈ ps) :
    (x.1, bigSize x.2) ∈ bigBlocks fl res rk ls ps := by
  unfold bigBlocks
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨x, List.mem_append.mpr hx, rfl⟩

/-- Memory transport for the complete ownership invariant, with every read
inside a listed allocation or a reentrancy word. -/
theorem reentMpAt_congr {m m' : Mem} {B : Nat → Prop} {fl res rk p5 : Nat}
    {hds : List Nat} {ls : List (List (Nat × Nat))} {ps : List (Nat × Nat)}
    (h : ReentMpAt m B fl res rk p5 hds ls ps)
    (hr : ∀ a, ReentWord a → m'[a]? = m[a]?)
    (hb : ∀ x ∈ bigBlocks fl res rk ls ps, ∀ a,
      x.1 ≤ a → a < x.1 + x.2 → m'[a]? = m[a]?) :
    ReentMpAt m' B fl res rk p5 hds ls ps := by
  have rr : ∀ a n, symImpureData + reentResultOff ≤ a →
      a + n ≤ symImpureData + reentFreelistOff + 8 → rdLE m' a n = rdLE m a n :=
    fun a n h1 h2 => rdLE_congr fun i hi => hr _ ⟨by omega, by omega⟩
  have rb : ∀ x ∈ bigBlocks fl res rk ls ps, ∀ a n,
      x.1 ≤ a → a + n ≤ x.1 + x.2 → rdLE m' a n = rdLE m a n :=
    fun x hx a n h1 h2 => rdLE_congr fun i hi => hb x hx _ (by omega) (by omega)
  have headers : ∀ x ∈ ls.flatten ++ ps, BigHeaderKeep m m' x.1 := by
    intro x hx
    have hx := bigBlocks_node (List.mem_append.mp hx) (fl := fl) (res := res) (rk := rk)
    refine ⟨rb _ hx _ _ (by omega) (by simp [bigSize]; omega),
      rb _ hx _ _ (by omega) (by simp [bigSize]; omega),
      rb _ hx _ _ (by omega) (by simp [bigSize]; omega)⟩
  refine { h with
    res_w := (rr _ _ (by decide) (by decide)).trans h.res_w
    rk_w := fun hn => (rr _ _ (by decide) (by decide)).trans (h.rk_w hn)
    p5_w := (rr _ _ (by decide) (by decide)).trans h.p5_w
    fl_w := (rr _ _ (by decide) (by decide)).trans h.fl_w
    heads := ?_
    chains := ?_
    p5s := h.p5s.congr (fun x hx => headers x (List.mem_append_right _ hx))
    p5v := ?_
    p5cap := ?_ }
  · intro hn i hi
    have hx : (fl, 520) ∈ bigBlocks fl res rk ls ps := by simp [bigBlocks, hn]
    exact (rb _ hx _ _ (by omega) (by have := h.hds_len; omega)).trans (h.heads hn i hi)
  · intro hn i hi hj
    exact (h.chains hn i hi hj).congr fun x hx =>
      headers x (List.mem_append_left _ (List.mem_flatten.mpr ⟨ls[i], List.getElem_mem hj, hx⟩))
  · intro j x hx
    have hm := List.mem_of_getElem? hx
    obtain ⟨w, hw, hc⟩ := h.p5cap x hm
    exact (bigVal_congr hw hc (hb _ (bigBlocks_node (.inr hm)))).trans (h.p5v j x hx)
  · intro x hx
    obtain ⟨w, hw, hc⟩ := h.p5cap x hx
    exact ⟨w, (rb _ (bigBlocks_node (.inr hx)) _ _ (by omega)
      (by simp [bigSize]; omega)).trans hw, hc⟩

/-- Stores respect total-byte equality, including absent zero bytes. -/
theorem bfreeMem_total {m m' : Mem} (hk : ∀ a, bytesT1 m' a = bytesT1 m a)
    (b fl k : Nat) (head : BitVec 64) :
    ∀ a, bytesT1 (bfreeMem m' b fl k head) a = bytesT1 (bfreeMem m b fl k head) a := by
  have store : ∀ (m m' : Mem) (p : Nat) (d : BitVec 64),
      (∀ a, bytesT1 m' a = bytesT1 m a) →
      ∀ a, bytesT1 (writeMap8 m' p d) a = bytesT1 (writeMap8 m p d) a := by
    intro m m' p d h a
    by_cases ha : a < p ∨ p + 8 ≤ a
    · simpa only [bytesT1_writeMap8_out _ _ _ ha] using h a
    · have he : a = p + (a - p) := by omega
      have hi : a - p < 8 := by omega
      rw [he]
      simp only [bytesT1, getElem_writeMap8 _ _ _ _ hi, Option.getD_some]
  unfold bfreeMem
  split
  · exact hk
  · exact store _ _ _ _ (store _ _ _ _ hk)

/-- An active allocation, separate from every registered bignum block,
including the array, last result and power-five cache. All owned bytes are
live heap payload, which justifies keeping the allocator ledger unchanged. -/
structure BfreeHeapIn (m : Mem) (H : HeapIx) (B : Nat → Prop)
    (b fl k res rk p5 : Nat) (hds : List Nat)
    (ls : List (List (Nat × Nat))) (ps : List (Nat × Nat)) (head : BitVec 64) : Prop where
  heap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins
  mp : ReentMpAt (fillZeroMem m) B fl res rk p5 hds ls ps
  push : BfreePushIn symImpureData b fl k head m
  cls : rd32 (fillZeroMem m) (b + 8) = some k
  maxwds : rd32 (fillZeroMem m) (b + 12) = some (2 ^ k)
  active : ∀ x ∈ bigBlocks fl res rk ls ps, Apart b (bigSize k) x.1 x.2
  block_in : ∀ a, b ≤ a → a < b + bigSize k → B a
  region : ∀ a, B a → HeapIn H.chunks a

/-- Every old allocation except the freelist array is byte-for-byte kept;
this includes the complete last result and every power-five cache block. -/
theorem bfree_keep_owned {m : Mem} {H : HeapIx} {B : Nat → Prop}
    {b fl k res rk p5 : Nat} {hds : List Nat} {ls : List (List (Nat × Nat))}
    {ps : List (Nat × Nat)} {head : BitVec 64}
    (h : BfreeHeapIn m H B b fl k res rk p5 hds ls ps head)
    {x : Nat × Nat} (hx : x ∈ bigBlocks fl res rk ls ps) (hnx : x.1 ≠ fl)
    {a : Nat} (h1 : x.1 ≤ a) (h2 : a < x.1 + x.2) :
    (bfreeMem m b fl k head)[a]? = m[a]? := by
  have hn : fl ≠ 0 := by have := h.push.fl_lo; omega
  have ha := h.mp.apart
  have ab := h.active x hx
  simp only [bigBlocks, if_neg hn, List.cons_append, List.mem_cons] at hx
  rcases hx with he | hx
  · exact False.elim (hnx (congrArg Prod.fst he))
  · simp only [bigBlocks, if_neg hn, List.cons_append, List.pairwise_cons] at ha
    have af := ha.1 x hx
    simp only [Apart] at ab af
    have sz : 8 ≤ bigSize k := by simp [bigSize]; omega
    exact bfreeMem_keep _ _ _ _ _ _ (by omega) (by have := h.push.k_hi; omega)

/-- Optional-byte frame of a push, packaged by ranges. -/
theorem bfreeMem_frame {m : Mem} {b fl k : Nat} {head : BitVec 64} {a : Nat}
    (hb : ¬ (b ≤ a ∧ a < b + 8))
    (hf : ¬ (fl + 8 * k ≤ a ∧ a < fl + 8 * k + 8)) :
    (bfreeMem m b fl k head)[a]? = m[a]? :=
  bfreeMem_keep _ _ _ _ _ _ (by omega) (by omega)

/-- The full ownership update from the two stores, including the unchanged
result and power-five cache. The active block has not yet been registered. -/
theorem reentMpAt_bfree {m : Mem} {B : Nat → Prop} {b fl k res rk p5 : Nat}
    {hds : List Nat} {ls : List (List (Nat × Nat))} {ps : List (Nat × Nat)} {head : BitVec 64}
    (h : ReentMpAt m B fl res rk p5 hds ls ps)
    (hp : BfreePushIn symImpureData b fl k head m)
    (cls : rd32 m (b + 8) = some k) (cap : rd32 m (b + 12) = some (2 ^ k))
    (hd : ∀ hk : k < hds.length, hds[k] = head.toNat)
    (active : ∀ x ∈ bigBlocks fl res rk ls ps, Apart b (bigSize k) x.1 x.2)
    (block_in : ∀ a, b ≤ a → a < b + bigSize k → B a) :
    ReentMpAt (bfreeMem m b fl k head) B fl res rk p5 (hds.set k b) (bfreeLists b k ls) ps := by
  have hn : fl ≠ 0 := by have := hp.fl_lo; omega
  have kh : k < hds.length := by have := h.hds_len; have := hp.k_hi; omega
  have kl : k < ls.length := by have := h.lists_len; have := hp.k_hi; omega
  have arr : ∀ x ∈ ls.flatten ++ ps, Apart fl 520 x.1 (bigSize x.2) := by
    have ha := h.apart
    simp only [bigBlocks, if_neg hn, List.cons_append, List.pairwise_cons] at ha
    intro x hx
    exact ha.1 _ (List.mem_append_right _ (List.mem_map.mpr ⟨x, hx, rfl⟩))
  have keepnode : ∀ x ∈ ls.flatten ++ ps, ∀ a,
      x.1 ≤ a → a < x.1 + bigSize x.2 → (bfreeMem m b fl k head)[a]? = m[a]? := by
    intro x hx a h1 h2
    have ab := active _ (bigBlocks_node (List.mem_append.mp hx))
    have af := arr x hx
    simp only [Apart] at ab af
    have sz : 8 ≤ bigSize k := by simp [bigSize]; omega
    have hk := hp.k_hi
    exact bfreeMem_keep _ _ _ _ _ _ (by omega) (by omega)
  have header : ∀ x ∈ ls.flatten ++ ps, BigHeaderKeep m (bfreeMem m b fl k head) x.1 := by
    intro x hx
    have rr : ∀ a n, x.1 ≤ a → a + n ≤ x.1 + bigSize x.2 →
        rdLE (bfreeMem m b fl k head) a n = rdLE m a n :=
      fun a n h1 h2 => rdLE_congr fun i hi => keepnode x hx _ (by omega) (by omega)
    exact ⟨rr _ _ (by omega) (by simp [bigSize]; omega),
      rr _ _ (by omega) (by simp [bigSize]; omega),
      rr _ _ (by omega) (by simp [bigSize]; omega)⟩
  have reent : ∀ a n, symImpureData + reentResultOff ≤ a →
      a + n ≤ symImpureData + reentFreelistOff + 8 →
      rdLE (bfreeMem m b fl k head) a n = rdLE m a n := by
    intro a n h1 h2
    have hb := hp.b_lo
    have hf := hp.fl_lo
    apply bfree_rdLE_keep <;>
      simp only [symImpureData, reentResultOff, reentFreelistOff] at h1 h2 <;> omega
  have perm := bfreeBlocks_perm b k fl res rk ls ps kl
  refine { h with
    res_w := (reent _ _ (by decide) (by decide)).trans h.res_w
    rk_w := fun hz => (reent _ _ (by decide) (by decide)).trans (h.rk_w hz)
    p5_w := (reent _ _ (by decide) (by decide)).trans h.p5_w
    fl_w := (reent _ _ (by decide) (by decide)).trans h.fl_w
    fl_zero := fun hz => absurd hz hn
    hds_len := by simpa using h.hds_len
    lists_len := by simpa [bfreeLists] using h.lists_len
    heads := ?_
    chains := ?_
    classes := ?_
    p5s := h.p5s.congr (fun x hx => header x (List.mem_append_right _ hx))
    p5v := ?_
    p5cap := ?_
    apart := ?_
    inB := ?_ }
  · intro _ i hi
    have hi' : i < hds.length := by simpa using hi
    by_cases he : k = i
    · subst i
      simp only [List.getElem_set_self]
      have hb : b ≠ 0 := by have := hp.b_lo; omega
      unfold bfreeMem
      rw [if_neg hb, AllocHeap.rd64_eq, read64_writeMap8, sdData_toNat,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hp.b_hi; omega)]
    · rw [List.getElem_set_ne he]
      have il : i < 65 := by simpa only [h.hds_len] using hi'
      exact (bfree_rdLE_keep (by
        have ha := hp.apart; have := hp.k_hi; omega)
        (by omega)).trans (h.heads hn i hi')
  · intro _ i hi hj
    have hi' : i < hds.length := by simpa using hi
    have hj' : i < ls.length := by simpa [bfreeLists] using hj
    by_cases he : k = i
    · subst i
      simp only [List.getElem_set_self, bfreeLists, List.getElem_modify_eq]
      have hc := h.chains hn k hi' hj'
      rw [hd hi'] at hc
      apply bfree_chain hp ⟨cls, cap, ?_, ?_⟩ hc
      · intro x hx
        exact active _ (bigBlocks_node (.inl (List.mem_flatten.mpr
          ⟨ls[k], List.getElem_mem hj', hx⟩)))
      · intro x hx
        exact arr x (List.mem_append_left _ (List.mem_flatten.mpr
          ⟨ls[k], List.getElem_mem hj', hx⟩))
    · simp only [List.getElem_set_ne he, bfreeLists, List.getElem_modify_ne _ _ he]
      exact (h.chains hn i hi' hj').congr fun x hx => header x
        (List.mem_append_left _ (List.mem_flatten.mpr ⟨ls[i], List.getElem_mem hj', hx⟩))
  · intro i hi x hx
    have hi' : i < ls.length := by simpa [bfreeLists] using hi
    by_cases he : k = i
    · subst i
      simp only [bfreeLists, List.getElem_modify_eq, List.mem_cons] at hx
      rcases hx with rfl | hx
      · rfl
      · exact h.classes k hi' x hx
    · simp only [bfreeLists, List.getElem_modify_ne _ _ he] at hx
      exact h.classes i hi' x hx
  · intro j x hx
    have hm := List.mem_of_getElem? hx
    obtain ⟨w, hw, hc⟩ := h.p5cap x hm
    exact (bigVal_congr hw hc (keepnode x (List.mem_append_right _ hm))).trans (h.p5v j x hx)
  · intro x hx
    obtain ⟨w, hw, hc⟩ := h.p5cap x hx
    refine ⟨w, ?_, hc⟩
    exact (rdLE_congr fun i hi => keepnode x (List.mem_append_right _ hx) _
      (by omega) (by simp [bigSize]; omega)).trans hw
  · exact (List.pairwise_cons.mpr ⟨active, h.apart⟩).perm perm.symm
      (fun hab => hab.elim Or.inr Or.inl)
  · intro x hx a ha hz
    rcases List.mem_cons.mp (perm.subset hx) with rfl | hx
    · exact block_in a ha hz
    · exact h.inB x hx a ha hz

/-- On RAM, filling zero bytes commutes with these two stores. -/
theorem bfreeMem_fill (m : Mem) (b fl k a : Nat) (head : BitVec 64) (ha : Ram a) :
    (bfreeMem (fillZeroMem m) b fl k head)[a]? =
      (fillZeroMem (bfreeMem m b fl k head))[a]? := by
  have present : ∀ (m : Mem) (p : Nat) (d : BitVec 64),
      m[a]? = some (bytesT1 m a) →
      (writeMap8 m p d)[a]? = some (bytesT1 (writeMap8 m p d) a) := by
    intro m p d hm
    by_cases h : a < p ∨ p + 8 ≤ a
    · simpa only [getElem?_writeMap8_out _ _ _ _ h, bytesT1_writeMap8_out _ _ _ h] using hm
    · have he : a = p + (a - p) := by omega
      have hi : a - p < 8 := by omega
      rw [he] at hm ⊢
      simp only [bytesT1, getElem_writeMap8 _ _ _ _ hi, Option.getD_some]
  have hp : (bfreeMem (fillZeroMem m) b fl k head)[a]? =
      some (bytesT1 (bfreeMem (fillZeroMem m) b fl k head) a) := by
    have hm : (fillZeroMem m)[a]? = some (bytesT1 (fillZeroMem m) a) := by
      rw [fillZeroMem_ram _ ha.1 ha.2, bytesT1_fill]
    unfold bfreeMem
    split
    · exact hm
    · exact present _ _ _ (present _ _ _ hm)
  rw [hp, fillZeroMem_ram _ ha.1 ha.2, bfreeMem_total (fun a => bytesT1_fill m a)]

/-- The ownership invariant and its honest footprint at the new memory. -/
theorem bfree_frozen {m : Mem} {H : HeapIx} {B : Nat → Prop}
    {b fl k res rk p5 : Nat} {hds : List Nat} {ls : List (List (Nat × Nat))}
    {ps : List (Nat × Nat)} {head : BitVec 64}
    (h : BfreeHeapIn m H B b fl k res rk p5 hds ls ps head) :
    Frozen (BigFoot B) (fun M => ReentMp (fillZeroMem M) B) (bfreeMem m b fl k head) := by
  have hp : BfreePushIn symImpureData b fl k head (fillZeroMem m) :=
    { h.push with
      cls := (bytesT4_congrT (fun i hi => bytesT1_fill m _)).trans h.push.cls
      freelist := (bytesT8_congrT (fun i hi => bytesT1_fill m _)).trans h.push.freelist
      slot := (bytesT8_congrT (fun i hi => bytesT1_fill m _)).trans h.push.slot }
  have hn : fl ≠ 0 := by have := h.push.fl_lo; omega
  have hd : ∀ hk : k < hds.length, hds[k] = head.toNat := by
    intro hk
    have hw := h.mp.heads hn k hk
    have he := congrArg BitVec.toNat ((bT8_of_fill (bytesT8_of_rd64 hw)).symm.trans h.push.slot)
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (rd64_lt hw)] using he
  have hm := reentMpAt_bfree h.mp hp h.cls h.maxwds hd h.active h.block_in
  intro M hM
  have ramB : ∀ a, B a → Ram a := by
    intro a ha
    have ha := h.region a ha
    simp only [Ram, ramBase, ramSize]
    have h1 := ha.lo; have h2 := ha.hi
    simp only [heapStart, heapEnd, symEnd, symHeapEnd] at h1 h2
    omega
  have ramR : ∀ a, ReentWord a → Ram a := by
    intro a ha
    simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at ha
    simp only [Ram, ramBase, ramSize]
    omega
  refine .intro fl res rk p5 (hds.set k b) (bfreeLists b k ls) ps
    (reentMpAt_congr hm (fun a ha => ?_) (fun x hx a h1 h2 => ?_))
  · exact (fill_total (ramR a ha) (hM a (.inr ha))).trans
      (bfreeMem_fill m b fl k a head (ramR a ha)).symm
  · have hb := hm.inB x hx a h1 h2
    exact (fill_total (ramB a hb) (hM a (.inl hb))).trans
      (bfreeMem_fill m b fl k a head (ramB a hb)).symm

/-- `_Bfree` changes no allocator metadata: both stores lie in live payloads. -/
theorem bfree_bigRun {m : Mem} {H : HeapIx} {B F : Nat → Prop}
    {b fl k res rk p5 : Nat} {hds : List Nat} {ls : List (List (Nat × Nat))}
    {ps : List (Nat × Nat)} {head : BitVec 64}
    (h : BfreeHeapIn m H B b fl k res rk p5 hds ls ps head) :
    BigRun F m (bfreeMem m b fl k head) H H B B 0 := by
  have hn : fl ≠ 0 := by have := h.push.fl_lo; omega
  have arr : (fl, 520) ∈ bigBlocks fl res rk ls ps := by simp [bigBlocks, hn]
  have writes : ∀ a, (b ≤ a ∧ a < b + 8) ∨
      (fl + 8 * k ≤ a ∧ a < fl + 8 * k + 8) → B a := by
    intro a ha
    rcases ha with ha | ha
    · exact h.block_in a ha.1 (by have := ha.2; simp [bigSize]; omega)
    · exact h.mp.inB _ arr a (by omega) (by have := h.push.k_hi; omega)
  have keep : ∀ a, ¬ B a → bytesT1 (bfreeMem m b fl k head) a = bytesT1 m a := by
    intro a ha
    unfold bytesT1
    rw [bfreeMem_frame (fun hb => ha (writes a (.inl hb))) (fun hf => ha (writes a (.inr hf)))]
  refine ⟨h.heap.ofTotal (fun a _ hu => ?_), fun _ hc _ => hc, by omega,
    bfree_frozen h, fun _ hb => .inl hb, fun a ha => keep a (fun hb => ha (.inr (.inl hb)))⟩
  exact (keep a (fun hb => hu (h.region a hb).inuse)).trans (bytesT1_fill m a).symm

/-- ABI/exact-store result and the ownership effect of the same machine run. -/
structure BfreeHeapPost (sp b fl k : Nat) (r head : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (H : HeapIx) (B F : Nat → Prop) (c : Vsa.Machine.Config) : Prop where
  machine : BfreePost sp b fl k r head f m o c
  bigRun : BigRun F m (bfreeMem m b fl k head) H H B B 0

/-- Machine summary with the reusable ownership contract and zero heap growth. -/
theorem bfree_heap_sum (sp b fl k res rk p5 : Nat) (r head : BitVec 64) (f : AbiFrame)
    (m : Mem) (o : Array String) (H : HeapIx) (B F : Nat → Prop)
    (hds : List Nat) (ls : List (List (Nat × Nat))) (ps : List (Nat × Nat))
    (h : BfreeHeapIn m H B b fl k res rk p5 hds ls ps head)
    (hs : sp ≤ 2 ^ 32) (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8003d700#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 b⟩] sp r f) (ArmPay m o))
      (BfreeHeapPost sp b fl k r head f m o H B F) := by
  intro c hc
  obtain ⟨c', run, post⟩ := bfree_sum sp symImpureData b fl k r head f m o
    ⟨hs, hr, fun _ => h.push⟩ c hc
  exact ⟨c', run, post, bfree_bigRun h⟩

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.CallClose
import Lua.Vm.Boot.Check
import Lua.Vm.Sim.Kit.Intern

/-!
# The literals' facts after a new string (lane F1-20)

A new short string `p` (`internshrstr`'s creation path) is linked at its
bucket's head and counted: three words change that the literals' facts read
or might read (`TabWr`: the bucket's word, `nuse`, `g->allgc`). Every other
fact they state reads bytes off those words: the chains' nodes, the literals,
the cache's candidates and the string metatable lie apart from the table's
words (`StrtOff`, boot-checked), `g`'s other words by their offsets. So the
facts hold again at the new table (`LitsIn.insert`, `StrtSafe.insert`), and
frozen on the old footprint with the changed words and the new object
(`frozen_insert`).

The congruences below are stated for a memory `m'` agreeing with `m` off a
set `Wr` of written bytes that lies inside the table's words `T`.
-/

open Vsa.Sim

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Vsa.Densify

/-! ## Reads off the written bytes -/

/-- A read whose bytes are off `Wr` is the same in a memory agreeing off `Wr`. -/
theorem rdLE_off {m m' : Mem} {Wr : Nat → Prop} (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {a n : Nat}
    (h : ∀ i, i < n → ¬ Wr (a + i)) : rdLE m' a n = rdLE m a n :=
  rdLE_congr fun i hi => hA _ (h i hi)

/-- **A chain alive and off the table's words, again** (it reads its nodes'
lengths, links and marks, all inside their objects). -/
theorem _root_.Lua.Vm.ChainOff.congr_off {m m' : Mem} {T Wr : Nat → Prop} {cw : Nat} {lits : List Nat}
    (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat} (h : ChainOff m T cw lits p) :
    ChainOff m' T cw lits p := by
  induction h with
  | nil => exact .nil
  | @cons ts nx l h0 hl hnx hT hal _ ih =>
    have hc : tstringContentsOff = 24 := rfl
    have off : ∀ k, k < tstringContentsOff + l + 1 → ¬ Wr (ts + k) := fun k hk hw =>
      hT (ts + k) (by omega) (by omega) (hW _ hw)
    refine .cons h0 ?_ ?_ hT ?_ ih
    · rw [show rd8 m' (ts + tstringShrlenOff) = rd8 m (ts + tstringShrlenOff) from
        rdLE_off hA fun i hi => by have := off (11 + i) (by simp only [tstringShrlenOff] at *; omega)
                                   simpa [tstringShrlenOff, Nat.add_assoc] using this]
      exact hl
    · rw [show rd64 m' (ts + tstringLnglenOff) = rd64 m (ts + tstringLnglenOff) from
        rdLE_off hA fun i hi => by have := off (16 + i) (by omega)
                                   simpa [tstringLnglenOff, Nat.add_assoc] using this]
      exact hnx
    · intro hn
      obtain ⟨mk, hm, hz⟩ := hal hn
      refine ⟨mk, ?_, hz⟩
      rw [show rd8 m' (ts + gcMarkedOff) = rd8 m (ts + gcMarkedOff) from
        rdLE_off hA fun i hi => by have := off (9 + i) (by omega)
                                   simpa [gcMarkedOff, Nat.add_assoc] using this]
      exact hm

/-- The bytes of a node's header and contents are off `Wr` (`ChainOff`'s
object off `T`). -/
theorem node_off {m : Mem} {T Wr : Nat → Prop} (hW : ∀ a, Wr a → T a) {ts l : Nat}
    (hT : ∀ a, ts ≤ a → a < ts + tstringContentsOff + l + 1 → ¬ T a) {k : Nat}
    (hk : k < tstringContentsOff + l + 1) : ¬ Wr (ts + k) := fun hw => hT _ (by omega) (by omega) (hW _ hw)

/-- A node's read of `n` bytes at offset `o` inside its object, again. -/
theorem node_rd {m m' : Mem} {T Wr : Nat → Prop} (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?)
    {ts l : Nat} (hT : ∀ a, ts ≤ a → a < ts + tstringContentsOff + l + 1 → ¬ T a) {o n : Nat}
    (h : o + n ≤ tstringContentsOff + l + 1) : rdLE m' (ts + o) n = rdLE m (ts + o) n :=
  rdLE_off hA fun i hi => by
    have := node_off (m := m) hW hT (k := o + i) (by omega)
    rwa [← Nat.add_assoc] at this

/-- **A bucket's chain, again**, its nodes off the written bytes (`ChainOff`). -/
theorem _root_.Lua.Vm.StrChain.congr_off {m m' : Mem} {T Wr : Nat → Prop} {cw : Nat} {lits : List Nat} {size i : Nat}
    (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat} (h : StrChain m size i p)
    (ho : ChainOff m T cw lits p) : StrChain m' size i p := by
  induction h with
  | nil => exact .nil
  | @cons ts hh nx h0 htt hhs hmod hnx _ ih =>
    cases ho with
    | nil => exact absurd rfl h0
    | @cons _ nx' l _ hl hnx' hT _ hrest =>
      have e : nx' = nx := Option.some.inj (hnx'.symm.trans hnx)
      subst e
      have hc : tstringContentsOff = 24 := rfl
      refine .cons h0 ?_ ?_ hmod ?_ (ih hrest)
      · rw [show rd8 m' (ts + gcTtOff) = rd8 m (ts + gcTtOff) from node_rd hW hA hT (by simp [gcTtOff]; omega)]
        exact htt
      · rw [show rd32 m' (ts + tstringHashOff) = rd32 m (ts + tstringHashOff) from
          node_rd hW hA hT (by simp [tstringHashOff]; omega)]
        exact hhs
      · rw [show rd64 m' (ts + tstringLnglenOff) = rd64 m (ts + tstringLnglenOff) from
          node_rd hW hA hT (by simp [tstringLnglenOff]; omega)]
        exact hnx

/-- **A bucket's safe chain, again.** -/
theorem _root_.Lua.Vm.StrChainK.congr_off {m m' : Mem} {T Wr K X W : Nat → Prop} {cw : Nat} {lits : List Nat} {size i : Nat}
    (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat} (h : StrChainK m K X W size i p)
    (ho : ChainOff m T cw lits p) : StrChainK m' K X W size i p := by
  induction h with
  | nil => exact .nil
  | @cons ts hh nx l h0 htt hl hle hhs hmod hnx hobj hmk hhn _ ih =>
    cases ho with
    | nil => exact absurd rfl h0
    | @cons _ nx' l' _ hl' hnx' hT _ hrest =>
      have e : nx' = nx := Option.some.inj (hnx'.symm.trans hnx)
      subst e
      have hc : tstringContentsOff = 24 := rfl
      refine .cons h0 ?_ ?_ hle ?_ hmod ?_ hobj hmk hhn (ih hrest)
      · rw [show rd8 m' (ts + gcTtOff) = rd8 m (ts + gcTtOff) from node_rd hW hA hT (by simp [gcTtOff]; omega)]
        exact htt
      · rw [show rd8 m' (ts + tstringShrlenOff) = rd8 m (ts + tstringShrlenOff) from
          node_rd hW hA hT (by simp [tstringShrlenOff]; omega)]
        exact hl
      · rw [show rd32 m' (ts + tstringHashOff) = rd32 m (ts + tstringHashOff) from
          node_rd hW hA hT (by simp [tstringHashOff]; omega)]
        exact hhs
      · rw [show rd64 m' (ts + tstringLnglenOff) = rd64 m (ts + tstringLnglenOff) from
          node_rd hW hA hT (by simp [tstringLnglenOff]; omega)]
        exact hnx

/-- **A chain reaching `ts`, again.** -/
theorem _root_.Lua.Vm.ChainHas.congr_off {m m' : Mem} {T Wr : Nat → Prop} {cw : Nat} {lits : List Nat} {ts : Nat}
    (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat} (h : ChainHas m ts p)
    (ho : ChainOff m T cw lits p) : ChainHas m' ts p := by
  induction h with
  | here => exact .here
  | @next p nx h0 hnx _ ih =>
    cases ho with
    | nil => exact absurd rfl h0
    | @cons _ nx' l _ hl hnx' hT _ hrest =>
      have e : nx' = nx := Option.some.inj (hnx'.symm.trans hnx)
      subst e
      have hc : tstringContentsOff = 24 := rfl
      refine .next h0 ?_ (ih hrest)
      rw [show rd64 m' (p + tstringLnglenOff) = rd64 m (p + tstringLnglenOff) from
        node_rd hW hA hT (by simp [tstringLnglenOff]; omega)]
      exact hnx

/-- A failed test, again (it reads the length, and the contents only where the
length is the bytes'). -/
theorem _root_.Lua.Vm.NoMatch.congr_off {m m' : Mem} {T Wr : Nat → Prop} (hW : ∀ a, Wr a → T a)
    (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p l : Nat} {b : List UInt8}
    (hl : rd8 m (p + tstringShrlenOff) = some l)
    (hT : ∀ a, p ≤ a → a < p + tstringContentsOff + l + 1 → ¬ T a) (h : NoMatch m p b) : NoMatch m' p b := by
  have hc : tstringContentsOff = 24 := rfl
  have el : rd8 m' (p + tstringShrlenOff) = rd8 m (p + tstringShrlenOff) :=
    node_rd hW hA hT (by simp [tstringShrlenOff]; omega)
  rcases h with h | ⟨i, hi, hb⟩
  · exact .inl (by rw [el]; exact h)
  · by_cases hlb : l = b.length
    · subst hlb
      refine .inr ⟨i, hi, ?_⟩
      rw [show rd8 m' (p + tstringContentsOff + i) = rd8 m (p + tstringContentsOff + i) by
        rw [Nat.add_assoc]; exact node_rd hW hA hT (by omega)]
      exact hb
    · exact .inl (by rw [el, hl]; intro e; exact hlb (Option.some.inj e))

/-- **The walk meeting `ts` first, again.** -/
theorem _root_.Lua.Vm.ChainFirst.congr_off {m m' : Mem} {T Wr : Nat → Prop} {cw : Nat} {lits : List Nat} {b : List UInt8}
    {ts : Nat} (hW : ∀ a, Wr a → T a) (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat} (h : ChainFirst m b ts p)
    (ho : ChainOff m T cw lits p) : ChainFirst m' b ts p := by
  induction h with
  | here => exact .here
  | @next p nx h0 hne hlo hhi hnx hnm _ ih =>
    cases ho with
    | nil => exact absurd rfl h0
    | @cons _ nx' l _ hl hnx' hT _ hrest =>
      have e : nx' = nx := Option.some.inj (hnx'.symm.trans hnx)
      subst e
      have hc : tstringContentsOff = 24 := rfl
      refine .next h0 hne hlo hhi ?_ (NoMatch.congr_off hW hA hl hT hnm) (ih hrest)
      rw [show rd64 m' (p + tstringLnglenOff) = rd64 m (p + tstringLnglenOff) from
        node_rd hW hA hT (by simp [tstringLnglenOff]; omega)]
      exact hnx

/-- A read inside a range off `Wr`. -/
theorem rd_in {m m' : Mem} {Wr : Nat → Prop} (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {lo k : Nat}
    (hR : ∀ a, lo ≤ a → a < lo + k → ¬ Wr a) {a n : Nat} (h1 : lo ≤ a) (h2 : a + n ≤ lo + k) :
    rdLE m' a n = rdLE m a n :=
  rdLE_off hA fun i hi => hR _ (by omega) (by omega)

/-- **`strcmp` differs, again** (it reads at most the literal's bytes and its
terminator). -/
theorem _root_.Lua.Vm.CDiffers.congr_off {m m' : Mem} {Wr : Nat → Prop} (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {p : Nat}
    {b : List UInt8} (hR : ∀ a, p + tstringContentsOff ≤ a → a < p + tstringContentsOff + (b.length + 1) → ¬ Wr a)
    (h : CDiffers m p b) : CDiffers m' p b := by
  obtain ⟨k, hk, hb, hne⟩ := h
  refine ⟨k, hk, fun i hi => ?_, ?_⟩
  · rw [show rd8 m' (p + tstringContentsOff + i) = rd8 m (p + tstringContentsOff + i) from
      rd_in hA hR (by omega) (by omega)]
    exact hb i hi
  · rw [show rd8 m' (p + tstringContentsOff + k) = rd8 m (p + tstringContentsOff + k) from
      rd_in hA hR (by omega) (by omega)]
    exact hne

/-- **A cache candidate, again** (the literals' bytes at most 10). -/
theorem _root_.Lua.Vm.CandOk.congr_off {m m' : Mem} {Wr : Nat → Prop} (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {lits : List CLit}
    {r p : Nat} (hl : ∀ l ∈ lits, l.bytes.length ≤ 10)
    (hR : ∀ a, p + tstringContentsOff ≤ a → a < p + tstringContentsOff + 11 → ¬ Wr a) (h : CandOk m lits r p) :
    CandOk m' lits r p :=
  ⟨h.lo, h.hi, fun l hl' hr => (h.ok l hl' hr).imp id fun hd =>
    CDiffers.congr_off hA (fun a h1 h2 => hR a h1 (by have := hl l hl'; omega)) hd⟩

/-- **The string metatable's walk missing, again** (it reads the nodes of the
array). -/
theorem _root_.Lua.Vm.NodeMiss.congr_off {m m' : Mem} {Wr : Nat → Prop} (hA : ∀ a, ¬ Wr a → m'[a]? = m[a]?) {ts lo hi : Nat}
    (hR : ∀ a, lo ≤ a → a < hi → ¬ Wr a) {n : Nat} (h : NodeMiss m ts lo hi n) : NodeMiss m' ts lo hi n := by
  have hR' : ∀ a, lo ≤ a → a < lo + (hi - lo) → ¬ Wr a := fun a h1 h2 => hR a h1 (by omega)
  have ns : nodeSize = 24 := rfl
  induction h with
  | @last n h1 h2 hk hz =>
    refine .last h1 h2 ?_ ?_
    · rcases hk with hk | ⟨kv, hkv, hne⟩
      · left
        rw [show rd8 m' (n + nodeKeyTtOff) = rd8 m (n + nodeKeyTtOff) from
          rd_in hA hR' (by omega) (by simp [nodeKeyTtOff]; omega)]
        exact hk
      · right
        refine ⟨kv, ?_, hne⟩
        rw [show rd64 m' (n + nodeKeyValOff) = rd64 m (n + nodeKeyValOff) from
          rd_in hA hR' (by omega) (by simp [nodeKeyValOff]; omega)]
        exact hkv
    · rw [show rd32 m' (n + nodeNextOff) = rd32 m (n + nodeNextOff) from
        rd_in hA hR' (by omega) (by simp [nodeNextOff]; omega)]
      exact hz
  | @next n gg h1 h2 hk hg hg0 _ ih =>
    refine .next h1 h2 ?_ ?_ hg0 ih
    · rcases hk with hk | ⟨kv, hkv, hne⟩
      · left
        rw [show rd8 m' (n + nodeKeyTtOff) = rd8 m (n + nodeKeyTtOff) from
          rd_in hA hR' (by omega) (by simp [nodeKeyTtOff]; omega)]
        exact hk
      · right
        refine ⟨kv, ?_, hne⟩
        rw [show rd64 m' (n + nodeKeyValOff) = rd64 m (n + nodeKeyValOff) from
          rd_in hA hR' (by omega) (by simp [nodeKeyValOff]; omega)]
        exact hkv
    · rw [show rd32 m' (n + nodeNextOff) = rd32 m (n + nodeNextOff) from
        rd_in hA hR' (by omega) (by simp [nodeNextOff]; omega)]
      exact hg

/-! ## The new table -/

/-- **The words a new string's insertion writes** in the table `rt`: bucket
`j`'s head, `nuse`, `g->allgc`. -/
def TabWr (rt : RtPtrs) (j a : Nat) : Prop :=
  Rng (rt.strtHash + 8 * j) 8 a ∨ Rng (rt.g + gStrtNuseOff) 4 a ∨ Rng (rt.g + gAllgcOff) 8 a

theorem TabWr.tab {rt : RtPtrs} {j a : Nat} (hj : j < rt.strtSize) (h : TabWr rt j a) : TabW rt a := by
  simp only [TabWr, TabW, Rng, gStrtNuseOff, gAllgcOff, gStrcacheOff, strcacheN, strcacheM] at h ⊢
  omega

/-- The table after the insertion: one more string, `p` at bucket `j`'s head. -/
def _root_.Lua.Vm.RtPtrs.ins (rt : RtPtrs) (j p : Nat) : RtPtrs :=
  { rt with strtNuse := rt.strtNuse + 1, strtHeads := rt.strtHeads.set j p }

/-- **The new string at the new table**, over the memory `m'` (a fill): the
object `p` of the bytes `b` (header, length, the hash `h` of bucket `j`,
contents, terminator, linked to the old head), alive (`mk & (cw ^ 24) = 0`),
off the table's words, not a literal's bytes nor a literal's object; the
bucket and `nuse` updated. -/
structure NewStr (m' : Mem) (rt : RtPtrs) (ls : LitPtrs) (cw : Nat) (b : List UInt8) (h : UInt32) (p j : Nat) :
    Prop where
  p0 : p ≠ 0
  p_lo : symTohost + 16 ≤ p
  p_hi : p + 128 ≤ symHeapEnd
  tt : rd8 m' (p + gcTtOff) = some gcShrStr
  len : rd8 m' (p + tstringShrlenOff) = some b.length
  short : b.length ≤ maxShortLen
  hash : rd32 m' (p + tstringHashOff) = some h.toNat
  j_def : h.toNat % rt.strtSize = j
  j_lt : j < rt.strtHeads.length
  hnext : rd64 m' (p + tstringLnglenOff) = some rt.strtHeads[j]
  bytes : BytesAt m' (p + tstringContentsOff) b
  nul : m'[p + tstringContentsOff + b.length]? = some 0
  mark : ∃ mk, rd8 m' (p + gcMarkedOff) = some mk ∧ mk &&& (cw ^^^ 24) = 0
  off : ∀ a, p ≤ a → a < p + tstringContentsOff + b.length + 1 → ¬ TabW rt a
  lits : ∀ l ∈ ls.table, l.bytes ≠ b
  nlit : ∀ ts ∈ ls.strs, p ≠ ts
  bucket : rd64 m' (rt.strtHash + 8 * j) = some p
  nuse : rd32 m' (rt.g + gStrtNuseOff) = some (rt.strtNuse + 1)
  nuse_lt : rt.strtNuse < rt.strtSize

/-- The bucket array and `g` apart, as `TabWr`'s words need. -/
structure TabApart (rt : RtPtrs) : Prop where
  kg : rt.strtHash + 8 * rt.strtSize ≤ rt.g ∨ rt.g + (gStrcacheOff + 8 * strcacheN * strcacheM) ≤ rt.strtHash

/-- The new string fails every literal's test (`b` is none of their bytes). -/
theorem NewStr.noMatch {m' : Mem} {rt : RtPtrs} {ls : LitPtrs} {cw : Nat} {b : List UInt8} {h : UInt32} {p j : Nat}
    (hn : NewStr m' rt ls cw b h p j) {l : CLit} (hl : l ∈ ls.table) : NoMatch m' p l.bytes := by
  by_cases hlen : b.length = l.bytes.length
  · have hne := hn.lits l hl
    have : ∃ i, i < l.bytes.length ∧ b.getD i 0 ≠ l.bytes.getD i 0 := by
      refine Classical.byContradiction fun hc => hne (List.ext_getElem hlen.symm fun i h1 h2 => ?_)
      have e := Classical.not_not.mp fun hne' => hc ⟨i, h1, hne'⟩
      simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2,
        Option.getD_some] at e
      exact e.symm
    obtain ⟨i, hi, hd⟩ := this
    refine .inr ⟨i, hi, fun e => hd ?_⟩
    have hb := hn.bytes i (by omega)
    have e2 : rd8 m' (p + tstringContentsOff + i) = some (b.getD i 0).toNat := by
      simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero, hb]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      simp [Nat.mod_eq_of_lt (UInt8.toNat_lt _)]
    rw [e2, Option.some.injEq] at e
    exact UInt8.toNat_inj.mp e
  · exact .inl (by rw [hn.len]; intro e; exact hlen (Option.some.inj e))

section Ins

variable {m m' : Mem} {rt : RtPtrs} {ls : LitPtrs} {cw : Nat} {b : List UInt8} {h : UInt32} {p j : Nat}

/-- `g`'s words the facts read besides the written ones, off `TabWr`. -/
theorem g_off (ha : TabApart rt) (hj : j < rt.strtSize) {o n : Nat}
    (ho : (o + n ≤ gStrtNuseOff ∨ gStrtNuseOff + 4 ≤ o) ∧ (o + n ≤ gAllgcOff ∨ gAllgcOff + 8 ≤ o))
    (hon : o + n ≤ gStrcacheOff + 8 * strcacheN * strcacheM) :
    ∀ i, i < n → ¬ TabWr rt j (rt.g + o + i) := by
  intro i hi hw
  have := ha.kg
  simp only [TabWr, Rng, gStrtNuseOff, gAllgcOff, gStrcacheOff, strcacheN, strcacheM] at hw ho hon this
  omega

/-- **`g->strt` after the insertion** (`StrtAt` at `rt.ins j p`). -/
theorem strtAt_ins (hA : ∀ a, ¬ TabWr rt j a → m'[a]? = m[a]?) (ha : TabApart rt)
    (hn : NewStr m' rt ls cw b h p j) (hS : StrtAt m rt) (hO : StrtOff m ls rt) :
    StrtAt m' (rt.ins j p) := by
  have hj := hn.j_lt
  have hjs : j < rt.strtSize := by rw [← hS.heads_len]; exact hj
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  obtain ⟨cw0, hcw0, hch⟩ := hO.white
  have hrd : ∀ o n, (o + n ≤ gStrtNuseOff ∨ gStrtNuseOff + 4 ≤ o) ∧ (o + n ≤ gAllgcOff ∨ gAllgcOff + 8 ≤ o) →
      o + n ≤ gStrcacheOff + 8 * strcacheN * strcacheM → rdLE m' (rt.g + o) n = rdLE m (rt.g + o) n :=
    fun o n h1 h2 => rdLE_off hA (g_off ha hjs h1 h2)
  have hlen : (rt.strtHeads.set j p).length = rt.strtSize := by rw [List.length_set, hS.heads_len]
  refine ⟨?_, ?_, hn.nuse, by have := hn.nuse_lt; simp only [RtPtrs.ins]; omega, hS.size_pos, hS.size_pow2,
    hlen, fun i hi => ?_, fun i hi => ?_⟩
  · show rd64 m' (rt.g + gStrtHashOff) = some rt.strtHash
    rw [show rd64 m' (rt.g + gStrtHashOff) = rd64 m (rt.g + gStrtHashOff) from
      hrd _ 8 (by simp [gStrtHashOff, gStrtNuseOff, gAllgcOff]) (by simp [gStrtHashOff, gStrcacheOff, strcacheN, strcacheM])]
    exact hS.hash
  · show rd32 m' (rt.g + gStrtSizeOff) = some rt.strtSize
    rw [show rd32 m' (rt.g + gStrtSizeOff) = rd32 m (rt.g + gStrtSizeOff) from
      hrd _ 4 (by simp [gStrtSizeOff, gStrtNuseOff, gAllgcOff]) (by simp [gStrtSizeOff, gStrcacheOff, strcacheN, strcacheM])]
    exact hS.size
  · -- the bucket words
    simp only [RtPtrs.ins] at hi ⊢
    have hi' : i < rt.strtHeads.length := by rw [List.length_set] at hi; exact hi
    by_cases e : i = j
    · subst e; rw [List.getElem_set_self]; exact hn.bucket
    · rw [List.getElem_set_ne (Ne.symm e)]
      rw [show rd64 m' (rt.strtHash + 8 * i) = rd64 m (rt.strtHash + 8 * i) from rdLE_off hA fun k hk hw => by
        have := ha.kg
        have hi'' : i < rt.strtSize := by rw [← hS.heads_len]; exact hi'
        simp only [TabWr, Rng, gStrtNuseOff, gAllgcOff, gStrcacheOff, strcacheN, strcacheM] at hw this
        omega]
      exact hS.bucket i hi'
  · -- the chains
    simp only [RtPtrs.ins] at hi ⊢
    have hi' : i < rt.strtHeads.length := by rw [List.length_set] at hi; exact hi
    by_cases e : i = j
    · subst e
      rw [List.getElem_set_self]
      have hc : tstringContentsOff = 24 := rfl
      have hT := hn.off
      refine .cons hn.p0 hn.tt hn.hash hn.j_def hn.hnext ?_
      exact (hS.chain i hi').congr_off hW hA (hch i hi')
    · rw [List.getElem_set_ne (Ne.symm e)]
      exact (hS.chain i hi').congr_off hW hA (hch i hi')

/-- **The current white and the chains, alive and off the table's words,
after the insertion.** -/
theorem strtOff_ins (hA : ∀ a, ¬ TabWr rt j a → m'[a]? = m[a]?) (ha : TabApart rt)
    (hn : NewStr m' rt ls cw b h p j) (hS : StrtAt m rt) (hO : StrtOff m ls rt)
    (hcw : rd8 m (rt.g + gCurrentwhiteOff) = some cw) : StrtOff m' ls (rt.ins j p) := by
  have hj := hn.j_lt
  have hjs : j < rt.strtSize := by rw [← hS.heads_len]; exact hj
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  obtain ⟨cw0, hcw0, hch⟩ := hO.white
  have e0 : cw0 = cw := Option.some.inj (hcw0.symm.trans hcw)
  subst e0
  have hT : TabW (rt.ins j p) = TabW rt := rfl
  refine ⟨⟨cw0, ?_, fun i hi => ?_⟩, hT ▸ hO.lits, hT ▸ hO.cands, hT ▸ hO.smt, hT ▸ hO.node, hO.hash_al⟩
  · rw [show rd8 m' ((rt.ins j p).g + gCurrentwhiteOff) = rd8 m (rt.g + gCurrentwhiteOff) from
      rdLE_off hA (g_off ha hjs (by simp [gCurrentwhiteOff, gStrtNuseOff, gAllgcOff])
        (by simp [gCurrentwhiteOff, gStrcacheOff, strcacheN, strcacheM]))]
    exact hcw0
  · simp only [RtPtrs.ins] at hi ⊢
    have hi' : i < rt.strtHeads.length := by rw [List.length_set] at hi; exact hi
    change ChainOff m' (TabW rt) cw0 ls.strs _
    by_cases e : i = j
    · subst e
      rw [List.getElem_set_self]
      exact .cons hn.p0 hn.len hn.hnext hn.off (fun _ => hn.mark) ((hch i hi').congr_off hW hA)
    · rw [List.getElem_set_ne (Ne.symm e)]
      exact (hch i hi').congr_off hW hA

/-- **A literal interned, after the insertion**: its object off the written
words, its walk past the new string (whose bytes are not the literal's). -/
theorem litInterned_ins {M M' : Mem} {seed : UInt32} {l : CLit} (hl : l ∈ ls.table)
    (hA : ∀ a, ¬ TabWr rt j a → (fillZeroMem M')[a]? = (fillZeroMem M)[a]?) (ha : TabApart rt)
    (hn : NewStr (fillZeroMem M') rt ls cw b h p j) (hO : StrtOff (fillZeroMem M) ls rt)
    (hlit : l.ts ∈ ls.strs) (hb10 : l.bytes.length ≤ 10)
    (hI : LitInterned M rt seed l.bytes l.ts) : LitInterned M' (rt.ins j p) seed l.bytes l.ts := by
  have hS := hI.strt
  have hj := hn.j_lt
  have hjs : j < rt.strtSize := by rw [← hS.heads_len]; exact hj
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  obtain ⟨cw0, hcw0, hch⟩ := hO.white
  have hc : tstringContentsOff = 24 := rfl
  have hlen : (rt.strtHeads.set j p).length = rt.strtSize := by rw [List.length_set, hS.heads_len]
  have hk := Nat.mod_lt (luaHash seed l.bytes).toNat hS.size_pos
  refine ⟨hI.repr.congr fun a h1 h2 => hA a fun hw => hO.lits l.ts hlit a h1 (by omega) (hW a hw), hI.short,
    strtAt_ins (ls := ls) hA ha hn hS hO, ?_, fun hk' => ?_, fun hk' => ?_, hI.ts_lo, hI.ts_hi⟩
  · show rd32 (fillZeroMem M') (rt.g + gSeedOff) = some seed.toNat
    rw [show rd32 (fillZeroMem M') (rt.g + gSeedOff) = rd32 (fillZeroMem M) (rt.g + gSeedOff) from
      rdLE_off hA (g_off ha hjs (by simp [gSeedOff, gStrtNuseOff, gAllgcOff])
        (by simp [gSeedOff, gStrcacheOff, strcacheN, strcacheM]))]
    exact hI.seed_w
  · simp only [RtPtrs.ins] at hk' ⊢
    have hk2 : (luaHash seed l.bytes).toNat % rt.strtSize < rt.strtHeads.length := by rw [hS.heads_len]; exact hk
    by_cases e : (luaHash seed l.bytes).toNat % rt.strtSize = j
    · simp only [e, List.getElem_set_self]
      have hold := hI.bucket hk2
      simp only [e] at hold
      exact .next hn.p0 hn.hnext (hold.congr_off hW hA (hch j hj))
    · rw [List.getElem_set_ne (Ne.symm e)]
      exact (hI.bucket hk2).congr_off hW hA (hch _ hk2)
  · simp only [RtPtrs.ins] at hk' ⊢
    have hk2 : (luaHash seed l.bytes).toNat % rt.strtSize < rt.strtHeads.length := by rw [hS.heads_len]; exact hk
    by_cases e : (luaHash seed l.bytes).toNat % rt.strtSize = j
    · simp only [e, List.getElem_set_self]
      have hold := hI.first hk2
      simp only [e] at hold
      exact .next hn.p0 (hn.nlit l.ts hlit) hn.p_lo hn.p_hi hn.hnext (hn.noMatch hl)
        (hold.congr_off hW hA (hch j hj))
    · rw [List.getElem_set_ne (Ne.symm e)]
      exact (hI.first hk2).congr_off hW hA (hch _ hk2)

/-- **The string metatable missing `"__tostring"`, after the insertion.** -/
theorem strMt_ins (hA : ∀ a, ¬ TabWr rt j a → m'[a]? = m[a]?) (ha : TabApart rt) (hjs : j < rt.strtSize)
    (hO : StrtOff m ls rt) (hM : StrMtMiss m rt.g ls.tos ls.smt ls.smtNode ls.smtLsz ls.tosHash) :
    StrMtMiss m' rt.g ls.tos ls.smt ls.smtNode ls.smtLsz ls.tosHash := by
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  have htos : ls.tos ∈ ls.strs := by simp [LitPtrs.strs]
  refine ⟨?_, hM.ne, ?_, ?_, ?_, hM.lsz_lt, hM.smt_lo, hM.smt_hi, hM.node_lo, hM.node_hi,
    hM.miss.congr_off hA fun a h1 h2 hw => hO.node a h1 h2 (hW a hw)⟩
  · rw [show rd64 m' (rt.g + gMtOff + 8 * luaTstring) = rd64 m (rt.g + gMtOff + 8 * luaTstring) from
      rdLE_off hA (g_off ha hjs (o := gMtOff + 8 * luaTstring) (by simp [gMtOff, luaTstring, gStrtNuseOff, gAllgcOff])
        (by simp [gMtOff, luaTstring, gStrcacheOff, strcacheN, strcacheM]))]
    exact hM.mt_w
  · rw [show rd8 m' (ls.smt + tableLsizenodeOff) = rd8 m (ls.smt + tableLsizenodeOff) from
      rd_in hA (lo := ls.smt) (k := 64) (fun a h1 h2 hw => hO.smt a h1 h2 (hW a hw)) (by omega)
        (by simp [tableLsizenodeOff])]
    exact hM.lsz_w
  · rw [show rd64 m' (ls.smt + tableNodeOff) = rd64 m (ls.smt + tableNodeOff) from
      rd_in hA (lo := ls.smt) (k := 64) (fun a h1 h2 hw => hO.smt a h1 h2 (hW a hw)) (by omega)
        (by simp [tableNodeOff])]
    exact hM.node_w
  · rw [show rd32 m' (ls.tos + tstringHashOff) = rd32 m (ls.tos + tstringHashOff) from
      rd_in hA (lo := ls.tos) (k := 40) (fun a h1 h2 hw => hO.lits ls.tos htos a h1 h2 (hW a hw)) (by omega)
        (by simp [tstringHashOff])]
    exact hM.hash_w

/-- The literals' bytes are at most ten. -/
theorem table_len (ls : LitPtrs) : ∀ l ∈ ls.table, l.bytes.length ≤ 10 := by
  intro l hl
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> dsimp only <;> decide

/-- **The literals interned after the insertion** (`LitsIn` at `rt.ins j p`). -/
theorem _root_.Lua.Vm.LitsIn.insert {M M' : Mem} {g sl : Nat} (hL : LitsIn M g sl ls rt)
    (hA : ∀ a, ¬ TabWr rt j a → (fillZeroMem M')[a]? = (fillZeroMem M)[a]?) (ha : TabApart rt)
    (hn : NewStr (fillZeroMem M') rt ls cw b h p j)
    (hcw : rd8 (fillZeroMem M) (rt.g + gCurrentwhiteOff) = some cw) : LitsIn M' g sl ls (rt.ins j p) := by
  have hS := hL.nil.strt
  have hjs : j < rt.strtSize := by rw [← hS.heads_len]; exact hn.j_lt
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  have hO := hL.off
  have hl10 := table_len ls
  refine ⟨hL.g, hL.sl,
    litInterned_ins (l := ⟨litNilAddr, nilB, ls.nil⟩) (by simp [LitPtrs.table]) hA ha hn hO
      (by simp [LitPtrs.strs]) (by dsimp only; decide) hL.nil,
    litInterned_ins (l := ⟨litTrueAddr, trueB, ls.tru⟩) (by simp [LitPtrs.table]) hA ha hn hO
      (by simp [LitPtrs.strs]) (by dsimp only; decide) hL.tru,
    litInterned_ins (l := ⟨litFalseAddr, falseB, ls.fls⟩) (by simp [LitPtrs.table]) hA ha hn hO
      (by simp [LitPtrs.strs]) (by dsimp only; decide) hL.fls,
    litInterned_ins (l := ⟨litTosAddr, tosB, ls.tos⟩) (by simp [LitPtrs.table]) hA ha hn hO
      (by simp [LitPtrs.strs]) (by dsimp only; decide) hL.tos,
    fun c hc => (hL.cands c hc).congr_off hA hl10 fun a h1 h2 hw => hO.cands c hc a h1 h2 (hW a hw),
    ?_, hL.hash_lo, hL.hash_hi, hL.size_hi, hL.lit_cands, strtOff_ins hA ha hn hS hO hcw⟩
  exact strMt_ins (rt := rt) hA ha hjs hO hL.strmt

/-- **The table safe after the insertion**: the new object in `K'`, off `W`,
its mark and `u.hnext` off `X`. -/
theorem _root_.Lua.Vm.StrtSafe.insert {K K' X W : Nat → Prop} (hSS : StrtSafe m rt K X W) (hS : StrtAt m rt)
    (hO : StrtOff m ls rt) (hA : ∀ a, ¬ TabWr rt j a → m'[a]? = m[a]?) (hn : NewStr m' rt ls cw b h p j)
    (hK : ∀ a, K a → K' a)
    (hpK : ∀ a, p ≤ a → a < p + tstringContentsOff + b.length + 1 → K' a ∧ ¬ W a) (hpm : ¬ X (p + gcMarkedOff))
    (hpn : ∀ a, p + tstringLnglenOff ≤ a → a < p + tstringLnglenOff + 8 → ¬ X a) :
    StrtSafe m' (rt.ins j p) K' X W := by
  have hjs : j < rt.strtSize := by rw [← hS.heads_len]; exact hn.j_lt
  have hW : ∀ a, TabWr rt j a → TabW rt a := fun a hw => hw.tab hjs
  obtain ⟨cw0, _, hch⟩ := hO.white
  refine ⟨fun a h1 h2 => ?_, fun i hi => ?_⟩
  · obtain ⟨k, x, w⟩ := hSS.hash a h1 h2
    exact ⟨hK a k, x, w⟩
  · simp only [RtPtrs.ins] at hi ⊢
    have hi' : i < rt.strtHeads.length := by rw [List.length_set] at hi; exact hi
    by_cases e : i = j
    · subst e
      rw [List.getElem_set_self]
      exact .cons hn.p0 hn.tt hn.len hn.short hn.hash hn.j_def hn.hnext hpK hpm hpn
        (((hSS.chains i hi').congr_off hW hA (hch i hi')).weaken hK (fun _ _ h => h) fun _ _ h => h)
    · rw [List.getElem_set_ne (Ne.symm e)]
      exact ((hSS.chains i hi').congr_off hW hA (hch i hi')).weaken hK (fun _ _ h => h) fun _ _ h => h

end Ins

/-! ## Frozen again -/

/-- A zero fill reads its RAM words (four bytes) as the total reads. -/
theorem rd32_fill (m : Mem) {a : Nat} (h1 : 0x80000000 ≤ a) (h2 : a + 4 ≤ 0x88000000) :
    rd32 (fillZeroMem m) a = some (bytesT4 m a).toNat := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (rdLE_isSome (m := fillZeroMem m) (a := a) (n := 4)
    fun j hj => by rw [fill_get m (a := a + j) (by omega) (by omega)]; rfl)
  have hx' : rd32 (fillZeroMem m) a = some x := hx
  have e := bytesT4_of_rd32 hx'
  have hlt := (rdLE_spec 4 _ a x hx').1
  rw [hx', ← bytesT4_congrT (m := fillZeroMem m) (m' := m) fun i _ => bytesT1_fill m _, e,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-- A memory with the bytes `as` taken from `src`. -/
def patchL (M src : Mem) : List Nat → Mem
  | [] => M
  | a :: as => (patchL M src as).insert a (bytesT1 src a)

theorem patchL_get (M src : Mem) (as : List Nat) (a : Nat) :
    (patchL M src as)[a]? = if a ∈ as then some (bytesT1 src a) else M[a]? := by
  induction as with
  | nil => simp [patchL]
  | cons x t ih =>
    simp only [patchL, List.mem_cons]
    by_cases e : a = x
    · subst e; simp
    · simp [Std.ExtHashMap.getElem?_insert, Ne.symm e, e, ih]

theorem patchL_bT1 (M src : Mem) (as : List Nat) (a : Nat) :
    bytesT1 (patchL M src as) a = if a ∈ as then bytesT1 src a else bytesT1 M a := by
  simp only [bytesT1, patchL_get]; split <;> rfl

/-- `TabWr`'s bytes as a list. -/
def twList (rt : RtPtrs) (j : Nat) : List Nat :=
  (List.range 8).map (rt.strtHash + 8 * j + ·) ++ (List.range 4).map (rt.g + gStrtNuseOff + ·) ++
    (List.range 8).map (rt.g + gAllgcOff + ·)

theorem mem_twList {rt : RtPtrs} {j a : Nat} : a ∈ twList rt j ↔ TabWr rt j a := by
  simp only [twList, List.mem_append, List.mem_map, List.mem_range, TabWr, Rng]
  constructor
  · rintro ((⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) <;> omega
  · rintro (h | h | h)
    · exact .inl (.inl ⟨a - (rt.strtHash + 8 * j), by omega, by omega⟩)
    · exact .inl (.inr ⟨a - (rt.g + gStrtNuseOff), by omega, by omega⟩)
    · exact .inr ⟨a - (rt.g + gAllgcOff), by omega, by omega⟩

/-- **A new string in the table, in total reads at the memory `m'`** (what the
creation path leaves): the object at `p` (its header, the current white's
`& WHITEBITS` as its mark, its length, the hash `h`, `u.hnext` the old head,
its contents `b` and terminator), the bucket's head `p`, `nuse + 1`. -/
structure NewObjT (m' : Mem) (g bkt p nuse head : Nat) (b : List UInt8) (h : UInt32) (cw : BitVec 8) : Prop where
  tt : bytesT1 m' (p + 8) = 0x04#8
  mark : bytesT1 m' (p + 9) = cw &&& 0x18#8
  len : bytesT1 m' (p + 11) = BitVec.ofNat 8 b.length
  hash : bytesT4 m' (p + 12) = h.toBitVec
  hnext : bytesT8 m' (p + 16) = BitVec.ofNat 64 head
  bytes : ∀ i, i < b.length → bytesT1 m' (p + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  nul : bytesT1 m' (p + 24 + b.length) = 0#8
  bucket : bytesT8 m' bkt = BitVec.ofNat 64 p
  nuse : bytesT4 m' (g + gStrtNuseOff) = BitVec.ofNat 32 (nuse + 1)

/-- The new object's footprint and the table words the facts read again. -/
def InsFoot (rt : RtPtrs) (j p l : Nat) (a : Nat) : Prop :=
  TabWr rt j a ∨ (p ≤ a ∧ a < p + tstringContentsOff + l + 1) ∨ Rng (rt.g + gStrtHashOff) 16 a ∨
    Rng (rt.g + gCurrentwhiteOff) 1 a

/-- **What the creation path must show of the new string** for the facts to
hold again: the object, apart from the table's words and the literals, alive,
in `K'` and off `W`, its mark and `u.hnext` off `X`; room in the table. -/
structure InsOk (rt : RtPtrs) (ls : LitPtrs) (K' X W : Nat → Prop) (b : List UInt8) (p : Nat) : Prop where
  p0 : p ≠ 0
  p_lo : symTohost + 16 ≤ p
  p_hi : p + 128 ≤ symHeapEnd
  off : ∀ a, p ≤ a → a < p + tstringContentsOff + b.length + 1 → ¬ TabW rt a
  lits : ∀ l ∈ ls.table, l.bytes ≠ b
  nlit : ∀ ts ∈ ls.strs, p ≠ ts
  short : b.length ≤ maxShortLen
  nuse_lt : rt.strtNuse < rt.strtSize
  inK : ∀ a, p ≤ a → a < p + tstringContentsOff + b.length + 1 → K' a ∧ ¬ W a
  mark : ¬ X (p + gcMarkedOff)
  hnext : ∀ a, p + tstringLnglenOff ≤ a → a < p + tstringLnglenOff + 8 → ¬ X a
  apart : TabApart rt

/-- The new string's mark is alive (`(cw & 24) & (cw ^ 24) = 0`). -/
theorem white_alive (cw : BitVec 8) : (cw &&& 0x18#8).toNat &&& (cw.toNat ^^^ 24) = 0 := by
  revert cw; decide

section Frz

variable {m m' : Mem} {g sl : Nat} {ls : LitPtrs} {FL K K' X W : Nat → Prop} {rt0 : RtPtrs} {p j : Nat}
  {b : List UInt8} {h : UInt32}

/-- The re-read of the table at `Mx` (the memory patched with `m`'s table
words) names `rt0`'s header, the bucket `j`'s head and `g`. -/
structure SameTab (rt rt0 : RtPtrs) (j : Nat) : Prop where
  g : rt.g = rt0.g
  hash : rt.strtHash = rt0.strtHash
  size : rt.strtSize = rt0.strtSize
  nuse : rt.strtNuse = rt0.strtNuse
  len : rt.strtHeads.length = rt0.strtHeads.length
  head : ∀ (h1 : j < rt.strtHeads.length) (h2 : j < rt0.strtHeads.length), rt.strtHeads[j] = rt0.strtHeads[j]

theorem TabWr.same {rt rt0 : RtPtrs} {j : Nat} (e : SameTab rt rt0 j) : TabWr rt j = TabWr rt0 j := by
  funext a; simp only [TabWr, e.hash, e.g]

theorem _root_.Lua.Vm.TabW.same {rt rt0 : RtPtrs} {j : Nat} (e : SameTab rt rt0 j) : TabW rt = TabW rt0 := by
  funext a; simp only [TabW, e.hash, e.g, e.size]

/-- **Two readings of tables agreeing on the header, `nuse` and bucket `j`'s
word are the same there.** -/
theorem sameTab_of {Mx : Mem} {rt rt0 : RtPtrs} (hS : StrtAt (fillZeroMem Mx) rt) (hS0 : StrtAt (fillZeroMem m) rt0)
    (hg : rt.g = rt0.g) (hj : j < rt0.strtHeads.length)
    (hag : ∀ a, (Rng (rt0.g + gStrtHashOff) 16 a ∨ Rng (rt0.strtHash + 8 * j) 8 a) → bytesT1 Mx a = bytesT1 m a)
    (hgh : rt0.g + gStrtHashOff + 16 ≤ 0x88000000) (hgl : 0x80000000 ≤ rt0.g)
    (hkh : rt0.strtHash + 8 * rt0.strtSize ≤ 0x88000000) (hkl : 0x80000000 ≤ rt0.strtHash) :
    SameTab rt rt0 j := by
  have r : ∀ {a n : Nat}, (∀ i, i < n → Rng (rt0.g + gStrtHashOff) 16 (a + i) ∨ Rng (rt0.strtHash + 8 * j) 8 (a + i)) →
      0x80000000 ≤ a → a + n ≤ 0x88000000 → rdLE (fillZeroMem Mx) a n = rdLE (fillZeroMem m) a n :=
    fun {a n} hin h1 h2 => rdLE_congr fun i hi => by
      rw [fill_get m (a := a + i) (by omega) (by omega), fill_get Mx (a := a + i) (by omega) (by omega),
        hag _ (hin i hi)]
  have eh : rt.strtHash = rt0.strtHash := by
    have := hS.hash; rw [hg] at this
    rw [show rd64 (fillZeroMem Mx) (rt0.g + gStrtHashOff) = rd64 (fillZeroMem m) (rt0.g + gStrtHashOff) from
      r (fun i hi => .inl (by simp only [Rng]; omega)) (by simp [gStrtHashOff]; omega) (by omega), hS0.hash] at this
    exact (Option.some.inj this).symm
  have es : rt.strtSize = rt0.strtSize := by
    have := hS.size; rw [hg] at this
    rw [show rd32 (fillZeroMem Mx) (rt0.g + gStrtSizeOff) = rd32 (fillZeroMem m) (rt0.g + gStrtSizeOff) from
      r (fun i hi => .inl (by simp only [Rng, gStrtSizeOff, gStrtHashOff]; omega))
        (by simp [gStrtSizeOff]; omega) (by simp only [gStrtSizeOff, gStrtHashOff] at hgh ⊢; omega), hS0.size] at this
    exact (Option.some.inj this).symm
  have en : rt.strtNuse = rt0.strtNuse := by
    have := hS.nuse; rw [hg] at this
    rw [show rd32 (fillZeroMem Mx) (rt0.g + gStrtNuseOff) = rd32 (fillZeroMem m) (rt0.g + gStrtNuseOff) from
      r (fun i hi => .inl (by simp only [Rng, gStrtNuseOff, gStrtHashOff]; omega))
        (by simp [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff, gStrtHashOff] at hgh ⊢; omega), hS0.nuse] at this
    exact (Option.some.inj this).symm
  have el : rt.strtHeads.length = rt0.strtHeads.length := by rw [hS.heads_len, hS0.heads_len, es]
  refine ⟨hg, eh, es, en, el, fun h1 h2 => ?_⟩
  have hjs : j < rt0.strtSize := by rw [← hS0.heads_len]; exact h2
  have := hS.bucket j h1
  rw [eh, show rd64 (fillZeroMem Mx) (rt0.strtHash + 8 * j) = rd64 (fillZeroMem m) (rt0.strtHash + 8 * j) from
    r (fun i hi => .inr (by simp only [Rng]; omega)) (by omega) (by omega), hS0.bucket j h2] at this
  exact (Option.some.inj this).symm

/-- **The facts again at a memory agreeing with the new one on the old
footprint and the insertion's** (`InsFoot`): the table re-read at the memory
`Mx` patched with the old table words is `rt0`'s there, so the literals hold
at `Mx` (frozen) and at the new table (`LitsIn.insert`); the safety too. -/
theorem ins_core (hL0 : LitsIn m g sl ls rt0) (hjd : h.toNat % rt0.strtSize = j) (hjl : j < rt0.strtHeads.length)
    (hgb : 0x80000000 ≤ g ∧ g + 1400 ≤ 0x87800000)
    (hFL : Frozen FL (fun M => LitsHold M g sl ls) m)
    (hNO : NewObjT m' g (rt0.strtHash + 8 * j) p rt0.strtNuse rt0.strtHeads[j] b h (bytesT1 m (g + gCurrentwhiteOff)))
    (hk : ∀ a, FL a → ¬ TabWr rt0 j a → bytesT1 m' a = bytesT1 m a)
    (hkg : ∀ a, (Rng (g + gStrtHashOff) 16 a ∨ Rng (g + gCurrentwhiteOff) 1 a) → ¬ TabWr rt0 j a →
      bytesT1 m' a = bytesT1 m a)
    (hok : InsOk rt0 ls K' X W b p) {M2 : Mem}
    (hM2 : ∀ a, (FL a ∨ InsFoot rt0 j p b.length a) → bytesT1 M2 a = bytesT1 m' a) :
    ∃ rt, LitsIn (patchL M2 m (twList rt0 j)) g sl ls rt ∧ SameTab rt rt0 j ∧ LitsIn M2 g sl ls (rt.ins j p) ∧
      (∀ a, ¬ TabWr rt j a → (fillZeroMem M2)[a]? = (fillZeroMem (patchL M2 m (twList rt0 j)))[a]?) ∧
      NewStr (fillZeroMem M2) rt ls (bytesT1 m (g + gCurrentwhiteOff)).toNat b h p j := by
  have hS0 := hL0.nil.strt
  have hg0 := hL0.g
  have hjs : j < rt0.strtSize := by rw [← hS0.heads_len]; exact hjl
  have hhl := hL0.hash_lo; have hhh := hL0.hash_hi; have hsz := hL0.size_hi
  have hap := hok.apart.kg
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hHE : symHeapEnd = 0x87800000 := rfl
  have hc : tstringContentsOff = 24 := rfl
  have hp1 := hok.p_lo; have hp2 := hok.p_hi; have hl40 := hok.short
  have hml : maxShortLen = 40 := rfl
  rw [hTH] at hp1 hhl; rw [hHE] at hp2 hhh
  -- the patched memory agrees with `m` on the old footprint
  have hMx : ∀ a, FL a → bytesT1 (patchL M2 m (twList rt0 j)) a = bytesT1 m a := by
    intro a ha
    rw [patchL_bT1]
    split
    · rfl
    · rename_i hn
      exact (hM2 a (.inl ha)).trans (hk a ha fun hw => hn (mem_twList.mpr hw))
  obtain ⟨rt, hLx⟩ := hFL _ hMx
  have hSx := hLx.nil.strt
  have hgx : rt.g = rt0.g := hLx.g.trans hg0.symm
  have hsame : SameTab rt rt0 j := sameTab_of hSx hS0 hgx hjl (fun a ha => by
      rw [patchL_bT1]
      split
      · rfl
      · rename_i hn
        rcases ha with ha | ha
        · rw [hg0] at ha
          exact (hM2 a (.inr (.inr (.inr (.inl (by rw [hg0]; exact ha)))))).trans
            (hkg a (.inl ha) fun hw => hn (mem_twList.mpr hw))
        · exact absurd (mem_twList.mpr (.inl ha)) hn)
    (by rw [hg0]; simp only [gStrtHashOff]; omega) (by rw [hg0]; omega) (by omega) (by omega)
  have hTW : TabWr rt j = TabWr rt0 j := TabWr.same hsame
  have hTb : TabW rt = TabW rt0 := TabW.same hsame
  -- the agreement off the written words
  have hA : ∀ a, ¬ TabWr rt j a → (fillZeroMem M2)[a]? = (fillZeroMem (patchL M2 m (twList rt0 j)))[a]? := by
    intro a ha
    rw [hTW] at ha
    rw [fillZeroMem_get, fillZeroMem_get, patchL_get, if_neg fun hm => ha (mem_twList.mp hm)]
  -- the new string at `M2`
  have kO : ∀ a, (p ≤ a ∧ a < p + tstringContentsOff + b.length + 1) → bytesT1 M2 a = bytesT1 m' a :=
    fun a ha => hM2 a (.inr (.inr (.inl ha)))
  have kW : ∀ a, TabWr rt0 j a → bytesT1 M2 a = bytesT1 m' a := fun a ha => hM2 a (.inr (.inl ha))
  have r8 : ∀ o, o < tstringContentsOff + b.length + 1 → rd8 (fillZeroMem M2) (p + o) = some (bytesT1 m' (p + o)).toNat :=
    fun o ho => by rw [rd8_fill (by omega) (by omega), kO _ ⟨by omega, by omega⟩]
  have hhead := hS0.bucket j hjl
  have hheadl := rd64_lt hhead
  have hn : NewStr (fillZeroMem M2) rt ls (bytesT1 m (g + gCurrentwhiteOff)).toNat b h p j := {
    p0 := hok.p0, p_lo := by rw [hTH]; exact hp1, p_hi := by rw [hHE]; exact hp2
    tt := by rw [show p + gcTtOff = p + 8 from rfl, r8 8 (by omega), hNO.tt]; rfl
    len := by
      rw [show p + tstringShrlenOff = p + 11 from rfl, r8 11 (by omega), hNO.len]
      simp only [BitVec.toNat_ofNat]; congr 1; omega
    short := hl40
    hash := by
      rw [show p + tstringHashOff = p + 12 from rfl, rd32_fill M2 (by omega) (by omega),
        bytesT4_congrT fun i _ => kO _ ⟨by omega, by omega⟩, hNO.hash]
      rfl
    j_def := by rw [hsame.size]; exact hjd
    j_lt := by rw [hsame.len]; exact hjl
    hnext := by
      rw [show p + tstringLnglenOff = p + 16 from rfl, rd64_fill M2 (by omega) (by omega),
        bytesT8_congrT fun i _ => kO _ ⟨by omega, by omega⟩, hNO.hnext, hsame.head (by rw [hsame.len]; exact hjl) hjl]
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hheadl]
    bytes := fun i hi => by
      rw [fill_get M2 (by omega) (by omega), kO _ ⟨by omega, by omega⟩,
        show p + tstringContentsOff + i = p + 24 + i from rfl, hNO.bytes i hi, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hi, Option.getD_some]
    nul := by
      rw [fill_get M2 (by omega) (by omega), kO _ ⟨by omega, by omega⟩,
        show p + tstringContentsOff + b.length = p + 24 + b.length from rfl, hNO.nul]
      rfl
    mark := ⟨(bytesT1 m (g + gCurrentwhiteOff) &&& 0x18#8).toNat, by
        rw [show p + gcMarkedOff = p + 9 from rfl, r8 9 (by omega), hNO.mark], white_alive _⟩
    off := by rw [hTb]; exact hok.off
    lits := hok.lits, nlit := hok.nlit
    bucket := by
      rw [hsame.hash, rd64_fill M2 (by omega) (by omega), bytesT8_congrT fun i _ => kW _ (.inl ⟨by omega, by omega⟩),
        hNO.bucket]
      simp only [BitVec.toNat_ofNat]; congr 1; omega
    nuse := by
      rw [hgx, hg0, rd32_fill M2 (by simp [gStrtNuseOff]; omega) (by simp [gStrtNuseOff]; omega),
        bytesT4_congrT fun i _ => kW _ (.inr (.inl ⟨by rw [hg0]; omega, by rw [hg0]; omega⟩)), hsame.nuse, hNO.nuse]
      simp only [BitVec.toNat_ofNat]
      have := hok.nuse_lt; have := hS0.nuse_le
      congr 1; omega
    nuse_lt := by rw [hsame.nuse, hsame.size]; exact hok.nuse_lt }
  have hcw : rd8 (fillZeroMem (patchL M2 m (twList rt0 j))) (rt.g + gCurrentwhiteOff) =
      some (bytesT1 m (g + gCurrentwhiteOff)).toNat := by
    rw [hgx, hg0, rd8_fill (by simp [gCurrentwhiteOff]; omega) (by simp [gCurrentwhiteOff]; omega), patchL_bT1]
    split
    · rfl
    · rename_i hnm
      rw [hM2 _ (.inr (.inr (.inr (.inr (by rw [hg0]; exact ⟨Nat.le_refl _, by omega⟩))))),
        hkg _ (.inr ⟨Nat.le_refl _, by omega⟩) fun hw => hnm (mem_twList.mpr hw)]
  exact ⟨rt, hLx, hsame, hLx.insert hA ⟨by rw [hsame.hash, hsame.size, hsame.g]; exact hok.apart.kg⟩ hn hcw,
    hA, hn⟩

/-- **The literals' facts and the table's safety, frozen again after a new
string**, on the old footprint with the insertion's (`InsFoot`). -/
theorem frozen_insert (hL0 : LitsIn m g sl ls rt0) (hjd : h.toNat % rt0.strtSize = j)
    (hjl : j < rt0.strtHeads.length) (hgb : 0x80000000 ≤ g ∧ g + 1400 ≤ 0x87800000)
    (hFL : Frozen FL (fun M => LitsHold M g sl ls) m)
    (hFS : Frozen FL (fun M => ∀ rt, LitsIn M g sl ls rt → StrtSafe (fillZeroMem M) rt K X W) m)
    (hNO : NewObjT m' g (rt0.strtHash + 8 * j) p rt0.strtNuse rt0.strtHeads[j] b h (bytesT1 m (g + gCurrentwhiteOff)))
    (hk : ∀ a, FL a → ¬ TabWr rt0 j a → bytesT1 m' a = bytesT1 m a)
    (hkg : ∀ a, (Rng (g + gStrtHashOff) 16 a ∨ Rng (g + gCurrentwhiteOff) 1 a) → ¬ TabWr rt0 j a →
      bytesT1 m' a = bytesT1 m a)
    (hok : InsOk rt0 ls K' X W b p) (hKK : ∀ a, K a → K' a) :
    Frozen (fun a => FL a ∨ InsFoot rt0 j p b.length a) (fun M => LitsHold M g sl ls) m' ∧
    Frozen (fun a => FL a ∨ InsFoot rt0 j p b.length a)
      (fun M => ∀ rt, LitsIn M g sl ls rt → StrtSafe (fillZeroMem M) rt K' X W) m' := by
  refine ⟨fun M2 hM2 => ?_, fun M2 hM2 rt2 hL2 => ?_⟩
  · obtain ⟨rt, -, -, hL, -⟩ := ins_core hL0 hjd hjl hgb hFL hNO hk hkg hok hM2
    exact ⟨_, hL⟩
  · have hMx : ∀ a, FL a → bytesT1 (patchL M2 m (twList rt0 j)) a = bytesT1 m a := by
      intro a ha
      rw [patchL_bT1]
      split
      · rfl
      · rename_i hn
        exact (hM2 a (.inl ha)).trans (hk a ha fun hw => hn (mem_twList.mpr hw))
    obtain ⟨rt, hLx, hsame, hL, hA, hn⟩ := ins_core hL0 hjd hjl hgb hFL hNO hk hkg hok hM2
    have hSS := hFS _ hMx rt hLx
    have hjs : j < rt.strtSize := by rw [hsame.size, ← hL0.nil.strt.heads_len]; exact hjl
    have hTb : TabW rt = TabW rt0 := TabW.same hsame
    have h1 := hSS.insert hLx.nil.strt hLx.off hA hn hKK hok.inK hok.mark hok.hnext
    have e := Lua.Vm.Boot.strtAt_same hL.nil.strt hL2.nil.strt (hL2.g.trans hL.g.symm)
    exact h1.congr_rt e

end Frz

/-! ## Why a new string's header joins the literals' footprint -/

/-- **A frozen footprint of the literals' facts holds every bucket head's tag
byte** (lane F1-20): a memory differing from `M` only at a nonzero head's
`tt` has that bucket's chain start at a node of the wrong tag, so no table
reading satisfies `LitsIn` there. So after `internshrstr` links a new string
`p` at its bucket's head, every footprint on which the literals' facts are
frozen (`PrSt.lits`, `LitsFoot.facts`) contains `p + gcTtOff`, which
`LitsFoot.apart` must keep off the dirty set `D`: `TolInt_Statement`
(`TolArg`, for every `D`) needs `D` off the new string's header. -/
theorem frozen_lits_head_tt {M : Mem} {F : Nat → Prop} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs}
    (hF : Frozen F (fun M => LitsHold M g sl ls) M) (hL : LitsIn M g sl ls rt) {j : Nat}
    (hj : j < rt.strtHeads.length) (hp : rt.strtHeads[j] ≠ 0) : F (rt.strtHeads[j] + gcTtOff) := by
  have hS := hL.nil.strt
  obtain ⟨cw, -, hch⟩ := hL.off.white
  have hc0 := hch j hj
  have hbk := hS.bucket j hj
  generalize hpj : rt.strtHeads[j] = p at hp hc0 hbk ⊢
  refine Classical.byContradiction fun hc => ?_
  have hA : ∀ a, ¬ a = p + gcTtOff →
      (fillZeroMem (M.insert (p + gcTtOff) 0#8))[a]? = (fillZeroMem M)[a]? := by
    intro a ha
    have : ¬ p + gcTtOff = a := fun e => ha e.symm
    simp [fillZeroMem_get, Std.ExtHashMap.getElem?_insert, this]
  have hag : ∀ a, F a → bytesT1 (M.insert (p + gcTtOff) 0#8) a = bytesT1 M a := fun a ha => by
    have hne : ¬ p + gcTtOff = a := fun e => hc (e ▸ ha)
    simp [bytesT1, Std.ExtHashMap.getElem?_insert, hne]
  obtain ⟨rt', hL'⟩ := hF _ hag
  have hS' := hL'.nil.strt
  -- the head's object is off the table's words
  have hoff : ¬ TabW rt (p + gcTtOff) := by
    cases hc0 with
    | nil => exact absurd rfl hp
    | cons _ _ _ hT _ _ => exact hT _ (by simp [gcTtOff]) (by simp [gcTtOff, tstringContentsOff]; omega)
  have hW : ∀ a, (rt.g ≤ a ∧ a < rt.g + 64) ∨ (rt.strtHash ≤ a ∧ a < rt.strtHash + 8 * rt.strtSize) →
      ¬ a = p + gcTtOff := fun a ha he => hoff (by
    subst he
    simp only [TabW, gStrcacheOff, strcacheN, strcacheM] at ha ⊢
    omega)
  have eg : rt'.g = rt.g := hL'.g.trans hL.g.symm
  have rd : ∀ {a n : Nat}, (∀ i, i < n → (rt.g ≤ a + i ∧ a + i < rt.g + 64) ∨
      (rt.strtHash ≤ a + i ∧ a + i < rt.strtHash + 8 * rt.strtSize)) →
      rdLE (fillZeroMem (M.insert (p + gcTtOff) 0#8)) a n = rdLE (fillZeroMem M) a n :=
    fun {a n} h => rdLE_off hA fun i hi => hW _ (h i hi)
  have ehash : rt'.strtHash = rt.strtHash := by
    have h1 := hS'.hash
    rw [eg, show rd64 (fillZeroMem (M.insert (p + gcTtOff) 0#8)) (rt.g + gStrtHashOff) =
      rd64 (fillZeroMem M) (rt.g + gStrtHashOff) from rd fun i hi => .inl ⟨by simp only [gStrtHashOff]; omega,
        by simp only [gStrtHashOff]; omega⟩, hS.hash] at h1
    exact (Option.some.inj h1).symm
  have esize : rt'.strtSize = rt.strtSize := by
    have h1 := hS'.size
    rw [eg, show rd32 (fillZeroMem (M.insert (p + gcTtOff) 0#8)) (rt.g + gStrtSizeOff) =
      rd32 (fillZeroMem M) (rt.g + gStrtSizeOff) from rd fun i hi => .inl ⟨by simp only [gStrtSizeOff]; omega,
        by simp only [gStrtSizeOff]; omega⟩, hS.size] at h1
    exact (Option.some.inj h1).symm
  have hj' : j < rt'.strtHeads.length := by rw [hS'.heads_len, esize, ← hS.heads_len]; exact hj
  have ehead : rt'.strtHeads[j] = p := by
    have h1 := hS'.bucket j hj'
    rw [ehash, show rd64 (fillZeroMem (M.insert (p + gcTtOff) 0#8)) (rt.strtHash + 8 * j) =
      rd64 (fillZeroMem M) (rt.strtHash + 8 * j) from rd fun i hi => .inr ⟨by omega, by
        have := hS.heads_len; omega⟩, hbk] at h1
    exact (Option.some.inj h1).symm
  have hch' := hS'.chain j hj'
  generalize rt'.strtHeads[j] = q at hch' ehead
  subst ehead
  cases hch' with
  | nil => exact hp rfl
  | cons _ htt _ _ _ _ =>
    have h0 : (fillZeroMem (M.insert (q + gcTtOff) 0#8))[q + gcTtOff]? = some 0#8 :=
      fillZeroMem_some (by simp)
    simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero, h0] at htt
    simp [gcShrStr] at htt

end Lua.Vm.Sim.Kit

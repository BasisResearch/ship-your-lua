import Lua.Vm.Sim.Kit.TolInt
import Lua.Vm.Sim.Kit.TolStrProof
import Lua.Vm.Sim.Kit.LitsInsert
import Lua.Vm.Sim.Kit.IntFmtLoop
import Lua.Vm.Sim.Kit.AllocProof

/-!
# `TolInt_Statement` (lane F1-23)

`luaL_tolstring` on an integer argument in `luaB_print`'s loop (`TolArg
IsInt`), from the machine run `tolint_sum` (lane F1-20, `Kit/TolInt.lean`) and
`luaB_print`'s entry facts (`PrintIn`) and state (`PrSt`):

* the run's inputs: `TolIIn` from the state (`tolI_in`), and `luaS_newlstr`'s
  table (`NlTab`, `tolI_tab`): the chains' walk from the table's safety
  (`PrSt.safe`) and the literals' chains (`StrtOff`) by `kwalk_of`, read at any
  memory agreeing below the stack (`KWalk.congr`);
* its outcome: a string found (`PfHit`: the state with one more value, as a
  literal's push leaves it) or created (`IaNewPost`: the literals' facts and
  the table's safety re-frozen on the footprint with the insertion's,
  `frozen_insert`; the footprint stays apart from `D` by `PrintIn`'s upper
  bound on it, `dirty_in`/`dirty_g`, and `LitsFoot.tab`; the heap's new
  chunk in `stdout`'s state by `StdoutIn.congrA`).

The bytes it writes are `TiW`'s; every fact the state carries is read off them.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The digits and the literals -/

/-- The bytes `%lld` prints are `-` or digits: below `64`. -/
theorem intBytes_lt64 (x : BitVec 64) : ∀ c ∈ intBytes x, c.toNat < 64 := by
  intro c hc
  rw [intBytes_eq] at hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · split at hc
    · simp only [List.mem_singleton] at hc; subst hc; decide
    · simp at hc
  · simp only [decBytes, List.mem_map] at hc
    obtain ⟨ch, hch, rfl⟩ := hc
    have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h2 : ch.val.toNat ≤ 57 := by
      have := hd.2
      rw [UInt32.le_iff_toNat_le] at this
      simpa using this
    simp only [BitVec.toNat_ofNat, Char.toNat]
    omega

/-- The digits' first byte, below `64`. -/
theorem intU8_head_lt (x : BitVec 64) : ((intU8 x).getD 0 0).toNat < 64 := by
  have hl := (intBytes_len x).1
  have h := intU8_get x 0 (by omega)
  have hlt := intBytes_lt64 x ((intBytes x)[0]'(by omega)) (List.getElem_mem _)
  rw [← h, BitVec.toNat_ofNat] at hlt
  have := UInt8.toNat_lt ((intU8 x).getD 0 0)
  omega

/-- **No literal is the digits**: their first bytes differ (a letter or `_`
against a digit or `-`). -/
theorem lits_ne_intU8 (ls : LitPtrs) (x : BitVec 64) : ∀ l ∈ ls.table, l.bytes ≠ intU8 x := by
  intro l hl he
  have h := intU8_head_lt x
  rw [← he] at h
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> dsimp only at h <;> revert h <;> decide

/-- A literal's first content byte is at least `64`. -/
theorem lit_head_ge {M : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (hL : LitsIn M g sl ls rt) :
    ∀ ts ∈ ls.strs, 64 ≤ (bytesT1 M (ts + 24)).toNat := by
  have key : ∀ {seed b ts}, LitInterned M rt seed b ts → 64 ≤ (b.getD 0 0).toNat →
      0 < b.length → 64 ≤ (bytesT1 M (ts + 24)).toNat := fun {seed b ts} hl hb h0 => by
    have e := hl.repr.bytes.1 0 h0
    rw [Nat.add_zero, show ts + tstringContentsOff = ts + 24 from rfl] at e
    have e2 : bytesT1 M (ts + 24) = BitVec.ofNat 8 (b[0]'h0).toNat := by
      rw [← bytesT1_fill]; simp only [bytesT1, e, Option.getD_some]
    rw [e2, BitVec.toNat_ofNat]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h0, Option.getD_some] at hb
    have := UInt8.toNat_lt (b[0]'h0)
    omega
  intro ts hts
  simp only [LitPtrs.strs, List.mem_cons, List.not_mem_nil, or_false] at hts
  rcases hts with rfl | rfl | rfl | rfl
  · exact key hL.nil (by decide) (by decide)
  · exact key hL.tru (by decide) (by decide)
  · exact key hL.fls (by decide) (by decide)
  · exact key hL.tos (by decide) (by decide)

/-- **No literal's object holds the digits** (`kwalk_of`'s `hnl`). -/
theorem lits_nomatch {M : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (hL : LitsIn M g sl ls rt)
    (x : BitVec 64) : ∀ p ∈ ls.strs, bytesT1 M (p + 11) = BitVec.ofNat 8 (intU8 x).length →
      (∀ i, i < (intU8 x).length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 ((intU8 x).getD i 0).toNat) → False := by
  intro p hp _ hb
  have hl := (intBytes_len x).1
  have e := hb 0 (by rw [intU8_length]; omega)
  have h1 := lit_head_ge hL p hp
  have h2 := intU8_head_lt x
  rw [Nat.add_zero, e, BitVec.toNat_ofNat] at h1
  omega

/-! ## The walk at a memory agreeing below the stack -/

/-- **`internshrstr`'s walk across a change above the arena**: every byte it
reads is a node's, in `K`, below the stack. -/
theorem KWalk.congr {M M' : Mem} {b : List UInt8} {cw : BitVec 8} {K X W : Nat → Prop} (hbl : b.length < 256)
    (hK : ∀ a, K a → a < 0x87800000) (hk : ∀ a, a < 0x87800000 → bytesT1 M' a = bytesT1 M a) {d p : Nat}
    (h : KWalk M b cw (IaNode M K X W) d p) : KWalk M' b cw (IaNode M' K X W) d p := by
  induction h with
  | nil => exact .nil
  | @cons d p nx h0 h1 h2 hP hnx hlt hm _ ih =>
    have k8 := hK _ (hP.obj (p + 8) (by omega) (by omega)).1
    have k11 := hK _ (hP.obj (p + 11) (by omega) (by omega)).1
    have e11 : bytesT1 M' (p + 11) = bytesT1 M (p + 11) := hk _ k11
    have kin : ∀ a, p ≤ a → a < p + 24 + (bytesT1 M (p + 11)).toNat + 1 → bytesT1 M' a = bytesT1 M a :=
      fun a l u => hk _ (hK _ (hP.obj a l u).1)
    have hP' : IaNode M' K X W p :=
      ⟨(hk _ k8).trans hP.tt, fun a l u => hP.obj a l (by rw [← e11]; exact u), hP.mark, hP.hnext⟩
    refine .cons h0 h1 h2 hP' ((bytesT8_congrT fun j _ => kin _ (by omega) (by omega)).trans hnx) hlt
      (fun hl => ?_) ih
    rw [e11] at hl
    obtain ⟨hb, ha⟩ := hm hl
    have hl8 : (bytesT1 M (p + 11)).toNat = b.length := by rw [hl, BitVec.toNat_ofNat]; omega
    refine ⟨hb, fun hc => ?_⟩
    have hA := ha fun j hj => (kin _ (by omega) (by omega)).symm.trans (hc j hj)
    simp only [AliveB] at hA ⊢
    rw [kin _ (by omega) (by omega)]; exact hA

/-- `IaTab` at a memory agreeing below the stack. -/
theorem IaTab.congr {M M' : Mem} {g : Nat} {H : UInt32} {b : List UInt8} {cw : BitVec 8} {K X W : Nat → Prop}
    {size hash head d : Nat} (h : IaTab M g H b cw (IaNode M K X W) size hash head d) (hbl : b.length < 256)
    (hK : ∀ a, K a → a < 0x87800000) (hg : g + 64 ≤ 0x87800000)
    (hk : ∀ a, a < 0x87800000 → bytesT1 M' a = bytesT1 M a) :
    IaTab M' g H b cw (IaNode M' K X W) size hash head d := by
  have hh := h.hash_hi
  have hm : H.toNat % size < size := Nat.mod_lt _ h.size_pos
  exact ⟨(bytesT4_congrT fun j _ => hk _ (by omega)).trans h.size_w,
    (bytesT8_congrT fun j _ => hk _ (by omega)).trans h.hash_w, h.size_pos, h.size_hi, h.size_pow2, h.hash_lo,
    h.hash_hi, (bytesT8_congrT fun j _ => hk _ (by omega)).trans h.head_w, h.head_lt, h.walk.congr hbl hK hk⟩

/-! ## The run's inputs at `luaB_print`'s state -/

/-- A represented integer's tag and payload. -/
theorem _root_.Lua.Vm.Sim.ValRepr.int_inv {mo : Mem} {ι : Strs} {t : BitVec 8} {v x : BitVec 64}
    (h : ValRepr mo ι t v (.int x)) : t = BitVec.ofNat 8 vNumInt ∧ v = x := by
  cases h; exact ⟨rfl, rfl⟩

/-- An integer argument makes a string (`prAllocs` counts it). -/
theorem prAllocs_int_pos {args : List Value} {i : Nat} {x : BitVec 64} (hi : 1 ≤ i)
    (hv : args[i - 1]? = some (.int x)) : 0 < prAllocs args i := by
  rw [prAllocs_succ hi hv]; simp [argCost]; omega

/-- An integer argument's break room (`prCost` counts it). -/
theorem prCost_int {args : List Value} {i : Nat} {x : BitVec 64} (hi : 1 ≤ i)
    (hv : args[i - 1]? = some (.int x)) : prCost args i = 16384 + 4096 + 128 + prCost args (i + 1) := by
  rw [prCost_succ hi hv]; rfl

/-- **`luaL_tolstring`'s entry facts on an integer argument** (`TolIIn`), at
`luaB_print`'s state before argument `i`. -/
theorem tolI_in {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {i : Nat} {r x : BitVec 64}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hv : args[i - 1]? = some (.int x))
    (hi1 : 1 ≤ i) (hin : i ≤ n) (hr : r.toNat % 4 = 0) :
    TolIIn m (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g x r := by
  have q := hn.ok
  have q1 := q.sp_lo; have q2 := q.sp_hi; have q3 := q.sp_al; have q4 := q.L_al; have q5 := q.L_lo
  have q6 := hn.sp_big; have q7 := hn.n_small; have q8 := hn.nci_lo; have q9 := hn.f_lo
  have hp := hIn.placed
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  have hga := hIn.g_al; have hfa := hIn.f_al
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM, hHE, hHS] at p1 p2 p3 p4 p5 p6 p7 p8 p9
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM, hHE, hHS] at p10 p11 p12 p13 p14 q1 q6
  have hpos := prAllocs_int_pos hi1 hv
  have hA : ArgsAt func ι args m := hIn.args_fz m fun a ha =>
    hS.keep a (ha.elim (fun h => .inl h) fun h => .inr (.inl h))
  have hidx : func + 16 * (i - 1 + 1) = func + 16 * i := by congr 1; omega
  have hR := hA (i - 1) (.int x) hv
  rw [hidx] at hR
  obtain ⟨htag, hval⟩ := hR.int_inv
  have kG : ∀ a, Rng (L + stateGOff) 8 a → bytesT1 m a = bytesT1 M0 a := fun a h =>
    hS.keep a (.inr (.inr (.inr (.inr (.inr (.inl h))))))
  have kM : ∀ a, Rng (g + gMtOff) 32 a → bytesT1 m a = bytesT1 M0 a := fun a h =>
    hS.keep a (.inr (.inr (.inr (.inr (.inl h)))))
  have hapi := hS.api
  exact {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := hr, L_lo := q5, L_al := q4
    L_he := by omega, i_lo := hi1, i_hi := by omega, l_lo := by omega, l_hi := by omega, l_al := by omega
    ci_lo := q8, ci_he := by omega, f_lo := q9, f_top := by omega, t_lo := by omega, t_hi := by omega
    t_al := by omega, g_lo := by omega, g_hi := by omega, g_al := hga, tL := by omega, tg := by omega
    Lg := by omega, ci_w := hapi.ci_w, func_w := hapi.func_w, top_w := hapi.top_w
    g_w := (bytesT8_congrT fun j _ => kG _ (by simp only [Rng, stateGOff]; omega)).trans hIn.g_w
    tag_w := by
      rw [show 16 * i + func + 8 = func + 16 * i + tvalueTagOff by simp only [tvalueTagOff]; omega]
      exact htag
    val_w := by
      rw [show 16 * i + func = func + 16 * i + tvalueValOff by simp only [tvalueValOff]; omega]
      exact hval
    mt_w := by
      have := hIn.mt luaTnumber (by simp)
      rw [show g + 504 = g + gMtOff + 8 * luaTnumber by simp only [gMtOff, luaTnumber]]
      exact (bytesT8_congrT fun j _ => kM _ (by simp only [Rng, gMtOff, luaTnumber]; omega)).trans this
    rod := fun o ho => (hS.keep _ (.inr (.inr (.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ho _⟩)))).trans
      (hIn.ro o ho)
    stat := (hS.stat hpos).fmt
    gcstp := (hS.keep _ (.inr (.inr (.inr (.inl ⟨Nat.le_refl _, Nat.lt_succ_self _⟩))))).trans hIn.gcstp }

/-- **`luaS_newlstr`'s table at `luaB_print`'s state** (`NlTab`): the chains
of the literals' reading of `g->strt` (`rt0`) walked by `kwalk_of` (their
safety `PrSt.safe`, the literals' chains `StrtOff`, no literal the digits),
at any memory agreeing below the stack (`IaTab.congr`); the creation path's
inputs from the state's budget (`PrSt.room`, `PrSt.strt`) and static words
(`PrSt.stat`). -/
theorem tolI_tab {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {i : Nat} {x : BitVec 64}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hv : args[i - 1]? = some (.int x)) (hi1 : 1 ≤ i) {rt0 : RtPtrs} (hL : LitsIn m g sl ls rt0) {j : Nat}
    (hjd : (luaHash ls.seed (intU8 x)).toNat % rt0.strtSize = j) (hj : j < rt0.strtHeads.length) :
    ∃ d, NlTab m L g (func + 16 * n + 16) (intU8 x) ls.seed (Kept H ph)
      (fun a => PrX L nci g func n sl G a ∨ B a) (fun a => B a ∨ D a) (bytesT1 m (g + 100)) rt0.strtSize rt0.strtHash
      rt0.strtHeads[j] d rt0.strtNuse H := by
  have q := hn.ok
  have q4 := q.L_al; have q5 := q.L_lo; have q8 := hn.nci_lo; have q9 := hn.f_lo
  have hp := hIn.placed
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM, hHE, hHS] at p1 p2 p3 p4 p5 p6 p7 p8 p9
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM, hHE, hHS] at p10 p11 p12 p13 p14
  have hpos := prAllocs_int_pos hi1 hv
  have hS0 := hL.nil.strt
  have hg := hL.g
  have hSS : StrtSafe (fillZeroMem m) rt0 (Kept H ph) (fun a => PrX L nci g func n sl G a ∨ B a) (fun a => B a ∨ D a) :=
    hS.safe.self rt0 hL
  obtain ⟨cw, hcw, hch⟩ := hL.off.white
  have hcwL : cw < 256 := (rdLE_spec 1 _ _ _ hcw).1
  have hcwB : bytesT1 m (g + 100) = BitVec.ofNat 8 cw :=
    bT1_of_rd8_fill (by rw [hg] at hcw; exact hcw) (by omega) (by omega)
  have hK : ∀ a, Kept H ph a → 0x8006ecd0 ≤ a ∧ a < 0x87800000 := fun a ha => ⟨ha.lo, ha.hi⟩
  have hb40 : (intU8 x).length ≤ 40 := by rw [intU8_length]; have := (intBytes_len x).2; omega
  obtain ⟨d, hw⟩ := kwalk_of hK (lits_nomatch hL x) hb40 hcwL (hSS.chains j hj) (hch j hj)
  rw [← hcwB] at hw
  have hsz := hS0.size_pos
  have hjs : j < rt0.strtSize := by rw [← hS0.heads_len]; exact hj
  have hh1 := hL.hash_lo; have hh2 := hL.hash_hi; have hh3 := hL.size_hi
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hSH : symHeapEnd = 0x87800000 := rfl
  rw [hTH] at hh1; rw [hSH] at hh2
  -- the bucket's word: in a chunk in use, apart from `L`, `g`
  have hbk : ∀ a, rt0.strtHash + 8 * j ≤ a → a < rt0.strtHash + 8 * j + 8 →
      Kept H ph a ∧ ¬ (PrX L nci g func n sl G a ∨ B a) := fun a h1 h2 => by
    have := hSS.hash a (by omega) (by omega); exact ⟨this.1, this.2.1⟩
  have b0 := hbk (rt0.strtHash + 8 * j) (by omega) (by omega)
  have b7 := hbk (rt0.strtHash + 8 * j + 7) (by omega) (by omega)
  have hbL : rt0.strtHash + 8 * j + 8 ≤ L ∨ L + 200 ≤ rt0.strtHash + 8 * j := by
    have x0 := b0.2; have x7 := b7.2
    simp only [PrX, Rng, stateSize, not_or, not_and, Nat.not_lt] at x0 x7
    omega
  have hbg : rt0.strtHash + 8 * j + 8 ≤ g ∨ g + 1400 ≤ rt0.strtHash + 8 * j := by
    have x0 := b0.2; have x7 := b7.2
    simp only [PrX, Rng, gEnd, gStrcacheOff, strcacheN, strcacheM, not_or, not_and, Nat.not_lt] at x0 x7
    omega
  have hnuse : bytesT4 m (g + 56) = BitVec.ofNat 32 rt0.strtNuse := by
    have := hS0.nuse; rw [hg] at this; exact bT4_of_fill (bytesT4_of_rd32 this)
  have hsize : bytesT4 m (g + 60) = BitVec.ofNat 32 rt0.strtSize := by
    have := hS0.size; rw [hg] at this; exact bT4_of_fill (bytesT4_of_rd32 this)
  have hhash : bytesT8 m (g + 48) = BitVec.ofNat 64 rt0.strtHash := by
    have := hS0.hash; rw [hg] at this; exact bT8_of_fill (bytesT8_of_rd64 this)
  have hhead : bytesT8 m (rt0.strtHash + 8 * j) = BitVec.ofNat 64 rt0.strtHeads[j] :=
    bT8_of_fill (bytesT8_of_rd64 (hS0.bucket j hj))
  have hheadlt := rd64_lt (hS0.bucket j hj)
  have hgw : bytesT8 m (L + 24) = BitVec.ofNat 64 g :=
    (bytesT8_congrT fun j _ => hS.keep _ (.inr (.inr (.inr (.inr (.inr (.inl
      (by simp only [Rng, stateGOff]; omega)))))))).trans hIn.g_w
  have hroom := hS.room (by rw [prCost_int hi1 hv]; omega)
  rw [prCost_int hi1 hv] at hroom
  have hst := hS.strt hpos
  have hnl : rt0.strtNuse < rt0.strtSize := by
    have h1 := hS0.nuse_le
    have e1 : strtNuse m g = rt0.strtNuse := by
      simp only [strtNuse, gStrtNuseOff, hnuse, BitVec.toNat_ofNat]; omega
    have e2 : strtSize m g = rt0.strtSize := by
      simp only [strtSize, gStrtSizeOff, hsize, BitVec.toNat_ofNat]; omega
    rw [e1, e2] at hst
    omega
  have hT : IaTab m g (luaHash ls.seed (intU8 x)) (intU8 x) (bytesT1 m (g + 100))
      (IaNode m (Kept H ph) (fun a => PrX L nci g func n sl G a ∨ B a) (fun a => B a ∨ D a)) rt0.strtSize rt0.strtHash
      rt0.strtHeads[j] d := by
    refine ⟨hsize, hhash, hsz, hh3, hS0.size_pow2, hh1, hh2, ?_, hheadlt, hw⟩
    rw [hjd]; exact hhead
  refine ⟨d, {
    seed_w := ?_
    hK := hK
    xt := fun a ha => .inl (.inr (.inr (.inr (.inl ⟨by simp only [Rng] at ha; omega,
      by simp only [Rng] at ha; omega⟩))))
    xL := fun a ha => .inl (.inr (.inl ha))
    xg := fun a ha => .inl (.inr (.inr (.inl ha)))
    tab := fun M hM => ⟨hM _ (by omega), hT.congr (by omega) (fun a ha => (hK a ha).2) (by omega) hM⟩
    new := ?_
    top_in := fun a ha => (hS.kept (hIn.stack_in a (by simp only [Rng] at ha; omega)
      (by simp only [Rng] at ha; omega))).inuse
    Lk := by rw [hjd]; exact hbL }⟩
  · have := hL.nil.seed_w
    rw [hg] at this
    rw [show g + 96 = g + gSeedOff from rfl, bT4_of_fill (bytesT4_of_rd32 this)]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, UInt32.toNat_toBitVec]
    exact Nat.mod_eq_of_lt (UInt32.toNat_lt _)
  · rw [hjd]
    exact {
      bkt_lo := by omega, bkt_he := by omega, kg := hbg, k_al := by have := hL.off.hash_al; omega
      g_al := hIn.g_al, nuse_w := hnuse, nuse_lt := hnl, size_hi := hh3, head_w := hhead, head_lt := hheadlt
      heap := hP.heap, room := by omega
      frealloc := (hS.stat hpos).frealloc, impure := hP.cells.impure, Lg := hgw
      g_in := fun a h1 h2 => (hS.kept (hIn.g_in a h1
        (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))).inuse
      L_in := fun a h1 h2 => (hS.kept (hIn.L_in a h1 (by simp only [stateSize]; omega))).inuse
      k_in := fun a h1 h2 => (hbk a h1 h2).1.inuse }

end Lua.Vm.Sim.Kit

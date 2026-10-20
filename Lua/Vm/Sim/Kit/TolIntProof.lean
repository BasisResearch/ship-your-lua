import Lua.Vm.Sim.Kit.TolInt
import Lua.Vm.Sim.Kit.TolStrProof
import Lua.Vm.Sim.Kit.LitsInsert
import Lua.Vm.Sim.Kit.IntFmtLoop
import Lua.Vm.Sim.Kit.AllocProof
import Lua.Vm.Sim.Kit.ExtendCI

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

/-! ## Chunks in use (moved from `Kit/CallPrint.lean`, lane F1-23) -/

/-- A byte of a chunk in use is no byte `_malloc_r` writes. -/
theorem Kept.not_mallocW {H : HeapIx} {ph : StdoutPh} {a : Nat} (h : Kept H ph a) : ¬ MallocW H.chunks a := by
  rintro (hg | ⟨-, -, hu⟩)
  · have := h.lo
    have e0 : heapStart = symEnd := rfl
    have e1 : symEnd = 0x8006ecd0 := rfl
    have e4 : symMallocAv = 0x8005c6d0 := rfl
    have e5 : symMallocSbrkBase = 0x8005d388 := rfl
    have e6 : symBrk = 0x8005d3b8 := rfl
    have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
    have e9 : symMallocMallinfo = 0x8005e560 := rfl
    have e10 : errnoAddr = 0x8005d408 := rfl
    simp only [MallocGlobal] at hg
    omega
  · exact hu h.inuse

/-- `stdout`'s buffer lies in a chunk in use. -/
theorem StdoutIn.buf_inUse {m : Mem} {H : HeapIx} {ph : StdoutPh} {a : Nat} (h : StdoutIn m H ph)
    (hb : ph.Buf a) : InUse H.chunks a := by
  cases h with
  | boot => exact hb.elim
  | fresh => exact hb.elim
  | up _ _ ho _ =>
    obtain ⟨sz, hc, hsz⟩ := ho.block
    have hl := ho.lo
    simp only [StdoutPh.Buf, Rng] at hb
    exact ⟨_, hc, rfl, by dsimp only; omega, by dsimp only; omega⟩

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

/-! ## A string found -/

/-- (lane F1-23) **What an integer's `luaL_tolstring` writes, a string
found**: `g->totalbytes` and `g->GCdebt`, the pushed slot, `L->top`, the
callees' frames below `sp`, the length word `lw`. -/
def TiWH (g top L sp lw : Nat) (a : Nat) : Prop :=
  Rng (g + 16) 16 a ∨ Rng top 9 a ∨ Rng (L + 16) 8 a ∨ TolFr sp a ∨ Rng lw 8 a

/-- **A found string's run keeps every byte off `TiWH`.** -/
theorem ti_keepH {m M3 M : Mem} {sp L g top ts lw : Nat} {b : List UInt8} {K X W : Nat → Prop}
    {v : BitVec 64} (hh : PfHit m M3 (TolFr sp) K X W ts b) (hpost : PfPost M3 M (sp - 48) L g top ts)
    (hsp : 48 ≤ sp) : ∀ a, ¬ TiWH g top L sp lw a → bytesT1 (writeMap8 M lw (sdData_val v)) a = bytesT1 m a := by
  intro a ha
  simp only [TiWH, not_or] at ha
  obtain ⟨h1, h2, h3, h4, h5⟩ := ha
  rw [fw1_wm8 (by simp only [Rng] at h5; omega)]
  refine (hpost.keep a fun hw => ?_).trans (hh.keep a h4)
  rcases hw with hw | hw | hw | hw | hw
  · exact h2 hw
  · exact h3 hw
  · exact h1 (by simp only [Rng, gTotalbytesOff] at hw ⊢; omega)
  · exact h1 (by simp only [Rng, gGCdebtOff] at hw ⊢; omega)
  · exact h4 (by simp only [PfFr, TolFr] at hw ⊢; omega)

/-- A string's contents in the arena lie above `errno`. -/
theorem srcLo_of_heap {ts n : Nat} (h : heapStart ≤ ts) : SrcLo (ts + 24) n :=
  SrcLo.of_hi (by have : errnoAddr = 0x8005d408 := rfl; have : heapStart = 0x8006ecd0 := rfl; omega)

/-- A string's contents in the arena lie apart from `stdout`. -/
theorem srcOut_of_heap {s l : Nat} (h : heapStart ≤ s) : s + l ≤ stdoutFile ∨ stdoutFile + fileSize ≤ s :=
  .inr (by have : stdoutFile = 0x8005e668 := rfl; have : fileSize = 184 := rfl
           have : heapStart = 0x8006ecd0 := rfl; omega)

/-- The bytes an integer prints are `%lld`'s. -/
theorem argBytes_int (x : BitVec 64) : argBytes (.int x) = intBytes x := rfl

/-- **The digits at a memory**, from their bytes as `UInt8`s. -/
theorem bytesAt_intU8 {M : Mem} {s : Nat} {x : BitVec 64}
    (h : ∀ j, j < (intU8 x).length → bytesT1 M (s + j) = BitVec.ofNat 8 ((intU8 x).getD j 0).toNat) :
    bytesAt M s (intBytes x).length = intBytes x := by
  apply List.ext_getElem (by simp [bytesAt])
  intro j h1 h2
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [h j (by rw [intU8_length]; exact h2), intU8_get x j h2]

/-- (lane F1-23) **`TolPost` from an integer's `luaL_tolstring`, the string
found** (`PfHit`): as a literal's push leaves the state (`litKeeps_of`), the
budget of the arguments after `i` at most argument `i`'s (`PrSt.nextKeep`),
the string's bytes off what the push writes (`StrtSafe`'s `W` holds `D`). -/
theorem prIntHit {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m M3 M : Mem}
    {i ts : Nat} {x : BitVec 64}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hv : args[i - 1]? = some (.int x)) (hi1 : 1 ≤ i)
    (hh : PfHit m M3 (TolFr (sp0 - 64)) (Kept H ph) (fun a => PrX L nci g func n sl G a ∨ B a)
      (fun a => B a ∨ D a) ts (intU8 x))
    (hpost : PfPost M3 M (sp0 - 64 - 48) L g (func + 16 * n + 16) ts) :
    TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (argBytes (.int x)) ph m
      (writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 (intU8 x).length))) (ts + 24) H H := by
  have q := hn.ok
  have hp := hIn.placed
  have hp' := hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp'
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hl := hS.lits
  have hk := ti_keepH (lw := sp0 - 56) (v := BitVec.ofNat 64 (intU8 x).length) hh hpost (by homega)
  have hn1 := (intBytes_len x).1
  have hn2 := (intBytes_len x).2
  have hlx : (intU8 x).length = (intBytes x).length := intU8_length x
  have hlen8 : bytesT8 (writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 (intU8 x).length))) (sp0 - 56) =
      BitVec.ofNat 64 (intU8 x).length := fw8_same rfl
  have htop : bytesT8 (writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 (intU8 x).length))) (L + 16) =
      BitVec.ofNat 64 (func + 16 * n + 16 + 16) :=
    (bytesT8_congrT fun j _ => fw1_wm8 (by simp only [stateSize] at p2; homega)).trans hpost.top_w
  generalize writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 (intU8 x).length)) = m' at hk hlen8 htop ⊢
  -- the push's stores, as a literal's
  have kW : ∀ a, a < heapEnd + 32 → ¬ Rng (L + 16) 8 a → ¬ Rng (func + 16 * n + 16) 16 a →
      ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a → ¬ Rng (g + gTotalbytesOff) 8 a →
      ¬ Rng (g + gGCdebtOff) 8 a → ¬ Rng (ls.tos + gcMarkedOff) 1 a → bytesT1 m' a = bytesT1 m a :=
    fun a h0 h1 h2 _ h4 h5 _ => hk a fun hw => by
      simp only [TiWH, Rng, TolFr, gTotalbytesOff, gGCdebtOff, not_and, Nat.not_lt] at hw h1 h2 h4 h5
      omega
  have K := litKeeps_of hIn hn hS hP kW (by simp [LitPtrs.strs])
  have kFL := K.fl; have kT := K.strt; have kK := K.keep; have kA := K.api; have kP := K.io
  have hl' : LitsFoot g sl ls H ph D FL m' := hl.trans kFL (hl.cache.congr fun a h1 h2 => hk a fun hw => by
    simp only [TiWH, Rng, TolFr, gEnd, gStrcacheOff, strcacheN, strcacheM, stateSize] at hw h1 h2 p10 p12 p6
    have := hp.room
    omega)
  -- the string: in a chunk in use, off `D`
  have hnode := hh.node
  have hl8 : (bytesT1 m (ts + 11)).toNat = (intU8 x).length := by rw [hh.len, BitVec.toNat_ofNat]; omega
  have hobj : ∀ a, ts ≤ a → a < ts + 24 + (intU8 x).length + 1 → Kept H ph a ∧ ¬ D a := fun a h1 h2 => by
    have := hnode.obj a h1 (by rw [hl8]; exact h2)
    exact ⟨this.1, fun hd => this.2 (.inr hd)⟩
  have kObj : ∀ a, ts ≤ a → a < ts + 24 + (intU8 x).length + 1 → bytesT1 m' a = bytesT1 m a := by
    intro a h1 h2
    obtain ⟨hka, hda⟩ := hobj a h1 h2
    have hlo := hka.hi
    refine hk a fun hw => ?_
    rcases hw with hw | hw | hw | hw | hw
    · by_cases e : a < g + 24
      · exact hda (hIn.dirty a (.inr (.inr (.inl (by simp only [Rng, gTotalbytesOff] at hw ⊢; omega)))))
      · exact hda (hIn.dirty a (.inr (.inr (.inr (.inl (by simp only [Rng, gGCdebtOff] at hw ⊢; omega))))))
    · exact hda (hIn.dirty a (.inr (.inl (by simp only [Rng] at hw; have := hp.room; omega))))
    · exact hda (hIn.dirty a (.inl (by simpa only [stateTopOff] using hw)))
    · simp only [TolFr] at hw; homega
    · simp only [Rng] at hw; homega
  have hb : bytesAt m' (ts + 24) (intBytes x).length = intBytes x := bytesAt_intU8 fun j hj => by
    rw [show ts + 24 + j = ts + 24 + j from rfl, kObj _ (by omega) (by omega)]; exact hh.bytes j hj
  have hts := (hobj ts (Nat.le_refl _) (by omega)).1
  have hapi := hS.api
  refine
    { lua := ⟨FL, B, hS.nextKeep (by rw [prCost_int hi1 hv]; omega) (by rw [prAllocs_succ hi1 hv]; omega)
        ⟨?_, ?_, ?_, ?_, by have := hapi.tbc_lt; omega⟩ hl' (fun a ha => (kK a ha).trans (hS.keep a ha)) kFL kT
        K.big⟩
      io := hP.keep kP
      kept := fun c hc _ => hc
      frame := fun a h1 h2 => hk a fun hw => by
        simp only [TiWH, Rng, TolFr] at hw
        rcases hw with hw | hw | hw | hw | hw <;> homega
      len := by rw [hlen8, argBytes_int, ← hlx]
      bytes := by rw [argBytes_int]; exact hb
      src_lo := srcLo_of_heap hts.lo
      src_hi := by rw [argBytes_int]; have := hts.hi; homega
      src_ok := fun a h1 h2 => ?_
      src_out := by
        rw [argBytes_int]; have := hts.lo; have : stdoutFile = 0x8005e668 := rfl; have : fileSize = 184 := rfl
        omega
      src_buf := fun a h1 h2 => (hobj a (by omega) (by rw [argBytes_int] at h2; omega)).1.nbuf }
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inl ⟨by omega, by omega⟩)) (by simp only [Rng]; omega)).trans
      hapi.ci_w
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inr ⟨by omega, by omega⟩))) (by
      have := hn.sep; simp only [Rng]; omega)).trans hapi.func_w
  · rw [htop]; congr 1
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inl ⟨by omega, by omega⟩))) (by
      simp only [Rng]; omega)).trans hapi.tbc_w
  · rw [argBytes_int] at h2
    have hk' := (hobj a (by omega) (by omega)).1
    have hsp : heapEnd + 4096 ≤ sp0 - 64 := by homega
    exact ⟨fun hg => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inl hg)),
      fun hm => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inl hm))),
      fun hs => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inr (.inl hs))))⟩

/-! ## A string created -/

/-- (lane F1-23) **What an integer's `luaL_tolstring` writes, a string
created** (`IaNewPost` and the push): the allocator's writes off the chunks in
use, the new object, the bucket's word, `nuse`, `g->allgc`, and `TiWH`'s. -/
def TiWN (H : HeapIx) (p l bkt g top L sp lw : Nat) (a : Nat) : Prop :=
  MallocW H.chunks a ∨ Rng p (l + 25) a ∨ Rng bkt 8 a ∨ Rng (g + 56) 4 a ∨ Rng (g + 112) 8 a ∨
    TiWH g top L sp lw a

/-- **A created string's run keeps every byte off `TiWN`.** -/
theorem ti_keepN {m M3 M : Mem} {sp L g top lw bkt nuse head p : Nat} {b : List UInt8} {hh v : BitVec 64}
    {H H' : HeapIx} (hnew : IaNewPost m M3 (TolFr sp) g bkt nuse head b hh H p H')
    (hpost : PfPost M3 M (sp - 48) L g top p) (hsp : 48 ≤ sp) :
    ∀ a, ¬ TiWN H p b.length bkt g top L sp lw a → bytesT1 (writeMap8 M lw (sdData_val v)) a = bytesT1 m a := by
  intro a ha
  simp only [TiWN, TiWH, not_or] at ha
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := ha
  rw [fw1_wm8 (by simp only [Rng] at h10; omega)]
  refine (hpost.keep a fun hw => ?_).trans (hnew.keep a fun hw => ?_)
  · rcases hw with hw | hw | hw | hw | hw
    · exact h7 hw
    · exact h8 hw
    · exact h6 (by simp only [Rng, gTotalbytesOff] at hw ⊢; omega)
    · exact h6 (by simp only [Rng, gGCdebtOff] at hw ⊢; omega)
    · exact h9 (by simp only [PfFr, TolFr] at hw ⊢; omega)
  · rcases hw with hw | hw | hw | hw | hw | hw | hw
    · exact h1 hw
    · exact h2 hw
    · exact h3 hw
    · exact h4 hw
    · exact h5 hw
    · exact h6 (by simp only [Rng] at hw ⊢; omega)
    · exact h9 hw

/-- The memory `luaL_tolstring` returns with (the length word stored). -/
abbrev tiM (M : Mem) (sp0 : Nat) (x : BitVec 64) : Mem :=
  writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 (intU8 x).length))

/-- (lane F1-23) **A created string's context** (`TolPost`'s inputs):
`luaB_print`'s entry and state before argument `i`, the literals' reading
`rt0` of `g->strt` and the bucket `j` of the digits, the creation path's
outcome (`IaNewPost`, the object `p`, the heap `H'`) and the push (`PfPost`). -/
structure TiNew (sp0 L nci func tbc sl g n : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs)
    (D G B FL : Nat → Prop) (M0 : Mem) (ph0 : StdoutPh) (H0 : HeapIx) (i : Nat) (ph : StdoutPh) (H : HeapIx)
    (m M3 M : Mem) (x : BitVec 64) (rt0 : RtPtrs) (j p : Nat) (H' : HeapIx) : Prop where
  hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0
  hn : PrNums sp0 L nci func n 0x8000ac8c#64
  hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m
  hP : PrintSt m ph H
  hv : args[i - 1]? = some (.int x)
  hi1 : 1 ≤ i
  hL : LitsIn m g sl ls rt0
  hjd : (luaHash ls.seed (intU8 x)).toNat % rt0.strtSize = j
  hj : j < rt0.strtHeads.length
  new : IaNewPost m M3 (TolFr (sp0 - 64)) g (rt0.strtHash + 8 * j) rt0.strtNuse rt0.strtHeads[j] (intU8 x)
    (hw (luaHash ls.seed (intU8 x))) H p H'
  post : PfPost M3 M (sp0 - 64 - 48) L g (func + 16 * n + 16) p

/-- **What the caller holds lies in chunks in use at the entry, or below the
heap** (`PrX`). -/
theorem PrintIn.prX_kept {L nci func n tbc sl g : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G : Nat → Prop} {ph : StdoutPh} {H : HeapIx} {M : Mem}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph H M) {a : Nat}
    (h : PrX L nci g func n sl G a) : Kept H ph a ∨ a < heapStart := by
  have hp := hIn.placed
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hrb : Image.rodataBase = 0x8004ecc8 := rfl
  have hrs : Image.rodataSize = 55776 := rfl
  rcases h with (hG | hA | hro | hgc | hmt | hlg | hhk) | hL | hg | hs | hn | hlo
  · exact (hIn.keep_in a hG).imp id fun k => by
      simp only [PrintStatic, Rng, symTohost, symAtexit, LocaleW, symImpurePtr] at k; omega
  · simp only [ArgSlot] at hA
    exact .inl (hIn.stack_in a (by omega) (by have := hp.room; omega))
  · exact .inr (by omega)
  · simp only [Rng, gGcstpOff] at hgc
    exact .inl (hIn.g_in a (by omega) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))
  · simp only [Rng, gMtOff] at hmt
    exact .inl (hIn.g_in a (by omega) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))
  · simp only [Rng, stateGOff] at hlg
    exact .inl (hIn.L_in a (by omega) (by simp only [stateSize]; omega))
  · simp only [Rng, stateHookmaskOff] at hhk
    exact .inl (hIn.L_in a (by omega) (by simp only [stateSize]; omega))
  · exact .inl (hIn.L_in a hL.1 hL.2)
  · exact .inl (hIn.g_in a hg.1 hg.2)
  · exact .inl (hIn.stack_in a hs.1 hs.2)
  · exact .inl (hIn.nci_in a hn.1 hn.2)
  · exact .inr hlo

/-- The allocator's globals lie below the heap. -/
theorem MallocGlobal.lt {a : Nat} (h : MallocGlobal a) : a < heapStart := by
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  have : heapStart = 0x8006ecd0 := rfl
  simp only [MallocGlobal] at h; omega

/-- The stdio globals lie below the heap. -/
theorem stdioGlob_lt {a : Nat} (h : StdioGlob a) : a < heapStart := by
  have : heapStart = 0x8006ecd0 := rfl
  simp only [StdioGlob] at h; omega

section New

variable {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
  {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {i : Nat} {ph : StdoutPh} {H : HeapIx}
  {m M3 M : Mem} {x : BitVec 64} {rt0 : RtPtrs} {j p : Nat} {H' : HeapIx}

/-- The new object is fresh: no byte of a chunk in use at `H` (or at the entry). -/
theorem TiNew.fresh (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hk : Kept H ph a) : ¬ Rng p ((intU8 x).length + 25) a := fun hr =>
  h.new.fresh a hr.1 hr.2 hk.inuse

theorem TiNew.fresh0 (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hk : Kept H0 ph0 a) : ¬ Rng p ((intU8 x).length + 25) a :=
  h.fresh (h.hS.kept hk)

/-- The bucket's word: in a chunk in use, off what the caller keeps and off `W`. -/
theorem TiNew.bkt (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (ha : Rng (rt0.strtHash + 8 * j) 8 a) :
    Kept H ph a ∧ ¬ (PrX L nci g func n sl G a ∨ B a) ∧ ¬ (B a ∨ D a) := by
  have hS0 := h.hL.nil.strt
  have hjs : j < rt0.strtSize := by rw [← hS0.heads_len]; exact h.hj
  have := (h.hS.safe.self rt0 h.hL).hash a (by simp only [Rng] at ha; omega) (by simp only [Rng] at ha; omega)
  exact this

/-- **A byte of a chunk in use off the bucket, `nuse`, `g->allgc`, `g`'s
counters, the pushed slot and `L->top` is kept** by a created string's run. -/
theorem TiNew.keepU (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hu : InUse H.chunks a) (hlo : heapStart ≤ a) (hhi : a < heapEnd)
    (h1 : ¬ Rng (rt0.strtHash + 8 * j) 8 a) (h2 : ¬ Rng (g + 56) 4 a)
    (h3 : ¬ Rng (g + 112) 8 a) (h4 : ¬ Rng (g + 16) 16 a) (h5 : ¬ Rng (func + 16 * n + 16) 9 a)
    (h6 : ¬ Rng (L + 16) 8 a) : bytesT1 (tiM M sp0 x) a = bytesT1 m a := by
  have hsb := h.hn.sp_big
  refine ti_keepN h.new h.post (by homega) a fun hw => ?_
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · rcases hw with hg | ⟨-, -, hn⟩
    · exact absurd hlo (Nat.not_le.mpr hg.lt)
    · exact hn hu
  · exact h.new.fresh a hw.1 hw.2 hu
  · exact h1 hw
  · exact h2 hw
  · exact h3 hw
  · exact h4 hw
  · exact h5 hw
  · exact h6 hw
  · simp only [TolFr] at hw; homega
  · simp only [Rng] at hw; homega

theorem TiNew.keepIn (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hk : Kept H ph a) (h1 : ¬ Rng (rt0.strtHash + 8 * j) 8 a) (h2 : ¬ Rng (g + 56) 4 a)
    (h3 : ¬ Rng (g + 112) 8 a) (h4 : ¬ Rng (g + 16) 16 a) (h5 : ¬ Rng (func + 16 * n + 16) 9 a)
    (h6 : ¬ Rng (L + 16) 8 a) : bytesT1 (tiM M sp0 x) a = bytesT1 m a :=
  h.keepU hk.inuse hk.lo hk.hi h1 h2 h3 h4 h5 h6

/-- **A static byte off the allocator's globals is kept** by a created string's run. -/
theorem TiNew.keepS (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hlo : a < heapStart) (hm : ¬ MallocGlobal a) : bytesT1 (tiM M sp0 x) a = bytesT1 m a := by
  have hsb := h.hn.sp_big
  have hp := h.hIn.placed
  have b0 := (h.bkt (a := rt0.strtHash + 8 * j) ⟨Nat.le_refl _, by omega⟩).1.lo
  have hpl := h.new.lo
  have hSE : heapStart ≤ heapEnd := by decide
  refine ti_keepN h.new h.post (by homega) a fun hw => ?_
  simp only [TiWN, TiWH, Rng, TolFr] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · rcases hw with hw | ⟨h1, -, -⟩
    · exact hm hw
    · omega
  all_goals (have := hp.g_lo; have := hp.L_lo; have := hp.f_lo; homega)

/-- `g->strt`'s count and size at `luaB_print`'s state, against the budget: room
for the strings still to make. -/
theorem PrSt.strt_lt {L nci func tbc sl g n i k : Nat} {ls : LitPtrs} {args : List Value}
    {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {rt0 : RtPtrs} (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i k ph H m)
    (hL : LitsIn m g sl ls rt0) (hpos : 0 < prAllocs args i) :
    strtNuse m g = rt0.strtNuse ∧ strtSize m g = rt0.strtSize ∧ rt0.strtNuse + prAllocs args i ≤ rt0.strtSize := by
  have hS0 := hL.nil.strt
  have hg := hL.g
  have h1 := hS0.nuse_le
  have hh3 := hL.size_hi
  have e1 : strtNuse m g = rt0.strtNuse := by
    have := hS0.nuse; rw [hg] at this
    simp only [strtNuse, bT4_of_fill (bytesT4_of_rd32 this), BitVec.toNat_ofNat]; omega
  have e2 : strtSize m g = rt0.strtSize := by
    have := hS0.size; rw [hg] at this
    simp only [strtSize, bT4_of_fill (bytesT4_of_rd32 this), BitVec.toNat_ofNat]; omega
  have := hS.strt hpos
  rw [e1, e2] at this
  exact ⟨e1, e2, this⟩

/-- **What the push writes leaves a created string's facts**: the object, the
bucket's word and `nuse`, as the creation path left them. -/
theorem TiNew.post_keep
    (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (hk : ¬ Rng (func + 16 * n + 16) 9 a ∧ ¬ Rng (L + 16) 8 a ∧ ¬ Rng (g + 16) 16 a ∧ a < heapEnd + 32) :
    bytesT1 (tiM M sp0 x) a = bytesT1 M3 a := by
  have hsb := h.hn.sp_big
  obtain ⟨h1, h2, h3, h4⟩ := hk
  rw [fw1_wm8 (by homega)]
  refine h.post.keep a fun hw => ?_
  rcases hw with hw | hw | hw | hw | hw
  · exact h1 hw
  · exact h2 hw
  · exact h3 (by simp only [Rng, gTotalbytesOff] at hw ⊢; omega)
  · exact h3 (by simp only [Rng, gGCdebtOff] at hw ⊢; omega)
  · simp only [PfFr] at hw; homega

/-- **The new object at `luaL_tolstring`'s return** (`NewObjT`). -/
theorem TiNew.obj (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    NewObjT (tiM M sp0 x) g (rt0.strtHash + 8 * j) p rt0.strtNuse (rt0.strtHeads[j]'h.hj) (intU8 x)
      (luaHash ls.seed (intU8 x)) (bytesT1 m (g + gCurrentwhiteOff)) := by
  have hp := h.hIn.placed
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  have hHE : heapEnd = 0x87800000 := rfl
  simp only [stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at p2 p6 p10 p12
  have hl20 := (intBytes_len x).2
  have hlx := intU8_length x
  have hpl := h.new.lo; have hph := h.new.hi
  -- the object, fresh, is off the push's stores (in chunks in use)
  have kO : ∀ a, p ≤ a → a < p + (intU8 x).length + 25 → bytesT1 (tiM M sp0 x) a = bytesT1 M3 a := by
    intro a h1 h2
    have fr : ∀ y, Kept H ph y → ¬ (y = a) := fun y hy e => h.fresh hy (by subst e; exact ⟨h1, h2⟩)
    refine h.post_keep ⟨fun hr => fr _ (h.hS.kept (h.hIn.stack_in a (by simp only [Rng] at hr; omega)
      (by simp only [Rng] at hr; have := h.hIn.room; omega))) rfl, fun hr => fr _ (h.hS.kept (h.hIn.L_in a
      (by simp only [Rng] at hr; omega) (by simp only [Rng, stateSize] at hr ⊢; omega))) rfl,
      fun hr => fr _ (h.hS.kept (h.hIn.g_in a (by simp only [Rng] at hr; omega)
      (by simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at hr ⊢; omega))) rfl, by omega⟩
  -- the bucket's word and `nuse`: off `L`, the stack and `g`'s counters
  have b0 := h.bkt (a := rt0.strtHash + 8 * j) ⟨Nat.le_refl _, by omega⟩
  have b7 := h.bkt (a := rt0.strtHash + 8 * j + 7) ⟨by omega, by omega⟩
  have hbx : ∀ y, Rng (rt0.strtHash + 8 * j) 8 y → ¬ PrX L nci g func n sl G y := fun y hy hx =>
    (h.bkt hy).2.1 (.inl hx)
  have x0 := hbx (rt0.strtHash + 8 * j) ⟨Nat.le_refl _, by omega⟩
  have x7 := hbx (rt0.strtHash + 8 * j + 7) ⟨by omega, by omega⟩
  simp only [PrX, Rng, stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM, not_or, not_and, Nat.not_lt]
    at x0 x7
  have bhi := b7.1.hi
  have kB : ∀ a, Rng (rt0.strtHash + 8 * j) 8 a → bytesT1 (tiM M sp0 x) a = bytesT1 M3 a := fun a ha => by
    simp only [Rng] at ha
    refine h.post_keep ⟨?_, ?_, ?_, by omega⟩ <;> simp only [Rng, not_and, Nat.not_lt] <;>
      (intro _; have := h.hIn.room; omega)
  have kN : ∀ a, Rng (g + 56) 4 a → bytesT1 (tiM M sp0 x) a = bytesT1 M3 a := fun a ha => by
    simp only [Rng] at ha
    refine h.post_keep ⟨?_, ?_, ?_, by omega⟩ <;> simp only [Rng, not_and, Nat.not_lt] <;>
      (intro _; have := h.hIn.room; omega)
  have hn := h.new
  exact {
    tt := (kO _ (by omega) (by omega)).trans hn.tt
    mark := (kO _ (by omega) (by omega)).trans hn.mark
    len := (kO _ (by omega) (by omega)).trans hn.len
    hash := ((bytesT4_congrT fun k _ => (kO _ (by omega) (by omega)).symm).symm.trans hn.hash).trans
      (swData_sext _)
    hnext := (bytesT8_congrT fun k _ => (kO _ (by omega) (by omega)).symm).symm.trans hn.hnext
    bytes := fun k hk => (kO _ (by omega) (by omega)).trans (hn.bytes k hk)
    nul := (kO _ (by omega) (by omega)).trans hn.nul
    bucket := (bytesT8_congrT (a := rt0.strtHash + 8 * j) fun k _ =>
      (kB (rt0.strtHash + 8 * j + k) ⟨by omega, by omega⟩).symm).symm.trans hn.bucket
    nuse := (bytesT4_congrT (a := g + 56) fun k _ => (kN (g + 56 + k) ⟨by omega, by omega⟩).symm).symm.trans
      hn.nuse }

/-- A byte of the new object is no byte the caller holds, nor a bignum's, nor
`D`'s: those lie in chunks in use at the entry (or below the heap). -/
theorem TiNew.obj_off (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (ha : Rng p ((intU8 x).length + 25) a) :
    ¬ (PrX L nci g func n sl G a ∨ B a) ∧ ¬ (B a ∨ D a) := by
  have hpl := h.new.lo
  have nB : ¬ B a := fun hb => h.fresh0 (h.hS.bigIn.inK a hb) ha
  refine ⟨fun hx => hx.elim (fun hx => ?_) nB, fun hw => hw.elim nB fun hd => h.fresh0 (h.hIn.dirty_in a hd) ha⟩
  rcases h.hIn.prX_kept hx with hk | hlo
  · exact h.fresh0 hk ha
  · simp only [Rng] at ha; omega

/-- **What the creation path shows of the new string** (`InsOk`, for
`frozen_insert`): fresh, so apart from the table, the literals, the caller's
places, the bignums and `D`; in a chunk in use at the new heap. -/
theorem TiNew.insOk (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    InsOk rt0 ls (Kept H' ph) (fun a => PrX L nci g func n sl G a ∨ B a) (fun a => B a ∨ D a) (intU8 x) p := by
  have hp := h.hIn.placed
  have hpl := h.new.lo; have hph := h.new.hi
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hl20 := (intBytes_len x).2
  have hlx := intU8_length x
  have hc : tstringContentsOff = 24 := rfl
  have hS0 := h.hL.nil.strt
  have hSS : StrtSafe (fillZeroMem m) rt0 (Kept H ph) (fun a => PrX L nci g func n sl G a ∨ B a)
      (fun a => B a ∨ D a) := h.hS.safe.self rt0 h.hL
  have hsz := hS0.size_pos
  have hpos := prAllocs_int_pos h.hi1 h.hv
  obtain ⟨-, -, hst⟩ := h.hS.strt_lt h.hL hpos
  refine {
    p0 := by omega
    p_lo := by have : symTohost = 0x8005c6c0 := rfl; omega
    p_hi := hph
    off := fun a h1 h2 hT => ?_
    lits := lits_ne_intU8 ls x
    nlit := fun ts hts e => by
      subst e
      exact h.fresh (h.hS.lits.strs p hts p (Nat.le_refl _) (by omega)) ⟨Nat.le_refl _, by omega⟩
    short := by simp only [maxShortLen]; omega
    nuse_lt := by omega
    inK := fun a h1 h2 => ⟨⟨h.new.obj_in a h1 (by omega), by omega, by omega, fun hb =>
        h.new.fresh a h1 (by omega) (h.hP.io.buf_inUse hb)⟩, (h.obj_off ⟨h1, by omega⟩).2⟩
    mark := (h.obj_off ⟨by simp only [gcMarkedOff]; omega, by simp only [gcMarkedOff]; omega⟩).1
    hnext := fun a h1 h2 => (h.obj_off ⟨by simp only [tstringLnglenOff] at h1; omega,
      by simp only [tstringLnglenOff] at h2; omega⟩).1
    apart := ⟨by
      rw [h.hL.g]; simp only [gStrcacheOff, strcacheN, strcacheM]
      refine Classical.byContradiction fun hc => ?_
      simp only [not_or, Nat.not_le] at hc
      by_cases e : rt0.strtHash ≤ g
      · have := (hSS.hash g e (by omega)).2.1
        simp only [PrX, Rng, gEnd, gStrcacheOff, strcacheN, strcacheM, not_or, not_and, Nat.not_lt] at this
        omega
      · have := (hSS.hash rt0.strtHash (Nat.le_refl _) (by omega)).2.1
        simp only [PrX, Rng, gEnd, gStrcacheOff, strcacheN, strcacheM, not_or, not_and, Nat.not_lt] at this
        omega⟩ }
  rcases hT with hT | hT
  · exact h.fresh (hSS.hash a hT.1 hT.2).1 ⟨h1, by omega⟩
  · rw [h.hL.g] at hT
    exact h.fresh0 (h.hIn.g_in a hT.1 hT.2) ⟨h1, by omega⟩

/-- (lane F1-23) **The literals after a created string**: their facts and the
table's safety frozen on the footprint with the insertion's (`frozen_insert`),
apart from `D` (`PrintIn.dirty_in`/`dirty_g`, `LitsFoot.tab`), `_dtoa_r`'s
bignums apart from it. -/
structure TiIns (L nci func n sl g : Nat) (ls : LitPtrs) (D G B : Nat → Prop) (ph : StdoutPh) (H' : HeapIx)
    (m' : Mem) (FL' : Nat → Prop) : Prop where
  lits : LitsFoot g sl ls H' ph D FL' m'
  safe : Frozen FL' (StrtSafeIn L nci g func n sl ls D G B (Kept H' ph)) m'
  big_fl : ∀ a, B a → ¬ FL' a

/-- `g->strt`'s words at a memory, as a reading of the table names them. -/
theorem tabFoot_rt {m : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (hL : LitsIn m g sl ls rt) {a : Nat} :
    TabFoot m g a ↔ (g + gStrtHashOff ≤ a ∧ a < g + gStrtHashOff + 16) ∨
      (rt.strtHash ≤ a ∧ a < rt.strtHash + 8 * rt.strtSize) := by
  have hS0 := hL.nil.strt
  have hg := hL.g
  have eh := Lua.Vm.Boot.bytesT8_toNat_of_fill (hg ▸ hS0.hash)
  have es := Lua.Vm.Boot.bytesT4_toNat_of_fill (hg ▸ hS0.size)
  unfold TabFoot
  rw [eh, es]

/-- **The literals' footprint after a created string** (`TiIns`). -/
theorem TiNew.ins (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    TiIns L nci func n sl g ls D G B ph H' (tiM M sp0 x)
      (fun a => FL a ∨ InsFoot rt0 j p (intU8 x).length a) := by
  have hp := h.hIn.placed
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at p2 p4 p6 p10 p11 p12
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hroom := h.hIn.room
  have hl := h.hS.lits
  have hS0 := h.hL.nil.strt
  have hg := h.hL.g
  have hjs : j < rt0.strtSize := by rw [← hS0.heads_len]; exact h.hj
  have hpl := h.new.lo; have hph := h.new.hi
  have hl20 := (intBytes_len x).2
  have hlx := intU8_length x
  have hc : tstringContentsOff = 24 := rfl
  have hok := h.insOk
  have hKK : ∀ a, Kept H ph a → Kept H' ph a := fun a ha => ha.mono h.new.kept fun _ hb => .inl hb
  -- what the run keeps of `g` and of the literals' footprint
  have hgb0 : ∀ a, g ≤ a → a < g + 1400 → Kept H ph a := fun a h1 h2 =>
    h.hS.kept (h.hIn.g_in a h1 (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))
  have kG : ∀ a, g ≤ a → a < g + 1400 → ¬ Rng (rt0.strtHash + 8 * j) 8 a → ¬ Rng (g + 56) 4 a →
      ¬ Rng (g + 112) 8 a → ¬ Rng (g + 16) 16 a → bytesT1 (tiM M sp0 x) a = bytesT1 m a :=
    fun a h1 h2 hb hn ha hc => h.keepIn (hgb0 a h1 h2) hb hn ha hc (by simp only [Rng]; omega)
      (by simp only [Rng]; omega)
  have hTW : ∀ a, ¬ TabWr rt0 j a → ¬ Rng (rt0.strtHash + 8 * j) 8 a ∧ ¬ Rng (g + 56) 4 a ∧
      ¬ Rng (g + 112) 8 a := fun a ha => by
    simp only [TabWr, hg, gStrtNuseOff, gAllgcOff, not_or] at ha
    exact ⟨ha.1, ha.2.1, ha.2.2⟩
  have hk : ∀ a, FL a → ¬ TabWr rt0 j a → bytesT1 (tiM M sp0 x) a = bytesT1 m a := by
    intro a ha hw
    obtain ⟨w1, w2, w3⟩ := hTW a hw
    have hd : ¬ D a := hl.apart a ha
    exact h.keepIn (hl.kept a ha) w1 w2 w3
      (fun hr => by
        by_cases e : a < g + 24
        · exact hd (h.hIn.dirty a (.inr (.inr (.inl (by simp only [Rng, gTotalbytesOff] at hr ⊢; omega)))))
        · exact hd (h.hIn.dirty a (.inr (.inr (.inr (.inl (by simp only [Rng, gGCdebtOff] at hr ⊢; omega)))))))
      (fun hr => hd (h.hIn.dirty a (.inr (.inl (by simp only [Rng] at hr; omega)))))
      (fun hr => hd (h.hIn.dirty a (.inl (by simpa only [stateTopOff] using hr))))
  have hkg : ∀ a, (Rng (g + gStrtHashOff) 16 a ∨ Rng (g + gCurrentwhiteOff) 1 a) → ¬ TabWr rt0 j a →
      bytesT1 (tiM M sp0 x) a = bytesT1 m a := by
    intro a ha hw
    obtain ⟨w1, w2, w3⟩ := hTW a hw
    simp only [Rng, gStrtHashOff, gCurrentwhiteOff] at ha
    exact kG a (by omega) (by omega) w1 w2 w3 (by simp only [Rng]; omega)
  have hFS : Frozen FL (fun M => ∀ rt, LitsIn M g sl ls rt → StrtSafe (fillZeroMem M) rt (Kept H ph)
      (fun a => PrX L nci g func n sl G a ∨ B a) (fun a => B a ∨ D a)) m := h.hS.safe
  obtain ⟨fL, fS⟩ := frozen_insert h.hL h.hjd h.hj ⟨by omega, by omega⟩ hl.facts hFS h.obj hk hkg hok hKK
  -- the bucket's word lies off `g`
  have hbg : ∀ a, Rng (rt0.strtHash + 8 * j) 8 a → ¬ (g ≤ a ∧ a < g + 1400) := fun a ha hga =>
    (h.bkt ha).2.1 (.inl (.inr (.inr (.inl hga))))
  have kGb : ∀ a, g ≤ a → a < g + 1400 → ¬ Rng (g + 56) 4 a → ¬ Rng (g + 112) 8 a → ¬ Rng (g + 16) 16 a →
      bytesT1 (tiM M sp0 x) a = bytesT1 m a := fun a h1 h2 hn ha hc => kG a h1 h2 (fun hb => hbg a hb ⟨h1, h2⟩)
    hn ha hc
  have hgK : ∀ a, g ≤ a → a < g + 1400 → Kept H' ph a := fun a h1 h2 => hKK _ (hgb0 a h1 h2)
  have hTF : ∀ a, (g + 48 ≤ a ∧ a < g + 64) ∨ Rng (rt0.strtHash + 8 * j) 8 a → FL a := fun a ha => by
    refine hl.tab a ((tabFoot_rt h.hL).2 ?_)
    simp only [Rng, gStrtHashOff] at ha ⊢
    rcases ha with ha | ha
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr ⟨by omega, by omega⟩
  have hInsD : ∀ a, InsFoot rt0 j p (intU8 x).length a →
      (g + 48 ≤ a ∧ a < g + 64) ∨ Rng (rt0.strtHash + 8 * j) 8 a ∨ InsG g a ∨
        (p ≤ a ∧ a < p + tstringContentsOff + (intU8 x).length + 1) := fun a ha => by
    simp only [InsFoot, TabWr, InsG, hg, Rng, gStrtNuseOff, gAllgcOff, gStrtHashOff, gCurrentwhiteOff] at ha ⊢
    rcases ha with (ha | ha | ha) | ha | ha | ha
    · exact .inr (.inl ha)
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inr (.inl (.inr ha)))
    · exact .inr (.inr (.inr ha))
    · exact .inl ⟨by omega, by omega⟩
    · exact .inr (.inr (.inl (.inl ha)))
  -- `g->strt`'s pointer and size, kept
  have e8 : bytesT8 (tiM M sp0 x) (g + gStrtHashOff) = bytesT8 m (g + gStrtHashOff) :=
    bytesT8_congrT fun k hk => kGb _ (by simp only [gStrtHashOff]; omega)
      (by simp only [gStrtHashOff]; omega) (by simp only [Rng, gStrtHashOff]; omega)
      (by simp only [Rng, gStrtHashOff]; omega) (by simp only [Rng, gStrtHashOff]; omega)
  have e4 : bytesT4 (tiM M sp0 x) (g + gStrtSizeOff) = bytesT4 m (g + gStrtSizeOff) :=
    bytesT4_congrT fun k hk => kGb _ (by simp only [gStrtSizeOff]; omega)
      (by simp only [gStrtSizeOff]; omega) (by simp only [Rng, gStrtSizeOff]; omega)
      (by simp only [Rng, gStrtSizeOff]; omega) (by simp only [Rng, gStrtSizeOff]; omega)
  refine ⟨⟨fL, ?_, ?_, fun ts hts a h1 h2 => hKK _ (hl.strs ts hts a h1 h2), ?_, ?_, ?_⟩, fS, ?_⟩
  · -- kept
    rintro a (ha | ha)
    · exact hKK _ (hl.kept a ha)
    · rcases hInsD a ha with ha | ha | ha | ha
      · exact hgK a (by omega) (by omega)
      · exact hKK _ (h.bkt ha).1
      · simp only [InsG, Rng, gCurrentwhiteOff, gAllgcOff] at ha
        exact hgK a (by omega) (by omega)
      · exact (hok.inK a ha.1 ha.2).1
  · -- apart from `D`
    rintro a (ha | ha) hd
    · exact hl.apart a ha hd
    · rcases hInsD a ha with ha | ha | ha | ha
      · exact hl.apart a (hTF a (.inl ha)) hd
      · exact hl.apart a (hTF a (.inr ha)) hd
      · exact h.hIn.dirty_g a hd ha
      · exact (hok.inK a ha.1 ha.2).2 (.inr hd)
  · -- the literals' marks
    rintro ts hts (ha | ha)
    · exact hl.marks ts hts ha
    · have hoff := h.hL.off.lits ts hts (ts + gcMarkedOff) (by simp only [gcMarkedOff]; omega)
        (by simp only [gcMarkedOff]; omega)
      rcases ha with hw | ho | hh | hc
      · exact hoff (hw.tab hjs)
      · exact h.fresh (hl.strs ts hts (ts + gcMarkedOff) (by simp only [gcMarkedOff]; omega)
          (by simp only [gcMarkedOff]; omega)) ⟨ho.1, by omega⟩
      · exact hoff (.inr (by simp only [Rng, gStrtHashOff, gStrcacheOff, strcacheN, strcacheM] at hh ⊢; omega))
      · exact hoff (.inr (by simp only [Rng, gCurrentwhiteOff, gStrcacheOff, strcacheN, strcacheM] at hc ⊢; omega))
  · -- the string cache's candidates
    exact hl.cache.congr fun a h1 h2 => kGb a (by simp only [gStrcacheOff] at h1; omega)
      (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h2; omega)
      (by simp only [Rng, gStrcacheOff] at h1 ⊢; omega) (by simp only [Rng, gStrcacheOff] at h1 ⊢; omega)
      (by simp only [Rng, gStrcacheOff] at h1 ⊢; omega)
  · -- `g->strt`'s words
    intro a ha
    refine .inl (hl.tab a ?_)
    unfold TabFoot at ha ⊢
    rwa [e8, e4] at ha
  · -- `_dtoa_r`'s bignums
    rintro a hb (hf | ha)
    · exact h.hS.big_fl a hb hf
    · have hx := h.hS.bigIn.x a hb
      rcases hInsD a ha with ha | ha | ha | ha
      · exact hx (.inr (.inr (.inl ⟨by omega, by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega⟩)))
      · exact (h.bkt ha).2.2 (.inl hb)
      · simp only [InsG, Rng, gCurrentwhiteOff, gAllgcOff] at ha
        exact hx (.inr (.inr (.inl ⟨by omega, by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega⟩)))
      · exact h.fresh0 (h.hS.bigIn.inK a hb) ⟨ha.1, by omega⟩

/-- `L->top` after the push: one slot more. -/
theorem TiNew.top_w (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    bytesT8 (tiM M sp0 x) (L + 16) = BitVec.ofNat 64 (func + 16 * (n + 1) + 16) := by
  have hsb := h.hn.sp_big
  have hp := h.hIn.placed
  have := hp.L_hi
  have e := (bytesT8_congrT (m := tiM M sp0 x) (m' := M) (a := L + 16) fun j _ => fw1_wm8 (by
    simp only [stateSize] at this; homega)).trans h.post.top_w
  rw [e, show func + 16 * n + 16 + 16 = func + 16 * (n + 1) + 16 by omega]

/-- **What a created string's run keeps of `luaB_print`'s Lua state**: what
the state keeps from the entry (`PrKeep`), the API frame's words, the static
words an allocation reads, `_dtoa_r`'s bignums. -/
structure TiKeeps (L nci g func n : Nat) (G B : Nat → Prop) (m m' : Mem) : Prop where
  keep : ∀ a, PrKeep L g func n G a → bytesT1 m' a = bytesT1 m a
  api : ∀ a, ApiFoot L nci a → ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a
  stat : ∀ a, AllocStaticFoot g a → bytesT1 m' a = bytesT1 m a
  big : ∀ a, BigFoot B a → bytesT1 m' a = bytesT1 m a
  size : ∀ k, k < 4 → bytesT1 m' (g + gStrtSizeOff + k) = bytesT1 m (g + gStrtSizeOff + k)

theorem TiNew.keeps (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    TiKeeps L nci g func n G B m (tiM M sp0 x) := by
  have hp := h.hIn.placed
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  simp only [stateSize, ciSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at p2 p4 p6 p10 p11 p12 p13 p14
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hroom := h.hIn.room
  have hsep := h.hn.sep
  have hpos := prAllocs_int_pos h.hi1 h.hv
  -- the bucket's word off what the caller holds
  have hbx : ∀ a, Rng (rt0.strtHash + 8 * j) 8 a → ¬ PrX L nci g func n sl G a := fun a ha hx =>
    (h.bkt ha).2.1 (.inl hx)
  have kS : ∀ a, 0x80000000 ≤ a → a < heapStart → ¬ MallocGlobal a → bytesT1 (tiM M sp0 x) a = bytesT1 m a :=
    fun a _ h1 h2 => h.keepS h1 h2
  have hMG : ∀ a, MallocGlobal a → (0x8005c6d0 ≤ a ∧ a < 0x8005cee0) ∨ (0x8005d1b8 ≤ a ∧ a < 0x8005d1bc) ∨
      (0x8005d388 ≤ a ∧ a < 0x8005d398) ∨ (0x8005d3b8 ≤ a ∧ a < 0x8005d3c0) ∨
      (0x8005d3c8 ≤ a ∧ a < 0x8005d3e0) ∨ (0x8005d408 ≤ a ∧ a < 0x8005d40c) ∨ (0x8005e560 ≤ a ∧ a < 0x8005e5b0) :=
    fun a hg => by
      have : symMallocAv = 0x8005c6d0 := rfl
      have : symMallocSbrkBase = 0x8005d388 := rfl
      have : symBrk = 0x8005d3b8 := rfl
      have : symMallocMallinfo = 0x8005e560 := rfl
      have : errnoAddr = 0x8005d408 := rfl
      simp only [MallocGlobal] at hg; omega
  refine ⟨fun a ha => ?_, fun a ha h6 => ?_, fun a ha => ?_, fun a ha => ?_, fun k hk => ?_⟩
  · -- what the state keeps
    have hx : PrX L nci g func n sl G a := .inl ha
    have hgc := h.hS.gc hpos a
    rcases h.hIn.prX_kept hx with hk | hlo
    · have hk' := h.hS.kept hk
      refine h.keepIn hk' (fun hb => hbx a hb hx) ?_ (fun hr => hgc hr ha) ?_ ?_ ?_
      all_goals
        rcases ha with hG | hA | hro | hgs | hmt | hlg | hhk
        · obtain ⟨g1, g2, g3, -, -⟩ := h.hIn.keep_apart a hG
          simp only [Rng, stateTopOff] at g1 g2 g3 ⊢
          omega
        all_goals (have := hk'.hi; simp only [ArgSlot, Rng, gGcstpOff, gMtOff, stateGOff, stateHookmaskOff,
          Image.rodataBase, Image.rodataSize] at *; omega)
    · have hrb : Image.rodataBase = 0x8004ecc8 := rfl
      have hrs : Image.rodataSize = 55776 := rfl
      refine h.keepS hlo fun hg => ?_
      have := hMG a hg
      rcases ha with hG | hA | hro | hgs | hmt | hlg | hhk
      · rcases h.hIn.keep_in a hG with hk | hs
        · have := hk.lo; omega
        · simp only [PrintStatic, Rng, symTohost, symAtexit, LocaleW, symImpurePtr] at hs; omega
      all_goals (simp only [ArgSlot, Rng, gGcstpOff, gMtOff, stateGOff, stateHookmaskOff] at *; omega)
  · -- the API frame's words
    simp only [ApiFoot, Rng] at ha h6
    rcases ha with ha | ha | ha | ha
    · omega
    all_goals first
      | (refine h.keepIn (h.hS.kept (h.hIn.L_in a (by omega) (by simp only [stateSize]; omega)))
          (fun hb => hbx a hb (.inr (.inl ⟨by omega, by simp only [stateSize]; omega⟩))) ?_ ?_ ?_ ?_ ?_ <;>
          (simp only [Rng]; omega))
      | (refine h.keepIn (h.hS.kept (h.hIn.nci_in a (by omega) (by simp only [ciSize]; omega)))
          (fun hb => hbx a hb (.inr (.inr (.inr (.inr (.inl ⟨by omega, by simp only [ciSize]; omega⟩))))))
          ?_ ?_ ?_ ?_ ?_ <;> (simp only [Rng]; omega))
  · -- the static words an allocation reads
    simp only [AllocStaticFoot, Rng] at ha
    by_cases hg8 : g ≤ a ∧ a < g + 8
    · exact h.keepIn (h.hS.kept (h.hIn.g_in a hg8.1 (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)))
        (fun hb => hbx a hb (.inr (.inr (.inl ⟨hg8.1, by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega⟩))))
        (by simp only [Rng]; omega) (by simp only [Rng]; omega) (by simp only [Rng]; omega)
        (by simp only [Rng]; omega) (by simp only [Rng]; omega)
    · refine h.keepS (by omega) fun hg => ?_
      have := hMG a hg
      omega
  · -- `_dtoa_r`'s bignums
    rcases ha with hb | hr
    · have hx := h.hS.bigIn.x a hb
      have hk := h.hS.kept (h.hS.bigIn.inK a hb)
      simp only [PrX, not_or] at hx
      obtain ⟨-, hxL, hxg, hxs, -, -⟩ := hx
      refine h.keepIn hk (fun hw => (h.bkt hw).2.2 (.inl hb)) ?_ ?_ ?_ ?_ ?_
      all_goals (intro hr; first
        | exact hxg ⟨by simp only [Rng] at hr; omega, by simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at hr ⊢; omega⟩
        | exact hxs ⟨by simp only [Rng] at hr; omega, by simp only [Rng] at hr; omega⟩
        | exact hxL ⟨by simp only [Rng] at hr; omega, by simp only [Rng, stateSize] at hr ⊢; omega⟩)
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr
      refine h.keepS (by omega) fun hg => ?_
      have := hMG a hg
      omega
  · -- `g->strt.size`
    have hge : g + gStrtSizeOff + k < g + gEnd := by
      simp only [gEnd, gStrcacheOff, strcacheN, strcacheM, gStrtSizeOff]; omega
    exact h.keepIn (h.hS.kept (h.hIn.g_in _ (by omega) hge)) (fun hb => hbx _ hb (.inr (.inr (.inl ⟨by omega, hge⟩))))
      (by simp only [Rng, gStrtSizeOff]; omega) (by simp only [Rng, gStrtSizeOff]; omega)
      (by simp only [Rng, gStrtSizeOff]; omega) (by simp only [Rng, gStrtSizeOff]; omega)
      (by simp only [Rng, gStrtSizeOff]; omega)

/-- **`luaB_print`'s state after a created string** (`PrSt` before argument
`i + 1`): the literals on the footprint with the insertion's (`TiNew.ins`), the
budget less the argument's allocation, one string more in `g->strt`. -/
theorem TiNew.st (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    PrSt L nci func tbc sl g n ls args D G B (fun a => FL a ∨ InsFoot rt0 j p (intU8 x).length a) M0 ph0 H0
      (i + 1) (n + 1) ph H' (tiM M sp0 x) := by
  have hI := h.ins
  have K := h.keeps
  have hapi := h.hS.api
  have hpos := prAllocs_int_pos h.hi1 h.hv
  obtain ⟨e1, e2, hst⟩ := h.hS.strt_lt h.hL hpos
  have hc := prCost_int h.hi1 h.hv
  have ha := prAllocs_succ h.hi1 h.hv
  simp only [argCost, show (0 : Nat) < 16384 + 4096 + 128 from by decide, ite_true] at ha
  have hsz := h.hL.size_hi
  have hNO := h.obj
  have eN : strtNuse (tiM M sp0 x) g = rt0.strtNuse + 1 := by
    simp only [strtNuse, hNO.nuse, BitVec.toNat_ofNat]; omega
  have eS : strtSize (tiM M sp0 x) g = rt0.strtSize := by
    rw [← e2]; simp only [strtSize]; congr 1; exact bytesT4_congrT fun k hk => K.size k hk
  have hbrk := h.new.brk
  exact {
    api := ⟨(bytesT8_congrT fun k _ => (K.api _ (.inr (.inl ⟨by omega, by omega⟩)) (by simp only [Rng]; omega)).symm).symm.trans
        hapi.ci_w,
      (bytesT8_congrT fun k _ => (K.api _ (.inr (.inr (.inr ⟨by omega, by omega⟩))) (by
        have := h.hn.sep; simp only [Rng]; omega)).symm).symm.trans hapi.func_w,
      h.top_w,
      (bytesT8_congrT fun k _ => (K.api _ (.inr (.inr (.inl ⟨by omega, by omega⟩))) (by
        simp only [Rng]; omega)).symm).symm.trans hapi.tbc_w,
      by have := hapi.tbc_lt; omega⟩
    lits := hI.lits
    keep := fun a ha => (K.keep a ha).trans (h.hS.keep a ha)
    buf := h.hS.buf
    chunks := fun c hc hu => h.new.kept c (h.hS.chunks c hc hu) hu
    room := fun hb => by
      have := h.hS.room (by omega)
      omega
    strt := fun hb => by rw [eN, eS]; omega
    safe := hI.safe
    gc := fun hb => h.hS.gc (by omega)
    stat := fun hb => (h.hS.stat (by omega)).congr K.stat
    big := h.hS.big.trans K.big
    bigIn := h.hS.bigIn
    big_fl := hI.big_fl }

/-- The new object's bytes: in a chunk in use at the new heap, off `stdout`'s buffer. -/
theorem TiNew.objKept (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    ∀ a, p ≤ a → a < p + 24 + (intU8 x).length + 1 → Kept H' ph a := by
  intro a h1 h2
  have hpl := h.new.lo; have hph := h.new.hi
  have hl20 : (intU8 x).length ≤ 20 := by rw [intU8_length]; exact (intBytes_len x).2
  have h3 : a < p + (intU8 x).length + 25 := by omega
  exact ⟨h.new.obj_in a h1 h3, by omega, by omega, fun hb => h.new.fresh a h1 h3 (h.hP.io.buf_inUse hb)⟩

/-- **`stdout`'s phase after a created string**, with the new heap: it reads no
allocator word, its buffer is apart from the run's stores. -/
theorem TiNew.io (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    StdoutIn (tiM M sp0 x) H' ph := by
  have hP := h.hP
  have hpos := prAllocs_int_pos h.hi1 h.hv
  have hc := prCost_int h.hi1 h.hv
  have hbrk := h.new.brk
  refine hP.io.congrA (fun a ha => ?_) (fun hn => ?_) fun buf hb => ?_
  · rcases ha with ha | hb
    · exact h.keepS (stdioGlob_lt ha.1) fun hg => ha.2 (hg.alloc ha.1)
    · have hu := hP.io.buf_inUse hb
      have hlo := hP.io.buf_lo a hb
      have hhi := hP.io.buf_hi a hb
      have hp := h.hIn.placed
      have hgE := hp.g_hi
      have hroom := h.hIn.room
      have nG : ¬ (g ≤ a ∧ a < g + 1400) := fun hr =>
        (h.hS.kept (h.hIn.g_in a hr.1 (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega))).nbuf hb
      have nS : ¬ (func ≤ a ∧ a < sl) := fun hr => (h.hS.kept (h.hIn.stack_in a hr.1 hr.2)).nbuf hb
      have nL : ¬ (L ≤ a ∧ a < L + 200) := fun hr => (h.hS.kept (h.hIn.L_in a hr.1 hr.2)).nbuf hb
      refine h.keepU hu (by omega) hhi (fun hr => (h.bkt hr).1.nbuf hb) ?_ ?_ ?_ ?_ ?_ <;>
        (simp only [Rng]; intro hr
         first
           | exact nG ⟨by omega, by omega⟩
           | exact nS ⟨by omega, by omega⟩
           | exact nL ⟨by omega, by omega⟩)
  · have hr := h.hS.room (by omega)
    cases ph with
    | up buf pend => exact absurd rfl (hn buf pend)
    | boot => simp only [stdoutNeed] at hr; omega
    | fresh => simp only [stdoutNeed] at hr; omega
  · obtain ⟨sz, hc, hs⟩ := hb.block
    exact ⟨⟨sz, h.new.kept _ hc rfl, hs⟩, hb.lo, hb.hi⟩

/-- **The heap's walk after a created string**: the push's stores lie in chunks in use. -/
theorem TiNew.heap (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    HeapAt (fillZeroMem (tiM M sp0 x)) H'.top H'.brk H'.chunks H'.bins := by
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  refine h.new.heap.ofTotal fun a hr hu => (h.post_keep ⟨?_, ?_, ?_, ?_⟩).trans (bytesT1_fill M3 a).symm
  · intro hw
    exact hu (Kept.inuse (Kept.mono (h.hS.kept (h.hIn.stack_in a (by simp only [Rng] at hw; omega)
      (by simp only [Rng] at hw; have := h.hIn.room; omega))) h.new.kept fun _ hb => .inl hb))
  · intro hw
    exact hu (Kept.inuse (Kept.mono (h.hS.kept (h.hIn.L_in a (by simp only [Rng] at hw; omega)
      (by simp only [Rng, stateSize] at hw ⊢; omega))) h.new.kept fun _ hb => .inl hb))
  · intro hw
    exact hu (Kept.inuse (Kept.mono (h.hS.kept (h.hIn.g_in a (by simp only [Rng] at hw; omega)
      (by simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at hw ⊢; omega))) h.new.kept
      fun _ hb => .inl hb))
  · simp only [HeapReads] at hr
    have : symMallocAv = 0x8005c6d0 := rfl
    have : symMallocSbrkBase = 0x8005d388 := rfl
    have : symBrk = 0x8005d3b8 := rfl
    have : symMallocTopPad = 0x8005d3d8 := rfl
    have : symMallocMaxSbrked = 0x8005d3d0 := rfl
    have : symMallocMallinfo = 0x8005e560 := rfl
    omega

/-- **`stdout`'s cells after a created string**: static words off the allocator's globals. -/
theorem TiNew.cells (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    PrintCells (tiM M sp0 x) := by
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hP := h.hP
  have hc := hP.cells
  have kL : ∀ a, a < 0x8005c6d0 ∨ (0x8005d1bc ≤ a ∧ a < 0x8005d388) ∨ (0x8005d398 ≤ a ∧ a < 0x8005d3b8) →
      0x80000000 ≤ a → bytesT1 (tiM M sp0 x) a = bytesT1 m a := fun a ha h0 =>
    h.keepS (by omega) fun hg => by
      have : symMallocAv = 0x8005c6d0 := rfl
      have : symMallocSbrkBase = 0x8005d388 := rfl
      have : symBrk = 0x8005d3b8 := rfl
      have : symMallocMallinfo = 0x8005e560 := rfl
      have : errnoAddr = 0x8005d408 := rfl
      simp only [MallocGlobal] at hg; omega
  exact ⟨(bytesT8_congrT fun k _ => (kL _ (.inr (.inr ⟨by omega, by omega⟩)) (by omega)).symm).symm.trans hc.impure,
    (bytesT8_congrT fun k _ => (kL _ (.inr (.inl ⟨by omega, by omega⟩)) (by omega)).symm).symm.trans hc.stdout,
    by rw [bytesAt_congr fun k hk => kL _ (.inl (by omega)) (by omega)]; exact hc.tab,
    by rw [bytesAt_congr fun k hk => kL _ (.inl (by omega)) (by omega)]; exact hc.nl⟩

/-- What a created string's run keeps of `luaB_print`'s frame (but the length word). -/
theorem TiNew.frame (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H')
    {a : Nat} (h1 : sp0 - 64 ≤ a) (h2 : a < sp0 - 56 ∨ sp0 - 48 ≤ a) : bytesT1 (tiM M sp0 x) a = bytesT1 m a := by
  have hsb := h.hn.sp_big
  have hp := h.hIn.placed
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have g1 := hp.g_hi; have g2 := hp.L_hi; have g3 := hp.sl_hi; have g4 := h.hIn.room
  have hph := h.new.hi
  have hl20 : (intU8 x).length ≤ 20 := by rw [intU8_length]; exact (intBytes_len x).2
  have hbk := (h.bkt (a := rt0.strtHash + 8 * j + 7) ⟨by omega, by omega⟩).1.hi
  simp only [gEnd, gStrcacheOff, strcacheN, strcacheM, stateSize] at g1 g2
  refine ti_keepN h.new h.post (by omega) a fun hw => ?_
  simp only [TiWN, TiWH, Rng, TolFr] at hw
  rcases hw with hw | hw | hw | hw | hw | hw | hw | hw | hw | hw
  · rcases hw with hg | ⟨-, hw, -⟩
    · have := hg.lt; omega
    · omega
  all_goals omega

/-- (lane F1-23) **`TolPost` from an integer's `luaL_tolstring`, the string
created** (`IaNewPost`): the state before argument `i + 1` (`TiNew.st`),
`stdout`'s state with the new heap (`TiNew.io`, `TiNew.heap`, `TiNew.cells`),
the new string's bytes (`NewObjT`), where they lie (a fresh block, in use at
the new heap). -/
theorem prIntNew (h : TiNew sp0 L nci func tbc sl g n ls args ι D G B FL M0 ph0 H0 i ph H m M3 M x rt0 j p H') :
    TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (intBytes x) ph m
      (tiM M sp0 x) (p + 24) H H' := by
  have hsb := h.hn.sp_big
  have hpl := h.new.lo; have hph := h.new.hi
  have hl20 : (intBytes x).length ≤ 20 := (intBytes_len x).2
  have hobj : ∀ a, p + 24 ≤ a → a < p + 24 + (intBytes x).length + 1 → Kept H' ph a := fun a h1 h2 =>
    h.objKept a (by omega) (by rw [intU8_length]; omega)
  have hsp : heapEnd + 4096 ≤ sp0 - 64 := by homega
  refine
    { lua := ⟨_, _, h.st⟩
      io := ⟨h.io, h.heap, h.cells⟩
      kept := h.new.kept
      frame := fun a h1 h2 => h.frame h1 h2
      len := by rw [fw8_same rfl, intU8_length]
      bytes := bytesAt_intU8 fun k hk => h.obj.bytes k hk
      src_lo := srcLo_of_heap (Nat.le_trans (Nat.le_add_right _ _) hpl)
      src_hi := by homega
      src_ok := fun a h1 h2 => ?_
      src_out := srcOut_of_heap (Nat.le_trans (Nat.le_trans (Nat.le_add_right _ _) hpl) (Nat.le_add_right _ _))
      src_buf := fun a h1 h2 => (hobj a h1 h2).nbuf }
  have hk' := hobj a h1 h2
  exact ⟨fun hg => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inl hg)),
    fun hm => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inl hm))),
    fun hs => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp (fun _ h => .inl h) (.inl (.inr (.inr (.inl hs))))⟩

end New

/-! ## `TolInt_Statement` -/

/-- **`luaL_tolstring` on an integer argument in `luaB_print`'s loop**
(`TolInt_Statement`, lane F1-23): the run `tolint_sum` from `TolIIn`
(`tolI_in`) and `luaS_newlstr`'s table (`tolI_tab`, the literals' reading of
`g->strt` at `luaB_print`'s state); `TolPost` from a found string
(`prIntHit`) or a created one (`prIntNew`). -/
theorem tolInt_proved : TolInt_Statement := by
  intro sp0 L nci func n tbc sl g ls args ι D G B FL ph0 H0 M0 i v hIn hn hv hC hi1 hin ph H m o r f hS hP hr
  cases v with
  | int x =>
    have hx := tolI_in hIn hn hS hv hi1 hin hr
    obtain ⟨rt0, hL⟩ := hS.lits.facts.self
    have hS0 := hL.nil.strt
    have hj : (luaHash ls.seed (intU8 x)).toNat % rt0.strtSize < rt0.strtHeads.length := by
      rw [hS0.heads_len]; exact Nat.mod_lt _ hS0.size_pos
    obtain ⟨d, hT⟩ := tolI_tab hIn hn hS hP hv hi1 hL rfl hj
    intro c h
    obtain ⟨c', s', ts, M3, M, H', hstr, hpost, -, hret⟩ := tolint_sum AllocProof.mallocR_proved
      integerToStr_proved (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g x r f m o hx ls.seed
      (Kept H ph) _ _ (bytesT1 m (g + 100)) rt0.strtSize rt0.strtHash _ d rt0.strtNuse H hT c h
    rcases hstr with ⟨hh, rfl⟩ | hnew
    · exact ⟨c', s', _, ts + 24, _, hret, prIntHit hIn hn hS hP hv hi1 hh hpost⟩
    · have hP' := prIntNew ⟨hIn, hn, hS, hP, hv, hi1, hL, rfl, hj, hnew, hpost⟩
      rw [← argBytes_int] at hP'
      exact ⟨c', s', _, ts + 24, H', hret, hP'⟩
  | nil => exact absurd hC id
  | bool _ => exact absurd hC id
  | flt _ _ => exact absurd hC id
  | str _ => exact absurd hC id
  | builtin _ => exact absurd hC id

/-- **`luaB_print` on the C frame** from `CALL`'s open part (lane F1-15;
F1-17; F1-18; F1-23): `lua_pushstring` of the literals proved
(`pushLit_proved`), `luaL_tolstring` on strings and integers proved
(`tolStr_proved`, `tolInt_proved`), `_malloc_r` proved (lane F1-A0-M,
`AllocProof.mallocR_proved`); floats and functions by `CallOpen`'s fields
(`printFlt`, `printFn`). (Moved from `Kit/TolStrProof.lean`.) -/
theorem CallOpen.print (O : CallOpen) : PrintRel_Statement :=
  printRel_of AllocProof.mallocR_proved pushLit_proved tolStr_proved tolInt_proved O.printFlt O.printFn

end Lua.Vm.Sim.Kit

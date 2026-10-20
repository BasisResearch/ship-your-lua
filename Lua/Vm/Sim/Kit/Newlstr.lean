import Lua.Vm.Sim.Kit.InternNew

/-!
# `luaS_newlstr` on short contents in a caller's frame (lane F1-20)

The whole call: `internshrstr`'s hash, bucket and chain walk
(`ia_walk_sum`), a node found returned (`IaHit`), else the creation path
(`ia_new`: the new string, `IaNewPost`). The creation path's inputs are stated
of the caller's memory and moved to the loops' root memory (the entry's with
`internshrstr`'s frame stored) by `IaNewIn.congr`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- **The creation path's inputs at another memory** agreeing below the
stack (the heap's reads reach `heapEnd + 32`). -/
theorem IaNewIn.congr {M M' : Mem} {L g bkt size nuse head : Nat} {b : List UInt8} {H : HeapIx}
    (h : IaNewIn M L g bkt size nuse head b H)
    (hk : ∀ a, a < 0x87800000 + 64 → bytesT1 M' a = bytesT1 M a) : IaNewIn M' L g bkt size nuse head b H := by
  have e2 : heapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have hIn : ∀ a, InUse H.chunks a → a < heapEnd + 8 := fun a hu => Nat.lt_of_not_le fun hc =>
    ChunkWalk.notInUse_hi h.heap.walk a (by have := h.heap.top_le; have := h.heap.brk_le; omega) hu
  have kg : ∀ a, g ≤ a → a < g + 1400 → bytesT1 M' a = bytesT1 M a := fun a h1 h2 =>
    hk a (by have := hIn a (h.g_in a h1 h2); omega)
  exact {
    bkt_lo := h.bkt_lo, bkt_he := h.bkt_he, kg := h.kg, k_al := h.k_al, g_al := h.g_al
    nuse_w := (bytesT4_congrT fun i _ => kg _ (by omega) (by omega)).trans h.nuse_w
    nuse_lt := h.nuse_lt, size_hi := h.size_hi
    head_w := (bytesT8_congrT fun i _ => hk _ (by have := h.bkt_he; omega)).trans h.head_w
    head_lt := h.head_lt
    heap := h.heap.ofTotal fun a hr _ => by
      rw [hk a (by simp only [HeapReads] at hr; omega), bytesT1_fill]
    room := h.room
    frealloc := (bytesT8_congrT fun i _ => kg _ (by omega) (by omega)).trans h.frealloc
    impure := (bytesT8_congrT fun i _ => hk _ (by omega)).trans h.impure
    Lg := (bytesT8_congrT fun i _ => hk _ (by
        have := hIn _ (h.L_in (L + 24 + i) (by omega) (by omega)); omega)).trans h.Lg
    g_in := h.g_in, L_in := h.L_in, k_in := h.k_in }

/-- **A string found by `luaS_newlstr`**, at the caller's memory `m`: the
node's facts, its length and contents `b`; the memory after the call `m'`
the caller's off `internshrstr`'s frame. -/
structure NlHit (m m' : Mem) (K X W : Nat → Prop) (sp ts : Nat) (b : List UInt8) : Prop where
  node : IaNode m K X W ts
  len : bytesT1 m (ts + 11) = BitVec.ofNat 8 b.length
  bytes : ∀ i, i < b.length → bytesT1 m (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  keep : ∀ a, ¬ Below sp 80 a → bytesT1 m' a = bytesT1 m a

/-- A found node's facts at the caller's memory (the node in `K`, below the
stack). -/
theorem IaHit.toNl {m M : Mem} {K X W : Nat → Prop} {sp ts : Nat} {b : List UInt8} {r : BitVec 64}
    {f : AbiFrame} {o : Array String} {c : Config} (hK : ∀ a, K a → a < 0x87800000) (hb40 : b.length ≤ 40)
    (hM : ∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a) (h : IaHit m M K X W sp ts b r f o c) :
    ∃ m', wrRet r sp ts f m' o c ∧ NlHit m m' K X W sp ts b := by
  obtain ⟨hn, hl, hb, m', hr, hk⟩ := h
  have hts : ∀ a, ts ≤ a → a < ts + 24 + (bytesT1 M (ts + 11)).toNat + 1 → a < 0x87800000 :=
    fun a h1 h2 => hK a (hn.obj a h1 h2).1
  have h11 : ts + 11 < 0x87800000 := hts _ (by omega) (by omega)
  have e11 : bytesT1 M (ts + 11) = bytesT1 m (ts + 11) := hM _ h11
  refine ⟨m', hr, ⟨⟨?_, fun a h1 h2 => ?_, hn.mark, hn.hnext⟩, e11 ▸ hl, fun i hi => ?_, hk⟩⟩
  · rw [← hM _ (hts _ (by omega) (by omega))]; exact hn.tt
  · rw [← e11] at h2; exact hn.obj a h1 h2
  · have hlen : (bytesT1 M (ts + 11)).toNat = b.length := by
      rw [hl, BitVec.toNat_ofNat]; omega
    rw [← hM _ (hts _ (by omega) (by rw [hlen]; omega))]; exact hb i hi

/-- **The new string's facts at the caller's memory**: the loops' root
memory is the caller's off `internshrstr`'s frame. -/
theorem IaNewPost.ofM0 {m m' : Mem} {sp g bkt nuse head p : Nat} {b : List UInt8} {hh r : BitVec 64}
    {f : AbiFrame} {o : Array String} {H H' : HeapIx} (hsp : 0x87800000 + 16384 ≤ sp)
    (h : IaNewPost (iaM0 sp r f m o) m' (Below sp 2048) g bkt nuse head b hh H p H') (hg : g + 1400 ≤ 0x87800000) :
    IaNewPost m m' (Below sp 2048) g bkt nuse head b hh H p H' := by
  have k : ∀ a, a + 80 < sp → bytesT1 (iaM0 sp r f m o) a = bytesT1 m a := fun a ha =>
    iaM0_keep (by omega) a (by simp only [Below]; omega)
  refine ⟨h.heap, h.brk, h.kept, h.obj_in, h.fresh, h.lo, h.hi, h.al, h.tt, ?_, h.extra, h.len, h.hash, h.hnext,
    ?_, h.bytes, h.nul, h.bucket, h.nuse, h.allgc, fun a ha => ?_⟩
  · rw [h.mark, k _ (by omega)]
  · rw [h.next]; exact bytesT8_congrT fun i _ => k _ (by omega)
  · rw [h.keep a ha]
    refine iaM0_keep (by omega) a fun hb => ha ?_
    simp only [Below] at hb
    exact .inr (.inr (.inr (.inr (.inr (.inr ⟨hb.1, by omega⟩)))))

/-- **`luaS_newlstr(L, s, l)`** on short contents `b` in a caller's frame
(`IaIn`), the table read as `internshrstr` reads it (`hT`), the creation
path's inputs (`IaNewIn`): a string found (`NlHit`) or created
(`IaNewPost`). -/
theorem newlstr_any_sum (hM : MallocR_Statement) (sp L s g size hash head d nuse : Nat) (b : List UInt8)
    (seed : UInt32) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) (hI : IaIn m sp L s g b seed r)
    (K X W : Nat → Prop) (cw : BitVec 8) (hK : ∀ a, K a → a < 0x87800000)
    (hT : ∀ M : Mem, (∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a) →
      bytesT1 M (g + 100) = cw ∧ IaTab M g (luaHash seed b) b cw (IaNode M K X W) size hash head d)
    (H : HeapIx) (hN : IaNewIn m L g (hash + 8 * ((luaHash seed b).toNat % size)) size nuse head b H) :
    Triple (SegSt 0x80017694#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 s⟩,
        ⟨Register.x12, BitVec.ofNat 64 b.length⟩] sp r f) (ArmPay m o))
      (fun c => (∃ ts m', wrRet r sp ts f m' o c ∧ NlHit m m' K X W sp ts b) ∨
        ∃ m' p H', wrRet r sp p f m' o c ∧ IaNewPost m m' (Below sp 2048) g (hash + 8 * ((luaHash seed b).toNat % size))
          nuse head b (hw (luaHash seed b)) H p H') := by
  intro c h
  have := hI.sp_lo; have := hI.g_hi
  have k : ∀ a, a < 0x87800000 + 64 → bytesT1 (iaM0 sp r f m o) a = bytesT1 m a := fun a ha =>
    iaM0_keep (by omega) a (by simp only [Below]; omega)
  obtain ⟨c', s', hq⟩ := ia_walk_sum sp L s g size hash head d b seed r f m o hI K X W cw hT
    (fun c => ∃ m' p H', wrRet r sp p f m' o c ∧ IaNewPost m m' (Below sp 2048) g (hash + 8 * ((luaHash seed b).toNat % size))
      nuse head b (hw (luaHash seed b)) H p H')
    (fun c F h' => by
      obtain ⟨c2, s2, m', p, H', hr, hp⟩ := ia_new hM m (iaM0 sp r f m o) sp L s g
        (hash + 8 * ((luaHash seed b).toNat % size)) size nuse head b r f (hw (luaHash seed b)) (bytesT8 m (g + 8)) o
        H F (hN.congr fun a ha => k a ha) (bytesT8_congrT fun i _ => k _ (by omega)) c h'
      exact ⟨c2, s2, m', p, H', hr, hp.ofM0 (by omega) (by omega)⟩) c h
  refine ⟨c', s', ?_⟩
  rcases hq with hq | ⟨ts, hq⟩
  · exact .inr hq
  · obtain ⟨m', hr, hn⟩ := hq.toNl hK hI.l_hi fun a ha => k a (by omega)
    exact .inl ⟨ts, m', hr, hn⟩

end Lua.Vm.Sim.Kit

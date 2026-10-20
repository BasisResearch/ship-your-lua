import Lua.Vm.Sim.Kit.InternAny
import Lua.Vm.Sim.Kit.Memcpy
import Lua.Vm.Sim.Kit.ExtendCI

/-!
# `internshrstr`'s creation path (lane F1-20)

From `0x8001742c` (the end of the bucket's chain): the table has room (`nuse <
size`: no `luaS_resize`, A8), `luaC_newobj(L, LUA_VSHRSTR, l + 25)` →
`luaM_malloc_` → `g->frealloc` (main.c's `l_alloc`, a call node:
`lalloc_sumN`, then `_malloc_r`'s summary), `GCdebt += l + 25`, the header
(`tt`, the current white, `next = g->allgc`, `g->allgc = ts`), the hash, the
length, the terminator, `memcpy` of the contents (a call node,
`memcpy_sum`), the link at the bucket's head, `nuse + 1`. Its at-lemmas are
`Lua/Vm/AtF/InternAny.lean`'s from the roots `N` (`0x8001742c`), `P` (after
`l_alloc`) and the return from `memcpy`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `l_alloc(ud, NULL, osize, n)` of any size -/

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_zero,
    Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub, Nat.reduceAdd,
    symGlobalPointer, sext64_id, himp] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | exact hnz
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.reduceAdd,
          symGlobalPointer, sext64_id, himp, Vsa.Sim.sext_zero, BitVec.add_zero]
         decide))

/-- **`l_alloc(ud, NULL, osize, n)`** (main.c's `g->frealloc`, `n ≥ 1`):
`realloc` → `_realloc_r(_REENT, NULL, n)` → `_malloc_r(_REENT, n)`, whose
summary (`MallocR_Statement`) is the result. -/
theorem lalloc_sumN (hM : MallocR_Statement) (sp n top brk : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (ud os r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hH : HeapAt (fillZeroMem m) top brk chunks bins) (hra : r.toNat % 4 = 0) (hsp : sp ≤ 2 ^ 32)
    (hal : sp % 16 = 0) (hlo : heapEnd + 1024 ≤ sp) (hn1 : 1 ≤ n) (hn : n < 2 ^ 32)
    (hroom : brk + n + 16384 ≤ heapEnd) (himp : bytesT8 m 0x8005d398 = 0x8005d1b8#64) :
    Triple (SegSt 0x8000172c#64 (callPre [⟨Register.x10, ud⟩, ⟨Register.x11, 0x0#64⟩, ⟨Register.x12, os⟩,
        ⟨Register.x13, BitVec.ofNat 64 n⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' p top' brk' chunks' bins', wrRet r sp p f m' o c ∧
        MallocPost m m' sp n p brk chunks top' brk' chunks' bins') := by
  intro c h
  have acc := Steps.refl c
  have hnz : (BitVec.ofNat 64 n == (0#64)) = false := by
    rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]; simp; omega
  simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append] at h
  kit_run h acc until [0x8002fa34]
  obtain ⟨c2, s2, hq⟩ := hM sp n top brk chunks bins r f m o hH hra hsp hal hlo hn1 hroom _ (by
    simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
    exact h.repin (by pins_of h))
  exact ⟨c2, acc.trans s2, hq⟩

/-! ## The creation path -/

/-- **What the creation path needs** at the loops' root memory `M`: the
bucket `bkt` (its head `head`), `nuse < size` (room: no `luaS_resize`), the
heap with room for the object, `g->frealloc` main.c's `l_alloc`,
`_impure_ptr`, `G(L)`, and where the objects it writes lie (in chunks in use:
the new block is fresh, so apart from them). -/
structure IaNewIn (M : Mem) (L g bkt size nuse head : Nat) (b : List UInt8) (H : HeapIx) : Prop where
  bkt_lo : 0x8005c6d0 ≤ bkt
  bkt_he : bkt + 8 ≤ 0x87800000
  kg : bkt + 8 ≤ g ∨ g + 1400 ≤ bkt
  k_al : bkt % 8 = 0
  g_al : g % 8 = 0
  nuse_w : bytesT4 M (g + 56) = BitVec.ofNat 32 nuse
  nuse_lt : nuse < size
  size_hi : size < 2 ^ 30
  head_w : bytesT8 M bkt = BitVec.ofNat 64 head
  head_lt : head < 2 ^ 64
  heap : HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins
  room : H.brk + (16384 + 4096 + 128) ≤ heapEnd
  frealloc : bytesT8 M g = 0x8000172c#64
  impure : bytesT8 M 0x8005d398 = 0x8005d1b8#64
  Lg : bytesT8 M (L + 24) = BitVec.ofNat 64 g
  g_in : ∀ a, g ≤ a → a < g + 1400 → InUse H.chunks a
  L_in : ∀ a, L ≤ a → a < L + 200 → InUse H.chunks a
  k_in : ∀ a, bkt ≤ a → a < bkt + 8 → InUse H.chunks a

/-- **What the creation path leaves**, from the loops' root memory `M`: the
heap with the new object's block `p` in use (fresh, in the arena, 16-aligned),
its header, hash (`hh`'s low word), length, contents `b` and terminator, its
`u.hnext` the old head and its `next` the old `g->allgc`; the bucket, `nuse`
and `g->allgc` updated; every other byte off the allocator's writes, `GCdebt`
and the frames below `sp` kept. -/
structure IaNewPost (M m' : Mem) (sp g bkt nuse head : Nat) (b : List UInt8) (hh : BitVec 64) (H : HeapIx)
    (p : Nat) (H' : HeapIx) : Prop where
  heap : HeapAt (fillZeroMem m') H'.top H'.brk H'.chunks H'.bins
  brk : H'.brk ≤ H.brk + (16384 + 4096 + 128)
  kept : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks
  obj_in : ∀ a, p ≤ a → a < p + b.length + 25 → InUse H'.chunks a
  fresh : ∀ a, p ≤ a → a < p + b.length + 25 → ¬ InUse H.chunks a
  lo : heapStart + 16 ≤ p
  hi : p + 128 ≤ heapEnd
  al : p % 16 = 0
  tt : bytesT1 m' (p + 8) = 0x04#8
  mark : bytesT1 m' (p + 9) = bytesT1 M (g + 100) &&& 0x18#8
  extra : bytesT1 m' (p + 10) = 0#8
  len : bytesT1 m' (p + 11) = BitVec.ofNat 8 b.length
  hash : bytesT4 m' (p + 12) = swData hh
  hnext : bytesT8 m' (p + 16) = BitVec.ofNat 64 head
  next : bytesT8 m' p = bytesT8 M (g + 112)
  bytes : ∀ i, i < b.length → bytesT1 m' (p + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  nul : bytesT1 m' (p + 24 + b.length) = 0#8
  bucket : bytesT8 m' bkt = BitVec.ofNat 64 p
  nuse : bytesT4 m' (g + 56) = BitVec.ofNat 32 (nuse + 1)
  allgc : bytesT8 m' (g + 112) = BitVec.ofNat 64 p
  keep : ∀ a, ¬ (MallocW H.chunks a ∨ Rng p (b.length + 25) a ∨ Rng bkt 8 a ∨ Rng (g + 56) 4 a ∨
      Rng (g + 112) 8 a ∨ Rng (g + 24) 8 a ∨ Below sp 2048 a) → bytesT1 m' a = bytesT1 M a

/-- The frame `l_alloc` sees from `luaM_malloc_` (via `luaC_newobj`, from
`internshrstr`): `s0 = g`, `s1 = L`, `s2 = tag`, `internshrstr`'s `s3`–`s7`. -/
abbrev iaAllocFr (L g bkt size l : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 g, BitVec.ofNat 64 L, 0x4#64, BitVec.ofNat 64 g, BitVec.ofNat 64 L, BitVec.ofNat 64 l,
    BitVec.ofNat 64 bkt, BitVec.ofNat 64 size, f.s8, f.s9, f.s10, f.s11⟩

/-- The frame `memcpy` sees from `internshrstr`: `s0 = ts`, `s1` the hash. -/
abbrev iaCopyFr (s g bkt size l p : Nat) (L : Nat) (hh : BitVec 64) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 p, hh, BitVec.ofNat 64 s, BitVec.ofNat 64 g, BitVec.ofNat 64 L, BitVec.ofNat 64 l,
    BitVec.ofNat 64 bkt, BitVec.ofNat 64 size, f.s8, f.s9, f.s10, f.s11⟩

/-- A stack word stored by the creation path's frames, read back. -/
macro "ia_slot" hM:ident : tactic => `(tactic| (
  rw [← $hM]
  simp only [Lua.Vm.AtF.InternAny.m3, iaX, iaN, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw8_same, fw8_wm8]; try rfl))

set_option hygiene false in
/-- The creation path's numeric context: the frame's and the table's facts,
the allocator's symbols. -/
local macro "ia_new_ctx" : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have := F.sp_lo; have := F.sp_hi; have := F.sp_al; have hra := F.ra; have := F.L_lo
  have := F.L_he; have := F.L_al; have := F.s_ge; have := F.s_hi; have := F.l_lo
  have := F.l_hi; have := F.g_lo; have := F.g_hi; have := F.s_al
  have := hN.bkt_lo; have := hN.bkt_he; have := hN.kg; have := hN.nuse_lt; have := hN.size_hi
  have := hN.room; have := hN.head_lt; have := hN.k_al; have := hN.g_al))

/-- The header's stores (the generated `m6`) over `_malloc_r`'s memory `m'`:
every other byte kept. -/
theorem ia_k6 {m' M6 : Mem} {sp L s g bkt size nuse p head : Nat} {b : List UInt8} {r : BitVec 64}
    {f : AbiFrame} {hh ud : BitVec 64} {o : Array String}
    (hM6 : Lua.Vm.AtF.InternAny.m6 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) = M6) :
    ∀ a, ¬ (Rng (g + 24) 8 a ∨ Rng p 24 a ∨ Rng (g + 112) 8 a ∨ a = p + 24 + b.length) →
      bytesT1 M6 a = bytesT1 m' a := by
  intro a ha
  simp only [Rng, not_or, not_and, Nat.not_lt] at ha
  rw [← hM6]
  simp only [Lua.Vm.AtF.InternAny.m6, iaX, iaN, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  simp (disch := omega) only [fw1_ins, fw1_wm4]

/-- **Where the new block lies**: in the arena, apart from `L`, `g` and the
bucket (in chunks in use before the allocation, the block fresh). -/
structure IaAllocFacts (H : HeapIx) (L g bkt p n : Nat) : Prop where
  inLo : ∀ a, InUse H.chunks a → heapStart + 16 ≤ a
  pL : L + 200 ≤ p ∨ p + n ≤ L
  pg : g + 1400 ≤ p ∨ p + n ≤ g
  pk : bkt + 8 ≤ p ∨ p + n ≤ bkt
  gLo : heapStart + 16 ≤ g
  kLo : heapStart + 16 ≤ bkt

theorem iaAllocFacts {M M3 m' : Mem} {L g bkt size nuse head : Nat} {b : List UInt8} {H : HeapIx}
    {sp' p top' brk' : Nat} {chunks' : List Chunk} {bins' : Nat → List Nat}
    (hN : IaNewIn M L g bkt size nuse head b H)
    (hP : MallocPost M3 m' sp' (b.length + 25) p H.brk H.chunks top' brk' chunks' bins') :
    IaAllocFacts H L g bkt p (b.length + 25) := by
  have inLo : ∀ a, InUse H.chunks a → heapStart + 16 ≤ a := fun a hu =>
    Nat.le_of_not_lt fun hc => ChunkWalk.notInUse_lo hN.heap.walk a hc hu
  exact {
    inLo := inLo
    pL := apart_of_use (fun a h1 h2 => hN.L_in a h1 h2) hP.fresh (by omega) (by omega)
    pg := apart_of_use (fun a h1 h2 => hN.g_in a h1 h2) hP.fresh (by omega) (by omega)
    pk := apart_of_use (fun a h1 h2 => hN.k_in a h1 h2) hP.fresh (by omega) (by omega)
    gLo := inLo g (hN.g_in g (Nat.le_refl _) (by omega))
    kLo := inLo bkt (hN.k_in bkt (Nat.le_refl _) (by omega)) }

/-- **The copy's memory** `M8` (the header over `_malloc_r`'s, then `memcpy`)
against the loops' root memory `M`: every byte off the object, `GCdebt`,
`g->allgc`, the allocator's writes and the frames below `sp - 80`. -/
theorem ia_keep8 {M M3 m' M6 M8 : Mem} {sp L s g bkt size nuse p head : Nat} {b : List UInt8} {r : BitVec 64}
    {f : AbiFrame} {hh ud : BitVec 64} {o : Array String} {H : HeapIx} {top' brk' : Nat}
    {chunks' : List Chunk} {bins' : Nat → List Nat}
    (k3 : ∀ a, (a + 152 < sp ∨ sp - 80 ≤ a) → bytesT1 M3 a = bytesT1 M a)
    (hP : MallocPost M3 m' (sp - 80 - 80) (b.length + 25) p H.brk H.chunks top' brk' chunks' bins')
    (hM6 : Lua.Vm.AtF.InternAny.m6 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) = M6)
    (hMo : MoveOut M6 M8 (p + 24) s b.length) (hsp : 0x87800000 + 16384 + 80 ≤ sp) :
    ∀ a, ¬ (Rng p (b.length + 25) a ∨ Rng (g + 24) 8 a ∨ Rng (g + 112) 8 a) →
      ¬ MallocGlobal a → (a < heapStart ∨ heapEnd ≤ a ∨ InUse H.chunks a) →
      (a + 2048 < sp ∨ sp - 80 ≤ a) → bytesT1 M8 a = bytesT1 M a := by
  intro a h1 h2 h3 h4
  simp only [Rng, not_or, not_and, Nat.not_lt] at h1
  rw [hMo.rd1 (by omega), ia_k6 hM6 a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega),
    bT1_congr (hP.keep a h2 h3 (by omega))]
  exact k3 a (by omega)

set_option hygiene false in
/-- A read of the header stores (`M6`, the generated `m6`) at a literal
offset of the new object. -/
local macro "ia_m6" : tactic => `(tactic| (
  rw [u6]
  simp only [Lua.Vm.AtF.InternAny.m6, Lua.Vm.AtF.InternAny.m4, iaX, iaN, FCx.mk', List.getD_cons_zero,
    List.getD_cons_succ]
  simp (disch := omega) only [fw1_ins, fw1_wm8, fw1_wm4, fw1_same, fw4_ins, fw4_wm8, fw4_wm4, fw4_same,
    fw8_ins, fw8_wm8, fw8_wm4, fw8_same]))

/-- **The creation path's memory**: from `_malloc_r`'s post (`hP`), the
header (`hM6`), `memcpy` (`hMo`) and the final stores (`hMF`), the new
object's facts (`IaNewPost`). -/
theorem ia_new_mem {m M M3 m' M6 M8 MF : Mem} {sp L s g bkt size nuse head p : Nat} {b : List UInt8}
    {r : BitVec 64} {f : AbiFrame} {hh ud : BitVec 64} {o : Array String} {H : HeapIx} {top' brk' : Nat}
    {chunks' : List Chunk} {bins' : Nat → List Nat}
    (F : IaFacts m M sp L s g b r f) (hN : IaNewIn M L g bkt size nuse head b H)
    (k3 : ∀ a, (a + 152 < sp ∨ sp - 80 ≤ a) → bytesT1 M3 a = bytesT1 M a)
    (hP : MallocPost M3 m' (sp - 80 - 80) (b.length + 25) p H.brk H.chunks top' brk' chunks' bins')
    (hM6 : Lua.Vm.AtF.InternAny.m6 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) = M6)
    (hMo : MoveOut M6 M8 (p + 24) s b.length)
    (hMF : Lua.Vm.AtF.InternAny.m7 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o) = MF) :
    IaNewPost M MF sp g bkt nuse head b hh H p ⟨top', brk', chunks', bins'⟩ := by
  ia_new_ctx
  have A := iaAllocFacts hN hP
  have := A.pL; have := A.pg; have := A.pk; have := A.gLo; have := A.kLo
  have hp1 := hP.lo; have hp2 := hP.hi; have hp3 := hP.al; have hp4 := hP.brk_hi
  have kS : ∀ a, sp - 160 ≤ a → bytesT1 m' a = bytesT1 M3 a :=
    fun a ha => bT1_congr (hP.keep a (fun hg => absurd hg.lo (by omega)) (.inr (.inl (by omega)))
      (.inr (by omega)))
  have kU : ∀ a, InUse H.chunks a → a < 0x87800000 → bytesT1 m' a = bytesT1 M a :=
    fun a hu hh' => have := A.inLo a hu; (bT1_congr (hP.keep a (fun hg => absurd hg.lo (by omega))
      (.inr (.inr hu)) (.inl (by omega)))).trans (k3 a (by omega))
  have kM8 := ia_keep8 k3 hP hM6 hMo (by omega)
  have hMFd : MF = writeMap4 (writeMap8 (writeMap8 M8 (p + 16) (sdData_val (BitVec.ofNat 64 head))) bkt
      (sdData_val (BitVec.ofNat 64 p))) (g + 56) (swData (BitVec.ofNat 64 (nuse + 1))) := by
    rw [← hMF]; rfl
  have kF : ∀ a, ¬ (Rng (p + 16) 8 a ∨ Rng bkt 8 a ∨ Rng (g + 56) 4 a) → bytesT1 MF a = bytesT1 M8 a := by
    intro a ha
    simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    rw [hMFd]; simp (disch := omega) only [fw1_wm4, fw1_wm8]
  have hl8 : b.length < 256 := by omega
  have u6 : M6 = Lua.Vm.AtF.InternAny.m6 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) := hM6.symm
  have hcw : bytesT1 m' (g + 100) = bytesT1 M (g + 100) := kU _ (hN.g_in _ (by omega) (by omega)) (by omega)
  have h112 : bytesT8 m' (g + 112) = bytesT8 M (g + 112) :=
    bytesT8_congrT fun i _ => kU _ (hN.g_in _ (by omega) (by omega)) (by omega)
  -- a byte off the outer stores and the copy's range: `M6`'s
  have kF6 : ∀ a, ¬ (Rng (p + 16) 8 a ∨ Rng bkt 8 a ∨ Rng (g + 56) 4 a ∨ Rng (p + 24) b.length a) →
      bytesT1 MF a = bytesT1 M6 a := by
    intro a ha
    simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    rw [kF a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega), hMo.rd1 (by omega)]
  refine
    { heap := hP.heap.ofTotal fun a hr hnu => ?_
      brk := by simp only; omega
      kept := hP.kept
      obj_in := fun a h1 h2 => by
        obtain ⟨sz, hblk, hsz⟩ := hP.block
        exact ⟨_, hblk, rfl, by simp only; omega, by simp only; omega⟩
      fresh := fun a h1 h2 => hP.fresh a h1 h2
      lo := hp1
      hi := by omega
      al := hp3
      tt := ?_, mark := ?_, extra := ?_, len := ?_, hash := ?_, hnext := ?_, next := ?_, bytes := ?_, nul := ?_
      bucket := ?_, nuse := ?_, allgc := ?_
      keep := fun a ha => ?_ }
  · -- the heap: the stores lie in chunks in use of the new heap
    have hng : ¬ (Rng p (b.length + 25) a ∨ Rng bkt 8 a ∨ Rng g 1400 a) := by
      rintro (h | h | h)
      · obtain ⟨sz, hblk, hsz⟩ := hP.block
        exact hnu ⟨_, hblk, rfl, by simp only [Rng] at h ⊢; omega, by simp only [Rng] at h ⊢; omega⟩
      · obtain ⟨c, hc, hu, h1, h2⟩ := hN.k_in a h.1 h.2
        exact hnu ⟨c, hP.kept c hc hu, hu, h1, h2⟩
      · obtain ⟨c, hc, hu, h1, h2⟩ := hN.g_in a h.1 h.2
        exact hnu ⟨c, hP.kept c hc hu, hu, h1, h2⟩
    simp only [Rng, not_or, not_and, Nat.not_lt] at hng
    rw [bytesT1_fill, kF a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega), hMo.rd1 (by omega),
      ia_k6 hM6 a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega)]
  · -- `tt`
    rw [kF6 _ (by simp only [Rng]; omega)]; ia_m6; decide
  · -- the mark: the current white
    rw [kF6 _ (by simp only [Rng]; omega)]; ia_m6
    rw [gs_addr (k := 100) (by decide) (by omega)]
    simp (disch := omega) only [fw1_wm8]
    rw [hcw]; generalize bytesT1 M (g + 100) = x; revert x; decide
  · -- `extra`
    rw [kF6 _ (by simp only [Rng]; omega)]; ia_m6; decide
  · -- `shrlen`
    rw [kF6 _ (by simp only [Rng]; omega)]; ia_m6; exact stData1_ofNat _
  · -- the hash
    rw [bytesT4_congrT (m' := M6) fun i _ => kF6 _ (by simp only [Rng]; omega)]; ia_m6
  · -- `u.hnext`: the old head
    rw [hMFd]; simp (disch := omega) only [fw8_wm4, fw8_wm8, fw8_same]
  · -- `next`: the old `g->allgc`
    rw [bytesT8_congrT (m' := M6) fun i _ => kF6 _ (by simp only [Rng]; omega)]; ia_m6; exact h112
  · -- the contents: `memcpy`'s
    intro i hi
    rw [kF _ (by simp only [Rng]; omega), hMo.moved i hi, ia_k6 hM6 _ (by simp only [Rng]; omega),
      kS _ (by omega), k3 _ (by omega)]
    exact F.bytes i hi
  · -- the terminator
    rw [kF6 _ (by simp only [Rng]; omega)]; ia_m6; decide
  · -- the bucket's head
    rw [hMFd]; simp (disch := omega) only [fw8_wm4, fw8_wm8, fw8_same]
  · -- `nuse + 1`
    rw [hMFd]; simp (disch := omega) only [fw4_same]; exact swData_ofNat _
  · -- `g->allgc`
    rw [bytesT8_congrT (m' := M6) fun i _ => kF6 _ (by simp only [Rng]; omega)]; ia_m6
  · -- the rest: off the allocator's writes, the object, the table's words, the frames
    have h1 : ¬ MallocGlobal a := fun h => ha (.inl (.inl h))
    have h2 : a < heapStart ∨ heapEnd ≤ a ∨ InUse H.chunks a := by
      by_cases hu : InUse H.chunks a
      · exact .inr (.inr hu)
      · by_cases hl : heapStart ≤ a
        · by_cases hr : a < heapEnd
          · exact absurd (.inl (.inr ⟨hl, hr, hu⟩)) ha
          · exact .inr (.inl (by omega))
        · exact .inl (by omega)
    simp only [Rng, Below, not_or, not_and, Nat.not_lt] at ha
    rw [kF a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega)]
    exact kM8 a (by simp only [Rng, not_or, not_and, Nat.not_lt]; omega) h1 h2 (by omega)

/-- **`internshrstr`'s creation path** from `0x8001742c` to its return: the
new short string `p` (`IaNewPost`). -/
theorem ia_new (hM : MallocR_Statement) (m M : Mem) (sp L s g bkt size nuse head : Nat) (b : List UInt8)
    (r : BitVec 64) (f : AbiFrame) (hh ud : BitVec 64) (o : Array String) (H : HeapIx)
    (F : IaFacts m M sp L s g b r f) (hN : IaNewIn M L g bkt size nuse head b H)
    (hud : bytesT8 M (g + 8) = ud) :
    Triple (SegSt 0x8001742c#64 (Lua.Vm.AtF.InternAny.r15 (iaX (iaN sp L s g bkt size 0 0 0 b) r f hh ud M o))
        (ArmPay M o))
      (fun c => ∃ m' p H', wrRet r sp p f m' o c ∧ IaNewPost M m' sp g bkt nuse head b hh H p H') := by
  intro c h
  ia_new_ctx
  -- the root `N`, with `nuse` and the old head
  have h : SegSt 0x8001742c#64 (Lua.Vm.AtF.InternAny.r15 (iaX (iaN sp L s g bkt size nuse 0 head b) r f hh ud M o))
      (ArmPay (iaX (iaN sp L s g bkt size nuse 0 head b) r f hh ud M o).m
        (iaX (iaN sp L s g bkt size nuse 0 head b) r f hh ud M o).o) c := by
    fcx_unfold at h ⊢; exact h
  have hX : Lua.Vm.AtF.InternAny.Ok_N (iaX (iaN sp L s g bkt size nuse 0 head b) r f hh ud M o) := by fcx_ok
  have hc10 : bytesT4 M (g + 56) = BitVec.ofNat 32 nuse := hN.nuse_w
  have hg2 : zopz0zKzJ_s (BitVec.ofNat 64 nuse) (BitVec.ofNat 64 size) = false := by
    simp only [zopz0zKzJ_s, fmt_toInt_ofNat (show nuse < 2 ^ 63 by omega),
      fmt_toInt_ofNat (show size < 2 ^ 63 by omega), decide_eq_false_iff_not]
    omega
  have hc0 : bytesT8 M (L + 24) = BitVec.ofNat 64 g := hN.Lg
  have hc11 : bytesT8 M g = 0x8000172c#64 := hN.frealloc
  have hc12 : bytesT8 M (g + 8) = ud := hud
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.InternAny h acc until [0x8000172c]
  -- `luaM_malloc_`'s frames, below `internshrstr`'s
  generalize hM3 : Lua.Vm.AtF.InternAny.m3 (iaX (iaN sp L s g bkt size nuse 0 head b) r f hh ud M o) = M3 at h
  have k3 : ∀ a, (a + 152 < sp ∨ sp - 80 ≤ a) → bytesT1 M3 a = bytesT1 M a := by
    intro a ha
    rw [← hM3]
    simp only [Lua.Vm.AtF.InternAny.m3, iaN, List.getD_cons_zero, List.getD_cons_succ]
    exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
  have hH3 : HeapAt (fillZeroMem M3) H.top H.brk H.chunks H.bins :=
    hN.heap.ofTotal fun a hr _ => by
      rw [k3 a (by simp only [HeapReads] at hr; omega), bytesT1_fill]
  have himp3 : bytesT8 M3 0x8005d398 = 0x8005d1b8#64 :=
    (bytesT8_congrT fun i _ => k3 _ (by omega)).trans hN.impure
  fcx_unfold at h
  obtain ⟨c2, s2, m', p, top', brk', chunks', bins', hret, hP⟩ := lalloc_sumN hM (sp - 80 - 80) (b.length + 25)
    H.top H.brk H.chunks H.bins ud 0x4#64 0x800110c0#64 (iaAllocFr L g bkt size b.length f) M3 o hH3 (by decide)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) himp3 _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
      exact h.repin (by pins_of h))
  have acc := acc.trans s2
  have A := iaAllocFacts hN hP
  have := A.pL; have := A.pg; have := A.pk; have := A.gLo; have := A.kLo
  have hp1 := hP.lo; have hp2 := hP.hi; have hp3 := hP.al; have hp4 := hP.brk_hi
  -- `_malloc_r`'s keep: the stack above its frame
  have kS : ∀ a, sp - 160 ≤ a → bytesT1 m' a = bytesT1 M3 a :=
    fun a ha => bT1_congr (hP.keep a (fun hg => absurd hg.lo (by omega)) (.inr (.inl (by omega)))
      (.inr (by omega)))
  -- the root `P` after `l_alloc`
  have hX1 : Lua.Vm.AtF.InternAny.Ok_P (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) := by
    fcx_ok
  simp only [wrRet] at hret
  have h : SegSt 0x800110c0#64 (Lua.Vm.AtF.InternAny.r18 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o))
      (ArmPay (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o).m
        (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o).o) c2 := hret.repin (by pins_of hret)
  have hc13 : bytesT8 m' (sp - 80 - 72) = BitVec.ofNat 64 (b.length + 25) :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc14 : bytesT8 m' (sp - 80 - 40) = 0x8000e910#64 :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc15 : bytesT8 m' (sp - 80 - 56) = 0x4#64 :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc16 : bytesT8 m' (sp - 80 - 48) = BitVec.ofNat 64 g :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc17 : bytesT8 m' (sp - 80 - 64) = BitVec.ofNat 64 s :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc18 : bytesT8 m' (sp - 80 - 8) = 0x80017444#64 :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc19 : bytesT8 m' (sp - 80 - 24) = hh :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hc20 : bytesT8 m' (sp - 80 - 16) = BitVec.ofNat 64 nuse :=
    (bytesT8_congrT fun i _ => kS _ (by omega)).trans (by ia_slot hM3)
  have hf4 : p ≠ 0 := by omega
  fat_run Lua.Vm.AtF.InternAny h acc until [0x8003b648]
  -- the header's stores over `_malloc_r`'s memory
  generalize hM6 : Lua.Vm.AtF.InternAny.m6 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud m' o) = M6 at h
  fcx_unfold at h
  obtain ⟨c3, s3, M8, hr3, hMo⟩ := memcpy_sum (sp - 80) (p + 24) s b.length 0x8001746c#64
    (iaCopyFr s g bkt size b.length p L hh f) M6 o
    ⟨⟨by omega, by omega, by omega, by omega, by omega, .inr (by omega)⟩, by omega, by decide, by omega,
      by omega, F.s_al⟩ _
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have acc := acc.trans s3
  have kM8 := ia_keep8 k3 hP hM6 hMo (by omega)
  -- the root after `memcpy`
  have hX2 : Lua.Vm.AtF.InternAny.Ok_P (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o) := by fcx_ok
  simp only [mmRet, AbiFrame.pins] at hr3
  have h : SegSt 0x8001746c#64 (Lua.Vm.AtF.InternAny.r21 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o))
      (ArmPay (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o).m
        (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o).o) c3 := hr3.repin (by pins_of hr3)
  have hc21 : bytesT8 M8 bkt = BitVec.ofNat 64 head :=
    (bytesT8_congrT fun i _ => kM8 _ (by simp only [Rng]; omega) (fun hg => absurd hg.lo (by omega))
      (.inr (.inr (hN.k_in _ (by omega) (by omega)))) (by omega)).trans hN.head_w
  have hc10 : bytesT4 M8 (g + 56) = BitVec.ofNat 32 nuse :=
    (bytesT4_congrT fun i _ => kM8 _ (by simp only [Rng]; omega) (fun hg => absurd hg.lo (by omega))
      (.inr (.inr (hN.g_in _ (by omega) (by omega)))) (by omega)).trans hN.nuse_w
  have fr : ∀ k, 1 ≤ k → k ≤ 9 → bytesT8 M8 (sp - 80 + 8 * k) = bytesT8 M (sp - 80 + 8 * k) := fun k h1 h2 =>
    bytesT8_congrT fun i _ => kM8 _ (by simp only [Rng]; omega) (fun hg => absurd hg.lo (by omega))
      (.inr (.inl (by omega))) (.inr (by omega))
  have hc1 : bytesT8 M8 (sp - 80 + 72) = r := (fr 9 (by omega) (by omega)).trans F.sv0
  have hc2 : bytesT8 M8 (sp - 80 + 64) = f.s0 := (fr 8 (by omega) (by omega)).trans F.sv1
  have hc3 : bytesT8 M8 (sp - 80 + 56) = f.s1 := (fr 7 (by omega) (by omega)).trans F.sv2
  have hc4 : bytesT8 M8 (sp - 80 + 48) = f.s2 := (fr 6 (by omega) (by omega)).trans F.sv3
  have hc5 : bytesT8 M8 (sp - 80 + 40) = f.s3 := (fr 5 (by omega) (by omega)).trans F.sv4
  have hc6 : bytesT8 M8 (sp - 80 + 32) = f.s4 := (fr 4 (by omega) (by omega)).trans F.sv5
  have hc7 : bytesT8 M8 (sp - 80 + 24) = f.s5 := (fr 3 (by omega) (by omega)).trans F.sv6
  have hc8 : bytesT8 M8 (sp - 80 + 16) = f.s6 := (fr 2 (by omega) (by omega)).trans F.sv7
  have hc9 : bytesT8 M8 (sp - 80 + 8) = f.s7 := (fr 1 (by omega) (by omega)).trans F.sv8
  fat_run Lua.Vm.AtF.InternAny h acc
  generalize hMF : Lua.Vm.AtF.InternAny.m7 (iaX (iaN sp L s g bkt size nuse p head b) r f hh ud M8 o) = MF at h
  fcx_unfold at h
  rw [show sp - 80 + 80 = sp by omega] at h
  exact ⟨_, acc, MF, p, ⟨top', brk', chunks', bins'⟩, h.repin (by pins_of h),
    ia_new_mem F hN k3 hP hM6 hMo hMF⟩

end Lua.Vm.Sim.Kit

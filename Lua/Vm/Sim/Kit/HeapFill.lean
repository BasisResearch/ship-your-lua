import Lua.Vm.Sim.Kit.HeapKeep
import Lua.Vm.Sim.Kit.StdoutSetup

/-!
# Presence-level keeps from total-read keeps (lane F1-11)

The stdio summaries keep the caller's bytes by their TOTAL reads (`bytesT1`,
the model's `getD 0`: `SfvKeep`, `StdoutKeep`, `SinitPost.keep`, …), while
the complement's facts (`DlHeap.HeapAt`, `LuaStateAt`, …) read with `rd64`
(bytes present). A total read does not say whether a byte is present, so a
total keep never gives `Agree` of the machine memories.

It does give `Agree` of their **zero fills** (`Vsa.Densify.fillZeroMem`):
in RAM every byte of a fill is present and holds the total read, so two
memories with the same total reads off a region have fills that agree there
(`Agree.ofTotal`, one lemma for every summary: no summary is restated). The
fill reads totally as the memory itself (`bytesT1_fill`), so it is a
complement for `Core.frame` as good as the machine memory, and everything
the old complement held of present bytes it holds of its fill (`Ext`:
presence-level facts are monotone, `HeapAt.ext`).

So after a `print`, `RuntimeMem.heap` holds again at the fill of the
machine's memory (`HeapAt.ofTotal`), given the total keep off what
`HeapAt` reads. That region is the arena *off the chunks in use*
(`HeapAt.congrU`: the walk reads headers, the free chunks' footers and
links, never an in-use payload), so the `stdout` buffer and every allocated
object may change under it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-! ## Extension: presence-level facts are monotone -/

/-- `m'` extends `m`: every byte present in `m` is present in `m'` with the
same value. -/
def Ext (m m' : Mem) : Prop := ∀ (a : Nat) (b : BitVec 8), m[a]? = some b → m'[a]? = some b

theorem Ext.refl (m : Mem) : Ext m m := fun _ _ h => h

theorem Ext.trans {m m1 m2 : Mem} (h1 : Ext m m1) (h2 : Ext m1 m2) : Ext m m2 :=
  fun a b h => h2 a b (h1 a b h)

theorem rdLE_ext {m m' : Mem} (h : Ext m m') : ∀ {n a x : Nat}, rdLE m a n = some x → rdLE m' a n = some x
  | 0, a, x, hx => by simpa [rdLE] using hx
  | n + 1, a, x, hx => by
    rw [rdLE_succ] at hx ⊢
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hx ⊢
    obtain ⟨b, hb, r, hr, rfl⟩ := hx
    exact ⟨b, h _ _ hb, r, rdLE_ext h hr, rfl⟩

theorem rd64_ext {m m' : Mem} (h : Ext m m') {a x : Nat} (hx : rd64 m a = some x) : rd64 m' a = some x :=
  rdLE_ext h hx

theorem rd64_ext_isSome {m m' : Mem} (h : Ext m m') {a : Nat} (hx : (rd64 m a).isSome) :
    (rd64 m' a).isSome := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hx
  rw [rd64_ext h hx]; rfl

theorem ChunkWalk.ext {m m' : Mem} (he : Ext m m') :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → ChunkWalk m' p top cs
  | _, _, _, .top => .top
  | _, _, _, .chunk e1 e2 e3 e4 e5 hw => .chunk (rd64_ext he e1) e2 e3 e4 (rd64_ext he e5) (ChunkWalk.ext he hw)

theorem BinChain.ext {m m' : Mem} (he : Ext m m') {b : Nat} :
    ∀ {q prev : Nat} {qs : List Nat}, BinChain m b q prev qs → BinChain m' b q prev qs
  | _, _, _, .close e => .close (rd64_ext he e)
  | _, _, _, .link ne e1 e2 hc => .link ne (rd64_ext he e1) (rd64_ext he e2) (BinChain.ext he hc)

/-- **The heap over a memory that extends it.** -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.ext {m m' : Mem} {top brk : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m top brk chunks bins) (he : Ext m m') :
    HeapAt m' top brk chunks bins where
  sbrk_base := rd64_ext he h.sbrk_base
  brk := rd64_ext he h.brk
  brk_le := h.brk_le
  top_ptr := rd64_ext he h.top_ptr
  top_le := h.top_le
  top_size := h.top_size
  top_header := rd64_ext he h.top_header
  top_pad := rd64_ext he h.top_pad
  max_sbrked := rd64_ext_isSome he h.max_sbrked
  mallinfo := rd64_ext_isSome he h.mallinfo
  first_prev := by
    have hf := h.first_prev
    cases hx : rd64 m (heapStart + 8) with
    | none => rw [hx] at hf; cases hf
    | some x => rw [hx] at hf; rw [rd64_ext he hx]; exact hf
  walk := ChunkWalk.ext he h.walk
  coalesced := h.coalesced
  footer := fun c hc hf => rd64_ext he (h.footer c hc hf)
  bins_list := fun i h0 h1 => ⟨rd64_ext he (h.bins_list i h0 h1).fd, BinChain.ext he (h.bins_list i h0 h1).chain⟩
  bins_nodup := h.bins_nodup
  bin_free := h.bin_free
  free_binned := h.free_binned
  remainder := h.remainder
  binblocks_present := rd64_ext_isSome he h.binblocks_present
  binblocks := fun bb hb => by
    obtain ⟨b0, h0⟩ := Option.isSome_iff_exists.1 h.binblocks_present
    rw [rd64_ext he h0, Option.some.injEq] at hb
    subst hb
    exact h.binblocks b0 h0

/-! ## The zero fill -/

/-- RAM, where the fill makes every byte present. -/
def Ram (a : Nat) : Prop := ramBase ≤ a ∧ a < ramBase + ramSize

/-- The fill extends the memory. -/
theorem fill_ext (m : Mem) : Ext m (fillZeroMem m) := fun _ _ h => fillZeroMem_some h

/-- **A total keep is a presence keep of the fills** at a RAM byte. -/
theorem fill_total {m m' : Mem} {a : Nat} (hr : Ram a) (h : bytesT1 m' a = bytesT1 m a) :
    (fillZeroMem m')[a]? = (fillZeroMem m)[a]? := by
  rw [fillZeroMem_ram _ hr.1 hr.2, fillZeroMem_ram _ hr.1 hr.2]
  exact congrArg some h

/-- **`Agree` from a total-read keep**: the fills agree off the region and
off RAM. -/
theorem Agree.ofTotal {R : Nat → Prop} {m m' : Mem} (h : ∀ a, ¬ R a → bytesT1 m' a = bytesT1 m a) :
    Agree (fun a => R a ∨ ¬ Ram a) (fillZeroMem m) (fillZeroMem m') := fun a ha =>
  fill_total (Classical.byContradiction fun hr => ha (.inr hr)) (h a fun hR => ha (.inl hR))

/-! ## What `HeapAt` reads, off the chunks in use -/

theorem _root_.Lua.Vm.InUse.cons {c : Chunk} {cs : List Chunk} {a : Nat} (h : InUse (c :: cs) a) :
    (c.inuse = true ∧ c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8) ∨ InUse cs a := by
  obtain ⟨d, hd, h1, h2, h3⟩ := h
  rcases List.mem_cons.1 hd with rfl | hd
  · exact .inl ⟨h1, h2, h3⟩
  · exact .inr ⟨d, hd, h1, h2, h3⟩

theorem ChunkWalk.size32 {m : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → ∀ c ∈ cs, 32 ≤ c.size
  | _, _, _, .top => fun _ h => absurd h List.not_mem_nil
  | _, _, _, .chunk _ _ e3 _ _ hw => fun c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact e3
    · exact ChunkWalk.size32 hw c hc

/-- No chunk of the walk from `p` is in use below `p + 16`. -/
theorem ChunkWalk.notInUse_lo {m : Mem} {p top : Nat} {cs : List Chunk} (hw : ChunkWalk m p top cs)
    (a : Nat) (ha : a < p + 16) : ¬ InUse cs a := fun ⟨c, hc, _, h2, _⟩ => by
  have := ChunkWalk.bound hw c hc; omega

/-- No chunk of the walk to `top` is in use from `top + 8`. -/
theorem ChunkWalk.notInUse_hi {m : Mem} {p top : Nat} {cs : List Chunk} (hw : ChunkWalk m p top cs)
    (a : Nat) (ha : top + 8 ≤ a) : ¬ InUse cs a := fun ⟨c, hc, _, _, h3⟩ => by
  have := ChunkWalk.bound hw c hc; omega

/-- **A free chunk's bytes past its header**, to its successor's `prev_size`,
are no chunk's in use. -/
theorem ChunkWalk.notInUse_free {m : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs → ∀ c ∈ cs, c.inuse = false →
      ∀ a, c.addr + 8 ≤ a → a < c.addr + c.size + 8 → ¬ InUse cs a
  | _, _, _, .top => fun _ h => absurd h List.not_mem_nil
  | _, _, _, .chunk _ _ _ _ _ hw => fun c hc hf a h1 h2 hu => by
    rcases List.mem_cons.1 hc with rfl | hc
    · rcases hu.cons with ⟨hi, _, _⟩ | hu
      · rw [hf] at hi; cases hi
      · exact ChunkWalk.notInUse_lo hw a (by simp only at h2; omega) hu
    · have hb := ChunkWalk.bound hw c hc
      rcases hu.cons with ⟨_, _, h3⟩ | hu
      · simp only at h3; omega
      · exact ChunkWalk.notInUse_free hw c hc hf a h1 h2 hu

/-- **The walk across a change off its headers**: it reads no byte of a chunk
in use. -/
theorem ChunkWalk.congrU {m m' : Mem} :
    ∀ {p top : Nat} {cs : List Chunk}, ChunkWalk m p top cs →
      (∀ a, p + 8 ≤ a → a < top + 16 → ¬ InUse cs a → m'[a]? = m[a]?) → ChunkWalk m' p top cs
  | _, _, _, .top, _ => .top
  | p, top, _, .chunk (h := hd) (h' := hd') e1 e2 e3 e4 e5 hw, hk => by
    have hle := ChunkWalk.le hw
    have nlo := ChunkWalk.notInUse_lo hw
    refine .chunk ((rd64_congr fun i _ => hk _ (by omega) (by omega) fun hu => ?_).trans e1) e2 e3 e4
      ((rd64_congr fun i _ => hk _ (by omega) (by omega) fun hu => ?_).trans e5)
      (ChunkWalk.congrU hw fun a h1 h2 hu => hk a (by omega) h2 fun hu' => ?_)
    · rcases hu.cons with ⟨_, h2, _⟩ | hu
      · simp only at h2; omega
      · exact nlo _ (by omega) hu
    · rcases hu.cons with ⟨_, _, h3⟩ | hu
      · simp only at h3; omega
      · exact nlo _ (by omega) hu
    · rcases hu'.cons with ⟨_, _, h3⟩ | hu'
      · simp only at h3; omega
      · exact hu hu'

/-- A binned chunk is a free chunk of the walk. -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.binned_free {m : Mem} {top brk : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m top brk chunks bins) {i q : Nat} (h0 : 0 < i) (h1 : i < numBins)
    (hq : q ∈ bins i) : ∃ c ∈ chunks, c.addr = q ∧ c.inuse = false := by
  have hf := h.bin_free i q h0 h1 hq
  obtain ⟨c, hc, hp⟩ : ∃ c ∈ chunks, (c.addr == q && !c.inuse && (i ≤ 1 || binIndex c.size == i)) = true :=
    Classical.byContradiction fun hn => hf (List.filter_eq_nil_iff.mpr fun c hc hp => hn ⟨c, hc, hp⟩)
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  exact ⟨c, hc, hp.1.1, hp.1.2⟩

/-- **The heap across a change off what it reads but the chunks in use.** -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.congrU {m m' : Mem} {top brk : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m top brk chunks bins)
    (hk : ∀ a, HeapReads a → ¬ InUse chunks a → m'[a]? = m[a]?) : HeapAt m' top brk chunks bins := by
  have e0 : heapStart = symEnd := rfl
  have e1 : heapEnd = symHeapEnd := rfl
  have e2 : symEnd = 0x8006ecd0 := rfl
  have e3 : symHeapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e10 : topAddr = avAddr + 16 := rfl
  have e11 : avAddr = symMallocAv := rfl
  have e12 : binblocksAddr = avAddr + 8 := rfl
  have htop := ChunkWalk.le h.walk
  have hbrk := h.brk_le
  have htb := h.top_le
  have nlo := ChunkWalk.notInUse_lo h.walk
  -- below the arena: no chunk in use
  have lo : ∀ a, HeapReads a → a < heapStart → m'[a]? = m[a]? := fun a hr ha =>
    hk a hr (nlo a (by omega))
  have arena : ∀ a, heapStart ≤ a → a < heapEnd + 32 → ¬ InUse chunks a → m'[a]? = m[a]? :=
    fun a h1 h2 hu => hk a (.inl ⟨h1, h2⟩) hu
  have av : ∀ a, symMallocAv ≤ a → a < symMallocAv + 0x810 → m'[a]? = m[a]? := fun a h1 h2 =>
    lo a (.inr (.inl ⟨h1, h2⟩)) (Nat.lt_of_lt_of_le h2 (by rw [e4, e0, e2]; decide))
  refine
    { sbrk_base := (rd64_congr fun i _ => lo _ (.inr (.inr (.inl ⟨by omega, by omega⟩))) (by omega)).trans h.sbrk_base
      brk := (rd64_congr fun i _ => lo _ (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))) (by omega)).trans h.brk
      brk_le := h.brk_le
      top_ptr := (rd64_congr fun i _ => av _ (by omega) (by omega)).trans h.top_ptr
      top_le := h.top_le
      top_size := h.top_size
      top_header := (rd64_congr fun i _ => arena _ (by omega) (by omega)
        (ChunkWalk.notInUse_hi h.walk _ (by omega))).trans h.top_header
      top_pad := (rd64_congr fun i _ =>
        lo _ (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩))))) (by omega)).trans h.top_pad
      max_sbrked := by
        rw [rd64_congr fun i _ => lo _ (.inr (.inr (.inr (.inr (.inr (.inl ⟨by omega, by omega⟩)))))) (by omega)]
        exact h.max_sbrked
      mallinfo := by
        rw [rd64_congr fun i _ => lo _ (.inr (.inr (.inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))))) (by omega)]
        exact h.mallinfo
      first_prev := by
        rw [rd64_congr fun i _ => arena _ (by omega) (by omega) (nlo _ (by omega))]
        exact h.first_prev
      walk := ChunkWalk.congrU h.walk fun a h1 h2 hu => arena a (by omega) (by omega) hu
      coalesced := h.coalesced
      footer := fun c hc hf => by
        have := ChunkWalk.bound h.walk c hc
        have := ChunkWalk.size32 h.walk c hc
        rw [rd64_congr fun i _ => arena _ (by omega) (by omega)
          (ChunkWalk.notInUse_free h.walk c hc hf _ (by omega) (by omega))]
        exact h.footer c hc hf
      bins_list := fun i h0 h1 => by
        have hb : binAt i + 32 ≤ symMallocAv + 0x810 := by simp only [binAt, avAddr, numBins] at *; omega
        have hb' : symMallocAv ≤ binAt i := by simp only [binAt, avAddr]; omega
        have bl := h.bins_list i h0 h1
        exact ⟨(rd64_congr fun j _ => av _ (by omega) (by omega)).trans bl.fd,
          BinChain.congr bl.chain (fun a h2 h3 => av a (by omega) (by omega)) fun x hx a h2 h3 => by
            obtain ⟨c, hc, rfl, hf⟩ := h.binned_free h0 h1 hx
            have := ChunkWalk.bound h.walk c hc
            have := ChunkWalk.size32 h.walk c hc
            exact arena a (by omega) (by omega)
              (ChunkWalk.notInUse_free h.walk c hc hf a (by omega) (by omega))⟩
      bins_nodup := h.bins_nodup
      bin_free := h.bin_free
      free_binned := h.free_binned
      remainder := h.remainder
      binblocks_present := by
        rw [rd64_congr fun i _ => av _ (by omega) (by omega)]
        exact h.binblocks_present
      binblocks := fun bb hb => by
        rw [rd64_congr fun i _ => av _ (by omega) (by omega)] at hb
        exact h.binblocks bb hb }

/-- What `HeapAt` reads lies in RAM. -/
theorem HeapReads.ram {a : Nat} (h : HeapReads a) : Ram a := by
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  simp only [HeapReads, Ram, ramBase, ramSize] at h ⊢
  omega

/-- **`HeapAt` after a run with a total-read keep** off what it reads but
the chunks in use: it holds at the fill of the new memory. The old memory
`m` is any memory the heap is stated of (the complement `w.mo`, or a
callee's post memory); the keep is the summaries' `bytesT1` form. -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.ofTotal {m m' : Mem} {top brk : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt m top brk chunks bins)
    (hk : ∀ a, HeapReads a → ¬ InUse chunks a → bytesT1 m' a = bytesT1 m a) :
    HeapAt (fillZeroMem m') top brk chunks bins :=
  (h.ext (fill_ext m)).congrU fun a hr hu => fill_total hr.ram (hk a hr hu)

/-! ## After a stdio call -/

/-- **`HeapAt` after a stdio call**, from the stdio summaries' common keep
shape (`SfvKeep.keep_lo`, `StdoutKeep.keep_lo`, `StdoutKeepD.keep_lo`):
every byte past the callees' stack depth `d` but `stdout`, its buffer and
`errno` reads as before. The buffer is the payload of a chunk in use. -/
theorem _root_.Lua.Vm.DlHeap.HeapAt.ofStdioKeep {M m' : Mem} {top brk : Nat} {chunks : List Chunk}
    {bins : Nat → List Nat} (h : HeapAt M top brk chunks bins) {sp buf d : Nat}
    (hbuf : ∃ sz, (⟨buf - 16, sz, true⟩ : Chunk) ∈ chunks ∧ 1024 + 8 ≤ sz) (hlo : heapStart + 16 ≤ buf)
    (hsp : heapEnd + 32 + d ≤ sp)
    (hk : ∀ a, a + d ≤ sp → (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) → (a < buf ∨ buf + 1024 ≤ a) →
      (a < errnoAddr ∨ errnoAddr + 4 ≤ a) → bytesT1 m' a = bytesT1 M a) :
    HeapAt (fillZeroMem m') top brk chunks bins := by
  obtain ⟨sz, hc, hsz⟩ := hbuf
  have e2 : heapStart = 0x8006ecd0 := rfl
  have e3 : heapEnd = 0x87800000 := rfl
  have e4 : symMallocAv = 0x8005c6d0 := rfl
  have e5 : symMallocSbrkBase = 0x8005d388 := rfl
  have e6 : symBrk = 0x8005d3b8 := rfl
  have e7 : symMallocTopPad = 0x8005d3d8 := rfl
  have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e9 : symMallocMallinfo = 0x8005e560 := rfl
  have e10 : stdoutFile = 0x8005e668 := rfl
  have e11 : fileSize = 184 := rfl
  have e12 : errnoAddr = 0x8005d408 := rfl
  refine h.ofTotal fun a hr hu => hk a ?_ ?_ ?_ ?_
  · simp only [HeapReads] at hr; omega
  · simp only [HeapReads] at hr; omega
  · by_cases h1 : buf ≤ a
    · by_cases h2 : a < buf + 1024
      · exact absurd ⟨_, hc, rfl, by simp only; omega, by simp only; omega⟩ hu
      · omega
    · omega
  · simp only [HeapReads] at hr; omega

/-- **The heap after the first `fwrite`** (`StdoutSetup_Statement`'s post):
the heap the set-up granted, at the fill of the memory the loop leaves. -/
theorem SetupPost.heapAfter {m M m' : Mem} {sp src n buf brk : Nat} {chunks : List Chunk} {top' brk' : Nat}
    {chunks' : List Chunk} {bins' : Nat → List Nat} {out pend' : List (BitVec 8)}
    (P : SetupPost m M m' sp src n buf brk chunks top' brk' chunks' bins' out pend') (hsp : heapEnd + 8192 ≤ sp) :
    HeapAt (fillZeroMem m') top' brk' chunks' bins' := by
  have hd : heapEnd + 32 + 3072 ≤ sp - 112 := by
    obtain ⟨H, hH⟩ : ∃ H, heapEnd = H := ⟨_, rfl⟩
    have : H = 0x87800000 := hH ▸ rfl
    rw [hH] at hsp ⊢; omega
  exact P.grant.heap.ofStdioKeep P.grant.block P.grant.lo hd fun a h1 h2 h3 h4 =>
    (P.keep.keep_lo a h1 h2 h3 h4).trans (bytesT1_fill M a).symm

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.TolIntProof

/-!
# An allocating argument whose `luaL_tolstring` computes with bignums first (lane F1-25)

A float's `luaL_tolstring` runs `_dtoa_r` (through `snprintf(…, "%.14g", …)`)
before it interns its string: a bignum computation (`BigRun`, `Kit/BigHeap.lean`)
that changes the heap, `_REENT`'s words and the bignums `B`, within the
argument's budget (`argCost`: sixteen `_malloc_r` for a float). This file
carries `luaB_print`'s state across such a prefix and reuses the one glue
(`tolPost_of_runP`) for the rest:

* `PrStR.bigRun`: the state `PrSt` before argument `i` at `(m, H, B)` and a
  `BigRun` to `(m1, H1, B1)` give the state at `(m1, H1, B1)` with the room
  left (`PrStR`), and `stdout` with the new heap;
* `TolPost.pre`: a `TolPost` from the prefix's end is one from its start;
* `tolPost_of_split`: the glue from a run cut after its bignum prefix.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- The static words `luaB_print`'s state reads (`PrintCells`, `AllocStatic`,
`PrintStatic`) are none of the allocator's globals and none of `_REENT`'s
`_dtoa_r` words. -/
theorem printStatic_not_big {a : Nat} (h : PrintStatic a) : ¬ MallocGlobal a ∧ ¬ ReentWord a := by
  have ht : symTohost = 0x8005c6c0 := rfl
  have hat : symAtexit = 0x8005d450 := rfl
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  simp only [PrintStatic, LocaleW, Rng] at h
  simp only [MallocGlobal, ReentWord, symImpureData, reentResultOff, reentFreelistOff]
  omega

/-- `AllocStatic`'s static words likewise. -/
theorem allocStaticFoot_not_big {g a : Nat} (h : AllocStaticFoot g a) (hg : ¬ Rng g 8 a) :
    ¬ MallocGlobal a ∧ ¬ ReentWord a ∧ a < heapStart := by
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  have : heapStart = 0x8006ecd0 := rfl
  simp only [AllocStaticFoot, Rng] at h hg
  simp only [MallocGlobal, ReentWord, symImpureData, reentResultOff, reentFreelistOff]
  omega

/-- `PrintCells`' words likewise. -/
theorem printCells_keep_big {m m' : Mem} (h : PrintCells m)
    (hk : ∀ a, a < heapStart → ¬ MallocGlobal a → ¬ ReentWord a → bytesT1 m' a = bytesT1 m a) :
    PrintCells m' := by
  have hHS : heapStart = 0x8006ecd0 := rfl
  have kL : ∀ a, (0x80000000 ≤ a ∧ a < 0x8005c6d0) ∨ (0x8005d1bc ≤ a ∧ a < 0x8005d208) ∨
      (0x8005d398 ≤ a ∧ a < 0x8005d3b8) → bytesT1 m' a = bytesT1 m a := fun a ha =>
    hk a (by omega) (fun hg => by
      have : symMallocAv = 0x8005c6d0 := rfl
      have : symMallocSbrkBase = 0x8005d388 := rfl
      have : symBrk = 0x8005d3b8 := rfl
      have : symMallocMallinfo = 0x8005e560 := rfl
      have : errnoAddr = 0x8005d408 := rfl
      simp only [MallocGlobal] at hg; omega)
      (fun hr => by simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr; omega)
  exact ⟨(bytesT8_congrT fun k _ => kL _ (.inr (.inr ⟨by omega, by omega⟩))).trans h.impure,
    (bytesT8_congrT fun k _ => kL _ (.inr (.inl ⟨by omega, by omega⟩))).trans h.stdout,
    by rw [bytesAt_congr fun k hk => kL _ (.inl ⟨by omega, by omega⟩)]; exact h.tab,
    by rw [bytesAt_congr fun k hk => kL _ (.inl ⟨by omega, by omega⟩)]; exact h.nl⟩

section BigRun

variable {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
  {D G B FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {i rm rm' c : Nat} {ph : StdoutPh}
  {H H1 : HeapIx} {m m1 : Mem} {B1 F : Nat → Prop}

/-- **A byte `luaB_print`'s caller holds is no new bignum's.** -/
theorem PrStR.not_big1 (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0)
    (hS : PrStR L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n rm ph H m)
    (hR : BigRun F m m1 H H1 B B1 c) {a : Nat} (hx : PrX L nci g func n sl G a) : ¬ B1 a :=
  hR.apart ((hIn.prX_kept hx).imp (fun hk => (hS.kept hk).inuse) id) (hS.bigIn.x a · hx)

/-- **A kept byte off the bignums survives the prefix.** -/
theorem BigRun.keepK (hR : BigRun F m m1 H H1 B B1 c) (hF : ∀ a, F a → heapEnd ≤ a) {a : Nat}
    (hk : Kept H ph a) (hB : ¬ B a) : bytesT1 m1 a = bytesT1 m a :=
  hR.keep_inUse hk.inuse hk.lo hB fun hf => absurd (hF a hf) (Nat.not_le.mpr hk.hi)

/-- **`luaB_print`'s state across a bignum computation** (lane F1-25): the
state before argument `i` at `(m, H, B)` and a `BigRun` to `(m1, H1, B1)`
within the room (`rm' + c ≤ rm`) give the state at `(m1, H1, B1)` with the room
`rm'`, the literals' facts, the table's safety and what the caller holds kept
(all in chunks in use apart from `B`, or static words off the allocator's),
the new bignums where the old ones were or fresh. -/
theorem PrStR.bigRun (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0)
    (hS : PrStR L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n rm ph H m) (hP : PrintSt m ph H)
    (hR : BigRun F m m1 H H1 B B1 c) (hF : ∀ a, F a → heapEnd ≤ a) (hc : rm' + c ≤ rm) (hpos : 0 < rm') :
    PrStR L nci func tbc sl g n ls args D G B1 FL M0 ph0 H0 i n rm' ph H1 m1 ∧ PrintSt m1 ph H1 := by
  have hp := hIn.placed
  have hl := hS.lits
  have hHS : heapStart = 0x8006ecd0 := rfl
  have hHE : heapEnd = 0x87800000 := rfl
  have hkept := hR.kept
  have hbf : BufFrom ph ph H := fun _ h => .inl h
  have kK : ∀ a, Kept H ph a → ¬ B a → bytesT1 m1 a = bytesT1 m a := fun a hk hb => hR.keepK hF hk hb
  have k0 : ∀ a, Kept H0 ph0 a → PrX L nci g func n sl G a → bytesT1 m1 a = bytesT1 m a := fun a hk hx =>
    kK a (hS.kept hk) (hS.bigIn.x a · hx)
  have kS : ∀ a, a < heapStart → ¬ MallocGlobal a → ¬ ReentWord a → bytesT1 m1 a = bytesT1 m a :=
    fun a h1 h2 h3 => hR.keep_static (fun a hb => (hS.bigIn.inK a hb).lo) h1 h2 h3 fun hf => by
      have := hF a hf; omega
  have kFL : ∀ a, FL a → bytesT1 m1 a = bytesT1 m a := fun a ha =>
    kK a (hl.kept a ha) fun hb => hS.big_fl a hb ha
  -- `g`'s words: in chunks in use, held by the caller
  have kg : ∀ a, g ≤ a → a < g + gEnd → bytesT1 m1 a = bytesT1 m a := fun a h1 h2 =>
    k0 a (hIn.g_in a h1 h2) (.inr (.inr (.inl ⟨h1, h2⟩)))
  have kT : ∀ a, g + gStrtNuseOff ≤ a → a < g + gStrtNuseOff + 8 → bytesT1 m1 a = bytesT1 m a := fun a h1 h2 =>
    kg a (by simp only [gStrtNuseOff] at h1; omega)
      (by simp only [gStrtNuseOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at h2 ⊢; omega)
  have hn' : strtNuse m1 g = strtNuse m g := by
    simp only [strtNuse]; congr 1
    exact bytesT4_congrT fun j hj => kT _ (by omega) (by omega)
  have hz : strtSize m1 g = strtSize m g := by
    simp only [strtSize, gStrtSizeOff]; congr 1
    exact bytesT4_congrT fun j hj => kT _ (by simp only [gStrtNuseOff]; omega) (by simp only [gStrtNuseOff]; omega)
  have kA : ∀ a, AllocStaticFoot g a → bytesT1 m1 a = bytesT1 m a := fun a ha => by
    by_cases hgr : Rng g 8 a
    · have h8 : (8 : Nat) ≤ gEnd := by decide
      exact kg a hgr.1 (by have := hgr.2; omega)
    · obtain ⟨h1, h2, h3⟩ := allocStaticFoot_not_big ha hgr
      exact kS a h3 h1 h2
  -- a fresh byte is in no chunk in use at `H`
  have fK : ∀ a, Fresh H H1 a → Kept H ph a → False := fun a hf hk => hf.2.1 hk.inuse
  have hroom : H1.brk + rm' + stdoutNeed ph ≤ heapEnd := by
    have h1 := hS.room (by omega)
    have h2 := hR.brk
    omega
  refine ⟨⟨?_, ?_, ?_, hS.buf, fun c hc hu => hkept c (hS.chunks c hc hu) hu, fun _ => hroom,
    by rw [hn', hz]; exact hS.strt, ?_, hS.gc, fun h => (hS.stat h).congr kA, hR.big, ?_, ?_⟩, ?_⟩
  · -- the API frame: `L`'s words and the C `CallInfo`'s
    refine hS.api.congrT fun a ha => ?_
    rcases ha with h | h | h | h
    all_goals first
      | exact k0 a (hIn.L_in a (by simp only [Rng] at h; omega) (by simp only [Rng, stateSize] at h ⊢; omega))
          (.inr (.inl (by simp only [Rng, stateSize] at h ⊢; omega)))
      | exact k0 a (hIn.nci_in a (by simp only [Rng] at h; omega) (by simp only [Rng, ciSize] at h ⊢; omega))
          (.inr (.inr (.inr (.inr (.inl (by simp only [Rng, ciSize] at h ⊢; omega))))))
  · -- the literals
    exact ⟨hl.facts.trans kFL, fun a ha => (hl.kept a ha).mono hkept hbf, hl.apart,
      fun ts hts a h1 h2 => (hl.strs ts hts a h1 h2).mono hkept hbf, hl.marks,
      hl.cache.congr fun a h1 h2 => kg a (by simp only [gStrcacheOff] at h1; omega) h2,
      TabFoot.trans hl.tab kFL⟩
  · -- what the state keeps of the entry
    intro a ha
    refine (?_ : bytesT1 m1 a = bytesT1 m a).trans (hS.keep a ha)
    have hrb : Image.rodataBase = 0x8004ecc8 := rfl
    have hrs : Image.rodataSize = 55776 := rfl
    have ht : symTohost = 0x8005c6c0 := rfl
    have hx : PrX L nci g func n sl G a := .inl ha
    rcases ha with h | h | h | h | h | h | h
    · rcases hIn.keep_in a h with hk | hst
      · exact k0 a hk hx
      · obtain ⟨n1, n2⟩ := printStatic_not_big hst
        exact kS a (by simp only [PrintStatic, Rng, LocaleW, symAtexit, symImpurePtr] at hst; omega) n1 n2
    · exact k0 a (hIn.stack_in a (by simp only [ArgSlot] at h; omega)
        (by simp only [ArgSlot] at h; have := hp.room; omega)) hx
    · exact kS a (by omega) (fun hg => by
          have : symMallocAv = 0x8005c6d0 := rfl
          have : symMallocSbrkBase = 0x8005d388 := rfl
          have : symBrk = 0x8005d3b8 := rfl
          have : symMallocMallinfo = 0x8005e560 := rfl
          have : errnoAddr = 0x8005d408 := rfl
          simp only [MallocGlobal] at hg; omega)
        (fun hr => by simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr; omega)
    all_goals first
      | exact kg a (by simp only [Rng, gGcstpOff, gMtOff] at h; omega)
          (by simp only [Rng, gGcstpOff, gMtOff, gEnd, gStrcacheOff, strcacheN, strcacheM] at h ⊢; omega)
      | exact k0 a (hIn.L_in a (by simp only [Rng, stateGOff, stateHookmaskOff] at h; omega)
          (by simp only [Rng, stateGOff, stateHookmaskOff, stateSize] at h ⊢; omega)) hx
  · -- the table's safety, at the new bignums
    refine (hS.safe.trans kFL).conseq fun M hM rt hrt => (hM rt hrt).weaken (fun a ha => ha.mono hkept hbf)
      (fun a ha hx => hx.imp id fun hb => ?_) fun a ha hw => hw.imp (fun hb => ?_) id
    · exact (hR.sub a hb).resolve_right fun hf => fK a hf ha
    · exact (hR.sub a hb).resolve_right fun hf => fK a hf ha
  · -- where the new bignums lie
    refine ⟨fun a hb => ?_, fun a hb hx => PrStR.not_big1 hIn hS hR hx hb, fun ts hts a h1 h2 hb => ?_⟩
    · rcases hR.sub a hb with hb0 | hf
      · exact (hS.bigIn.inK a hb0).mono hkept hbf
      · exact ⟨hf.1, hf.2.2.1, hf.2.2.2, fun hbuf => hf.2.1 (hP.io.buf_inUse hbuf)⟩
    · rcases hR.sub a hb with hb0 | hf
      · exact hS.bigIn.lit ts hts a h1 h2 hb0
      · exact fK a hf (hl.strs ts hts a h1 h2)
  · intro a hb hfl
    rcases hR.sub a hb with hb0 | hf
    · exact hS.big_fl a hb0 hfl
    · exact fK a hf (hl.kept a hfl)
  · -- `stdout` with the new heap
    refine ⟨hP.io.congrA (fun a ha => ?_) (fun hn => ?_) fun buf hb => ?_, hR.heap, printCells_keep_big hP.cells kS⟩
    · rcases ha with ha | hb
      · have hlt := stdioGlob_lt ha.1
        exact kS a hlt (fun hg => ha.2 (hg.alloc ha.1)) fun hr => ha.2 (ReentWord.alloc hr)
      · have hu := hP.io.buf_inUse hb
        exact hR.keep_inUse hu (by have := hP.io.buf_lo a hb; omega)
          (fun hb' => (hS.bigIn.inK a hb').nbuf hb) fun hf => by
            have := hF a hf; have := hP.io.buf_hi a hb; omega
    · have h2 := hR.brk
      have h1 := hS.room (by omega)
      cases ph with
      | up buf pend => exact absurd rfl (hn buf pend)
      | boot => simp only [stdoutNeed] at hroom; omega
      | fresh => simp only [stdoutNeed] at hroom; omega
    · obtain ⟨sz, hc, hs⟩ := hb.block
      exact ⟨⟨sz, hkept _ hc rfl, hs⟩, hb.lo, hb.hi⟩

end BigRun

/-- **A `TolPost` from the end of a prefix is one from its start**, the
prefix keeping the chunks in use and `luaB_print`'s frame. -/
theorem TolPost.pre {sp0 n : Nat} {S : Nat → StdoutPh → HeapIx → Mem → Prop} {b : List (BitVec 8)}
    {ph : StdoutPh} {m m1 m' : Mem} {s : Nat} {H H1 H' : HeapIx} (h : TolPost sp0 n S b ph m1 m' s H1 H')
    (hk : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H1.chunks)
    (hf : ∀ a, sp0 - 64 ≤ a → bytesT1 m1 a = bytesT1 m a) : TolPost sp0 n S b ph m m' s H H' :=
  { h with
    kept := fun c hc hu => h.kept c (hk c hc hu) hu
    frame := fun a h1 h2 => (h.frame a h1 h2).trans (hf a h1) }

/-- (lane F1-25) **The glue from an allocating argument's `luaL_tolstring`
cut after a bignum prefix** (a float's `_dtoa_r`): the prefix `hpre` from the
entry at `(m, H, B)` reaches the configurations `Q m1 H1 B1` after a
`BigRun` within the argument's budget beyond its string (`c`), its frames `F`
below `luaB_print`'s; the rest `hrun` from there interns the string as
`tolPost_of_runP` takes it, at the state the prefix leaves (`PrStR.bigRun`). -/
theorem tolPost_of_split {sp0 L nci func n tbc sl g : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G B FL : Nat → Prop} {ph0 : StdoutPh} {H0 : HeapIx} {M0 : Mem} {i c : Nat} {v : Value}
    {b : List UInt8} {ph : StdoutPh} {H : HeapIx} {m : Mem} {o : Array String} {r : BitVec 64} {f : AbiFrame}
    {F : Nat → Prop} {Q : Mem → HeapIx → (Nat → Prop) → Config → Prop}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G B FL M0 ph0 H0 i n ph H m) (hP : PrintSt m ph H)
    (hv : args[i - 1]? = some v) (hcls : ArgStr v b) (hi1 : 1 ≤ i)
    (hc : 16384 + 4096 + 128 + c ≤ argCost v) (hF : ∀ a, F a → heapEnd ≤ a ∧ a < sp0 - 64)
    (hpre : Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 i⟩, ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c' => ∃ m1 H1 B1, BigRun F m m1 H H1 B B1 c ∧ Q m1 H1 B1 c'))
    (hrun : ∀ m1 H1 B1, BigRun F m m1 H H1 B B1 c → ∀ (K X W : Nat → Prop) (cw : BitVec 8)
      (size hash head d nuse : Nat), NlTab m1 L g (func + 16 * n + 16) b ls.seed K X W cw size hash head d nuse H1 →
      Triple (Q m1 H1 B1)
        (fun c' => ∃ ts M3 M H', PfStr m1 M3 (TolFr (sp0 - 64)) g b ls.seed K X W size hash nuse head H1 ts H' ∧
          PfPost M3 M (sp0 - 64 - 48) L g (func + 16 * n + 16) ts ∧
          wrRet r (sp0 - 64) (ts + 24) f (writeMap8 M (sp0 - 56) (sdData_val (BitVec.ofNat 64 b.length))) o c')) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c' => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c' ∧
        TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (argBytes v) ph m m' s H H') := by
  intro c0 h0
  obtain ⟨c1, s1, m1, H1, B1, hR, hq⟩ := hpre c0 h0
  have hcost := prCost_succ hi1 hv
  have hF' : ∀ a, F a → heapEnd ≤ a := fun a ha => (hF a ha).1
  obtain ⟨hS1, hP1⟩ := hS.bigRun hIn hP hR hF'
    (rm' := 16384 + 4096 + 128 + prCost args (i + 1)) (by omega) (by omega)
  obtain ⟨c2, s2, m', s, H', hret, hpost⟩ :=
    tolPost_of_runP hIn hn hS1 hP1 (Nat.le_refl _) hv hcls hi1 (hrun m1 H1 B1 hR) c1 hq
  refine ⟨c2, s1.trans s2, m', s, H', hret, hpost.pre hR.kept fun a ha => hR.keep a fun hw => ?_⟩
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  rcases hw with hw | hw | hw | hw
  · rcases hw with hg | ⟨-, h2, -⟩
    · have := hg.lt; have : heapStart = 0x8006ecd0 := rfl; omega
    · omega
  · have := (hS.bigIn.inK a hw).hi; omega
  · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hw; omega
  · have := (hF a hw).2; omega

end Lua.Vm.Sim.Kit

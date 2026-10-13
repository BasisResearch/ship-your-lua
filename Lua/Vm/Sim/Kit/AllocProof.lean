import Lua.Vm.Sim.Kit.AllocHeap
import VsaIris.Vsa.FreeRunAll
import VsaIris.Vsa.SWPReach

/-!
# `_malloc_r` and `_free_r` at the Lua ELF's addresses (lane F1-A0-M)

**`mallocR_proved : MallocR_Statement`** and **`freeR_proved :
FreeR_Statement`**, the two allocator premises of `Kit.CallOpen`.

The instruction-level proofs are ship-your-interpreter's dlmalloc proofs
ported to the Lua ELF (`VsaIris/Vsa/{Heap,Malloc,Free}*.lean`: relocated by
`experiments/port/alloc/`, with `_malloc_r`'s and `_malloc_trim_r`'s inserted
`auipc` steps, the break bound `MBrk` and the precise `Starved`), on the SWP
route over the generated step tables (`VsaIris.Vsa.AllocSteps`). This file
instantiates them at a Lua call and lands the run on the Lua route's segment
states:

1. the context (`base`): the ledger is every chunk in use (`inuseBlocks`;
   for `_free_r`, all but the freed one), the owned bytes the window `MWin`
   (the allocator's globals, the arena off the ledger, 256 bytes of stack), the
   tracking memory the zero fill of the machine memory (the heap is stated of
   it);
2. the end condition `MQ`/`FQ` (what `MRet`/`FRet` leave, read at the owned
   values), the entry `MEntry`/`FEntry` from the call's pins, the heap
   `MHeap`/`FHeap` from `AllocHeap.heapV`;
3. `malloc_all`/`free_body` give the symbolic run, `LocalRun.reach`
   (`VsaIris/Vsa/SWPReach.lean`) the machine run with exact frames;
4. the return segment state and the post (`MallocPost`, `FreeR`'s keep).
-/

namespace Lua.Vm.Sim.Kit.AllocProof

open LeanRV64DExecutable Vsa Vsa.Sim
open Vsa.Machine (MState Config Steps)
open Lua.Vm Lua.Vm.Layout Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Vm.Sim.Kit.AllocHeap
open VsaIris VsaIris.Sym VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast

/-! ## The allocator's code in the image -/

/-- Every byte of the allocator's code is the image's `.text` byte. -/
theorem allocText_image : allocText.all (fun p =>
    decide (Image.textBase ≤ p.1 ∧ p.1 < Image.textBase + Image.textSize) &&
      Image.textByte (p.1 - Image.textBase) == p.2) = true := by decide +kernel

theorem allocText_at {p : Nat × BitVec 8} (hp : p ∈ allocText) :
    Image.textBase ≤ p.1 ∧ p.1 < Image.textBase + Image.textSize ∧
      Image.textByte (p.1 - Image.textBase) = p.2 := by
  have := List.all_eq_true.1 allocText_image p hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem allocText_loaded {m : Mem} (h : Arms.TextLoaded m) {p : Nat × BitVec 8} (hp : p ∈ allocText) :
    m[p.1]? = some p.2 := by
  obtain ⟨h1, h2, h3⟩ := allocText_at hp
  have := h (p.1 - Image.textBase) (by omega)
  rwa [Nat.add_sub_cancel' h1, h3] at this

theorem allocText_lt {p : Nat × BitVec 8} (hp : p ∈ allocText) : p.1 < 0x8004ecc8 := by
  have := (allocText_at hp).2.1
  have e1 : Image.textBase = 0x80000000 := rfl
  have e2 : Image.textSize = 322760 := rfl
  omega

/-! ## The window -/

theorem foot_ram {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) :
    Densify.ramBase ≤ a ∧ a < Densify.ramBase + Densify.ramSize := by
  have e1 : Densify.ramBase = 0x80000000 := rfl
  have e2 : Densify.ramSize = 0x08000000 := rfl
  rcases h with h | ⟨h1, h2, _⟩
  · unfold allocGlobal InRange at h; omega
  · unfold Vsa.Sim.DlHeap.heapStart at h1; unfold Vsa.Sim.DlHeap.heapEnd at h2; omega

theorem fill_pres {m : Mem} {H : List (Nat × Nat)} {a : Nat} (h : vsaFoot H a) :
    ((Densify.fillZeroMem m)[a]?).isSome := by
  rw [Densify.fillZeroMem_get, if_pos (foot_ram h)]; rfl

theorem fill_img (m : Mem) (a : Nat) : imgM (Densify.fillZeroMem m) a = (m[a]?).getD 0 := by
  unfold imgM; rw [Densify.fillZeroMem_get]; split <;> simp

/-- The stack window of a call above the heap is off the footprint. -/
theorem win_disj {H : List (Nat × Nat)} {sp a : Nat} (hsp : Lua.Vm.DlHeap.heapEnd + 1024 ≤ sp)
    (h1 : sp - 256 ≤ a) : ¬ vsaFoot H a := by
  have e : Lua.Vm.DlHeap.heapEnd = 0x87800000 := rfl
  rintro (h | ⟨_, h2, _⟩)
  · unfold allocGlobal InRange at h; omega
  · unfold Vsa.Sim.DlHeap.heapEnd at h2; omega

/-- A byte off the allocator's globals, off the arena but the ledger, and off
the 1 KiB of stack the statements allow, is off the window. -/
theorem not_win {H : List (Nat × Nat)} {sp a : Nat} (hg : ¬ MallocGlobal a)
    (ha : a < Lua.Vm.DlHeap.heapStart ∨ Lua.Vm.DlHeap.heapEnd ≤ a ∨ ∃ e ∈ H, InExt e a)
    (hs : a + 1024 ≤ sp ∨ sp ≤ a) (hsp : sp < 2 ^ 64) : ¬ MWin H (BitVec.ofNat 64 sp) a := by
  have hs' : (BitVec.ofNat 64 sp).toNat = sp := by rw [BitVec.toNat_ofNat]; omega
  rintro (h | ⟨h1, h2⟩)
  · rcases h with h | ⟨h1, h2, h3⟩
    · exact hg ((allocGlobal_iff a).1 h)
    · rcases ha with ha | ha | ⟨e, he, hin⟩
      · exact absurd h1 (by rw [heapStart_eq]; omega)
      · exact absurd h2 (by rw [heapEnd_eq]; omega)
      · exact h3 e he hin
  · rw [hs'] at h1 h2; unfold mHead at h1; omega

/-- The code is off the window of a call above the heap. -/
theorem low_off {H : List (Nat × Nat)} {s : BitVec 64} (hs : 0x87800000 ≤ s.toNat) {a : Nat}
    (ha : a < 0x8004ecc8) : ¬ MWin H s a := by
  rintro ((h | ⟨h1, _⟩) | ⟨h1, _⟩)
  · unfold allocGlobal InRange at h; omega
  · unfold Vsa.Sim.DlHeap.heapStart at h1; omega
  · unfold mHead at h1; omega

/-! ## The ledger -/

/-- A heap holds for any sub-ledger. -/
theorem _root_.VsaIris.VsaHeap.PHeapAt.subLedger {m : Mem} {L L' : List (Nat × Nat)} {top brkv : Nat} {cs : List VC}
    {bins : Nat → List Nat} (h : PHeapAt m L top brkv cs bins) (hs : ∀ e ∈ L', e ∈ L) :
    PHeapAt m L' top brkv cs bins :=
  ⟨⟨{ h.heap.heap with
      live := fun e he => h.heap.heap.live e (hs e he)
      exact := fun e he _ => h.heap.heap.exact e (hs e he) (hs e he) }, h.heap.top_room⟩,
    h.brk_page, h.bb_lt⟩

/-- The chunks in use of a Lua heap, as the ledger. -/
theorem kept_of {m : Mem} {top brk : Nat} {cs : List LC} {bins : Nat → List Nat}
    (hh : Lua.Vm.DlHeap.HeapAt m top brk cs bins) {B : MCtx} (hH : B.H = inuseBlocks (cs.map toV))
    (hM : B.Mt0 = m) {cs' : List VC} (hl : LiveKeep B cs') : ∀ c ∈ cs, c.inuse = true → c ∈ cs'.map toL := by
  intro c hc hu
  have he : (c.addr + 16, c.size - 8) ∈ B.H :=
    hH ▸ mem_inuseBlocks.2 ⟨toV c, List.mem_map_of_mem hc, hu, rfl⟩
  obtain ⟨h0, hr, hs, _⟩ := walk_header (walkV hh.walk) (toV c) (List.mem_map_of_mem hc)
  have := hl _ he h0 (by rw [hM, show c.addr + 16 - 8 = (toV c).addr + 8 by simp [toV]]; exact hr)
  refine mem_map_toL.2 ?_
  have e : (⟨c.addr + 16 - 16, Vsa.Sim.DlHeap.chunkSize h0, true⟩ : VC) = toV c := by
    obtain ⟨a, s, u⟩ := c; simp only at hu; subst hu; simp only [toV] at hs ⊢; rw [hs]; simp
  rwa [e] at this

/-! ## Registers at a call and at its return -/

theorem vsaReg_of_get {c : Config} {k : Nat} (hk1 : 1 ≤ k) (hk : k ≤ 31) {v : BitVec 64}
    (h : gprGet c.σ k = some v) : vsaReg c k = v := by
  rw [vsaReg_gpr (by unfold VsaIris.PC; omega), h]; rfl

theorem pc_of_vsaReg {live : Nat → Prop} {c : Config} (hok : VsaOk live c) {v : BitVec 64}
    (h : vsaReg c VsaIris.PC = v) : c.σ.regs.get? Register.PC = some v := by
  obtain ⟨w, hw⟩ := hok.good.PC
  have : pcVal c.σ = v := h
  unfold pcVal at this; rw [hw] at this ⊢; exact congrArg some this

theorem vsaReg_pc {c : Config} {v : BitVec 64} (h : c.σ.regs.get? Register.PC = some v) :
    vsaReg c VsaIris.PC = v := by
  show pcVal c.σ = v
  unfold pcVal; rw [h]; rfl

/-- The callee-saved pins at the return: `s0-s3` restored, `s4-s11` never owned. -/
theorem ret_pins {live : Nat → Prop} {c c' : Config} (hok' : VsaOk live c') {f : AbiFrame}
    (hf : PinsHold c.σ f.pins) (hregs : ∀ k, k ∉ aRegs → vsaReg c' k = vsaReg c k)
    (h8 : gprGet c'.σ 8 = some f.s0) (h9 : gprGet c'.σ 9 = some f.s1)
    (h18 : gprGet c'.σ 18 = some f.s2) (h19 : gprGet c'.σ 19 = some f.s3) : PinsHold c'.σ f.pins := by
  simp only [AbiFrame.pins, PinsHold] at hf ⊢
  obtain ⟨-, -, -, -, g20, g21, g22, g23, g24, g25, g26, g27, -⟩ := hf
  have keep : ∀ k, k ∉ aRegs → 1 ≤ k → k ≤ 31 → ∀ v, gprGet c.σ k = some v → gprGet c'.σ k = some v :=
    fun k hk h1 h31 v hv => gprGet_eq_of_vsaReg hok' h1 h31 ((hregs k hk).trans (vsaReg_of_get h1 h31 hv))
  exact ⟨h8, h9, h18, h19,
    keep 20 (by decide) (by decide) (by decide) _ g20, keep 21 (by decide) (by decide) (by decide) _ g21,
    keep 22 (by decide) (by decide) (by decide) _ g22, keep 23 (by decide) (by decide) (by decide) _ g23,
    keep 24 (by decide) (by decide) (by decide) _ g24, keep 25 (by decide) (by decide) (by decide) _ g25,
    keep 26 (by decide) (by decide) (by decide) _ g26, keep 27 (by decide) (by decide) (by decide) _ g27,
    trivial⟩

/-- The callee-saved registers at the call, read off its pins. -/
theorem frame_regs {c : Config} {f : AbiFrame} (hf : PinsHold c.σ f.pins) :
    vsaReg c 8 = f.s0 ∧ vsaReg c 9 = f.s1 ∧ vsaReg c 18 = f.s2 ∧ vsaReg c 19 = f.s3 := by
  simp only [AbiFrame.pins, PinsHold] at hf
  obtain ⟨g8, g9, g18, g19, -⟩ := hf
  exact ⟨vsaReg_of_get (c := c) (k := 8) (by decide) (by decide) g8, vsaReg_of_get (c := c) (k := 9) (by decide) (by decide) g9,
    vsaReg_of_get (c := c) (k := 18) (by decide) (by decide) g18, vsaReg_of_get (c := c) (k := 19) (by decide) (by decide) g19⟩

/-- The payload of a return: the code kept, the memory, the console, the registers. -/
theorem ret_pay {live : Nat → Prop} {c c' : Config} {pcv : BitVec 64} {L : List Pin} {m : Mem}
    {o : Array String} (h : SegSt pcv L (ArmPay m o) c) (hok' : VsaOk live c')
    (hmem : ∀ a, a < 0x8004ecc8 → c'.σ.mem[a]? = c.σ.mem[a]?)
    (hout : c'.σ.sailOutput = c.σ.sailOutput) : ArmPay c'.σ.mem o c'.σ := by
  refine ⟨fun off hoff => ?_, rfl, hout.trans h.armOut, ⟨hok'.gpr, hok'.htifIdle⟩⟩
  have e1 : Image.textBase = 0x80000000 := rfl
  have e2 : Image.textSize = 322760 := rfl
  rw [hmem _ (by omega)]
  exact h.armText off hoff

/-! ## The run at a call -/

/-- The allocator's live bytes: its code. -/
def liveA (a : Nat) : Prop := ∃ p ∈ allocText, p.1 = a

theorem allocLive : AllocLive liveA := fun p hp => ⟨p, hp, rfl⟩

/-- The configuration at a call satisfies the model's invariant. -/
theorem vsaOk_call {c : Config} {pcv : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    (h : SegSt pcv L (ArmPay m o) c) : VsaOk liveA c :=
  ⟨h.good, h.tick, h.armOk.gpr, fun a ⟨p, hp, e⟩ => by
    subst e; rw [allocText_loaded (h.armMem ▸ h.armText) hp]; rfl, h.armOk.htifIdle⟩

/-- The read-only cells at a call: `gp` and the code. -/
theorem roHolds_call {c : Config} {pcv : BitVec 64} {L : List Pin} {m : Mem} {o : Array String}
    (h : SegSt pcv L (ArmPay m o) c) (hgp : gprGet c.σ 3 = some (BitVec.ofNat 64 symGlobalPointer)) :
    ROHolds (vsaModel liveA) c roR allocText := by
  refine ⟨fun p hp => ?_, fun p hp => ?_⟩
  · simp only [roR, List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact (vsaReg_of_get (by decide) (by decide) hgp).trans (by decide)
  · show (c.σ.mem[p.1]?).getD 0 = p.2
    rw [allocText_loaded (h.armMem ▸ h.armText) hp]; rfl

/-- The context of a call (`Q` replaced by `mctx`/`fctx`). -/
def base (H : List (Nat × Nat)) (n r s : BitVec 64) (rv0 : Nat → BitVec 64) (Mt0 : Mem)
    (top0 brk0 : Nat) : MCtx :=
  ⟨liveA, MWin H s, fun _ _ => True, H, n, r, s, rv0, Mt0, top0, brk0⟩

/-- The window's stack bound and the context's `MSp`, for a call above the heap. -/
theorem mSp_call {sp : Nat} (hsplo : Lua.Vm.DlHeap.heapEnd + 1024 ≤ sp) (hsp32 : sp ≤ 2 ^ 32)
    (hsal : sp % 16 = 0) : MSp (BitVec.ofNat 64 sp) := by
  have e : Lua.Vm.DlHeap.heapEnd = 0x87800000 := rfl
  have hs : (BitVec.ofNat 64 sp).toNat = sp := by rw [BitVec.toNat_ofNat]; omega
  refine ⟨?_, ?_, ?_⟩ <;> rw [hs]
  · unfold mHead Vsa.Sim.tohostAddr; omega
  · omega
  · exact hsal

/-- From a symbolic run at a call, the machine run with exact frames. -/
theorem reach_call {C : MCtx} {c : Config} {pcv : BitVec 64} {L : List Pin} {m : Mem}
    {o : Array String} (hc : SegSt pcv L (ArmPay m o) c) (hlive : C.live = liveA)
    (hS : C.S = MWin C.H C.s) (hs : 0x87800000 ≤ C.s.toNat) (hM : C.Mt0 = Densify.fillZeroMem m)
    (hgp : gprGet c.σ 3 = some (BitVec.ofNat 64 symGlobalPointer))
    (h : AW C.live C.S C.Q pcv (vsaReg c) C.Mt0) :
    ∃ c', RunEnd liveA aRegs (MWin C.H C.s) C.Q c c' := by
  rw [hlive, hS, hM] at h
  obtain ⟨fuel, hf⟩ := h
  have hlr := hf (vsaReg c) (fun a => (c.σ.mem[a]?).getD 0)
    ⟨vsaReg_pc hc.pcAt, fun _ _ _ => rfl, fun a _ => by
      show (c.σ.mem[a]?).getD 0 = imgM (Densify.fillZeroMem m) a; rw [fill_img, hc.armMem]⟩
  exact LocalRun.reach (fun p hp => low_off hs (allocText_lt hp)) (by decide) fuel _ _ hlr c
    (vsaOk_call hc) (roHolds_call hc hgp) (fun _ _ => rfl) (fun _ _ => rfl)

/-! ## `_malloc_r` -/

theorem brk_hi_aux {brk brk' n : Nat} (h : brk' = brk ∨ brk' ≤ brk + sbReq (physSize n)) :
    brk' ≤ brk + n + 16384 + 4096 := by
  unfold sbReq physSize at h; omega

theorem hi_aux {a s t b p n : Nat} (h1 : a + 16 = p) (h2 : n + 8 ≤ s) (h3 : a + s ≤ t)
    (h4 : t + 16 ≤ b) : p + n ≤ b := by omega


/-- The end condition's heap (named fields). -/
structure MQHeap (B : MCtx) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) (Mt : Mem) (top brkv : Nat)
    (cs : List VC) (bins : Nat → List Nat) : Prop where
  img : ∀ a, B.S a → mv a = imgM Mt a
  pres : ∀ a, vsaFoot B.H a → (Mt[a]?).isSome
  heap : PHeapAt Mt (((rv 10).toNat, B.n.toNat) :: B.H) top brkv cs bins
  live : LiveKeep B cs
  brk : MBrk B brkv

/-- **`_malloc_r`'s end condition** at the owned values it ends with. -/
structure MQ (B : MCtx) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = B.r
  sp : rv 2 = B.s
  s0 : rv 8 = B.rv0 8
  s1 : rv 9 = B.rv0 9
  s2 : rv 18 = B.rv0 18
  s3 : rv 19 = B.rv0 19
  fresh : FreshAt B.H (rv 10).toNat B.n.toNat
  align : (rv 10).toNat % 16 = 0
  heap : ∃ Mt top brkv cs bins, MQHeap B rv mv Mt top brkv cs bins

def mctx (B : MCtx) : MCtx := { B with Q := MQ B }

/-- `_malloc_r`'s obligations at the return, from `MRet`. -/
theorem mq_of_ret {B : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (h : MRet (mctx B) R Mt) :
    AW (mctx B).live (mctx B).S (mctx B).Q (mctx B).r R Mt := by
  refine swp_done fun rv mv hmt => ?_
  have hr : ∀ k ∈ aRegs, k ≠ VsaIris.PC → rv k = R k := hmt.regs
  have h10 : rv 10 = R 10 := hr 10 (by decide) (by decide)
  obtain ⟨top', brk', cs', bins', hh, _, hlive, hbrk⟩ := h.heap
  exact
    { pc := hmt.pc
      sp := (hr 2 (by decide) (by decide)).trans h.regs.sp
      s0 := (hr 8 (by decide) (by decide)).trans h.regs.s0
      s1 := (hr 9 (by decide) (by decide)).trans h.regs.s1
      s2 := (hr 18 (by decide) (by decide)).trans h.regs.s2
      s3 := (hr 19 (by decide) (by decide)).trans h.regs.s3
      fresh := h10 ▸ h.fresh
      align := h10 ▸ h.align
      heap := ⟨Mt, top', brk', cs', bins',
        { img := fun a ha => hmt.img a ha, pres := h.pres, heap := h10 ▸ hh, live := hlive,
          brk := ⟨hbrk.lo, hbrk.once⟩ }⟩ }

/-- **`_malloc_r(_REENT, n)`** (lane F1-A0-M): the premise of lanes F1-10/14,
discharged. -/
theorem mallocR_proved : MallocR_Statement := by
  intro sp n top brk chunks bins r f m o hheap hr4 hsp32 hsal hsplo hn1 hroom c hc
  have hm : c.σ.mem = m := hc.armMem
  have hpins := hc.pins
  simp only [callPre, List.cons_append, List.nil_append, PinsHold] at hpins
  obtain ⟨g10, g11, g1, g2, g3, gf⟩ := hpins
  have eE : Lua.Vm.DlHeap.heapEnd = 0x87800000 := rfl
  have eS : Lua.Vm.DlHeap.heapStart = 0x8006ecd0 := rfl
  have htop0 : Lua.Vm.DlHeap.heapStart ≤ top := (walkV hheap.walk).le
  have hHT := hheap.top_le
  have hsp64 : sp < 2 ^ 64 := by omega
  have hnN : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; omega
  have hspN : (BitVec.ofNat 64 sp).toNat = sp := by rw [BitVec.toNat_ofNat]; omega
  -- the context
  let H := inuseBlocks (chunks.map toV)
  let B := base H (BitVec.ofNat 64 n) r (BitVec.ofNat 64 sp) (vsaReg c) (Densify.fillZeroMem m) top brk
  have HV := heapV hheap
  have O : MOK (mctx B) :=
    { live := allocLive
      sp := mSp_call hsplo hsp32 hsal
      own := fun _ h => h
      ral := hr4
      ok := fun _ _ h => mq_of_ret h
      null := fun R Mt h => by
        exfalso
        have hs : Starved (mctx B) := h.starved
        have hn' : (mctx B).n.toNat = n := hnN
        have hb' : (mctx B).brk0 = brk := rfl
        simp only [Starved, hn', hb'] at hs
        unfold physSize sbReq Vsa.Sim.DlHeap.heapEnd at hs
        omega
      room := by
        have hn' : (mctx B).n.toNat = n := hnN
        have hb' : (mctx B).brk0 = brk := rfl
        rw [hn', hb']; unfold physSize sbReq Vsa.Sim.DlHeap.heapEnd; omega }
  have E : MEntry (mctx B) (vsaReg c) :=
    { ra := vsaReg_of_get (c := c) (k := 1) (by decide) (by decide) g1
      sp := vsaReg_of_get (c := c) (k := 2) (by decide) (by decide) g2
      a0 := (vsaReg_of_get (c := c) (k := 10) (by decide) (by decide) g10).trans (by decide)
      a1 := vsaReg_of_get (c := c) (k := 11) (by decide) (by decide) g11
      s0 := rfl
      s1 := rfl
      s2 := rfl
      s3 := rfl }
  have Hp : MHeap (mctx B) (mctx B).Mt0 brk (chunks.map toV) bins :=
    { heap := HV
      pres := fun _ ha => fill_pres ha
      disj := fun a h1 _ => win_disj hsplo (by
        rw [show (mctx B).s.toNat = sp from hspN] at h1; unfold mHead at h1; omega)
      frame := fun _ _ => rfl
      live := LiveKeep.of_heap HV
      brk_rel := ⟨Nat.le_refl _, .inl rfl⟩ }
  obtain ⟨c', Ed⟩ := reach_call hc rfl rfl (by show 0x87800000 ≤ (BitVec.ofNat 64 sp).toNat; omega) rfl g3
    (malloc_all O E Hp)
  obtain ⟨rv', mv', hq, hrv, hmv⟩ := Ed.post
  have hq : MQ B rv' mv' := hq
  obtain ⟨Mt, top', brk', cs', bins', HQ⟩ := hq.heap
  have hok' := Ed.ok
  -- the block
  have hHH := HQ.heap.heap.heap
  obtain ⟨cb, hcb, hcbu, hcba, hcbs⟩ := hHH.exact _ List.mem_cons_self List.mem_cons_self
  have hcbb := hHH.walk.chunk_bounds cb hcb
  replace hcba : cb.addr + 16 = (rv' 10).toNat := hcba
  have hroom' := HQ.heap.heap.top_room
  have hbt := hHH.top_le
  have hbs := hHH.walk.le
  replace hcbs : n + 8 ≤ cb.size := by rw [← hnN]; exact hcbs
  -- the heap after, through the window
  have hag : AgreeP (vsaRead (((rv' 10).toNat, B.n.toNat) :: B.H)) Mt
      (Densify.fillZeroMem c'.σ.mem) := by
    intro a ha
    have hf' : vsaFoot B.H a := vsaFoot_cons_sub a ha.1
    rw [Densify.fillZeroMem_get, if_pos (foot_ram hf')]
    have hsome := HQ.pres a hf'
    have himg := HQ.img a (.inl hf')
    rw [← hmv a (.inl hf')] at himg
    cases hx : Mt[a]? with
    | none => rw [hx] at hsome; cases hsome
    | some b => unfold imgM at himg; rw [hx] at himg; simp only [Option.getD_some] at himg; rw [himg]
  have hheap' := heapL (HQ.heap.transport_read hag)
  have hblo : brk ≤ brk' := HQ.brk.lo
  have hbonce : brk' = brk ∨ (brk' ≤ brk + sbReq (physSize n) ∧ top + physSize n + 32 ≤ brk') := by
    have := HQ.brk.once; rw [show B.n.toNat = n from hnN] at this; exact this
  have hfr : ∀ e ∈ H, ∀ a, InExt ((rv' 10).toNat, n) a → ¬ InExt e a := by
    have := hq.fresh.block.destruct.2.2.2; rw [show B.n.toNat = n from hnN] at this; exact this
  obtain ⟨s0e, s1e, s2e, s3e⟩ := frame_regs gf
  have greg : ∀ k ∈ aRegs, 1 ≤ k → k ≤ 31 → gprGet c'.σ k = some (rv' k) :=
    fun k hk h1 h31 => gprGet_eq_of_vsaReg hok' h1 h31 (hrv k hk)
  refine ⟨c', Ed.steps, c'.σ.mem, (rv' 10).toNat, top', brk', cs'.map toL, bins', ?_, ?_⟩
  · -- the return segment state
    refine ⟨hok'.good, pc_of_vsaReg hok' ((hrv _ (by decide)).trans hq.pc), ?_, hok'.good.minstret,
      hok'.tick, ret_pay hc hok' (fun a ha => Ed.mem a (low_off (by
        show 0x87800000 ≤ (BitVec.ofNat 64 sp).toNat; omega) ha)) Ed.out⟩
    simp only [PinsHold]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [BitVec.ofNat_toNat]; exact greg 10 (by decide) (by decide) (by decide)
    · exact (greg 2 (by decide) (by decide) (by decide)).trans (congrArg some hq.sp)
    · exact gprGet_eq_of_vsaReg hok' (by decide) (by decide)
        ((Ed.regs 3 (by decide)).trans (vsaReg_of_get (c := c) (k := 3) (by decide) (by decide) g3))
    · exact ret_pins hok' gf Ed.regs
        ((greg 8 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s0.trans s0e)))
        ((greg 9 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s1.trans s1e)))
        ((greg 18 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s2.trans s2e)))
        ((greg 19 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s3.trans s3e)))
  · -- the post
    exact
      { heap := hheap'
        brk_le := hblo
        brk_hi := brk_hi_aux (hbonce.imp id And.left)
        lo := by
          have h1 : Lua.Vm.DlHeap.heapStart ≤ cb.addr := hcbb.1
          exact Nat.le_trans (Nat.add_le_add_right h1 16) (Nat.le_of_eq hcba)
        hi := hi_aux hcba hcbs hcbb.2.1 hroom'
        al := hq.align
        block := ⟨cb.size, mem_map_toL.2 (by
            obtain ⟨a, s, u⟩ := cb; simp only at hcbu hcba; subst hcbu
            simp only [toV]; rw [show (rv' 10).toNat - 16 = a by rw [← hcba]; exact Nat.add_sub_cancel _ _]
            exact hcb), hcbs⟩
        fresh := fun a h1 h2 hu => by
          obtain ⟨e, he, hin⟩ := inUse_iff.1 hu
          exact hfr e he a ⟨h1, h2⟩ hin
        kept := kept_of hheap rfl rfl HQ.live
        keep := fun a hg ha hs => (Ed.mem a (not_win hg (by
            rcases ha with ha | ha | ha
            · exact .inl ha
            · exact .inr (.inl ha)
            · exact .inr (.inr (inUse_iff.1 ha))) hs hsp64)).trans (by rw [hm]) }

/-! ## `_free_r` -/

/-- **`_free_r`'s end condition** at the owned values it ends with. -/
structure FQ (B : MCtx) (rv : Nat → BitVec 64) (mv : Nat → BitVec 8) : Prop where
  pc : rv VsaIris.PC = B.r
  sp : rv 2 = B.s
  s0 : rv 8 = B.rv0 8
  s1 : rv 9 = B.rv0 9
  s2 : rv 18 = B.rv0 18
  s3 : rv 19 = B.rv0 19

def fctx (B : MCtx) : MCtx := { B with Q := FQ B }

/-- `_free_r`'s obligations at the return, from `FRet`. -/
theorem fq_of_ret {B : MCtx} {R : Nat → BitVec 64} {Mt : Mem} (h : FRet (fctx B) R Mt) :
    AW (fctx B).live (fctx B).S (fctx B).Q (fctx B).r R Mt := by
  refine swp_done fun rv mv hmt => ?_
  have hr : ∀ k ∈ aRegs, k ≠ VsaIris.PC → rv k = R k := hmt.regs
  exact
    { pc := hmt.pc
      sp := (hr 2 (by decide) (by decide)).trans h.regs.sp
      s0 := (hr 8 (by decide) (by decide)).trans h.regs.s0
      s1 := (hr 9 (by decide) (by decide)).trans h.regs.s1
      s2 := (hr 18 (by decide) (by decide)).trans h.regs.s2
      s3 := (hr 19 (by decide) (by decide)).trans h.regs.s3 }

/-- **`_free_r(_REENT, p)`** (lane F1-A0-M): the premise of lane F1-14, discharged. -/
theorem freeR_proved : FreeR_Statement := by
  intro sp p top brk chunks bins r f m o hheap hr4 hsp32 hsal hsplo ⟨sz, hcp⟩ hplo c hc
  have hm : c.σ.mem = m := hc.armMem
  have hpins := hc.pins
  simp only [callPre, List.cons_append, List.nil_append, PinsHold] at hpins
  obtain ⟨g10, g11, g1, g2, g3, gf⟩ := hpins
  have eE : Lua.Vm.DlHeap.heapEnd = 0x87800000 := rfl
  have eS : Lua.Vm.DlHeap.heapStart = 0x8006ecd0 := rfl
  have hsp64 : sp < 2 ^ 64 := by omega
  have hcb := (walkV hheap.walk).chunk_bounds (toV (⟨p - 16, sz, true⟩ : LC)) (List.mem_map_of_mem hcp)
  simp only [toV] at hcb
  have hp64 : p < 2 ^ 64 := by
    have := hheap.top_le; have := hheap.brk_le; unfold Lua.Vm.DlHeap.heapEnd at *; omega
  have hpN : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; omega
  -- the ledger: the chunks in use but the freed one
  let H := (inuseBlocks (chunks.map toV)).filter (fun e => e.1 != p)
  let B := base H (BitVec.ofNat 64 p) r (BitVec.ofNat 64 sp) (vsaReg c) (Densify.fillZeroMem m) top brk
  have hfreed : (p, sz - 8) ∈ inuseBlocks (chunks.map toV) :=
    mem_inuseBlocks.2 ⟨toV (⟨p - 16, sz, true⟩ : LC), List.mem_map_of_mem hcp, rfl, by
      simp only [toV]; rw [show p - 16 + 16 = p by omega]⟩
  have HV := (heapV hheap).subLedger (L' := (p, sz - 8) :: H) fun e he => by
    rcases List.mem_cons.1 he with rfl | he
    · exact hfreed
    · exact (List.mem_filter.1 he).1
  have hst : Starts ((p, sz - 8) :: H) := by
    have h0 := starts_inuseBlocks (walkV hheap.walk)
    refine List.nodup_cons.2 ⟨fun hmem => ?_, ?_⟩
    · obtain ⟨e, he, hep⟩ := List.mem_map.1 hmem
      have := (List.mem_filter.1 he).2
      simp [hep] at this
    · exact h0.sublist (List.Sublist.map _ List.filter_sublist)
  have O : FOK (fctx B) :=
    { live := allocLive
      sp := mSp_call hsplo hsp32 hsal
      own := fun _ h => h
      ral := hr4
      ok := fun _ _ h => fq_of_ret h }
  have E : FEntry (fctx B) p (vsaReg c) :=
    { ra := vsaReg_of_get (c := c) (k := 1) (by decide) (by decide) g1
      sp := vsaReg_of_get (c := c) (k := 2) (by decide) (by decide) g2
      a0 := (vsaReg_of_get (c := c) (k := 10) (by decide) (by decide) g10).trans (by decide)
      a1 := by rw [vsaReg_of_get (c := c) (k := 11) (by decide) (by decide) g11]; exact hpN
      s0 := rfl
      s1 := rfl
      s2 := rfl
      s3 := rfl }
  have hspN : (BitVec.ofNat 64 sp).toNat = sp := by rw [BitVec.toNat_ofNat]; omega
  have Hp : FHeap (fctx B) (fctx B).Mt0 p (sz - 8) brk (chunks.map toV) bins :=
    { heap := HV
      starts := hst
      pres := fun _ ha => fill_pres ha
      disj := fun a h1 _ => win_disj hsplo (by
        rw [show (fctx B).s.toNat = sp from hspN] at h1; unfold mHead at h1; omega)
      frame := fun _ _ => rfl }
  obtain ⟨c', Ed⟩ := reach_call hc rfl rfl (by show 0x87800000 ≤ (BitVec.ofNat 64 sp).toNat; omega) rfl g3
    (free_body O E Hp)
  obtain ⟨rv', mv', hq, hrv, -⟩ := Ed.post
  have hq : FQ B rv' mv' := hq
  have hok' := Ed.ok
  obtain ⟨s0e, s1e, s2e, s3e⟩ := frame_regs gf
  have greg : ∀ k ∈ aRegs, 1 ≤ k → k ≤ 31 → gprGet c'.σ k = some (rv' k) :=
    fun k hk h1 h31 => gprGet_eq_of_vsaReg hok' h1 h31 (hrv k hk)
  refine ⟨c', Ed.steps, c'.σ.mem, ?_, fun a hg ha hs =>
    (Ed.mem a (not_win hg (by rcases ha with ha | ha; exact .inl ha; exact .inr (.inl ha)) hs hsp64)).trans
      (by rw [hm])⟩
  refine ⟨hok'.good, pc_of_vsaReg hok' ((hrv _ (by decide)).trans hq.pc), ?_, hok'.good.minstret,
    hok'.tick, ret_pay hc hok' (fun a ha => Ed.mem a (low_off (by
      show 0x87800000 ≤ (BitVec.ofNat 64 sp).toNat; omega) ha)) Ed.out⟩
  simp only [PinsHold]
  refine ⟨?_, ?_, ?_⟩
  · exact (greg 2 (by decide) (by decide) (by decide)).trans (congrArg some hq.sp)
  · exact gprGet_eq_of_vsaReg hok' (by decide) (by decide)
      ((Ed.regs 3 (by decide)).trans (vsaReg_of_get (c := c) (k := 3) (by decide) (by decide) g3))
  · exact ret_pins hok' gf Ed.regs
      ((greg 8 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s0.trans s0e)))
      ((greg 9 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s1.trans s1e)))
      ((greg 18 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s2.trans s2e)))
      ((greg 19 (by decide) (by decide) (by decide)).trans (congrArg some (hq.s3.trans s3e)))

end Lua.Vm.Sim.Kit.AllocProof

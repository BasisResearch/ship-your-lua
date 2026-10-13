import Lua.Vm.Sim.Kit.CallOpen
import Lua.Vm.Sim.Kit.AllocProof
import Lua.Vm.AtF.ExtendCI
import Lua.Vm.Arms.Segs.Hl_alloc
import Lua.Vm.Arms.Segs.Hrealloc
import Lua.Vm.Arms.Segs.Hrealloc_r

/-!
# `luaE_extendCI` from `_malloc_r` (lane F1-14)

`luaD_precall`'s `next_ci` with `ci->next` NULL calls `luaE_extendCI(L)`:
`luaM_malloc_(L, sizeof(CallInfo), 0)` adds the size to `g->GCdebt` and calls
`g->frealloc` through a `jalr` (main.c's `l_alloc`: `realloc(NULL, 64)` →
`_realloc_r(_REENT, NULL, 64)` → the tail `j _malloc_r`), then the links
`ci->next = nci`, `nci->previous = ci`, `nci->next = NULL`, `nci->u.l.trap =
0`, and `L->nci++`.

* `lalloc_sum`: `l_alloc` to `_malloc_r` over the generated segments
  (`kit_run`), then `MallocR_Statement`;
* `extendCI_of_malloc`: the at-lemmas `Lua/Vm/AtF/ExtendCI.lean` (two roots:
  the entry, the return from `l_alloc`), the call node `lalloc_sum`, and
  `ExtPost` from `MallocPost`: the heap (`HeapAt.ofTotal` over the links,
  all in chunks in use), the keeps, `stdout`'s state (`StdoutIn.congrA`:
  the stdio state reads no allocator word, `StdioFoot`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `l_alloc(ud, NULL, 0, 64)` -/

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_zero,
    Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub, Nat.reduceAdd,
    symGlobalPointer, sext64_id, himp] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.reduceAdd,
          symGlobalPointer, sext64_id, himp, Vsa.Sim.sext_zero, BitVec.add_zero]
         decide))

/-- **`l_alloc(ud, NULL, osize, 64)`** (main.c's `g->frealloc`): `realloc`
→ `_realloc_r(_REENT, NULL, 64)` → `_malloc_r(_REENT, 64)`, whose summary
(`MallocR_Statement`) is the result. -/
theorem lalloc_sum (hM : MallocR_Statement) (sp top brk : Nat) (chunks : List Chunk) (bins : Nat → List Nat)
    (ud r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hH : HeapAt (fillZeroMem m) top brk chunks bins) (hra : r.toNat % 4 = 0) (hsp : sp ≤ 2 ^ 32)
    (hal : sp % 16 = 0) (hlo : heapEnd + 1024 ≤ sp) (hroom : brk + 64 + 16384 ≤ heapEnd)
    (himp : bytesT8 m 0x8005d398 = 0x8005d1b8#64) :
    Triple (SegSt 0x8000172c#64 (callPre [⟨Register.x10, ud⟩, ⟨Register.x11, 0x0#64⟩, ⟨Register.x12, 0x0#64⟩,
        ⟨Register.x13, 0x40#64⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m' p top' brk' chunks' bins', wrRet r sp p f m' o c ∧
        MallocPost m m' sp 64 p brk chunks top' brk' chunks' bins') := by
  intro c h
  have acc := Steps.refl c
  simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append] at h
  kit_run h acc until [0x8002fa34]
  obtain ⟨c2, s2, hq⟩ := hM sp 64 top brk chunks bins r f m o hH hra hsp hal hlo (by decide) hroom _ (by
    simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
    exact h.repin (by pins_of h))
  exact ⟨c2, acc.trans s2, hq⟩

/-! ## `luaE_extendCI(L)` -/

/-- The context of `luaE_extendCI`'s rows: `sp`, `L`, `g`, `ci`, the new
block; `ra` and the frame. -/
@[at_row] abbrev extCx (sp L g ci n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, L, g, ci, n] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- The entry's context (the block not yet allocated: a stand-in). -/
@[at_row] abbrev ext0 (sp L g ci : Nat) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  extCx (sp - 96) L g ci 0x8006ece0 0x8000acc8#64 (pcFr L f) M o

/-- The context after `l_alloc` returns the block `p`. -/
@[at_row] abbrev ext1 (sp L g ci p : Nat) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  extCx (sp - 96) L g ci p 0x8000acc8#64 (pcFr L f) m o

/-- The allocator's globals lie below the arena. -/
theorem MallocGlobal.lo {a : Nat} (h : MallocGlobal a) : a < 0x8006ecd0 := by
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  simp only [MallocGlobal] at h; omega

/-- The allocator's globals among the stdio globals are `AllocWords`. -/
theorem MallocGlobal.alloc {a : Nat} (h : MallocGlobal a) (hs : StdioGlob a) : AllocWords a := by
  have : symMallocAv = 0x8005c6d0 := rfl
  have : symMallocSbrkBase = 0x8005d388 := rfl
  have : symBrk = 0x8005d3b8 := rfl
  have : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have : symMallocMallinfo = 0x8005e560 := rfl
  have : errnoAddr = 0x8005d408 := rfl
  simp only [MallocGlobal, StdioGlob, AllocWords] at *; omega

/-- The frame `l_alloc` sees from `luaM_malloc_`: `s0 = g`, `s1 = L`, `s2 = 0`. -/
abbrev extFr (L g : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 g, BitVec.ofNat 64 L, 0x0#64, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩

/-- Two ranges, one in chunks in use and one off them, are apart. -/
theorem apart_of_use {cs : List Chunk} {x n p k : Nat} (hx : ∀ a, x ≤ a → a < x + n → InUse cs a)
    (hp : ∀ a, p ≤ a → a < p + k → ¬ InUse cs a) (hn : 0 < n) (hk : 0 < k) : x + n ≤ p ∨ p + k ≤ x := by
  by_cases h1 : x ≤ p
  · by_cases h2 : p < x + n
    · exact absurd (hx p h1 h2) (hp p (Nat.le_refl _) (by omega))
    · omega
  · by_cases h2 : x < p + k
    · exact absurd (hx x (Nat.le_refl _) (by omega)) (hp x (by omega) h2)
    · omega

/-- The stack slots `luaE_extendCI` and `luaM_malloc_` saved, read back. -/
macro "ext_slot" : tactic => `(tactic| (
  simp only [Lua.Vm.AtF.ExtendCI.m1, Lua.Vm.AtF.ExtendCI.m0, extCx, FCx.mk', List.getD_cons_zero,
    List.getD_cons_succ]
  simp (disch := omega) only [fw8_same, fw8_wm8]; try rfl))

/-- **What `luaE_extendCI` leaves**, from `_malloc_r`'s post: the new `CallInfo`
placed, the frame and the hook mask kept, and `ExtPost` (the heap with the
links, every byte off the allocator's and the links' writes, `stdout`'s state). -/
theorem ext_post {sp L ci g p top' brk' : Nat} {chunks' : List Chunk} {bins' : Nat → List Nat}
    {f : AbiFrame} {M m' : Mem} {o : Array String} {H : HeapIx}
    (hP : MallocPost (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) m' (sp - 96 - 64) 64 p H.brk H.chunks top' brk' chunks' bins')
    (hroom : H.brk + extRoom ≤ heapEnd) (hhook : bytesT4 M (L + stateHookmaskOff) = 0#32)
    (hx : ExtCx L ci g H) (hsl : heapEnd + 8192 ≤ sp - 96) :
    PcNci sp p ∧ (∀ a, sp - 96 ≤ a → a < sp → bytesT1 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 M a) ∧
      bytesT4 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) (L + 192) = 0#32 ∧ ∃ H', ExtPost M (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) sp L ci g H H' p := by
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have e3 : extRoom = 20608 := rfl
  have e4 : stateSize = 200 := rfl
  have e5 : ciSize = 64 := rfl
  have e6 : gGCdebtOff = 24 := rfl
  have e7 : symMallocAv = 0x8005c6d0 := rfl
  have e8 : symMallocSbrkBase = 0x8005d388 := rfl
  have e9 : symBrk = 0x8005d3b8 := rfl
  have e10 : symMallocTopPad = 0x8005d3d8 := rfl
  have e11 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e12 : symMallocMallinfo = 0x8005e560 := rfl
  obtain ⟨xL1, xL2, xL3, xc1, xc2, xc3, xg1, xg2, xg3, xLg, xLc, xlive⟩ := hx
  simp only [e1, e2, e3, e4, e5, e6] at xL1 xL2 xc1 xc2 xg1 xg2 xLg xLc hsl hroom
  have km1 : ∀ a, (a < sp - 160 ∨ sp - 96 ≤ a) → bytesT1 (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) a = bytesT1 M a :=
    fun a ha => AtF.bT1_congr (by
      simp only [Lua.Vm.AtF.ExtendCI.m1, List.getD_cons_zero, List.getD_cons_succ]; fs_off)
  -- the block
  have hp1 := hP.lo; have hp2 := hP.hi; have hp3 := hP.al; have hp4 := hP.brk_hi
  have hfresh : ∀ a, p ≤ a → a < p + 64 → ¬ InUse H.chunks a := hP.fresh
  have aLp := apart_of_use (fun a h1 h2 => xlive a (.inl ⟨h1, h2⟩)) hfresh (by omega) (by omega)
  have aCp := apart_of_use (fun a h1 h2 => xlive a (.inr (.inl ⟨h1, h2⟩))) hfresh (by omega) (by omega)
  have aGp := apart_of_use (fun a h1 h2 => xlive a (.inr (.inr ⟨h1, h2⟩))) hfresh (by omega) (by omega)
  simp only [e4, e5, e6] at aLp aCp aGp
  -- the memory `luaE_extendCI` leaves: its links over `_malloc_r`'s
  have kW : ∀ a, ¬ Rng (g + gGCdebtOff) 8 a → ¬ Rng (ci + ciNextOff) 8 a → ¬ (p ≤ a ∧ a < p + 64) →
      ¬ Rng (L + stateNciOff) 2 a →
      bytesT1 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 m' a := fun a h1 h2 h3 h4 => by
    simp only [Rng, gGCdebtOff, ciNextOff, stateNciOff] at h1 h2 h4
    exact AtF.bT1_congr (by
      simp only [Lua.Vm.AtF.ExtendCI.m3, ext1, extCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]; fs_off)
  have kAll : ∀ a, ¬ (MallocW H.chunks a ∨ (p ≤ a ∧ a < p + ciSize) ∨ Rng (ci + ciNextOff) 8 a ∨
      Rng (L + stateNciOff) 2 a ∨ Below (sp - 96) 4096 a ∨ Rng (g + gGCdebtOff) 8 a) →
      bytesT1 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 M a := by
    intro a ha
    simp only [not_or] at ha
    obtain ⟨hw, hn, hc, hl, hb, hgd⟩ := ha
    rw [kW a hgd hc (by rw [e5] at hn; exact hn) hl]
    have hreg : a < heapStart ∨ heapEnd ≤ a ∨ InUse H.chunks a := by
      by_cases h1 : heapStart ≤ a
      · by_cases h2 : a < heapEnd
        · exact .inr (.inr (Classical.byContradiction fun hn => hw (.inr ⟨h1, h2, hn⟩)))
        · exact .inr (.inl (by omega))
      · exact .inl (by omega)
    simp only [Below] at hb
    rw [AtF.bT1_congr (hP.keep a (fun h => hw (.inl h)) hreg (by omega))]
    exact km1 a (by omega)
  -- a byte of a chunk in use off the links
  have kIn : ∀ a, InUse H.chunks a → heapStart ≤ a → a < heapEnd → ¬ (p ≤ a ∧ a < p + 64) →
      ¬ Rng (ci + ciNextOff) 8 a → ¬ Rng (L + stateNciOff) 2 a → ¬ Rng (g + gGCdebtOff) 8 a →
      bytesT1 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 M a :=
    fun a hu h1 h2 hn hc hl hg => kAll a (by
      rintro (hw | hw | hw | hw | hw | hw)
      · rcases hw with hw | hw
        · exact absurd hw.lo (by omega)
        · exact hw.2.2 hu
      · exact hn (by rw [e5] at hw; exact hw)
      · exact hc hw
      · exact hl hw
      · simp only [Below] at hw; omega
      · exact hg hw)
  -- a byte off the arena, the allocator's globals and the frame
  have kOff : ∀ a, (a < heapStart ∨ sp - 96 ≤ a) → ¬ MallocGlobal a →
      bytesT1 (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 M a :=
    fun a ha hmg => kAll a (by
      simp only [Rng, Below, ciNextOff, stateNciOff, gGCdebtOff]
      rintro (hw | hw | hw | hw | hw | hw)
      · rcases hw with hw | hw
        · exact hmg hw
        · omega
      all_goals omega)
  -- the heap
  have mono : ∀ a, InUse H.chunks a → InUse chunks' a := fun a ⟨c, hc, hu, h1, h2⟩ =>
    ⟨c, hP.kept c hc hu, hu, h1, h2⟩
  obtain ⟨sz, hblk, hsz⟩ := hP.block
  have nin : ∀ a, p ≤ a → a < p + 64 → InUse chunks' a := fun a h1 h2 =>
    ⟨_, hblk, rfl, by simp only; omega, by simp only; omega⟩
  have hH3 : HeapAt (fillZeroMem (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o))) top' brk' chunks' bins' :=
    hP.heap.ofTotal fun a _ hu => by
      rw [kW a (fun h => hu (mono a (xlive a (.inr (.inr h)))))
        (fun h => hu (mono a (xlive a (.inr (.inl (by simp only [Rng, ciNextOff] at h ⊢; omega))))))
        (fun h => hu (nin a h.1 h.2))
        (fun h => hu (mono a (xlive a (.inl (by simp only [Rng, stateNciOff] at h ⊢; omega))))),
        bytesT1_fill]
  -- `stdout`'s buffer in a chunk in use
  have bufU : ∀ ph, PrintSt M ph H → ∀ a, ph.Buf a → InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd := by
    intro ph hPS a ha
    cases hPS.io with
    | boot => exact absurd ha (by simp only [StdoutPh.Buf]; exact id)
    | fresh => exact absurd ha (by simp only [StdoutPh.Buf]; exact id)
    | up _ _ hb _ =>
      obtain ⟨sz, hc, hs⟩ := hb.block
      have := hb.lo; have := hb.hi
      simp only [StdoutPh.Buf, Rng] at ha
      exact ⟨⟨_, hc, rfl, by simp only; omega, by simp only; omega⟩, by omega, by omega⟩
  refine ⟨⟨by omega, by omega, by omega⟩,
    fun a h1 _ => kOff a (.inr h1) (fun h => absurd h.lo (by omega)), ?_, ⟨⟨top', brk', chunks', bins'⟩, ?_⟩⟩
  · show bytesT4 _ (L + stateHookmaskOff) = _
    rw [bytesT4_congrT fun i _ => kIn _ (xlive _ (.inl ⟨by omega, by simp only [stateHookmaskOff]; omega⟩))
      (by simp only [stateHookmaskOff]; omega) (by simp only [stateHookmaskOff]; omega)
      (by simp only [stateHookmaskOff]; omega) (by simp only [Rng, ciNextOff, stateHookmaskOff]; omega)
      (by simp only [Rng, stateNciOff, stateHookmaskOff]; omega)
      (by simp only [Rng, gGCdebtOff, stateHookmaskOff]; omega)]
    exact hhook
  refine
    { heap := hH3
      brk := by show brk' ≤ H.brk + extRoom; omega
      kept := hP.kept
      nci_in := fun a h1 h2 => nin a h1 (by omega)
      fresh := fun a h1 h2 => ⟨hfresh a h1 (by omega), by omega, by omega⟩
      next := ?_
      prev := ?_
      al := by omega
      keep := kAll
      stdio := fun ph hPS hbuf hrm => ?_ }
  · show bytesT8 _ (ci + 24) = _
    simp only [Lua.Vm.AtF.ExtendCI.m3, ext1, extCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw8_wm2, fw8_wm4, fw8_wm8, fw8_same]
  · show bytesT8 _ (p + 16) = _
    simp only [Lua.Vm.AtF.ExtendCI.m3, ext1, extCx, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    simp (disch := omega) only [fw8_wm2, fw8_wm4, fw8_wm8, fw8_same]
  -- `stdout`'s state: it reads no allocator word, and its buffer is apart from the links
  have hbu := bufU ph hPS
  refine ⟨hPS.io.congrA (fun a ha => ?_) hrm (fun buf hb => ?_), hH3, ?_⟩
  · rcases ha with ha | ha
    · exact kOff a (.inl (by have := ha.1.2; omega)) fun h => ha.2 (h.alloc ha.1)
    · obtain ⟨hu, h1, h2⟩ := hbu a ha
      have hx3 := hbuf a ha
      simp only [not_or] at hx3
      exact kIn a hu h1 h2 (fun h => hfresh a h.1 h.2 hu)
        (fun h => hx3.2.1 (by simp only [Rng, ciNextOff] at h ⊢; omega))
        (fun h => hx3.1 (by simp only [Rng, stateNciOff] at h ⊢; omega)) (fun h => hx3.2.2 h)
  · obtain ⟨sz, hc, hs⟩ := hb.block
    exact ⟨⟨sz, hP.kept _ hc rfl, hs⟩, hb.lo, hb.hi⟩
  · have hc := hPS.cells
    have kL : ∀ a, a < 0x8005c6d0 ∨ (0x8005d1bc ≤ a ∧ a < 0x8005d388) ∨ (0x8005d398 ≤ a ∧ a < 0x8005d3b8) → bytesT1
        (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) a = bytesT1 M a := fun a ha =>
      kOff a (.inl (by omega)) fun h => by
        have : errnoAddr = 0x8005d408 := rfl
        simp only [MallocGlobal] at h; omega
    exact ⟨(bytesT8_congrT fun i _ => kL _ (.inr (.inr ⟨by omega, by omega⟩))).trans hc.impure,
      (bytesT8_congrT fun i _ => kL _ (.inr (.inl ⟨by omega, by omega⟩))).trans hc.stdout,
      by rw [bytesAt_congr fun i hi => kL _ (.inl (by omega))]; exact hc.tab,
      by rw [bytesAt_congr fun i hi => kL _ (.inl (by omega))]; exact hc.nl⟩


/-- **`luaE_extendCI` after `l_alloc` returns `p`**: `luaM_malloc_`'s
`GCdebt`, the links, `L->nci++`, the return with `p`. -/
theorem ext_ret {sp L g ci p : Nat} {f : AbiFrame} {m' : Mem} {o : Array String} {c : Config}
    (hX1 : Lua.Vm.AtF.ExtendCI.Ok (ext1 sp L g ci p f m' o))
    (h : SegSt 0x800110c0#64 (Lua.Vm.AtF.ExtendCI.r3 (ext1 sp L g ci p f m' o)) (ArmPay m' o) c)
    (hc2 : bytesT8 m' (sp - 96 - 56) = 0x40#64) (hc3 : bytesT8 m' (sp - 96 - 24) = 0x80016a78#64)
    (hc4 : bytesT8 m' (sp - 96 - 40) = f.s1) (hc5 : bytesT8 m' (sp - 96 - 32) = BitVec.ofNat 64 L)
    (hc6 : bytesT8 m' (sp - 96 - 48) = f.s2) (hc7 : bytesT8 m' (L + 32) = BitVec.ofNat 64 ci)
    (hc8 : bytesT8 m' (sp - 96 - 8) = 0x8000acc8#64) (hc9 : bytesT8 m' (sp - 96 - 16) = BitVec.ofNat 64 L)
    (hp1 : p ≠ 0) (hp2 : p < 2 ^ 64) :
    ∃ c', Steps c c' ∧ wrRet 0x8000acc8#64 (sp - 96) p (pcFr L f) (Lua.Vm.AtF.ExtendCI.m3 (ext1 sp L g ci p f m' o)) o c' := by
  have acc := Steps.refl c
  have hc2 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 56) = 0x40#64 := hc2
  have hc3 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 24) = 0x80016a78#64 := hc3
  have hc4 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 40) =
      (ext1 sp L g ci p f m' o).b 2 := hc4
  have hc5 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 32) =
      BitVec.ofNat 64 ((ext1 sp L g ci p f m' o).n 1) := hc5
  have hc6 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 48) =
      (ext1 sp L g ci p f m' o).b 3 := hc6
  have hc8 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 8) =
      (ext1 sp L g ci p f m' o).b 0 := hc8
  have hc9 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 16) =
      (ext1 sp L g ci p f m' o).b 1 := hc9
  have hc7 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 1 + 32) =
      BitVec.ofNat 64 ((ext1 sp L g ci p f m' o).n 3) := hc7
  have hg_2 : (BitVec.ofNat 64 ((ext1 sp L g ci p f m' o).n 4) == 0x0#64) = false :=
    ofNat_beq0 (Nat.pos_of_ne_zero hp1) hp2
  have hf0 : (ext1 sp L g ci p f m' o).n 4 ≠ 0 := hp1
  have h : SegSt 0x800110c0#64 (Lua.Vm.AtF.ExtendCI.r3 (ext1 sp L g ci p f m' o))
      (ArmPay (ext1 sp L g ci p f m' o).m (ext1 sp L g ci p f m' o).o) c := h
  fat_run Lua.Vm.AtF.ExtendCI h acc
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- **`luaE_extendCI(L)` from `_malloc_r`'s summary.** -/
theorem extendCI_of_malloc (hM : MallocR_Statement) : ExtendCI_Statement := by
  intro sp L ci g f M o H hH hroom hci hnext hhook hg hfr himp hx hsl hsh hsa c h
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  have e3 : extRoom = 20608 := rfl
  have e4 : stateSize = 200 := rfl
  have e5 : ciSize = 64 := rfl
  have e6 : gGCdebtOff = 24 := rfl
  have e7 : symMallocAv = 0x8005c6d0 := rfl
  have e8 : symMallocSbrkBase = 0x8005d388 := rfl
  have e9 : symBrk = 0x8005d3b8 := rfl
  have e10 : symMallocTopPad = 0x8005d3d8 := rfl
  have e11 : symMallocMaxSbrked = 0x8005d3d0 := rfl
  have e12 : symMallocMallinfo = 0x8005e560 := rfl
  obtain ⟨xL1, xL2, xL3, xc1, xc2, xc3, xg1, xg2, xg3, xLg, xLc, xlive⟩ := hx
  simp only [e1, e2, e3, e4, e5, e6] at xL1 xL2 xc1 xc2 xg1 xg2 xLg xLc hsl hroom
  -- root 0: the entry, up to `g->frealloc`
  have hX0 : Lua.Vm.AtF.ExtendCI.Ok (ext0 sp L g ci f M o) := by
    have hra : (0x8000acc8#64 : BitVec 64).toNat % 4 = 0 := by decide
    fcx_ok
  simp only [PcExt] at h ⊢
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80016a5c#64 (Lua.Vm.AtF.ExtendCI.r0 (ext0 sp L g ci f M o)) (ArmPay (ext0 sp L g ci f M o).m (ext0 sp L g ci f M o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT8 (ext0 sp L g ci f M o).m ((ext0 sp L g ci f M o).n 1 + 24) = BitVec.ofNat 64 ((ext0 sp L g ci f M o).n 2) := hg
  have hc1 : bytesT8 (ext0 sp L g ci f M o).m ((ext0 sp L g ci f M o).n 2) = 0x8000172c#64 := hfr
  fat_run Lua.Vm.AtF.ExtendCI h acc until [0x8000172c]
  -- `luaM_malloc_`'s frame: below `sp - 96`
  have km1 : ∀ a, (a < sp - 160 ∨ sp - 96 ≤ a) → bytesT1 (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) a = bytesT1 M a :=
    fun a ha => AtF.bT1_congr (by
      simp only [Lua.Vm.AtF.ExtendCI.m1, List.getD_cons_zero, List.getD_cons_succ]; fs_off)
  have hH1 : HeapAt (fillZeroMem (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o))) H.top H.brk H.chunks H.bins :=
    hH.ofTotal fun a hr _ => by
      rw [km1 a (by simp only [HeapReads] at hr; omega), bytesT1_fill]
  have himp1 : bytesT8 (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) 0x8005d398 = 0x8005d1b8#64 :=
    (bytesT8_congrT fun i _ => km1 _ (by omega)).trans himp
  obtain ⟨c2, s2, m', p, top', brk', chunks', bins', hret, hP⟩ := lalloc_sum hM (sp - 96 - 64) H.top H.brk
    H.chunks H.bins (bytesT8 M (g + 8)) 0x800110c0#64 (extFr L g f) _ o hH1 (by decide) (by omega) (by omega)
    (by omega) (by omega) himp1 _ (by
      simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]
      fcx_unfold at h
      exact h.repin (by pins_of h))
  have acc := acc.trans s2
  have hp1 := hP.lo; have hp2 := hP.hi; have hp3 := hP.al; have hp4 := hP.brk_hi
  -- `_malloc_r`'s keep: the stack above its frame
  have kS : ∀ a, sp - 96 - 64 ≤ a → bytesT1 m' a = bytesT1 (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) a :=
    fun a ha => AtF.bT1_congr (hP.keep a (fun hg => absurd hg.lo (by omega)) (.inr (.inl (by omega)))
      (.inr ha))
  have kU : ∀ a, InUse H.chunks a → heapStart ≤ a → a < heapEnd → bytesT1 m' a = bytesT1 M a :=
    fun a hu hl hh => (AtF.bT1_congr (hP.keep a (fun hg => absurd hg.lo (by omega)) (.inr (.inr hu))
      (by omega))).trans (km1 a (by omega))
  -- root 3: the return from `l_alloc`
  have hX1 : Lua.Vm.AtF.ExtendCI.Ok (ext1 sp L g ci p f m' o) := by
    have hra : (0x8000acc8#64 : BitVec 64).toNat % 4 = 0 := by decide
    fcx_ok
  simp only [wrRet] at hret
  have h : SegSt 0x800110c0#64 (Lua.Vm.AtF.ExtendCI.r3 (ext1 sp L g ci p f m' o))
      (ArmPay (ext1 sp L g ci p f m' o).m (ext1 sp L g ci p f m' o).o) c2 := hret.repin (by pins_of hret)
  have fr : ∀ k, 1 ≤ k → k ≤ 7 → bytesT8 m' (sp - 96 - 8 * k) =
      bytesT8 (Lua.Vm.AtF.ExtendCI.m1 (ext0 sp L g ci f M o)) (sp - 96 - 8 * k) :=
    fun k h1 h2 => bytesT8_congrT fun i _ => kS _ (by omega)
  have hc2 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 56) = 0x40#64 :=
    (fr 7 (by omega) (by omega)).trans (by ext_slot)
  have hc3 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 24) = 0x80016a78#64 :=
    (fr 3 (by omega) (by omega)).trans (by ext_slot)
  have hc4 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 40) =
      (ext1 sp L g ci p f m' o).b 2 := (fr 5 (by omega) (by omega)).trans (by ext_slot)
  have hc5 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 32) =
      BitVec.ofNat 64 ((ext1 sp L g ci p f m' o).n 1) := (fr 4 (by omega) (by omega)).trans (by ext_slot)
  have hc6 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 48) =
      (ext1 sp L g ci p f m' o).b 3 := (fr 6 (by omega) (by omega)).trans (by ext_slot)
  have hc8 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 8) =
      (ext1 sp L g ci p f m' o).b 0 := (fr 1 (by omega) (by omega)).trans (by ext_slot)
  have hc9 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 0 - 16) =
      (ext1 sp L g ci p f m' o).b 1 := (fr 2 (by omega) (by omega)).trans (by ext_slot)
  have hc7 : bytesT8 (ext1 sp L g ci p f m' o).m ((ext1 sp L g ci p f m' o).n 1 + 32) =
      BitVec.ofNat 64 ((ext1 sp L g ci p f m' o).n 3) := by
    show bytesT8 m' (L + 32) = BitVec.ofNat 64 ci
    exact (bytesT8_congrT fun i _ => kU _ (xlive _ (.inl ⟨by omega, by omega⟩)) (by omega) (by omega)).trans hci
  obtain ⟨c3, s3, hw⟩ := ext_ret hX1 h hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 (by omega) (by omega)
  obtain ⟨hn, hs, hk, hE⟩ := ext_post hP (by rw [e3, e2]; omega) hhook
    ⟨xL1, xL2, xL3, xc1, xc2, xc3, xg1, xg2, xg3, xLg, xLc, xlive⟩ (by rw [e2]; omega)
  exact ⟨_, acc.trans s3, p, _, hw, hn, hs, hk, hE⟩

/-- `luaE_extendCI` (lane F1-14), `_malloc_r` discharged (lane F1-A0-M). -/
theorem extendCI_proved : ExtendCI_Statement := extendCI_of_malloc AllocProof.mallocR_proved

theorem CallOpen.extendCI (_O : CallOpen) : ExtendCI_Statement := extendCI_proved

end Lua.Vm.Sim.Kit

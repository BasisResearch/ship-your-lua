import Lua.Vm.Sim.Kit.SNew
import Lua.Vm.AtF.Pushstring

/-!
# `PushLit_Statement` proved (lane F1-15)

`lua_pushstring(L, s)` (`0x80002fe4`) of one of `luaL_tolstring`'s literals:
`luaS_new` (a call node: `snew_nil`, …, one per literal, `SNewSpec`), the push
of the short string at `L->top`, `luaC_checkGC` (the debt not positive: no
step; else `luaC_step` with the collector stopped, `luaC_step_sum`). Its
at-lemmas are generated (`Lua/Vm/AtF/Pushstring.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- **`luaS_new` on the literal `sel ls`**: its summary (`snew_nil`, …). -/
def SNewSpec (sel : LitPtrs → CLit) : Prop :=
  ∀ (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String),
    SNewIn m sp L g sl ls FL r → Apart (sel ls).ts 30 g gEnd →
    Triple (SegSt 0x8001772c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (sel ls).addr⟩] sp r f) (ArmPay m o))
      (snewPost r sp (sel ls).ts f g ls m o)

/-- One literal's `LitInterned`, from its place in the table. -/
theorem _root_.Lua.Vm.LitsIn.lit {M : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (h : LitsIn M g sl ls rt)
    {l : CLit} (hl : l ∈ ls.table) : LitInterned M rt ls.seed l.bytes l.ts := by
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact h.nil
  · exact h.tru
  · exact h.fls
  · exact h.tos

/-- The interned string's tag and length, as total reads. -/
theorem _root_.Lua.Vm.LitInterned.tag_len {m : Mem} {rt : RtPtrs} {seed : UInt32} {b : List UInt8} {ts : Nat}
    (h : LitInterned m rt seed b ts) :
    bytesT1 m (ts + 8) = 0x4#8 ∧ bytesT1 m (ts + 11) = BitVec.ofNat 8 b.length := by
  have hs := h.short
  cases h.repr with
  | short ht _ hl _ _ =>
    refine ⟨?_, ?_⟩
    · rw [← bytesT1_fill]; exact (bytesT1_of_rd8 ht).trans (by decide)
    · rw [← bytesT1_fill]; exact bytesT1_of_rd8 hl
  | long _ hl => exact absurd hs (by omega)


/-- **`lua_pushstring(L, s)` of the literal `sel ls`**, from `luaS_new`'s
summary on it (`SNewSpec`): `PushLit_Statement`'s post. -/
theorem pushstring_sum (sel : LitPtrs → CLit) (hsel : SNewSpec sel) (sp L top g sl : Nat) (ls : LitPtrs)
    (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hl : sel ls ∈ ls.table) (hA : 1 ≤ (sel ls).addr) (hA2 : (sel ls).addr < 2 ^ 32) (hcx : PushCx sp L top g r)
    (hap : LitApart (sel ls).ts L g top)
    (htop : bytesT8 m (L + 16) = BitVec.ofNat 64 top) (hG : bytesT8 m (L + 24) = BitVec.ofNat 64 g)
    (hroom : top + 16 + 16 ≤ sl) (hro : RodataRead m)
    (hfz : Frozen FL (fun M => LitsHold M g sl ls) m)
    (hfl : ∀ a, FL a → a < heapEnd ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a)
    (hca : LitCache m g ls) (hst : bytesT1 m (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr) :
    Triple (SegSt 0x80002fe4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (sel ls).addr⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp ((sel ls).ts + 24) f m' o c ∧
        PushPost m m' sp L g top (sel ls).ts (sel ls).bytes.length ls) := by
  intro c h
  obtain ⟨rt, hL⟩ := hfz m fun _ _ => rfl
  have hLI := hL.lit hl
  obtain ⟨htt, hlen⟩ := hLI.tag_len
  have hts1 := hLI.ts_lo; have hts2 := hLI.ts_hi; have hsh := hLI.short
  generalize hA' : (sel ls).addr = A at *
  generalize hT' : (sel ls).ts = ts at *
  generalize hB' : (sel ls).bytes = b at *
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hHE : heapEnd = 0x87800000 := rfl
  obtain ⟨hra, hspal, hsphi, hsplo, hLlo, hLhi, hLal, hglo, hghi, hgal, htlo, hthi, htal, htL, htg, hLg⟩ := hcx
  obtain ⟨apL, apg, apt⟩ := hap
  simp only [symTohost, symHeapEnd, heapEnd, maxShortLen] at hts1 hts2 hsh hsplo hLlo hLhi hglo hghi htlo hthi
  simp only [stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM, Apart] at hLhi hghi htL htg hLg apL apg apt
  have hX : Lua.Vm.AtF.Pushstring.Ok (plX [sp, L, A, ts, top, g] r f m o) := by fcx_ok
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80002fe4#64 (Lua.Vm.AtF.Pushstring.r0 (plX [sp, L, A, ts, top, g] r f m o))
      (ArmPay (plX [sp, L, A, ts, top, g] r f m o).m (plX [sp, L, A, ts, top, g] r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Pushstring h acc until [0x8001772c]
  -- the frame
  have hM1 : ∀ a, (a + 32 ≤ sp ∨ sp ≤ a) →
      bytesT1 (Lua.Vm.AtF.Pushstring.m1 (plX [sp, L, A, ts, top, g] r f m o)) a = bytesT1 m a := by
    intro a ha; fcx_unfold; exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
  have sv0 : bytesT8 (Lua.Vm.AtF.Pushstring.m1 (plX [sp, L, A, ts, top, g] r f m o)) (sp - 8) = r := by
    fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
  have sv1 : bytesT8 (Lua.Vm.AtF.Pushstring.m1 (plX [sp, L, A, ts, top, g] r f m o)) (sp - 24) =
      BitVec.ofNat 64 L := by
    fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
  generalize hM1e : Lua.Vm.AtF.Pushstring.m1 (plX [sp, L, A, ts, top, g] r f m o) = M1 at h hM1 sv0 sv1
  fcx_unfold at h
  -- `luaS_new(L, s)`
  have hSN : SNewIn M1 (sp - 32) L g sl ls FL 0x80002ffc#64 := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega,
    L_he := by omega, L_al := hLal, g_lo := by omega, g_hi := by omega, g_al := hgal, Lg_ap := by omega,
    Lg := (bytesT8_congrT fun i _ => hM1 _ (.inl (by omega))).trans hG,
    lits := hfz.trans fun a ha => hM1 a (.inl (by
      have := (hfl a ha).1; simp only [heapEnd, symHeapEnd] at this; omega)),
    foot := hfl,
    cache := hca.congr fun a h1 h2 => hM1 a (.inl (by
      simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2; omega)),
    ro := fun o' ho => (hM1 _ (.inl (by simp only [Image.rodataBase, Image.rodataSize] at ho ⊢; omega))).trans
      (hro o' ho) }
  have hsn := hsel (sp - 32) L g sl ls FL 0x80002ffc#64 f M1 o hSN (by
    rw [hT']; simp only [Apart, gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)
  rw [hA', hT'] at hsn
  simp only [callPre, List.cons_append, List.nil_append] at hsn
  obtain ⟨c1, acc, M2, h, hp2⟩ := h.call acc (by pins_of h) hsn
  dsimp only [wrRet] at h
  -- what `luaS_new` kept
  have hk2 : ∀ a, (a + 16384 ≤ sp ∨ sp - 32 ≤ a) → ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a →
      a ≠ ts + 9 → bytesT1 M2 a = bytesT1 M1 a := fun a ha hc hn =>
    hp2.keep a (by simp only [Rng, gStrcacheOff, strcacheN, strcacheM, gcMarkedOff, Below, not_or, not_and,
      Nat.not_le, Nat.not_lt] at hc ⊢; omega)
  have hk2m : ∀ a, (a + 16384 ≤ sp ∨ sp ≤ a) → ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a →
      a ≠ ts + 9 → bytesT1 M2 a = bytesT1 m a := fun a ha hc hn =>
    (hk2 a (by omega) hc hn).trans (hM1 a (by omega))
  have nc : ∀ a, a < g ∨ g + 1400 ≤ a → ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a := by
    intro a ha hr; simp only [Rng, gStrcacheOff, strcacheN, strcacheM] at hr; omega
  have hc0 : bytesT8 M2 (sp - 24) = BitVec.ofNat 64 L :=
    (bytesT8_congrT fun i _ => hk2 _ (.inr (by omega)) (nc _ (by omega)) (by omega)).trans sv1
  have hc4 : bytesT8 M2 (sp - 8) = r :=
    (bytesT8_congrT fun i _ => hk2 _ (.inr (by omega)) (nc _ (by omega)) (by omega)).trans sv0
  have hc1 : bytesT8 M2 (L + 16) = BitVec.ofNat 64 top :=
    (bytesT8_congrT fun i _ => hk2m _ (.inl (by omega)) (nc _ (by omega)) (by omega)).trans htop
  have hc3 : bytesT8 M2 (L + 24) = BitVec.ofNat 64 g :=
    (bytesT8_congrT fun i _ => hk2m _ (.inl (by omega)) (nc _ (by omega)) (by omega)).trans hG
  have hc2 : bytesT1 M2 (ts + 8) = 0x4#8 := (hk2m _ (.inl (by omega)) (nc _ (by omega)) (by omega)).trans htt
  have hl2 : bytesT1 M2 (ts + 11) = BitVec.ofNat 8 b.length :=
    (hk2m _ (.inl (by omega)) (nc _ (by omega)) (by omega)).trans hlen
  have hX3 : Lua.Vm.AtF.Pushstring.Ok (plX [sp, L, A, ts, top, g] r f M2 o) := by fcx_ok
  have h : SegSt 0x80002ffc#64 (Lua.Vm.AtF.Pushstring.r3 (plX [sp, L, A, ts, top, g] r f M2 o))
      (ArmPay (plX [sp, L, A, ts, top, g] r f M2 o).m (plX [sp, L, A, ts, top, g] r f M2 o).o) c1 := by
    fcx_unfold; exact h.repin (by pins_of h)
  -- the push's stores, as the rows print them
  have st : ∀ M : Mem, (∀ a, (a + 16384 ≤ sp ∨ sp ≤ a) → ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a →
      a ≠ ts + 9 → bytesT1 M a = bytesT1 m a) → LitCache M g ls →
      bytesT1 M (ts + 11) = BitVec.ofNat 8 b.length →
      PushPost m (writeMap8 ((writeMap8 M top (sdData_val (BitVec.ofNat 64 ts))).insert (top + 8)
        (stData 1 (0x44#64))) (L + 16) (sdData_val (BitVec.ofNat 64 (top + 16)))) sp L g top ts b.length ls := by
    intro M hk hc hl'
    refine ⟨fw8_same rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [fw1_wm8 (by omega), fw1_same rfl]; decide
    · rw [fw8_wm8 (by omega), fw8_ins (by omega), fw8_same rfl]
    · rw [fw1_wm8 (by omega), fw1_ins (by omega), fw1_wm8 (by omega)]; exact hl'
    · exact hc.congr fun a h1 h2 => by
        simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2
        rw [fw1_wm8 (by omega), fw1_ins (by omega), fw1_wm8 (by omega)]
    · intro a ha
      simp only [Rng, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff, gcMarkedOff, not_or,
        not_and, Nat.not_lt, Nat.not_le] at ha
      rw [fw1_wm8 (by omega), fw1_ins (by omega), fw1_wm8 (by omega)]
      exact hk a (by omega) (by simp only [Rng, gStrcacheOff, strcacheN, strcacheM]; omega) (by omega)
  by_cases hgc : zopz0zKzJ_s (0x0#64) (bytesT8 M2 (g + 24)) = true
  · -- no step
    fat_run Lua.Vm.AtF.Pushstring h acc
    fcx_unfold at h
    exact ⟨_, acc, _, h.repin (by pins_of h), st M2 hk2m hp2.cache hl2⟩
  · simp only [Bool.not_eq_true] at hgc
    fat_run Lua.Vm.AtF.Pushstring h acc until [0x8000ec80]
    fcx_unfold at h
    -- `luaC_step(L)` with the collector stopped
    have hG3 : bytesT8 (writeMap8 (writeMap8 ((writeMap8 M2 top (sdData_val (BitVec.ofNat 64 ts))).insert
        (top + 8) (stData 1 (0x44#64))) (L + 16) (sdData_val (BitVec.ofNat 64 (top + 16)))) (sp - 24)
        (sdData_val (BitVec.ofNat 64 (ts + 24)))) (L + 24) = BitVec.ofNat 64 g := by
      rw [fw8_wm8 (by omega), fw8_wm8 (by omega), fw8_ins (by omega), fw8_wm8 (by omega)]; exact hc3
    have hS3 : bytesT1 (writeMap8 (writeMap8 ((writeMap8 M2 top (sdData_val (BitVec.ofNat 64 ts))).insert
        (top + 8) (stData 1 (0x44#64))) (L + 16) (sdData_val (BitVec.ofNat 64 (top + 16)))) (sp - 24)
        (sdData_val (BitVec.ofNat 64 (ts + 24)))) (g + gGcstpOff) = 0x1#8 := by
      simp only [gGcstpOff]
      rw [fw1_wm8 (by omega), fw1_wm8 (by omega), fw1_ins (by omega), fw1_wm8 (by omega),
        hk2m _ (.inl (by omega)) (by simp only [Rng, gStrcacheOff, strcacheN, strcacheM]; omega) (by omega)]
      exact hst.trans (by decide)
    have hls := luaC_step_sum (sp - 32) L g 0x80003038#64 f _ o
      ⟨by omega, by omega, by omega, by decide, by omega, by omega, hLal, by omega, by omega, hgal⟩ hG3 hS3
    simp only [callPre, List.cons_append, List.nil_append] at hls
    obtain ⟨c2, acc, M4, h, hp4⟩ := h.call acc (by pins_of h) hls
    dsimp only [wrRet] at h
    have hk4 := hp4.keep
    have nb : ∀ a, sp - 32 ≤ a →
        ¬ (Rng (g + gTotalbytesOff) 8 a ∨ Rng (g + gGCdebtOff) 8 a ∨ Below (sp - 32) 80 a) := by
      intro a ha
      simp only [Rng, gTotalbytesOff, gGCdebtOff, Below, not_or, not_and, Nat.not_lt, Nat.not_le]
      omega
    have hc5 : bytesT8 M4 (sp - 24) = BitVec.ofNat 64 (ts + 24) := by
      rw [bytesT8_congrT fun i _ => hk4 _ (nb _ (by omega))]
      exact fw8_same rfl
    have hc4' : bytesT8 M4 (sp - 8) = r := by
      rw [bytesT8_congrT fun i _ => hk4 _ (nb _ (by omega)), fw8_wm8 (by omega), fw8_wm8 (by omega),
        fw8_ins (by omega), fw8_wm8 (by omega)]
      exact hc4
    have hX7 : Lua.Vm.AtF.Pushstring.Ok (plX [sp, L, A, ts, top, g] r f M4 o) := by fcx_ok
    have h : SegSt 0x80003038#64 (Lua.Vm.AtF.Pushstring.r7 (plX [sp, L, A, ts, top, g] r f M4 o))
        (ArmPay (plX [sp, L, A, ts, top, g] r f M4 o).m (plX [sp, L, A, ts, top, g] r f M4 o).o) c2 := by
      fcx_unfold; exact h.repin (by pins_of h)
    fat_run Lua.Vm.AtF.Pushstring h acc
    fcx_unfold at h
    have P := st M2 hk2m hp2.cache hl2
    refine ⟨_, acc, _, h.repin (by pins_of h), ?_⟩
    have k4 : ∀ a, (a + 16384 ≤ sp ∨ sp ≤ a) → ¬ Rng (g + gTotalbytesOff) 8 a → ¬ Rng (g + gGCdebtOff) 8 a →
        bytesT1 M4 a = bytesT1 (writeMap8 ((writeMap8 M2 top (sdData_val (BitVec.ofNat 64 ts))).insert (top + 8)
          (stData 1 (0x44#64))) (L + 16) (sdData_val (BitVec.ofNat 64 (top + 16)))) a := fun a ha h1 h2 => by
      rw [hk4 a (by simp only [Rng, Below, not_or, not_and, Nat.not_lt, Nat.not_le] at h1 h2 ⊢; omega)]
      exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
    have nt : ∀ a, a < g ∨ g + 1400 ≤ a → ¬ Rng (g + gTotalbytesOff) 8 a ∧ ¬ Rng (g + gGCdebtOff) 8 a := by
      intro a ha; simp only [Rng, gTotalbytesOff, gGCdebtOff]; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [bytesT8_congrT fun i _ => k4 _ (.inl (by omega)) (nt _ (by omega)).1 (nt _ (by omega)).2]; exact P.top_w
    · rw [k4 _ (.inl (by omega)) (nt _ (by omega)).1 (nt _ (by omega)).2]; exact P.tag_w
    · rw [bytesT8_congrT fun i _ => k4 _ (.inl (by omega)) (nt _ (by omega)).1 (nt _ (by omega)).2]; exact P.val_w
    · rw [k4 _ (.inl (by omega)) (nt _ (by omega)).1 (nt _ (by omega)).2]; exact P.len_w
    · exact P.cache.congr fun a h1 h2 => by
        simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at h1 h2
        exact k4 a (.inl (by omega)) (by simp only [Rng, gTotalbytesOff]; omega)
          (by simp only [Rng, gGCdebtOff]; omega)
    · intro a ha
      have hb := P.keep a ha
      rcases ha with ha | ⟨ha, -, -, -, h1, h2, -⟩
      · rw [k4 a (.inr ha) (by simp only [Rng, gTotalbytesOff]; omega) (by simp only [Rng, gGCdebtOff]; omega), hb]
      · rw [k4 a (.inl ha) h1 h2, hb]

theorem snewSpec_nil : SNewSpec fun ls => ⟨litNilAddr, nilB, ls.nil⟩ :=
  fun sp L g sl ls FL r f m o hx htg => snew_nil sp L g sl ls FL r f m o hx htg
theorem snewSpec_true : SNewSpec fun ls => ⟨litTrueAddr, trueB, ls.tru⟩ :=
  fun sp L g sl ls FL r f m o hx htg => snew_true sp L g sl ls FL r f m o hx htg
theorem snewSpec_false : SNewSpec fun ls => ⟨litFalseAddr, falseB, ls.fls⟩ :=
  fun sp L g sl ls FL r f m o hx htg => snew_false sp L g sl ls FL r f m o hx htg
theorem snewSpec_tos : SNewSpec fun ls => ⟨litTosAddr, tosB, ls.tos⟩ :=
  fun sp L g sl ls FL r f m o hx htg => snew_tos sp L g sl ls FL r f m o hx htg

/-- **`PushLit_Statement`, proved** (lane F1-15): `lua_pushstring` of each of
`luaL_tolstring`'s four literals (`pushstring_sum` over `snew_nil`, …). -/
theorem pushLit_proved : PushLit_Statement := by
  intro sp L top g sl l ls FL r f m o hl hcx hap htop hG hroom hro hfz hfl hca hst
  have hl' := hl
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl'
  rcases hl' with rfl | rfl | rfl | rfl
  · exact pushstring_sum _ snewSpec_nil sp L top g sl ls FL r f m o hl (by show 1 ≤ litNilAddr; decide) (by show litNilAddr < 2 ^ 32; decide) hcx hap htop hG hroom hro hfz
      hfl hca hst
  · exact pushstring_sum _ snewSpec_true sp L top g sl ls FL r f m o hl (by show 1 ≤ litTrueAddr; decide) (by show litTrueAddr < 2 ^ 32; decide) hcx hap htop hG hroom hro hfz
      hfl hca hst
  · exact pushstring_sum _ snewSpec_false sp L top g sl ls FL r f m o hl (by show 1 ≤ litFalseAddr; decide) (by show litFalseAddr < 2 ^ 32; decide) hcx hap htop hG hroom hro hfz
      hfl hca hst
  · exact pushstring_sum _ snewSpec_tos sp L top g sl ls FL r f m o hl (by show 1 ≤ litTosAddr; decide) (by show litTosAddr < 2 ^ 32; decide) hcx hap htop hG hroom hro hfz
      hfl hca hst

end Lua.Vm.Sim.Kit

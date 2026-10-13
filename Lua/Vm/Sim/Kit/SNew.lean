import Lua.Vm.Sim.Kit.Intern
import Lua.Vm.Sim.Kit.Strcmp
import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.AtF.LuaSNewNil
import Lua.Vm.AtF.LuaSNewTrue
import Lua.Vm.AtF.LuaSNewFalse
import Lua.Vm.AtF.LuaSNewTos

/-!
# `luaS_new` on a C literal (lane F1-15)

`luaS_new(L, s)` (`0x8001772c`) on one of `luaL_tolstring`'s literals: the
row `s % STRCACHE_N` of `g->strcache` (`__umoddi3`, `umoddi3_sum`), `strcmp`
against its two entries (`strcmp_sumS`: an answer `0` means the entry is the
literal's string, `CandOk`), on a miss `strlen`, `luaS_newlstr`
(`newlstr_sum`) and the row's shift. The literals' facts are frozen on a
footprint off the string cache (`Frozen`), so they hold of the memory
`internshrstr` reads. One proof for the four literals (`snew_run`), over
their generated at-lemmas (`LuaSNewNil`, …: the literal's address and row
are the generator's literals).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `strcmp` against a candidate -/

/-- **A zero `strcmp` of a literal**: the C string `b` (no NUL, then NUL) at
`A`; the answer `0` means `Q` holds `b` and its terminator. -/
theorem sc_zero_bytes {M : Mem} {A Q : Nat} {b : List UInt8} {v : BitVec 64}
    (hA : ∀ i, i < b.length → bytesT1 M (A + i) = BitVec.ofNat 8 (b.getD i 0).toNat)
    (hz : bytesT1 M (A + b.length) = 0#8) (hnz : ∀ i, i < b.length → b.getD i 0 ≠ 0)
    (hans : ScAns M A Q v) (hv : v = 0#64) :
    ∀ i, i ≤ b.length → bytesT1 M (Q + i) = BitVec.ofNat 8 ((b ++ [0]).getD i 0).toNat := by
  obtain ⟨k, hpre, hnot, hobs⟩ := hans.ans
  have heq : bytesT1 M (A + k) = bytesT1 M (Q + k) := by
    have := hobs.zero.1 hv
    exact BitVec.eq_of_toNat_eq this
  have hk0 : bytesT1 M (A + k) = 0#8 :=
    Classical.byContradiction fun hne => hnot ⟨heq, hne⟩
  have hb8 : ∀ i, i < b.length → BitVec.ofNat 8 (b.getD i 0).toNat ≠ 0#8 := fun i hi e => hnz i hi (by
    apply UInt8.toNat_inj.mp
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)] at this
    simpa using this)
  have hkl : k = b.length := by
    rcases Nat.lt_trichotomy k b.length with h | h | h
    · exact absurd ((hA k h).symm.trans hk0) (hb8 k h)
    · exact h
    · exact absurd hz (hpre _ h).2
  subst hkl
  intro i hi
  rcases Nat.lt_or_ge i b.length with h | h
  · rw [← (hpre i h).1, hA i h]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [show i = b.length by omega, ← heq, hz]
    simp [List.getD_eq_getElem?_getD]

/-- **The candidate a zero `strcmp` finds is the literal's string**
(`CandOk`, read through `keep` from the memory of the facts). -/
theorem cand_of_zero {m M : Mem} {lits : List CLit} {r p A : Nat} {b : List UInt8} {ts : Nat} {v : BitVec 64}
    (hc : CandOk (fillZeroMem m) lits r p) (hl : ⟨A, b, ts⟩ ∈ lits) (hr : A % strcacheN = r)
    (keep : ∀ a, p ≤ a → a < p + 64 → bytesT1 M a = bytesT1 m a) (hbl : b.length ≤ 39)
    (hA : ∀ i, i < b.length → bytesT1 M (A + i) = BitVec.ofNat 8 (b.getD i 0).toNat)
    (hz : bytesT1 M (A + b.length) = 0#8) (hnz : ∀ i, i < b.length → b.getD i 0 ≠ 0)
    (hans : ScAns M A (p + 24) v) (hv : v = 0#64) : p = ts := by
  rcases hc.ok _ hl hr with e | ⟨k, hk, hpre, hne⟩
  · exact e
  · exfalso
    simp only at hk hpre hne
    have hq := sc_zero_bytes hA hz hnz hans hv k hk
    apply hne
    have hlo := hc.lo; have hhi := hc.hi
    simp only [symTohost, symHeapEnd] at hlo hhi
    rw [show p + tstringContentsOff + k = p + 24 + k from rfl, rd8_fill (by omega) (by omega),
      ← keep _ (by omega) (by omega), hq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]


/-! ## The inputs and the post -/

/-- **A C literal in `.rodata`**: its bytes (no NUL) and its terminator. -/
structure LitStr (A : Nat) (b : List UInt8) : Prop where
  lo : Image.rodataBase ≤ A
  hi : A + b.length + 1 ≤ Image.rodataBase + Image.rodataSize
  bytes : ∀ i, i < b.length → Image.rodataByte (A - Image.rodataBase + i) = BitVec.ofNat 8 (b.getD i 0).toNat
  term : Image.rodataByte (A - Image.rodataBase + b.length) = 0#8
  nz : ∀ i, i < b.length → b.getD i 0 ≠ 0

theorem litStr_nil : LitStr litNilAddr nilB := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem litStr_true : LitStr litTrueAddr trueB := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem litStr_false : LitStr litFalseAddr falseB := ⟨by decide, by decide, by decide, by decide, by decide⟩
theorem litStr_tos : LitStr litTosAddr tosB := ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- A literal's bytes in a memory that reads `.rodata`. -/
theorem LitStr.read {A : Nat} {b : List UInt8} {M : Mem} (h : LitStr A b) (hr : RodataRead M) :
    (∀ i, i < b.length → bytesT1 M (A + i) = BitVec.ofNat 8 (b.getD i 0).toNat) ∧
      bytesT1 M (A + b.length) = 0#8 := by
  have hl := h.lo; have hh := h.hi
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [show A + i = Image.rodataBase + (A - Image.rodataBase + i) by omega, hr _ (by omega)]
    exact h.bytes i hi
  · rw [show A + b.length = Image.rodataBase + (A - Image.rodataBase + b.length) by omega, hr _ (by omega)]
    exact h.term

/-- **`luaS_new`'s inputs** for a literal: its frame, `G(L) = g`, the literals
frozen on `FL` (below the heap's end, off the string cache), the cache's
candidates, `.rodata`. -/
structure SNewIn (m : Mem) (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) : Prop where
  sp_lo : 0x87800000 + 16384 + 256 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  g_al : g % 8 = 0
  Lg_ap : L + 200 ≤ g ∨ g + 1400 ≤ L
  Lg : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  lits : Frozen FL (fun M => LitsHold M g sl ls) m
  foot : ∀ a, FL a → a < heapEnd ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a
  cache : LitCache m g ls
  ro : RodataRead m

/-- **What `luaS_new` leaves**: the cache holds candidates; every byte kept
but the cache's, the string's mark and the frames below `sp`. -/
structure SNewPost (m m' : Mem) (sp g ts : Nat) (ls : LitPtrs) : Prop where
  cache : LitCache m' g ls
  keep : ∀ a, ¬ (Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∨ a = ts + gcMarkedOff ∨ Below sp 128 a) →
    bytesT1 m' a = bytesT1 m a

/-- `luaS_new`'s return: `a0 = ts`. -/
abbrev snewPost (r : BitVec 64) (sp ts : Nat) (f : AbiFrame) (g : Nat) (ls : LitPtrs) (m : Mem) (o : Array String) :
    Config → Prop :=
  fun c => ∃ m', wrRet r sp ts f m' o c ∧ SNewPost m m' sp g ts ls

/-- The cache's two words of row `R`, candidates of the row. -/
theorem _root_.Lua.Vm.LitCache.row {m : Mem} {g : Nat} {ls : LitPtrs} (h : LitCache m g ls) (R : Nat) (hR : R < strcacheN) :
    (R, (bytesT8 m (g + gStrcacheOff + 16 * R)).toNat) ∈ ls.cands ∧
      (R, (bytesT8 m (g + gStrcacheOff + 16 * R + 8)).toNat) ∈ ls.cands := by
  have h0 := h (2 * R) (by simp only [strcacheN, strcacheM] at hR ⊢; omega)
  have h1 := h (2 * R + 1) (by simp only [strcacheN, strcacheM] at hR ⊢; omega)
  rw [show 2 * R / strcacheM = R by simp only [strcacheM]; omega, show g + gStrcacheOff + 8 * (2 * R) =
    g + gStrcacheOff + 16 * R by omega] at h0
  rw [show (2 * R + 1) / strcacheM = R by simp only [strcacheM]; omega, show g + gStrcacheOff + 8 * (2 * R + 1) =
    g + gStrcacheOff + 16 * R + 8 by omega] at h1
  exact ⟨h0, h1⟩

/-- **The cache after the row's shift**: word `2R + 1` the old word `2R`,
word `2R` the literal's string (a candidate of its row, `lit_cands`). -/
theorem _root_.Lua.Vm.LitCache.shift {m m' : Mem} {g R ts : Nat} {ls : LitPtrs} (h : LitCache m g ls) (hR : R < strcacheN)
    (h0 : (bytesT8 m' (g + gStrcacheOff + 16 * R)).toNat = ts) (hts : (R, ts) ∈ ls.cands)
    (h1 : bytesT8 m' (g + gStrcacheOff + 16 * R + 8) = bytesT8 m (g + gStrcacheOff + 16 * R))
    (hk : ∀ i, i < strcacheN * strcacheM → i / strcacheM ≠ R →
      bytesT8 m' (g + gStrcacheOff + 8 * i) = bytesT8 m (g + gStrcacheOff + 8 * i)) :
    LitCache m' g ls := by
  intro i hi
  by_cases hr : i / strcacheM = R
  · simp only [strcacheM] at hr
    rcases (by omega : i = 2 * R ∨ i = 2 * R + 1) with e | e
    · subst e
      rw [show g + gStrcacheOff + 8 * (2 * R) = g + gStrcacheOff + 16 * R by omega, h0,
        show 2 * R / strcacheM = R by simp only [strcacheM]; omega]
      exact hts
    · subst e
      rw [show g + gStrcacheOff + 8 * (2 * R + 1) = g + gStrcacheOff + 16 * R + 8 by omega, h1,
        show (2 * R + 1) / strcacheM = R by simp only [strcacheM]; omega]
      exact (h.row R hR).1
  · rw [hk i hi hr]; exact h i hi

/-- The bytes of a literal are not NUL in a memory that reads `.rodata`. -/
theorem LitStr.read_nz {A : Nat} {b : List UInt8} {M : Mem} (h : LitStr A b) (hr : RodataRead M) :
    ∀ i, i < b.length → bytesT1 M (A + i) ≠ 0#8 := fun i hi e => by
  have e' := ((h.read hr).1 i hi).symm.trans e
  apply h.nz i hi
  apply UInt8.toNat_inj.mp
  have := congrArg BitVec.toNat e'
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)] at this
  simpa using this

/-! ## `luaS_new` on a literal -/

set_option hygiene false in
/-- **`luaS_new(L, s)` on one literal's proof** over the at-lemmas of `ns`
(`LuaSNewNil`, …: the literal's address `A`, its cache row `R` and the row's
words `g + o0`, `g + o1` are the generator's literals): `__umoddi3`, `strcmp`
against the row's two candidates (`cand_of_zero`: a zero answer is the
literal's string), on a miss the row's shift, `strlen` and `luaS_newlstr`
(`newlstr_sum`, its `InternIn` from the literals frozen off the cache). -/
macro "snew_run " ns:ident A:num R:num o0:num o1:num fld:ident addrN:ident bN:ident lsN:ident len:num :
    tactic => do
  let okN := Lean.mkIdent (ns.getId ++ `Ok)
  let m0N := Lean.mkIdent (ns.getId ++ `m0)
  let rN (k : Nat) := Lean.mkIdent (ns.getId ++ Lean.Name.mkSimple s!"r{k}")
  let r0N := rN 0; let r2N := rN 2; let r4N := rN 4; let r6N := rN 6; let r8N := rN 8; let r11N := rN 11
  let r13N := rN 13; let r15N := rN 15
  let lsF := Lean.mkIdent (`ls ++ fld.getId)
  let hLF := Lean.mkIdent (`hL ++ fld.getId)
  let hL2F := Lean.mkIdent (`hL2 ++ fld.getId)
  `(tactic| (
    intro c h
    have hTH : tohostAddr = 0x8005c6c0 := rfl
    have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have hra := hx.ra; have := hx.L_lo; have := hx.L_he
    have := hx.L_al; have := hx.g_lo; have := hx.g_hi; have := hx.g_al; have := hx.Lg_ap
    obtain ⟨rt, hL⟩ := hx.lits m fun _ _ => rfl
    have hl : (⟨$addrN, $bN, $lsF⟩ : CLit) ∈ ls.table := by simp [LitPtrs.table]
    have hLS := $lsN
    have hts := hL.lit_cands _ hl
    simp only [show $addrN % strcacheN = $R by decide] at hts
    have htsb := ($hLF).ts_lo; have htsb2 := ($hLF).ts_hi
    simp only [Apart, gEnd, gStrcacheOff, strcacheN, strcacheM, symTohost, symHeapEnd] at htg htsb htsb2
    obtain ⟨hw0, hw1⟩ := hx.cache.row $R (by decide)
    rw [show g + gStrcacheOff + 16 * $R = g + $o0 by simp only [gStrcacheOff]] at hw0
    rw [show g + gStrcacheOff + 16 * $R + 8 = g + $o1 by simp only [gStrcacheOff]] at hw1
    generalize hp0 : (bytesT8 m (g + $o0)).toNat = p0 at hw0
    generalize hp1 : (bytesT8 m (g + $o1)).toNat = p1 at hw1
    have hm0 : bytesT8 m (g + $o0) = BitVec.ofNat 64 p0 := by rw [← hp0]; simp
    have hm1 : bytesT8 m (g + $o1) = BitVec.ofNat 64 p1 := by rw [← hp1]; simp
    have hC0 := hL.cands _ hw0; have hC1 := hL.cands _ hw1
    have hp0lo := hC0.lo; have hp0hi := hC0.hi; have hp1lo := hC1.lo; have hp1hi := hC1.hi
    simp only [symTohost, symHeapEnd] at hp0lo hp0hi hp1lo hp1hi
    have hX : $okN (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o) := by fcx_ok
    simp only [callPre, List.cons_append, List.nil_append] at h
    have h : SegSt 0x8001772c#64 ($r0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o))
        (ArmPay (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o).m (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o).o) c :=
      h.repin (by pins_of h)
    have acc := Steps.refl c
    fat_run $ns h acc until [0x8002f77c]
    -- the frame
    have hM0 : ∀ a, (a + 48 ≤ sp ∨ sp ≤ a) →
        bytesT1 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) a = bytesT1 m a := by
      intro a ha; fcx_unfold; exact bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])
    have sv0 : bytesT8 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) (sp - 8) = r := by
      fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    have sv1 : bytesT8 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) (sp - 16) = f.s0 := by
      fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    have sv2 : bytesT8 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) (sp - 24) = f.s1 := by
      fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    have sv3 : bytesT8 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) (sp - 32) = f.s2 := by
      fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    have sv4 : bytesT8 ($m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o)) (sp - 40) = f.s3 := by
      fcx_unfold; simp (disch := omega) only [fw8_same, fw8_wm8]
    generalize hM0e : $m0N (plX [sp, L, g, p0, 1, p1, 0, 0] r f m o) = M0 at h hM0 sv0 sv1 sv2 sv3 sv4
    fcx_unfold at h
    -- `__umoddi3(s, STRCACHE_N)`
    have hu := umoddi3_sum (sp - 48) $A 53 0x8001775c#64
      ⟨f.s0, f.s1, (BitVec.ofNat 64 $A), BitVec.ofNat 64 L, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M0 o
      (by decide) (by decide) (by decide) (by decide)
    simp only [callPre, List.cons_append, List.nil_append] at hu
    obtain ⟨c1, acc, h⟩ := h.call acc (by pins_of h) hu
    dsimp only [wrRet] at h
    have hX2 : $okN (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o) := by fcx_ok
    have hc0 : bytesT8 M0 (L + 24) = BitVec.ofNat 64 g :=
      (bytesT8_congrT fun i _ => hM0 _ (.inl (by omega))).trans hx.Lg
    have hc1 : bytesT8 M0 (g + $o0) = BitVec.ofNat 64 p0 :=
      (bytesT8_congrT fun i _ => hM0 _ (.inl (by omega))).trans hm0
    have hc7 : bytesT8 M0 (g + $o1) = BitVec.ofNat 64 p1 :=
      (bytesT8_congrT fun i _ => hM0 _ (.inl (by omega))).trans hm1
    have h : SegSt 0x8001775c#64 ($r2N (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o))
        (ArmPay (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o).m (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o).o) c1 := by
      fcx_unfold; exact h.repin (by pins_of h)
    fat_run $ns h acc until [0x8003b920]
    fcx_unfold at h
    -- `strcmp(s, getstr(p[0]))`
    have hro0 : RodataRead M0 := fun o' ho => (hM0 _ (.inl (by
      simp only [Image.rodataBase, Image.rodataSize] at ho ⊢; omega))).trans (hx.ro o' ho)
    obtain ⟨hA0, hz0⟩ := hLS.read hro0
    obtain ⟨c2, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h) (strcmp_sumS $A (p0 + 24) $len 0x80017780#64
      (BitVec.ofNat 64 (sp - 48)) ⟨0x8005ced0#64, BitVec.ofNat 64 p0, BitVec.ofNat 64 (g + $o0), (BitVec.ofNat 64 $A),
        BitVec.ofNat 64 L, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M0 o
      ⟨hro0, by decide, by decide, by omega, by decide, by omega, hz0, .inl (by decide)⟩)
    dsimp only [RetAtS] at h
    by_cases hv0 : v = 0#64
    · -- a hit on `p[0]`
      have e0 : p0 = $lsF := cand_of_zero hC0 hl (by show $addrN % strcacheN = $R; decide) (fun a h1 h2 => hM0 a (.inl (by omega)))
        (by decide) hA0 hz0 hLS.nz hv hv0
      subst hv0
      have h : SegSt 0x80017780#64 ($r4N (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o))
          (ArmPay (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o).m (plX [sp, L, g, p0, 1, p1, 0, 0] r f M0 o).o) c2 := by
        fcx_unfold; exact h.repin (by pins_of h)
      fat_run $ns h acc
      fcx_unfold at h
      rw [e0] at h
      refine ⟨_, acc, M0, h.repin (by pins_of h), ⟨hx.cache.congr fun a h1 h2 => hM0 a (.inl (by simp only [gStrcacheOff, gEnd, strcacheN, strcacheM] at h1 h2; omega)),
        fun a ha => hM0 a ?_⟩⟩
      simp only [Below, not_or, not_and, Nat.not_le] at ha; omega
    -- a miss: `p[1]`
    have hvl := v.isLt
    have hvn : v.toNat ≠ 0 := fun e => hv0 (BitVec.eq_of_toNat_eq (by simp [e]))
    have hX6 : $okN (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M0 o) := by fcx_ok
    have h : SegSt 0x80017780#64 ($r6N (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M0 o))
        (ArmPay (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M0 o).m
          (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M0 o).o) c2 := by
      fcx_unfold; rw [ofNat_toNat64 v] at h; exact h.repin (by pins_of h)
    fat_run $ns h acc until [0x8003b920]
    fcx_unfold at h
    have hM1 : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) → bytesT1 (writeMap8 M0 (sp - 48) (sdData_val f.s4)) a = bytesT1 m a :=
      fun a ha => (fw1_wm8 (by omega)).trans (hM0 a (by omega))
    have sv0 := (fw8_wm8 (m := M0) (a := sp - 48) (d := sdData_val f.s4) (x := sp - 8) (by omega)).trans sv0
    have sv1 := (fw8_wm8 (m := M0) (a := sp - 48) (d := sdData_val f.s4) (x := sp - 16) (by omega)).trans sv1
    have sv2 := (fw8_wm8 (m := M0) (a := sp - 48) (d := sdData_val f.s4) (x := sp - 24) (by omega)).trans sv2
    have sv3 := (fw8_wm8 (m := M0) (a := sp - 48) (d := sdData_val f.s4) (x := sp - 32) (by omega)).trans sv3
    have sv4 := (fw8_wm8 (m := M0) (a := sp - 48) (d := sdData_val f.s4) (x := sp - 40) (by omega)).trans sv4
    have sv5 : bytesT8 (writeMap8 M0 (sp - 48) (sdData_val f.s4)) (sp - 48) = f.s4 := fw8_same rfl
    clear hM0 hc0 hc1 hc7 hro0 hA0 hz0
    generalize hM1e : writeMap8 M0 (sp - 48) (sdData_val f.s4) = M1 at h hM1 sv0 sv1 sv2 sv3 sv4 sv5
    have hro1 : RodataRead M1 := fun o' ho => (hM1 _ (.inl (by
      simp only [Image.rodataBase, Image.rodataSize] at ho ⊢; omega))).trans (hx.ro o' ho)
    obtain ⟨hA1, hz1⟩ := hLS.read hro1
    obtain ⟨c3, acc, ⟨v', h, hv'⟩⟩ := h.call acc (by pins_of h) (strcmp_sumS $A (p1 + 24) $len 0x80017798#64
      (BitVec.ofNat 64 (sp - 48)) ⟨0x8005ced0#64, BitVec.ofNat 64 p0, BitVec.ofNat 64 (g + $o0), (BitVec.ofNat 64 $A),
        BitVec.ofNat 64 L, BitVec.ofNat 64 p1, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M1 o
      ⟨hro1, by decide, by decide, by omega, by decide, by omega, hz1, .inl (by decide)⟩)
    dsimp only [RetAtS] at h
    by_cases hv0' : v' = 0#64
    · -- a hit on `p[1]`
      have e1 : p1 = $lsF := cand_of_zero hC1 hl (by show $addrN % strcacheN = $R; decide) (fun a h1 h2 => hM1 a (.inl (by omega)))
        (by decide) hA1 hz1 hLS.nz hv' hv0'
      subst hv0'
      have hX8 : $okN (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M1 o) := by fcx_ok
      have h : SegSt 0x80017798#64 ($r8N (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M1 o))
          (ArmPay (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M1 o).m
            (plX [sp, L, g, p0, v.toNat, p1, 0, 0] r f M1 o).o) c3 := by
        fcx_unfold; exact h.repin (by pins_of h)
      fat_run $ns h acc
      fcx_unfold at h
      rw [e1] at h
      refine ⟨_, acc, M1, h.repin (by pins_of h), ⟨hx.cache.congr fun a h1 h2 => hM1 a (.inl (by simp only [gStrcacheOff, gEnd, strcacheN, strcacheM] at h1 h2; omega)),
        fun a ha => hM1 a ?_⟩⟩
      simp only [Below, not_or, not_and, Nat.not_le] at ha; omega
    -- a miss: the row's shift, `strlen`, `luaS_newlstr`
    have hvl' := v'.isLt
    have hvn' : v'.toNat ≠ 0 := fun e => hv0' (BitVec.eq_of_toNat_eq (by simp [e]))
    have hX11 : $okN (plX [sp, L, g, p0, v'.toNat, p1, 0, 0] r f M1 o) := by fcx_ok
    have h : SegSt 0x80017798#64 ($r11N (plX [sp, L, g, p0, v'.toNat, p1, 0, 0] r f M1 o))
        (ArmPay (plX [sp, L, g, p0, v'.toNat, p1, 0, 0] r f M1 o).m
          (plX [sp, L, g, p0, v'.toNat, p1, 0, 0] r f M1 o).o) c3 := by
      fcx_unfold; rw [ofNat_toNat64 v'] at h; exact h.repin (by pins_of h)
    fat_run $ns h acc until [0x8003b770]
    fcx_unfold at h
    have hM2 : ∀ a, (a + 128 ≤ sp ∨ sp ≤ a) → (a + 1 ≤ g + $o1 ∨ g + ($o1 + 8) ≤ a) →
        bytesT1 (writeMap8 M1 (g + $o1) (sdData_val (BitVec.ofNat 64 p0))) a = bytesT1 m a :=
      fun a ha hb => (fw1_wm8 (by omega)).trans (hM1 a ha)
    have sv0 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 8)
      (by omega)).trans sv0
    have sv1 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 16)
      (by omega)).trans sv1
    have sv2 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 24)
      (by omega)).trans sv2
    have sv3 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 32)
      (by omega)).trans sv3
    have sv4 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 40)
      (by omega)).trans sv4
    have sv5 := (fw8_wm8 (m := M1) (a := g + $o1) (d := sdData_val (BitVec.ofNat 64 p0)) (x := sp - 48)
      (by omega)).trans sv5
    have w2 : bytesT8 (writeMap8 M1 (g + $o1) (sdData_val (BitVec.ofNat 64 p0))) (g + $o1) = BitVec.ofNat 64 p0 :=
      fw8_same rfl
    clear hM1 hro1 hA1 hz1
    generalize hM2e : writeMap8 M1 (g + $o1) (sdData_val (BitVec.ofNat 64 p0)) = M2 at h hM2 sv0 sv1 sv2 sv3 sv4 sv5 w2
    have hro2 : RodataRead M2 := fun o' ho => (hM2 _ (.inl (by
      simp only [Image.rodataBase, Image.rodataSize] at ho ⊢; omega)) (.inl (by
      simp only [Image.rodataBase, Image.rodataSize] at ho ⊢; omega))).trans (hx.ro o' ho)
    obtain ⟨hA2, hz2⟩ := hLS.read hro2
    obtain ⟨c4, acc, h⟩ := h.call acc (by pins_of h) (strlen_sumS $A $len 0x800177a8#64
      (BitVec.ofNat 64 (sp - 48)) ⟨0x8005ced0#64, BitVec.ofNat 64 p0, BitVec.ofNat 64 (g + $o0), (BitVec.ofNat 64 $A),
        BitVec.ofNat 64 L, BitVec.ofNat 64 p1, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M2 o
      ⟨by decide, by decide, by decide, hz2, hLS.read_nz hro2, .inl (by decide)⟩)
    dsimp only [RetAtS] at h
    have hX13 : $okN (plX [sp, L, g, p0, v'.toNat, p1, $len, 0] r f M2 o) := by fcx_ok
    have h : SegSt 0x800177a8#64 ($r13N (plX [sp, L, g, p0, v'.toNat, p1, $len, 0] r f M2 o))
        (ArmPay (plX [sp, L, g, p0, v'.toNat, p1, $len, 0] r f M2 o).m
          (plX [sp, L, g, p0, v'.toNat, p1, $len, 0] r f M2 o).o) c4 := by
      fcx_unfold; exact h.repin (by pins_of h)
    fat_run $ns h acc until [0x80017694]
    fcx_unfold at h
    have hfa : ∀ a, FL a → a + 128 ≤ sp ∧ (a + 1 ≤ g + $o1 ∨ g + ($o1 + 8) ≤ a) := fun a ha => by
      have h1 := (hx.foot a ha).1; have h2 := (hx.foot a ha).2
      simp only [heapEnd, symHeapEnd, Rng, gStrcacheOff, strcacheN, strcacheM] at h1 h2
      omega
    obtain ⟨rt2, hL2⟩ := hx.lits M2 fun a ha => hM2 a (.inl (hfa a ha).1) (hfa a ha).2
    have hI : InternIn M2 (sp - 48) L $A g $bN ls.seed $lsF rt2 0x800177b8#64 := {
      sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega,
      L_he := by omega, L_al := by omega, s_lo := by decide, s_th := by decide, l_lo := by decide,
      g_lo := by omega, g_hi := by omega,
      Lg := (bytesT8_congrT fun i _ => hM2 _ (.inl (by omega)) (by omega)).trans hx.Lg,
      bytes := hA2, lit := $hL2F, rt_g := hL2.g, hash_lo := hL2.hash_lo, hash_hi := hL2.hash_hi,
      size_hi := hL2.size_hi }
    have hn := newlstr_sum (sp - 48) L $A g $lsF $bN
      ls.seed rt2 0x800177b8#64 ⟨BitVec.ofNat 64 p0, BitVec.ofNat 64 (g + $o0), (BitVec.ofNat 64 $A), BitVec.ofNat 64 L,
        BitVec.ofNat 64 p1, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩ M2 o hI
    simp only [callPre, List.cons_append, List.nil_append] at hn
    obtain ⟨c5, acc, M3, h, hp3⟩ := h.call acc (by pins_of h) hn
    dsimp only [wrRet] at h
    have hk3 : ∀ a, (a + 129 ≤ sp ∨ sp - 48 ≤ a) → a ≠ $lsF + 9 → bytesT1 M3 a = bytesT1 M2 a :=
      fun a ha hn => hp3.keep a (by simp only [gcMarkedOff, Below, not_or, not_and, Nat.not_le]; omega)
    have sv0 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv0
    have sv1 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv1
    have sv2 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv2
    have sv3 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv3
    have sv4 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv4
    have sv5 := (bytesT8_congrT fun i _ => hk3 _ (.inr (by omega)) (by omega)).trans sv5
    have hX15 : $okN (plX [sp, L, g, p0, v'.toNat, p1, $len, $lsF] r f M3 o) := by fcx_ok
    have h : SegSt 0x800177b8#64 ($r15N (plX [sp, L, g, p0, v'.toNat, p1, $len, $lsF] r f M3 o))
        (ArmPay (plX [sp, L, g, p0, v'.toNat, p1, $len, $lsF] r f M3 o).m
          (plX [sp, L, g, p0, v'.toNat, p1, $len, $lsF] r f M3 o).o) c5 := by
      fcx_unfold; exact h.repin (by pins_of h)
    fat_run $ns h acc
    fcx_unfold at h
    refine ⟨_, acc, _, h.repin (by pins_of h), ⟨?_, fun a ha => ?_⟩⟩
    · refine hx.cache.shift (R := $R) (by decide) ?_ hts ?_ fun i hi hr => ?_
      · rw [show g + gStrcacheOff + 16 * $R = g + $o0 by simp only [gStrcacheOff], fw8_same rfl, BitVec.toNat_ofNat]
        omega
      · rw [show g + gStrcacheOff + 16 * $R + 8 = g + $o1 by simp only [gStrcacheOff],
          show g + gStrcacheOff + 16 * $R = g + $o0 by simp only [gStrcacheOff], fw8_wm8 (by omega),
          bytesT8_congrT fun i _ => hk3 _ (.inl (by omega)) (by omega), w2, hm0]
      · simp only [strcacheN, strcacheM, gStrcacheOff] at hi hr ⊢
        rw [fw8_wm8 (by omega), bytesT8_congrT fun j _ => hk3 _ (.inl (by omega)) (by omega)]
        exact bytesT8_congrT fun j _ => hM2 _ (.inl (by omega)) (by omega)
    · simp only [Rng, gStrcacheOff, strcacheN, strcacheM, gcMarkedOff, Below, not_or, not_and, Nat.not_le,
        Nat.not_lt] at ha
      rw [fw1_wm8 (by omega), hk3 a (by omega) (by omega),
        hM2 a (by omega) (by omega)]))

/-- **`luaS_new(L, litNilAddr)`** returns the literal's interned string
(`snew_run`). -/
theorem snew_nil (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : SNewIn m sp L g sl ls FL r) (htg : Apart ls.nil 30 g gEnd) :
    Triple (SegSt 0x8001772c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004f2b8#64⟩] sp r f)
        (ArmPay m o))
      (snewPost r sp ls.nil f g ls m o) := by
  snew_run Lua.Vm.AtF.LuaSNewNil 0x8004f2b8 47 1304 1312 nil litNilAddr nilB litStr_nil 3

/-- **`luaS_new(L, litTrueAddr)`** returns the literal's interned string
(`snew_run`). -/
theorem snew_true (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : SNewIn m sp L g sl ls FL r) (htg : Apart ls.tru 30 g gEnd) :
    Triple (SegSt 0x8001772c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004f2e8#64⟩] sp r f)
        (ArmPay m o))
      (snewPost r sp ls.tru f g ls m o) := by
  snew_run Lua.Vm.AtF.LuaSNewTrue 0x8004f2e8 42 1224 1232 tru litTrueAddr trueB litStr_true 4

/-- **`luaS_new(L, litFalseAddr)`** returns the literal's interned string
(`snew_run`). -/
theorem snew_false (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : SNewIn m sp L g sl ls FL r) (htg : Apart ls.fls 30 g gEnd) :
    Triple (SegSt 0x8001772c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004f280#64⟩] sp r f)
        (ArmPay m o))
      (snewPost r sp ls.fls f g ls m o) := by
  snew_run Lua.Vm.AtF.LuaSNewFalse 0x8004f280 44 1256 1264 fls litFalseAddr falseB litStr_false 5

/-- **`luaS_new(L, litTosAddr)`** returns the literal's interned string
(`snew_run`). -/
theorem snew_tos (sp L g sl : Nat) (ls : LitPtrs) (FL : Nat → Prop) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : SNewIn m sp L g sl ls FL r) (htg : Apart ls.tos 30 g gEnd) :
    Triple (SegSt 0x8001772c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, 0x8004fd20#64⟩] sp r f)
        (ArmPay m o))
      (snewPost r sp ls.tos f g ls m o) := by
  snew_run Lua.Vm.AtF.LuaSNewTos 0x8004fd20 8 680 688 tos litTosAddr tosB litStr_tos 10

end Lua.Vm.Sim.Kit

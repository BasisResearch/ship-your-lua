import Lua.Vm.Sim.Kit.TolSplit
import Lua.Vm.Sim.Kit.TolFlt
import Lua.Vm.Sim.Kit.TolFnProof

/-!
# `TolFlt_Statement` from `FloatToStr_Statement` (lane F1-25)

`luaL_tolstring` on a float argument in `luaB_print`'s loop (`TolArg IsFlt`):
the run cut at `tostringbuff`'s return (`tolflt_pre`: a bignum computation,
`tolflt_post`: the interning), glued to `TolPost` by `tolPost_of_split` over
the class facts `argStr_flt` (the model's `tostringbuff`, no literal: every
byte of it is a sign, a digit, the point, `e` or a letter of `inf`/`nan`,
`G14Byte`, and every literal has a byte that is not). The one premise is
`lua_number2str`'s run, `FloatToStr_Statement`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The class facts -/

/-- Every byte `tostringbuff` writes for a float is `%.14g`'s or `".0"`'s. -/
theorem tsbU8_g14 (x : BitVec 64) : ∀ c ∈ tsbU8 x, Lua.Num.G14Byte c := by
  intro c hc
  simp only [tsbU8, Lua.Num.tostringbuffBits, Lua.Num.tostringbuff] at hc
  split at hc
  · rcases List.mem_append.mp hc with hc | hc
    · exact Lua.Num.fmt14g_byte _ _ c hc
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      rcases hc with rfl | rfl <;> decide
  · exact Lua.Num.fmt14g_byte _ _ c hc

/-- **No literal is a float's string**: each has a byte `%.14g` never writes. -/
theorem lits_ne_tsbU8 (ls : LitPtrs) (x : BitVec 64) : ∀ l ∈ ls.table, l.bytes ≠ tsbU8 x := by
  intro l hl he
  have h := tsbU8_g14 x
  rw [← he] at h
  simp only [LitPtrs.table, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> dsimp only at h <;> revert h <;> decide

/-- **A literal's object does not hold a string of `G14Byte`s**: at its byte
`j` the literal has a byte that is no `G14Byte`. -/
theorem lit_nomatch_g14 {M : Mem} {rt : RtPtrs} {seed : UInt32} {lb : List UInt8} {ts : Nat}
    (hl : LitInterned M rt seed lb ts) (j : Nat) (hj : j < lb.length) (hbad : ¬ Lua.Num.G14Byte (lb.getD j 0))
    {b : List UInt8} (hb : ∀ c ∈ b, Lua.Num.G14Byte c) (hb40 : b.length ≤ 40)
    (hlen : bytesT1 M (ts + 11) = BitVec.ofNat 8 b.length)
    (hbytes : ∀ i, i < b.length → bytesT1 M (ts + 24 + i) = BitVec.ofNat 8 (b.getD i 0).toNat) : False := by
  obtain ⟨hl1, hl2⟩ := hl.repr.total hl.short
  have hs := hl.short
  simp only [maxShortLen] at hs
  rw [hl1] at hlen
  have e : lb.length = b.length := by
    have := congrArg BitVec.toNat hlen
    simp only [BitVec.toNat_ofNat] at this
    omega
  have h2 := hl2 j hj
  rw [hbytes j (by omega)] at h2
  have e2 : b.getD j 0 = lb.getD j 0 := by
    have := congrArg BitVec.toNat h2
    simp only [BitVec.toNat_ofNat] at this
    apply UInt8.ext_iff.mpr
    have := (b.getD j 0).toNat_lt; have := (lb.getD j 0).toNat_lt
    simp only [UInt8.toNat] at *
    omega
  apply hbad
  rw [← e2]
  apply hb
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.getElem_mem _

/-- **No literal's object holds a float's string.** -/
theorem lits_nomatch_flt {M : Mem} {g sl : Nat} {ls : LitPtrs} {rt : RtPtrs} (hL : LitsIn M g sl ls rt)
    (x : BitVec 64) (hb40 : (tsbU8 x).length ≤ 40) :
    ∀ p ∈ ls.strs, bytesT1 M (p + 11) = BitVec.ofNat 8 (tsbU8 x).length →
      (∀ i, i < (tsbU8 x).length → bytesT1 M (p + 24 + i) = BitVec.ofNat 8 ((tsbU8 x).getD i 0).toNat) →
        False := by
  intro p hp hlen hbytes
  have hb := tsbU8_g14 x
  simp only [LitPtrs.strs, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact lit_nomatch_g14 hL.nil 2 (by decide) (by decide) hb hb40 hlen hbytes
  · exact lit_nomatch_g14 hL.tru 0 (by decide) (by decide) hb hb40 hlen hbytes
  · exact lit_nomatch_g14 hL.fls 2 (by decide) (by decide) hb hb40 hlen hbytes
  · exact lit_nomatch_g14 hL.tos 0 (by decide) (by decide) hb hb40 hlen hbytes

/-- The bytes `print` prints for a float are `tostringbuff`'s. -/
theorem argBytes_flt (x : BitVec 64) :
    argBytes (.flt (Float.Model.ofBits (UInt64.ofBitVec x)) x.msb) =
      (tsbU8 x).map fun c => BitVec.ofNat 8 c.toNat := by
  simp only [argBytes, Value.show, bytesToString, String.toList_ofList, List.map_map]
  apply List.map_congr_left
  intro c _
  simp only [Function.comp_apply]
  have := c.toNat_lt
  rw [show (Char.ofNat c.toNat).toNat = c.toNat by rw [Char.ofNat, dif_pos (Or.inl (by omega))]; rfl]
  rfl

/-- **A float's class facts** (its string's length from the run: `snprintf`
returns one to twenty-one bytes, `tostringbuff` adds two at most). -/
theorem argStr_flt (x : BitVec 64) (hlo : 1 ≤ (tsbBytes x).length) (hhi : (tsbBytes x).length ≤ 23) :
    ArgStr (.flt (Float.Model.ofBits (UInt64.ofBitVec x)) x.msb) (tsbU8 x) where
  arg := argBytes_flt x
  len_lo := by rw [tsbU8_length]; exact hlo
  len_hi := by rw [tsbU8_length]; omega
  cost := by decide
  lits := fun ls => lits_ne_tsbU8 ls x
  no_lit := fun hL => lits_nomatch_flt hL x (by rw [tsbU8_length]; omega)

/-! ## `TolFlt_Statement` -/

/-- **`luaL_tolstring` on a float argument in `luaB_print`'s loop**
(`TolFlt_Statement`, lane F1-25), from `lua_number2str`'s run
(`FloatToStr_Statement`): the two halves `tolflt_pre`/`tolflt_post` glued by
`tolPost_of_split` (the bignum computation within the float's budget beyond
its string, `dtoaRoom`), `luaS_newlstr`'s table read at the memory the first
half leaves (the caller's objects kept: in chunks in use, apart from the
bignums). -/
theorem tolFlt_of (hF : FloatToStr_Statement) : TolFlt_Statement := by
  intro sp0 L nci func n tbc sl g ls args ι D G B FL ph0 H0 M0 i v hIn hn hv hC hi1 hin ph H m o r f hS hP hr
  cases v with
  | flt xm nn =>
    have q := hn.ok
    have q6 := hn.sp_big
    have hp := hIn.placed
    have hHE : heapEnd = 0x87800000 := rfl
    have hHS : heapStart = 0x8006ecd0 := rfl
    -- the argument's bits, from its representation
    have hA : ArgsAt func ι args m := hIn.args_fz m fun a ha =>
      hS.keep a (ha.elim (fun h => .inl h) fun h => .inr (.inl h))
    have hidx : func + 16 * (i - 1 + 1) = func + 16 * i := by congr 1; omega
    have hR := hA (i - 1) _ hv
    rw [hidx] at hR
    generalize hw : slotVal m (func + 16 * i) = w at hR
    generalize ht : slotTag m (func + 16 * i) = t at hR
    cases hR with
    | flt hq =>
      have hcost : 0 < argCost (.flt (Float.Model.ofBits (UInt64.ofBitVec w)) w.msb) := by simp [argCost]
      have hpos : 0 < prAllocs args i := by rw [prAllocs_succ hi1 hv, if_pos hcost]; omega
      -- the entry facts at `luaB_print`'s state
      have hx : TolDIn m (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g w r :=
        tolV_in hIn hn hS hv hcost (fun _ => ⟨ht.symm.trans rfl, hw⟩) (by decide)
          (by rw [show g + 504 = g + gMtOff + 8 * luaTnumber by rfl]; exact hIn.mt luaTnumber (by simp))
          hi1 hin hr
      -- what `_dtoa_r` needs: the heap, the bignums, room for their allocations
      have hI : PffIn m H B := by
        refine ⟨(hS.stat hpos).fmt, hP.heap, ?_, hS.big, fun a hb => ?_⟩
        · have h1 := hS.room (by rw [prCost_succ hi1 hv]; simp [argCost])
          rw [prCost_succ hi1 hv] at h1
          simp only [argCost, dtoaRoom] at h1 ⊢
          omega
        · have hk := hS.bigIn.inK a hb
          exact ⟨hk.inuse, hk.lo, hk.hi⟩
      have hBh : ∀ a, B a → a < heapEnd := fun a ha => (hS.bigIn.inK a ha).hi
      have hFr : ∀ a, TfFr (sp0 - 64) a → heapEnd ≤ a ∧ a < sp0 - 64 := fun a ha => by
        simp only [TfFr] at ha; omega
      intro c h
      -- the string's length, from the run's first half
      obtain ⟨-, -, M1, H1, B1, -, hmid⟩ :=
        tolflt_pre hF (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g w r f m o H B hx hI c h
      have hcls := argStr_flt w hmid.pff.len_lo hmid.pff.len_hi
      refine tolPost_of_split (c := dtoaRoom) (F := TfFr (sp0 - 64))
        (Q := fun M H' B' c => TfMid (sp0 - 64) L i (sp0 - 56) g (func + 16 * n + 16) r w f M o c)
        hIn hn hS hP hv hcls hi1 (by simp [argCost, dtoaRoom]) hFr
        (tolflt_pre hF (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g w r f m o H B hx hI)
        (fun M1 H1 B1 hR1 K X W cw size hash head d nuse hT c' hq => ?_) c h
      -- the second half, at the memory the first leaves
      have hp' := hIn.placed
      have kL : ∀ a, L ≤ a → a < L + stateSize → bytesT1 M1 a = bytesT1 m a := fun a h1 h2 =>
        hR1.keep_inUse (hS.kept (hIn.L_in a h1 h2)).inuse (hIn.L_in a h1 h2).lo
          (fun hb => hS.bigIn.x a hb (.inr (.inl ⟨h1, h2⟩)))
          (fun hf => by have := (hFr a hf).1; have := (hIn.L_in a h1 h2).hi; omega)
      have kg : ∀ a, g ≤ a → a < g + gEnd → bytesT1 M1 a = bytesT1 m a := fun a h1 h2 =>
        hR1.keep_inUse (hS.kept (hIn.g_in a h1 h2)).inuse (hIn.g_in a h1 h2).lo
          (fun hb => hS.bigIn.x a hb (.inr (.inr (.inl ⟨h1, h2⟩))))
          (fun hf => by have := (hFr a hf).1; have := (hIn.g_in a h1 h2).hi; omega)
      have hrod : RodataRead M1 := hx.rod.congr_rod fun a h1 h2 => by
        have : Image.rodataBase + Image.rodataSize = 0x8005c6a8 := rfl
        have : Image.rodataBase = 0x8004ecc8 := rfl
        refine hR1.keep_static hBh (by omega) (fun hg => ?_) (fun hr' => ?_)
          (fun hf => by have := (hFr a hf).1; omega)
        · have : symMallocAv = 0x8005c6d0 := rfl
          have : symMallocSbrkBase = 0x8005d388 := rfl
          have : symBrk = 0x8005d3b8 := rfl
          have : symMallocMallinfo = 0x8005e560 := rfl
          have : errnoAddr = 0x8005d408 := rfl
          simp only [MallocGlobal] at hg; omega
        · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hr'; omega
      have hx' := hx
      ti_in hx'
      have hPf : PfIn M1 (sp0 - 64 - 48) L g (func + 16 * n + 16) 0x80021ccc#64 := {
        sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega
        L_al := by omega, L_he := by omega, g_lo := by omega, g_hi := by omega, t_lo := by omega
        t_hi := by omega, t_al := by omega, tL := by omega, tg := by omega, Lg := by omega
        Lg_w := (bytesT8_congrT fun j _ => kL _ (by omega) (by simp only [stateSize]; omega)).trans hx.g_w
        top_w := (bytesT8_congrT fun j _ => kL _ (by omega) (by simp only [stateSize]; omega)).trans hx.top_w
        rod := hrod }
      have hgc : bytesT1 M1 (g + gGcstpOff) = 0x1#8 :=
        (kg _ (by simp only [gGcstpOff]; omega)
          (by simp only [gGcstpOff, gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)).trans hx.gcstp
      exact tolflt_post AllocProof.mallocR_proved (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g w r f
        m M1 o hx hPf ls.seed K X W cw size hash head d nuse H1 hT hgc c' hq
  | nil => exact absurd hC id
  | bool _ => exact absurd hC id
  | int _ => exact absurd hC id
  | str _ => exact absurd hC id
  | builtin _ => exact absurd hC id

/-- **`luaB_print` on the C frame** from `CALL`'s open part (lane F1-15 …
F1-25): every value class per argument, floats by `tolFlt_of` over
`CallOpen`'s one field, `lua_number2str`'s run (`FloatToStr_Statement`).
(Moved from `Kit/TolFnProof.lean`.) -/
theorem CallOpen.print (O : CallOpen) : PrintRel_Statement := printRel_tol (tolFlt_of O.floatToStr)

/-- (lane F1-25) **`PrintFlt_Statement` from `lua_number2str`'s run.** -/
theorem printFlt_of (hF : FloatToStr_Statement) : PrintFlt_Statement := printFlt_of_tol (tolFlt_of hF)

/-- (lane F1-25) **`PrintFn_Statement` from `lua_number2str`'s run.** -/
theorem printFn_of (hF : FloatToStr_Statement) : PrintFn_Statement := printFn_of_tol (tolFlt_of hF)

end Lua.Vm.Sim.Kit

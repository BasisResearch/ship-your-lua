import Lua.Vm.Sim.Kit.Getmetafield
import Lua.Vm.Sim.Kit.Tolstring
import Lua.Vm.AtF.TolTopL
import Lua.Vm.AtF.TolStrS
import Lua.Vm.AtF.TolStrL

/-!
# `luaL_tolstring` on a string argument (lane F1-17)

`luaL_tolstring(L, i, &l)` (`0x80021b2c`) on a short or long string, on the
callee-context route (`Lua/Vm/AtF/{TolStrS,TolStrL}.lean`,
`gen_lua_at.py --fn luaL_tolstring/str,luaL_tolstring/lstr`, one module per
literal tag): `lua_absindex`, `luaL_callmeta` → `lua_getmetatable` (the
string metatable `G(L)->mt[LUA_TSTRING]`, pushed) → `luaL_getmetafield.part.0`
(a call node: `gmf_miss_sum`, the miss of `"__tostring"`, `Kit/Getmetafield.lean`)
→ 0, `lua_type` (`LUA_TSTRING`), `lua_pushvalue(L, i)`, then the tail
`lua_tolstring(L, -1, &l)` of the string at the top (`toltop_sum`, or
`toltopl_sum` for a long string's `u.lnglen`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `lua_tolstring(L, -1, &l)` of a long string at the top -/

/-- **A long string at the top**: `L->top`, the slot below it a long string
(`LUA_VLNGSTR`) at `ts`, `shrlen` `0xff` and `u.lnglen` its length. -/
structure TopStrL (m : Mem) (L top ts len : Nat) : Prop where
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  tag_w : bytesT1 m (top - 8) = 0x54#8
  val_w : bytesT8 m (top - 16) = BitVec.ofNat 64 ts
  shr_w : bytesT1 m (ts + 11) = 0xff#8
  len_w : bytesT8 m (ts + 16) = BitVec.ofNat 64 len

/-- **`lua_tolstring(L, -1, &l)` of a long string at the top**: `l` its
`u.lnglen`, the contents returned. -/
theorem toltopl_sum {sp L lenp top ts len : Nat} {r : BitVec 64} (f : AbiFrame) {m : Mem} (o : Array String)
    (hx : TopNums sp L lenp top ts r) (ht : TopStrL m L top ts len) :
    Triple (SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (wrRet r sp (ts + 24) f (writeMap8 m lenp (sdData_val (BitVec.ofNat 64 len))) o) := by
  intro c h
  have := hx.sp_hi; have := hx.ra; have := hx.L_lo; have := hx.L_hi; have := hx.L_al; have := hx.l_lo
  have := hx.l_hi; have := hx.l_al; have := hx.t_lo; have := hx.t_hi; have := hx.s_lo; have := hx.s_hi
  have hX : Lua.Vm.AtF.TolTopL.Ok (ttX sp L lenp top ts r f m o) := by fcx_ok
  have hc0 := ht.top_w; have hc1 := ht.tag_w; have hc2 := ht.val_w
  have hg_3 : (zero_extend (m := 64) (bytesT1 m (ts + 11) : BitVec (8 * 1)) == 0xff#64) = true := by
    rw [ht.shr_w]; decide
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80002994#64 (Lua.Vm.AtF.TolTopL.r0 (ttX sp L lenp top ts r f m o))
      (ArmPay (ttX sp L lenp top ts r f m o).m (ttX sp L lenp top ts r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TolTopL h acc
  fcx_unfold at h
  rw [ht.len_w] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ## `luaL_tolstring` on a string: the facts and the regions -/

/-- **What `luaL_tolstring` writes on a string argument**: its callees'
frames below `sp`, `&l`, `L->top`, the slots `[top, top + 32)` (the string,
`"__tostring"`'s key slot), `g`'s string cache, `totalbytes` and `GCdebt`,
`"__tostring"`'s mark. -/
def TolSW (sp L lenp g top : Nat) (ls : LitPtrs) (a : Nat) : Prop :=
  (sp ≤ a + 16384 + 256 ∧ a < sp) ∨ Rng lenp 8 a ∨ Rng (L + 16) 8 a ∨ Rng top 32 a ∨
    Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a ∨ Rng (g + gTotalbytesOff) 8 a ∨
    Rng (g + gGCdebtOff) 8 a ∨ Rng (ls.tos + gcMarkedOff) 1 a

/-- **What `luaL_tolstring` reads on a string argument**: `L->ci`, its
`func`, `L->top`, `G(L)`, the argument's tag and string. -/
structure TolSCells (m : Mem) (L i nci func top g ts : Nat) (tag : BitVec 8) : Prop where
  ci_w : bytesT8 m (L + 32) = BitVec.ofNat 64 nci
  func_w : bytesT8 m nci = BitVec.ofNat 64 func
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  g_w : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  tag_w : bytesT1 m (16 * i + func + 8) = tag
  val_w : bytesT8 m (16 * i + func) = BitVec.ofNat 64 ts

/-- **What `luaL_tolstring` needs on a string argument** beyond its numbers
(`TolNums`): room for its callees' frames, where `L`, `g` and the slots
`[top, top + 48)` lie (apart, with `"__tostring"`'s string), `L->tbclist`
below `top`, and `lua_pushstring`'s facts (`.rodata`, the literals frozen on
`FL` off what the run writes, the cache's candidates, the collector stopped). -/
structure TolSIn (m : Mem) (sp L i nci func top g sl tbc : Nat) (ls : LitPtrs) (FL : Nat → Prop) : Prop where
  sp_big : heapEnd + 16384 + 2048 ≤ sp
  L_lo : symTohost + 16 ≤ L
  L_hi : L + stateSize ≤ heapEnd
  g_lo : symTohost + 16 ≤ g
  g_hi : g + gEnd ≤ heapEnd
  g_al : g % 8 = 0
  t_lo : symTohost + 16 ≤ top
  t_hi : top + 48 ≤ heapEnd
  t_al : top % 8 = 0
  sL : Apart top 48 L stateSize
  sg : Apart top 48 g gEnd
  Lg : Apart L stateSize g gEnd
  st : Apart ls.tos 30 top 48
  lL : Apart ls.tos 30 L stateSize
  lg : Apart ls.tos 30 g gEnd
  room : top + 48 ≤ sl
  tbc_w : bytesT8 m (L + 64) = BitVec.ofNat 64 tbc
  tbc_lt : tbc < top
  ro : RodataRead m
  lits : Frozen FL (fun M => LitsHold M g sl ls) m
  foot : ∀ a, FL a → a < heapEnd ∧ ¬ Rng (g + gStrcacheOff) (8 * strcacheN * strcacheM) a
  fl_ap : ∀ a, FL a → ¬ (Rng (L + 16) 8 a ∨ Rng top 32 a ∨ Rng (g + gTotalbytesOff) 8 a ∨
    Rng (g + gGCdebtOff) 8 a ∨ a = ls.tos + gcMarkedOff)
  cache : LitCache m g ls
  gcstp : bytesT1 m (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr
  /-- `L->ci`'s `func` and the argument's slot, read after the metafield's
  miss, apart from what it writes -/
  ci_he : nci + 8 ≤ heapEnd
  ci_t : Apart nci 8 top 32
  ci_L : Apart nci 8 (L + 16) 8
  ci_g : Apart nci 8 g gEnd
  ci_s : Apart nci 8 ls.tos 30
  sl_L : Apart (16 * i + func) 16 L stateSize
  sl_g : Apart (16 * i + func) 16 g gEnd
  sl_s : Apart (16 * i + func) 16 ls.tos 30

/-- **What `luaL_tolstring` leaves on a string argument**: the string at the
top (`L->top` one slot up), `l` its length, the cache's candidates, every
byte kept off `TolSW`. -/
structure TolStrPost (m m' : Mem) (sp L lenp g top : Nat) (ls : LitPtrs) (len : Nat) : Prop where
  top_w : bytesT8 m' (L + 16) = BitVec.ofNat 64 (top + 16)
  len_w : bytesT8 m' lenp = BitVec.ofNat 64 len
  cache : LitCache m' g ls
  keep : ∀ a, ¬ TolSW sp L lenp g top ls a → bytesT1 m' a = bytesT1 m a

/-- The string metatable `G(L)->mt[LUA_TSTRING]` (`StrMtMiss.mt_w`), as `ld`
reads it. -/
theorem TolSIn.smt {m : Mem} {sp L i nci func top g sl tbc : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) :
    bytesT8 m (g + 512) = BitVec.ofNat 64 ls.smt ∧ ls.smt ≠ 0 ∧ symTohost + 16 ≤ ls.smt ∧
      ls.smt + 32 ≤ 2 ^ 32 := by
  obtain ⟨rt, hli⟩ := hT.lits.self
  have hs := hli.strmt
  rw [hli.g] at hs
  exact ⟨bT8_of_fill (bytesT8_of_rd64 hs.mt_w), hs.ne, hs.smt_lo, hs.smt_hi⟩

/-- **`luaL_getmetafield`'s facts at its call** (`GmfIn`) from `luaL_tolstring`'s
(`TolSIn`), through what the run wrote before it (`M2`: the frames, the
metatable's slot at `top`, `L->top`). -/
theorem gmfIn_of {m M2 : Mem} {sp L i nci func top g sl tbc : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hsp : sp ≤ 2 ^ 32) (hspa : sp % 16 = 0) (hLa : L % 8 = 0)
    (hg : bytesT8 m (L + 24) = BitVec.ofNat 64 g)
    (hM2 : ∀ a, ¬ ((sp - 80 ≤ a ∧ a < sp) ∨ Rng top 9 a ∨ Rng (L + 16) 8 a) → bytesT1 M2 a = bytesT1 m a)
    (htop : bytesT8 M2 (L + 16) = BitVec.ofNat 64 (top + 16))
    (hmt : bytesT8 M2 top = BitVec.ofNat 64 ls.smt) :
    GmfIn M2 (sp - 80) L (top + 16) g sl ls.smt tbc ls FL := by
  have := hT.sp_big; have := hT.L_lo; have := hT.L_hi; have := hT.g_lo; have := hT.g_hi; have := hT.g_al
  have := hT.t_lo; have := hT.t_hi; have := hT.t_al; have := hT.tbc_lt
  have hHE : heapEnd = 0x87800000 := rfl
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hgE : gEnd = 1400 := rfl
  have hSS : stateSize = 200 := rfl
  have hsL := hT.sL; have hsg := hT.sg; have hLg := hT.Lg; have hst := hT.st; have hlL := hT.lL
  have hlg := hT.lg
  simp only [Apart] at hsL hsg hLg hst hlL hlg
  -- a byte below `top` or at least `top + 9`, below the frames, off `L->top`
  have kM : ∀ a, a < sp - 80 → (a < top ∨ top + 9 ≤ a) → ¬ Rng (L + 16) 8 a → bytesT1 M2 a = bytesT1 m a :=
    fun a h1 h2 h3 => hM2 a (by simp only [Rng] at h3 ⊢; omega)
  have hcx : PushCx (sp - 80 - 32) L (top + 16) g 0x80020544#64 := by
    constructor
    · decide
    all_goals (try simp only [Apart]); (try generalize heapEnd = E at *); omega
  have hla : LitApart ls.tos L g (top + 16) := by
    constructor <;> (simp only [Apart]; omega)
  refine ⟨htop, ?_, by rw [show top + 16 - 16 = top by omega]; exact hmt, ?_, by omega, rfl, hcx,
    by omega, by omega, by omega, by simp only [Apart]; omega, by simp only [Apart]; omega,
    by simp only [Apart]; omega, hla, by have := hT.room; omega, fun o' ho => ?_,
    hT.lits.trans fun a ha => ?_, hT.foot, fun a ha => ?_, hT.cache.congr fun a h1 h2 => ?_, ?_⟩
  · rw [bytesT8_congrT fun j _ => kM _ (by omega) (by omega) (by simp only [Rng]; omega)]; exact hg
  · rw [bytesT8_congrT fun j _ => kM _ (by omega) (by omega) (by simp only [Rng]; omega)]; exact hT.tbc_w
  · have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl
    rw [kM _ (by omega) (by omega) (by simp only [Rng]; omega)]; exact hT.ro o' ho
  · have h1 := hT.foot a ha; have h2 := hT.fl_ap a ha
    simp only [not_or, Rng] at h2
    exact kM a (by omega) (by omega) (by simp only [Rng]; omega)
  · have h2 := hT.fl_ap a ha
    simp only [not_or, Rng] at h2 ⊢
    exact ⟨h2.1, fun h => h2.2.1 ⟨by omega, by omega⟩, h2.2.2.1, h2.2.2.2.1, h2.2.2.2.2⟩
  · exact kM a (by omega) (by omega) (by simp only [Rng]; omega)
  · rw [kM _ (by simp only [gGcstpOff]; omega) (by simp only [gGcstpOff]; omega)
      (by simp only [Rng, gGcstpOff]; omega)]; exact hT.gcstp

/-- `luaL_tolstring`'s root contexts on a string: `sp`, `L`, `i`, `&l`,
`L->ci`, `func`, `L->top`, `G(L)`, the string metatable, the string; `ra` and
the frame. -/
@[at_row] abbrev tsX (sp L i lenp nci func top g smt ts : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, L, i, lenp, nci, func, top, g, smt, ts]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- **The memory after the metafield's miss** (the root `0x80021a7c`):
`L->ci`, its `func`, `L->top` back at `top`, the argument's slot,
`luaL_callmeta`'s and `luaL_tolstring`'s saved words, the cache's
candidates, every byte kept off `TolSW` but `&l`. -/
structure TolSMid (m M : Mem) (sp L i lenp nci func top g ts : Nat) (r : BitVec 64) (f : AbiFrame) (ls : LitPtrs)
    (tag : BitVec 8) : Prop where
  ci_w : bytesT8 M (L + 32) = BitVec.ofNat 64 nci
  func_w : bytesT8 M nci = BitVec.ofNat 64 func
  top_w : bytesT8 M (L + 16) = BitVec.ofNat 64 top
  tag_w : bytesT1 M (16 * i + func + 8) = tag
  val_w : bytesT8 M (16 * i + func) = BitVec.ofNat 64 ts
  cra_w : bytesT8 M (sp - 56) = 0x80021b64#64
  cs0_w : bytesT8 M (sp - 64) = BitVec.ofNat 64 L
  cs1_w : bytesT8 M (sp - 72) = BitVec.ofNat 64 i
  cs2_w : bytesT8 M (sp - 80) = BitVec.ofNat 64 lenp
  ra_w : bytesT8 M (sp - 8) = r
  s0_w : bytesT8 M (sp - 16) = f.s0
  s1_w : bytesT8 M (sp - 24) = f.s1
  s2_w : bytesT8 M (sp - 32) = f.s2
  cache : LitCache M g ls
  keep : ∀ a, ¬ TolSW sp L lenp g top ls a → bytesT1 M a = bytesT1 m a

/-- **The run up to the metafield's miss, assembled** (`TolSMid`): the
stores before `luaL_getmetafield` (`M2`, the generated row's), its summary's
post (`GmfPost`). -/
theorem tolSMid_of {m M2 M3 : Mem} {sp L i lenp nci func top g sl tbc ts : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    {r : BitVec 64} {f : AbiFrame} {tag : BitVec 8} (hx : TolNums sp L i lenp nci func top g ts r)
    (hc : TolSCells m L i nci func top g ts tag) (hT : TolSIn m sp L i nci func top g sl tbc ls FL)
    (hM2 : ∀ a, ¬ ((sp - 80 ≤ a ∧ a < sp) ∨ Rng top 9 a ∨ Rng (L + 16) 8 a) → bytesT1 M2 a = bytesT1 m a)
    (hfr : bytesT8 M2 (sp - 56) = 0x80021b64#64 ∧ bytesT8 M2 (sp - 64) = BitVec.ofNat 64 L ∧
      bytesT8 M2 (sp - 72) = BitVec.ofNat 64 i ∧ bytesT8 M2 (sp - 80) = BitVec.ofNat 64 lenp ∧
      bytesT8 M2 (sp - 8) = r ∧ bytesT8 M2 (sp - 16) = f.s0 ∧ bytesT8 M2 (sp - 24) = f.s1 ∧
      bytesT8 M2 (sp - 32) = f.s2)
    (hg : GmfPost M2 M3 (sp - 80) L g (top + 16) ls) :
    TolSMid m M3 sp L i lenp nci func top g ts r f ls tag := by
  have := hT.sp_big; have := hT.L_lo; have := hT.L_hi; have := hT.g_lo; have := hT.g_hi
  have := hT.t_lo; have := hT.t_hi; have := hx.f_top; have := hx.ci_sp; have := hx.L_sp
  have hHE : heapEnd = 0x87800000 := rfl
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hgE : gEnd = 1400 := rfl
  have hSS : stateSize = 200 := rfl
  -- what `luaL_getmetafield` keeps of `M2`, below its frames
  have kG : ∀ a, a + 16384 + 64 ≤ sp - 80 → ¬ Rng (L + 16) 8 a → ¬ Rng (top + 16) 16 a →
      ¬ (g + 16 ≤ a ∧ a < g + 32) → ¬ (g + 552 ≤ a ∧ a < g + 1400) → ¬ Rng (ls.tos + gcMarkedOff) 1 a →
      bytesT1 M3 a = bytesT1 M2 a := fun a h1 h2 h3 h4 h5 h6 => hg.keep a (.inr ⟨h1, h2, h3,
    by simp only [Rng, gStrcacheOff, strcacheN, strcacheM]; omega, by simp only [Rng, gTotalbytesOff]; omega,
    by simp only [Rng, gGCdebtOff]; omega, h6⟩)
  have kF : ∀ a, sp - 80 ≤ a → bytesT1 M3 a = bytesT1 M2 a := fun a h => hg.keep a (.inl h)
  refine ⟨?_, ?_, by rw [hg.top_w, show top + 16 - 16 = top by omega], ?_, ?_,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.2.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.2.2.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.2.2.2.2.1,
    (bytesT8_congrT fun j _ => kF _ (by omega)).trans hfr.2.2.2.2.2.2.2, hg.cache, fun a ha => ?_⟩
  · have hsL := hT.sL; have hLg := hT.Lg; have hlL := hT.lL
    simp only [Apart] at hsL hLg hlL
    rw [bytesT8_congrT fun j _ => (kG _ (by omega) (by simp only [Rng]; omega) (by simp only [Rng]; omega)
      (by omega) (by omega) (by simp only [Rng, gcMarkedOff]; omega)).trans
      (hM2 _ (by simp only [Rng]; omega))]
    exact hc.ci_w
  · have h1 := hT.ci_t; have h2 := hT.ci_L; have h3 := hT.ci_g; have h4 := hT.ci_s; have := hT.ci_he
    simp only [Apart] at h1 h2 h3 h4
    rw [bytesT8_congrT fun j _ => (kG _ (by omega) (by simp only [Rng]; omega) (by simp only [Rng]; omega)
      (by omega) (by omega) (by simp only [Rng, gcMarkedOff]; omega)).trans
      (hM2 _ (by simp only [Rng]; omega))]
    exact hc.func_w
  · have h1 := hT.sl_L; have h3 := hT.sl_g; have h4 := hT.sl_s
    simp only [Apart] at h1 h3 h4
    rw [kG _ (by omega) (by simp only [Rng]; omega) (by simp only [Rng]; omega) (by omega) (by omega)
      (by simp only [Rng, gcMarkedOff]; omega), hM2 _ (by simp only [Rng]; omega)]
    exact hc.tag_w
  · have h1 := hT.sl_L; have h3 := hT.sl_g; have h4 := hT.sl_s
    simp only [Apart] at h1 h3 h4
    rw [bytesT8_congrT fun j _ => (kG _ (by omega) (by simp only [Rng]; omega) (by simp only [Rng]; omega)
      (by omega) (by omega) (by simp only [Rng, gcMarkedOff]; omega)).trans
      (hM2 _ (by simp only [Rng]; omega))]
    exact hc.val_w
  · simp only [TolSW, not_or, not_and, Nat.not_lt] at ha
    obtain ⟨h1, -, h2, h3, h4, h5, h6, h7⟩ := ha
    have h1' : a + 16384 + 256 < sp ∨ sp ≤ a := by
      by_cases e : sp ≤ a + 16384 + 256
      · exact .inr (h1 e)
      · exact .inl (by omega)
    rcases h1' with h1' | h1'
    · rw [kG a (by omega) h2 (by simp only [Rng] at h3 ⊢; omega)
        (by simp only [Rng, gTotalbytesOff, gGCdebtOff] at h5 h6; omega)
        (by simp only [Rng, gStrcacheOff, strcacheN, strcacheM] at h4 ⊢; omega) h7,
        hM2 a (by simp only [Rng] at h2 h3 ⊢; omega)]
    · rw [kF a (by omega), hM2 a (by simp only [Rng] at h2 h3 ⊢; omega)]

/-- **The stores before `luaL_getmetafield`** (the generated row's memory
`m2`, the same in both tag modules): the frames of `luaL_tolstring` and
`luaL_callmeta`, the metatable pushed at `top`, `L->top`. -/
theorem tolS_m2 {sp L i lenp nci func top g smt ts : Nat} {r : BitVec 64} {f : AbiFrame} {m : Mem}
    {o : Array String} (hsp : 0x87800000 + 16384 ≤ sp) (hL : L + 200 ≤ 0x87800000) (ht : top + 48 ≤ 0x87800000)
    (hsL : top + 48 ≤ L ∨ L + 200 ≤ top) (hl : sp ≤ lenp) :
    (∀ a, ¬ ((sp - 80 ≤ a ∧ a < sp) ∨ Rng top 9 a ∨ Rng (L + 16) 8 a) →
      bytesT1 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) a = bytesT1 m a) ∧
    (bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 56) =
        0x80021b64#64 ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 64) =
        BitVec.ofNat 64 L ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 72) =
        BitVec.ofNat 64 i ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 80) =
        BitVec.ofNat 64 lenp ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 8) = r ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 16) = f.s0 ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 24) = f.s1 ∧
      bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (sp - 32) = f.s2) ∧
    bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) (L + 16) =
      BitVec.ofNat 64 (top + 16) ∧
    bytesT8 (Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g smt ts r f m o)) top =
      BitVec.ofNat 64 smt := by
  fcx_unfold
  refine ⟨fun a ha => ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · simp only [Rng, not_or, not_and, Nat.not_lt] at ha
    simp (disch := omega) only [fw1_wm8, fw1_ins]
  all_goals fat_rd

set_option hygiene false in
/-- **`luaL_tolstring` on a string, up to the metafield's miss** (one tag
module `ns`, the generator's cells being literals): `lua_absindex`,
`luaL_callmeta` → `lua_getmetatable` (the string metatable pushed: `tolS_m2`),
`luaL_getmetafield.part.0` (`gmf_miss_sum`, its facts by `gmfIn_of`), the
root `0x80021a7c` (`tolSMid_of`). -/
macro "tol_pre_run " ns:ident : tactic => do
  let okN := Lean.mkIdent (ns.getId ++ `Ok)
  let r0N := Lean.mkIdent (ns.getId ++ `r0)
  let m2N := Lean.mkIdent (ns.getId ++ `m2)
  `(tactic| (
    have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.ra; have := hx.L_lo; have := hx.L_hi
    have := hx.L_al; have := hx.i_lo; have := hx.i_hi; have := hx.l_lo; have := hx.l_hi; have := hx.l_al
    have := hx.ci_lo; have := hx.ci_hi; have := hx.f_lo; have := hx.f_top; have := hx.t_hi; have := hx.g_lo
    have := hx.g_hi; have := hx.L_sp; have := hx.ci_sp; have := hx.t_sp; have := hx.g_sp; have := hx.t_lo
    have := hx.s_lo; have := hx.s_hi
    have := hT.sp_big; have := hT.t_al; have := hT.t_lo; have := hT.t_hi; have := hT.L_hi
    have hHE : heapEnd = 0x87800000 := rfl
    have hTH : symTohost = 0x8005c6c0 := rfl
    obtain ⟨hc5, hf1, hsm, hsm'⟩ := hT.smt
    have : 0x8005c6d0 ≤ ls.smt := by omega
    have hg_2' : (BitVec.ofNat 64 ls.smt == 0x0#64) = false := ofNat64_beq0 (by omega) hf1
    have hX : $okN (tsX sp L i lenp nci func top g ls.smt ts r f m o) := by fcx_ok
    have hc0 := hc.ci_w; have hc1 := hc.func_w; have hc2 := hc.top_w; have hc3 := hc.tag_w; have hc4 := hc.g_w
    have hc10 := hc.val_w
    have hf0 : 16 * i + func < top := by omega
    have hg_6 := absindex_pos i hx.i_lo hx.i_hi
    have hg_2 := sge0_pos i hx.i_lo (by omega)
    simp only [callPre, List.cons_append, List.nil_append] at h
    have h : SegSt 0x80021b2c#64 ($r0N (tsX sp L i lenp nci func top g ls.smt ts r f m o))
        (ArmPay (tsX sp L i lenp nci func top g ls.smt ts r f m o).m
          (tsX sp L i lenp nci func top g ls.smt ts r f m o).o) c := h.repin (by pins_of h)
    have acc := Steps.refl c
    fat_run $ns h acc until [0x8002052c]
    have hsL := hT.sL; simp only [Apart] at hsL
    rw [show $m2N (tsX sp L i lenp nci func top g ls.smt ts r f m o) =
      Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g ls.smt ts r f m o) from rfl] at h
    obtain ⟨hM2, hfr, htop2, hmt2⟩ := tolS_m2 (sp := sp) (L := L) (i := i) (lenp := lenp) (nci := nci)
      (func := func) (top := top) (g := g) (smt := ls.smt) (ts := ts) (r := r) (f := f) (m := m) (o := o)
      (by omega) (by simp only [stateSize] at *; omega) (by omega) (by simp only [stateSize] at hsL; omega) hx.l_lo
    generalize Lua.Vm.AtF.TolStrS.m2 (tsX sp L i lenp nci func top g ls.smt ts r f m o) = M2 at h hM2 hfr htop2 hmt2
    fcx_unfold at h
    have hgin := gmfIn_of hT hx.sp_hi hx.sp_al hx.L_al hc.g_w hM2 htop2 hmt2
    obtain ⟨c1, s1, M3, hret, hgp⟩ := gmf_miss_sum (r := 0x80021a7c#64)
      ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 i, 0x8004fd20#64, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11⟩
      o (by decide) hgin _ (by simp only [callPre, List.cons_append, List.nil_append, litTosAddr]; exact h.repin (by pins_of h))
    simp only [wrRet] at hret
    exact ⟨c1, acc.trans s1, M3, tolSMid_of hx hc hT hM2 hfr hgp, hret.repin (by pins_of hret)⟩))

/-- **`luaL_tolstring` on a short string, up to the metafield's miss** (`tol_pre_run`). -/
theorem tol_s_pre {sp L i lenp nci func top g sl tbc ts : Nat} {ls : LitPtrs} {FL : Nat → Prop} {r : BitVec 64}
    {f : AbiFrame} {m : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hc : TolSCells m L i nci func top g ts 0x44#8) (hT : TolSIn m sp L i nci func top g sl tbc ls FL) {c : Config}
    (h : SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o) c) :
    ∃ c1, Steps c c1 ∧ ∃ M3, TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x44#8 ∧
      SegSt 0x80021a7c#64 (Lua.Vm.AtF.TolStrS.r3 (tsX sp L i lenp nci func top g ls.smt ts r f M3 o))
        (ArmPay (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).m
          (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).o) c1 := by
  tol_pre_run Lua.Vm.AtF.TolStrS

/-- **`luaL_tolstring` on a long string, up to the metafield's miss** (`tol_pre_run`). -/
theorem tol_l_pre {sp L i lenp nci func top g sl tbc ts : Nat} {ls : LitPtrs} {FL : Nat → Prop} {r : BitVec 64}
    {f : AbiFrame} {m : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hc : TolSCells m L i nci func top g ts 0x54#8) (hT : TolSIn m sp L i nci func top g sl tbc ls FL) {c : Config}
    (h : SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o) c) :
    ∃ c1, Steps c c1 ∧ ∃ M3, TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x54#8 ∧
      SegSt 0x80021a7c#64 (Lua.Vm.AtF.TolStrL.r3 (tsX sp L i lenp nci func top g ls.smt ts r f M3 o))
        (ArmPay (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).m
          (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).o) c1 := by
  tol_pre_run Lua.Vm.AtF.TolStrL

/-- A byte off a range, as the forwarding lemmas take it. -/
theorem rng_split {a lo n : Nat} (h : lo ≤ a → lo + n ≤ a) : a + 1 ≤ lo ∨ lo + n ≤ a := by
  rcases Nat.lt_or_ge a lo with e | e
  · exact .inl e
  · exact .inr (h e)

/-- **The stores after the metafield's miss** (`lua_pushvalue`: the string
at `top`, `L->top`) and the tail's `&l`, from `TolSMid`: `TolStrPost`. -/
theorem tolStrPost_of {m M3 : Mem} {sp L i lenp nci func top g sl tbc ts len : Nat} {ls : LitPtrs}
    {FL : Nat → Prop} {r : BitVec 64} {f : AbiFrame} {tag : BitVec 8} (hx : TolNums sp L i lenp nci func top g ts r)
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hmid : TolSMid m M3 sp L i lenp nci func top g ts r f ls tag)
    (d : BitVec 64) :
    TolStrPost m (writeMap8 (writeMap8 ((writeMap8 M3 top (sdData_val (BitVec.ofNat 64 ts))).insert (top + 8)
      (stData 1 d)) (L + 16) (sdData_val (BitVec.ofNat 64 (top + 16)))) lenp
      (sdData_val (BitVec.ofNat 64 len))) sp L lenp g top ls len := by
  have := hx.l_lo; have := hT.sp_big; have := hT.L_hi; have := hT.t_hi; have := hT.g_hi; have := hT.L_lo
  have := hT.g_lo; have := hT.t_lo
  have hHE : heapEnd = 0x87800000 := rfl
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hgE : gEnd = 1400 := rfl
  have hSS : stateSize = 200 := rfl
  have hsL := hT.sL; simp only [Apart] at hsL
  refine ⟨by rw [fw8_wm8 (by omega), fw8_same rfl], fw8_same rfl, hmid.cache.congr fun a h1 h2 => ?_,
    fun a ha => ?_⟩
  · have hsg := hT.sg; have hLg := hT.Lg; simp only [Apart] at hsg hLg
    simp (disch := omega) only [fw1_wm8, fw1_ins]
  · simp only [TolSW, not_or, not_and, Nat.not_lt] at ha
    rw [← hmid.keep a (by simp only [TolSW, not_or, not_and, Nat.not_lt]; exact ha)]
    obtain ⟨-, h2, h3, h4, -⟩ := ha
    simp only [Rng, not_and, Nat.not_lt] at h2 h3 h4
    have e2 := rng_split h2; have e3 := rng_split h3; have e4 := rng_split h4
    rw [fw1_wm8 e2, fw1_wm8 e3, fw1_ins (by omega), fw1_wm8 (by omega)]

/-- **`lua_pushvalue`'s stores** of the string `ts` of tag `tag` at `top`. -/
abbrev TolPushMem (M : Mem) (L top ts : Nat) (tag : BitVec 64) : Mem :=
  writeMap8 ((writeMap8 M top (sdData_val (BitVec.ofNat 64 ts))).insert (top + 8) (stData 1 tag)) (L + 16)
    (sdData_val (BitVec.ofNat 64 (top + 16)))

set_option hygiene false in
/-- **`luaL_tolstring` on a string, from the metafield's miss to the tail**
(one tag module `ns`): `luaL_callmeta`'s return, `lua_type`, `lua_pushvalue`,
up to `j lua_tolstring`. -/
macro "tol_mid_run " ns:ident : tactic => do
  let okN := Lean.mkIdent (ns.getId ++ `Ok)
  `(tactic| (
    have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.ra; have := hx.L_lo; have := hx.L_hi
    have := hx.L_al; have := hx.i_lo; have := hx.i_hi; have := hx.l_lo; have := hx.l_hi; have := hx.l_al
    have := hx.ci_lo; have := hx.ci_hi; have := hx.f_lo; have := hx.f_top; have := hx.t_hi; have := hx.g_lo
    have := hx.g_hi; have := hx.L_sp; have := hx.ci_sp; have := hx.t_sp; have := hx.g_sp; have := hx.t_lo
    have := hx.s_lo; have := hx.s_hi
    have := hT.sp_big; have := hT.t_al; have := hT.t_lo; have := hT.t_hi; have := hT.L_hi
    obtain ⟨-, -, hsm, -⟩ := hT.smt
    have hTH : symTohost = 0x8005c6c0 := rfl
    have : 0x8005c6d0 ≤ ls.smt := by omega
    have hX : $okN (tsX sp L i lenp nci func top g ls.smt ts r f M3 o) := by fcx_ok
    have hc0 := hmid.ci_w; have hc1 := hmid.func_w; have hc2 := hmid.top_w; have hc3 := hmid.tag_w
    have hc10 := hmid.val_w; have hc6 := hmid.cra_w; have hc7 := hmid.cs0_w; have hc8 := hmid.cs1_w
    have hc9 := hmid.cs2_w; have hc11 := hmid.s0_w; have hc12 := hmid.ra_w; have hc13 := hmid.s1_w
    have hc14 := hmid.s2_w
    have hf0 : 16 * i + func < top := by omega
    have hg_6 := absindex_pos i hx.i_lo hx.i_hi
    have hg_2 := sge0_pos i hx.i_lo (by omega)
    have acc := Steps.refl c1
    fat_run $ns h acc until [0x80002994]
    fcx_unfold at h
    exact ⟨_, acc, by simp only [callPre, List.cons_append, List.nil_append]; exact h.repin (by pins_of h)⟩))

/-- **`luaL_tolstring` on a short string, from the metafield's miss to the tail**
(`tol_mid_run`): the string pushed (`TolPushMem`). -/
theorem tol_s_mid {sp L i lenp nci func top g sl tbc ts : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    {r : BitVec 64} {f : AbiFrame} {m M3 : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hmid : TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x44#8)
    {c1 : Config}
    (h : SegSt 0x80021a7c#64 (Lua.Vm.AtF.TolStrS.r3 (tsX sp L i lenp nci func top g ls.smt ts r f M3 o))
        (ArmPay (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).m
          (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).o) c1) :
    ∃ c2, Steps c1 c2 ∧ SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f)
      (ArmPay (TolPushMem M3 L top ts 0x44#64) o) c2 := by
  tol_mid_run Lua.Vm.AtF.TolStrS

/-- **`luaL_tolstring` on a long string, from the metafield's miss to the tail**
(`tol_mid_run`): the string pushed (`TolPushMem`). -/
theorem tol_l_mid {sp L i lenp nci func top g sl tbc ts : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    {r : BitVec 64} {f : AbiFrame} {m M3 : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hmid : TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x54#8)
    {c1 : Config}
    (h : SegSt 0x80021a7c#64 (Lua.Vm.AtF.TolStrL.r3 (tsX sp L i lenp nci func top g ls.smt ts r f M3 o))
        (ArmPay (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).m
          (tsX sp L i lenp nci func top g ls.smt ts r f M3 o).o) c1) :
    ∃ c2, Steps c1 c2 ∧ SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f)
      (ArmPay (TolPushMem M3 L top ts 0x54#64) o) c2 := by
  tol_mid_run Lua.Vm.AtF.TolStrL

set_option hygiene false in
/-- `luaL_tolstring`'s numbers in context (`omega`'s facts). -/
local macro "tol_nums" : tactic => `(tactic| (
  have := hx.sp_lo; have := hx.sp_hi; have := hx.sp_al; have := hx.ra; have := hx.L_lo; have := hx.L_hi
  have := hx.L_al; have := hx.l_lo; have := hx.l_hi; have := hx.l_al; have := hx.t_hi; have := hx.t_lo
  have := hx.t_sp; have := hx.L_sp; have := hx.s_lo; have := hx.s_hi
  have := hT.sp_big; have := hT.t_al; have := hT.t_lo; have := hT.t_hi; have := hT.L_hi
  have hsL := hT.sL; simp only [Apart, stateSize] at hsL))

/-- **The tail `lua_tolstring(L, -1, &l)` of a short string** (`toltop_sum`):
`TolStrPost`. -/
theorem tol_tail_s {sp L i lenp nci func top g sl tbc ts len : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    {r : BitVec 64} {f : AbiFrame} {m M3 : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hmid : TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x44#8)
    (hlen : bytesT1 M3 (ts + 11) = BitVec.ofNat 8 len) (hl : len < 255)
    (hsk : ¬ (Rng top 9 (ts + 11) ∨ Rng (L + 16) 8 (ts + 11))) {c2 : Config}
    (h : SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f)
      (ArmPay (TolPushMem M3 L top ts 0x44#64) o) c2) :
    ∃ c', Steps c2 c' ∧ ∃ m', wrRet r sp (ts + 24) f m' o c' ∧ TolStrPost m m' sp L lenp g top ls len := by
  tol_nums
  simp only [Rng, not_or, not_and, Nat.not_lt] at hsk
  have e1 := rng_split hsk.2; have e2 := rng_split hsk.1
  obtain ⟨c3, s3, hret⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (ts := ts) (top := top + 16)
    (len := len) f o
    ⟨by omega, hx.ra, by omega, by omega, hx.L_al, by omega, by omega, hx.l_al, by omega, by omega, hx.s_lo,
      hx.s_hi⟩
    ⟨by rw [fw8_same rfl], by rw [show top + 16 - 8 = top + 8 by omega, fw1_wm8 (by omega), fw1_same rfl]; rfl,
      by rw [show top + 16 - 16 = top by omega, fw8_wm8 (by omega), fw8_ins (by omega), fw8_same rfl],
      by rw [fw1_wm8 e1, fw1_ins (by omega), fw1_wm8 (by omega)]; exact hlen, hl⟩ _ h
  exact ⟨c3, s3, _, hret, tolStrPost_of hx hT hmid _⟩

/-- **The tail `lua_tolstring(L, -1, &l)` of a long string** (`toltopl_sum`:
`shrlen` `0xff`, `u.lnglen`): `TolStrPost`. -/
theorem tol_tail_l {sp L i lenp nci func top g sl tbc ts len : Nat} {ls : LitPtrs} {FL : Nat → Prop}
    {r : BitVec 64} {f : AbiFrame} {m M3 : Mem} {o : Array String} (hx : TolNums sp L i lenp nci func top g ts r)
    (hT : TolSIn m sp L i nci func top g sl tbc ls FL) (hmid : TolSMid m M3 sp L i lenp nci func top g ts r f ls 0x54#8)
    (hshr : bytesT1 M3 (ts + 11) = 0xff#8) (hlen : bytesT8 M3 (ts + 16) = BitVec.ofNat 64 len)
    (hsk : ∀ a, ts + 11 ≤ a → a < ts + 24 → ¬ (Rng top 9 a ∨ Rng (L + 16) 8 a)) {c2 : Config}
    (h : SegSt 0x80002994#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, 0xffffffffffffffff#64⟩, ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f)
      (ArmPay (TolPushMem M3 L top ts 0x54#64) o) c2) :
    ∃ c', Steps c2 c' ∧ ∃ m', wrRet r sp (ts + 24) f m' o c' ∧ TolStrPost m m' sp L lenp g top ls len := by
  tol_nums
  have kP : ∀ a, ts + 11 ≤ a → a < ts + 24 → bytesT1 (TolPushMem M3 L top ts 0x54#64) a = bytesT1 M3 a := by
    intro a h1 h2
    have := hsk a h1 h2
    simp only [Rng, not_or, not_and, Nat.not_lt] at this
    have e1 := rng_split this.2; have e2 := rng_split this.1
    rw [fw1_wm8 e1, fw1_ins (by omega), fw1_wm8 (by omega)]
  obtain ⟨c3, s3, hret⟩ := toltopl_sum (sp := sp) (L := L) (lenp := lenp) (ts := ts) (top := top + 16)
    (len := len) f o
    ⟨by omega, hx.ra, by omega, by omega, hx.L_al, by omega, by omega, hx.l_al, by omega, by omega, hx.s_lo,
      hx.s_hi⟩
    ⟨by rw [fw8_same rfl], by rw [show top + 16 - 8 = top + 8 by omega, fw1_wm8 (by omega), fw1_same rfl]; rfl,
      by rw [show top + 16 - 16 = top by omega, fw8_wm8 (by omega), fw8_ins (by omega), fw8_same rfl],
      by rw [kP _ (by omega) (by omega)]; exact hshr,
      by rw [bytesT8_congrT fun j _ => kP _ (by omega) (by omega)]; exact hlen⟩ _ h
  exact ⟨c3, s3, _, hret, tolStrPost_of hx hT hmid _⟩

end Lua.Vm.Sim.Kit

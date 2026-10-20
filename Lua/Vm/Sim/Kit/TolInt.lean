import Lua.Vm.Sim.Kit.PushfI
import Lua.Vm.Sim.Kit.Tolstring
import Lua.Vm.AtF.TolInt

/-!
# `luaL_tolstring` on an integer argument (lane F1-20)

`luaL_tolstring(L, i, &l)` on an integer: `luaL_callmeta` (no metatable for
numbers: `G(L)->mt[LUA_TNUMBER]` NULL), `lua_type`, `lua_isinteger`,
`lua_tointegerx`, `lua_pushfstring(L, "%I", i)` (a call node: `pushfI_sum`),
the tail `lua_tolstring(L, -1, &l)` (`toltop_sum`). Its at-lemmas are
generated (`Lua/Vm/AtF/TolInt.lean`): the entry and the return from
`lua_pushfstring` (`0x80021c40`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## The string's facts against another memory -/

/-- `NlTab` at a memory agreeing below the stack. -/
theorem NlTab.congr {m M : Mem} {L g top : Nat} {b : List UInt8} {seed : UInt32} {K X W : Nat → Prop}
    {cw : BitVec 8} {size hash head d nuse : Nat} {H : HeapIx}
    (h : NlTab m L g top b seed K X W cw size hash head d nuse H)
    (hk : ∀ a, a < 0x87800000 + 64 → bytesT1 M a = bytesT1 m a) :
    NlTab M L g top b seed K X W cw size hash head d nuse H := by
  have e2 : heapEnd = 0x87800000 := rfl
  have inHi : ∀ a, InUse H.chunks a → a < heapEnd + 8 := fun a hu => Nat.lt_of_not_le fun hc =>
    ChunkWalk.notInUse_hi h.new.heap.walk a (by have := h.new.heap.top_le; have := h.new.heap.brk_le; omega) hu
  exact {
  seed_w := (bytesT4_congrT fun j _ => hk _ (by
      have := inHi _ (h.new.g_in (g + 96 + j) (by omega) (by omega)); omega)).trans h.seed_w
  hK := h.hK
  xt := h.xt
  xL := h.xL
  xg := h.xg
  tab := fun M' hM' => h.tab M' fun a ha => (hM' a ha).trans (hk a (by omega))
  new := h.new.congr fun a ha => hk a ha
  top_in := h.top_in
  Lk := h.Lk }

/-- **`luaS_newlstr`'s outcome against another base memory** agreeing off
`G`, `G` (a stack region) containing the frames `F`. -/
theorem PfStr.trans {m0 m M3 : Mem} {F G : Nat → Prop} {g : Nat} {b : List UInt8} {seed : UInt32}
    {K X W : Nat → Prop} {size hash nuse head ts : Nat} {H H' : HeapIx}
    (h : PfStr m0 M3 F g b seed K X W size hash nuse head H ts H')
    (hK : ∀ a, K a → a < 0x87800000) (hG : ∀ a, G a → 0x87800000 ≤ a) (hFG : ∀ a, F a → G a)
    (hk : ∀ a, ¬ G a → bytesT1 m0 a = bytesT1 m a) (hg : g + 1400 ≤ 0x87800000) (hb : b.length ≤ 40) :
    PfStr m M3 G g b seed K X W size hash nuse head H ts H' := by
  have kK : ∀ a, a < 0x87800000 → bytesT1 m0 a = bytesT1 m a := fun a ha => hk a fun hga => by
    have := hG a hga; omega
  rcases h with ⟨hh, hH⟩ | hp
  · have o0 := hh.node.obj ts (Nat.le_refl _) (by omega)
    have o11 := hh.node.obj (ts + 11) (by omega) (by omega)
    have e11 : bytesT1 m0 (ts + 11) = bytesT1 m (ts + 11) := kK _ (hK _ o11.1)
    refine .inl ⟨⟨⟨(kK _ (hK _ (hh.node.obj (ts + 8) (by omega) (by omega)).1)).symm.trans hh.node.tt,
      fun a h1 h2 => ?_, hh.node.mark, hh.node.hnext⟩, e11 ▸ hh.len, fun j hj => ?_,
      fun a ha => (hh.keep a fun hf => ha (hFG a hf)).trans (hk a ha)⟩, hH⟩
    · rw [← e11] at h2; exact hh.node.obj a h1 h2
    · have hl : (bytesT1 m0 (ts + 11)).toNat = b.length := by
        rw [hh.len, BitVec.toNat_ofNat]; omega
      rw [← kK _ (hK _ (hh.node.obj _ (by omega) (by rw [hl]; omega)).1)]; exact hh.bytes j hj
  · refine .inr ((hp.trans (G := G) (fun a ha => hk a ha) (fun hga => by have := hG _ hga; omega)
      (fun j _ hga => by have := hG _ hga; omega)).mono fun a ha => ?_)
    rcases ha with ha | ha
    · exact hFG a ha
    · exact ha

/-- A stack byte off the frames `F`, as the call left it. -/
theorem PfStr.stack {m0 M3 : Mem} {F : Nat → Prop} {g : Nat} {b : List UInt8} {seed : UInt32}
    {K X W : Nat → Prop} {size hash nuse head ts : Nat} {H H' : HeapIx}
    (h : PfStr m0 M3 F g b seed K X W size hash nuse head H ts H') (hb : b.length ≤ 40)
    (hg : g + 1400 ≤ 0x87800000) (hbk : hash + 8 * ((luaHash seed b).toNat % size) + 8 ≤ 0x87800000) {a : Nat} (ha : 0x87800000 + 64 ≤ a) (hF : ¬ F a) : bytesT1 M3 a = bytesT1 m0 a := by
  have e1 : heapStart = 0x8006ecd0 := rfl
  have e2 : heapEnd = 0x87800000 := rfl
  rcases h with ⟨hh, -⟩ | hp
  · exact hh.keep a hF
  · have := hp.hi; have := hp.lo
    refine hp.keep a fun hc => ?_
    rcases hc with hc | hc | hc | hc | hc | hc | hc
    · rcases hc with hc | hc
      · exact absurd hc.lo (by omega)
      · omega
    all_goals first | (simp only [Rng] at hc; omega) | exact hF hc

/-- The context of `luaL_tolstring`'s rows on an integer: `sp`, `L`, `i`, `&l`,
`L->ci`, `func`, `L->top`, `G(L)`; `ra`, the frame, the integer. -/
@[at_row] abbrev tiX (sp L i lenp nci func top g : Nat) (r : BitVec 64) (f : AbiFrame) (v : BitVec 64) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, L, i, lenp, nci, func, top, g]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, v] m o

/-- **What `luaL_tolstring` needs on an argument of tag `tag` and payload
`w`** (lane F1-20; over the tag, lane F1-24): the frame (room for
`lua_pushfstring`'s below it), `L`, `L->ci`, `func`, `L->top`, `G(L)` and
where they lie, the argument's slot, no metatable for its type (the word
`g + mto`), `.rodata`, `snprintf`'s static words, the collector stopped. -/
structure TolVIn (m : Mem) (sp L i lenp nci func top g : Nat) (tag : BitVec 8) (mto : Nat) (w r : BitVec 64) :
    Prop where
  sp_lo : 0x87800000 + 16384 + 8192 + 48 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_al : L % 8 = 0
  L_he : L + 200 ≤ 0x87800000
  i_lo : 1 ≤ i
  i_hi : i < 2 ^ 20
  l_lo : sp ≤ lenp
  l_hi : lenp + 8 ≤ 2 ^ 32
  l_al : lenp % 8 = 0
  ci_lo : 0x8005c6d0 ≤ nci
  ci_he : nci + 64 ≤ 0x87800000
  f_lo : 0x8005c6d0 ≤ func
  f_top : func + 16 * i + 16 ≤ top
  t_lo : 0x8005c6d0 ≤ top
  t_hi : top + 32 ≤ 0x87800000
  t_al : top % 8 = 0
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  g_al : g % 8 = 0
  tL : top + 16 ≤ L ∨ L + 200 ≤ top
  tg : top + 16 ≤ g ∨ g + 1400 ≤ top
  Lg : L + 200 ≤ g ∨ g + 1400 ≤ L
  ci_w : bytesT8 m (L + 32) = BitVec.ofNat 64 nci
  func_w : bytesT8 m nci = BitVec.ofNat 64 func
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 top
  g_w : bytesT8 m (L + 24) = BitVec.ofNat 64 g
  tag_w : bytesT1 m (16 * i + func + 8) = tag
  val_w : bytesT8 m (16 * i + func) = w
  mt_w : bytesT8 m (g + mto) = 0x0#64
  rod : RodataRead m
  stat : FmtStatic m
  gcstp : bytesT1 m (g + gGcstpOff) = 0x1#8

/-- **What `luaL_tolstring` needs on an integer argument** (`LUA_VNUMINT`,
the integer `v`, `G(L)->mt[LUA_TNUMBER]`). -/
abbrev TolIIn (m : Mem) (sp L i lenp nci func top g : Nat) (v r : BitVec 64) : Prop :=
  TolVIn m sp L i lenp nci func top g 0x3#8 504 v r

/-- `luaL_tolstring`'s and its callees' frames: `[sp - 8240, sp)` (stated additively: `omega` on
nested truncated subtractions of large constants runs past the recursion limit). -/
def TolFr (sp a : Nat) : Prop := sp ≤ a + 8240 ∧ a < sp

/-- `RodataRead` at a memory agreeing on `.rodata`. -/
theorem RodataRead.congr {m M : Mem} (h : RodataRead m) (hk : ∀ a, a < 0x87800000 → bytesT1 M a = bytesT1 m a) :
    RodataRead M := fun o ho => by
  have : Image.rodataBase + Image.rodataSize ≤ 0x87800000 := by decide
  rw [hk _ (by omega)]; exact h o ho

/-- The frame `lua_pushfstring` sees from `luaL_tolstring`: `s0 = L`, `s1 = i`,
`s2 = &l`. -/
abbrev tiFr (L i lenp : Nat) (f : AbiFrame) : AbiFrame :=
  ⟨BitVec.ofNat 64 L, BitVec.ofNat 64 i, BitVec.ofNat 64 lenp, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9,
    f.s10, f.s11⟩

set_option hygiene false in
/-- `TolVIn`'s numbers in context. -/
macro "ti_in" hx:ident : tactic => `(tactic| (
  have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al; have := ($hx).ra; have := ($hx).L_lo
  have := ($hx).L_al; have := ($hx).L_he; have := ($hx).i_lo; have := ($hx).i_hi; have := ($hx).l_lo
  have := ($hx).l_hi; have := ($hx).l_al; have := ($hx).ci_lo; have := ($hx).ci_he; have := ($hx).f_lo
  have := ($hx).f_top; have := ($hx).t_lo; have := ($hx).t_hi; have := ($hx).t_al; have := ($hx).g_lo
  have := ($hx).g_hi; have := ($hx).g_al; have := ($hx).tL; have := ($hx).tg; have := ($hx).Lg))

/-- **`luaL_tolstring` on an integer, to `lua_pushfstring`'s call.** -/
theorem ti_pre (sp L i lenp nci func top g : Nat) (v r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : TolIIn m sp L i lenp nci func top g v r) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => SegSt 0x800030a4#64 (Lua.Vm.AtF.TolInt.r2 (tiX sp L i lenp nci func top g r f v m o))
        (ArmPay (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) o) c) := by
  intro c h
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.TolInt.Ok (tiX sp L i lenp nci func top g r f v m o) := by fcx_ok
  have hc0 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m ((tiX sp L i lenp nci func top g r f v m o).n 1 + 32) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 4) := hx.ci_w
  have hc1 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m ((tiX sp L i lenp nci func top g r f v m o).n 4) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 5) := hx.func_w
  have hc2 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m ((tiX sp L i lenp nci func top g r f v m o).n 1 + 16) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 6) := hx.top_w
  have hc3 : bytesT1 (tiX sp L i lenp nci func top g r f v m o).m
      (16 * (tiX sp L i lenp nci func top g r f v m o).n 2 + (tiX sp L i lenp nci func top g r f v m o).n 5 + 8) =
      0x3#8 := hx.tag_w
  have hc4 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m ((tiX sp L i lenp nci func top g r f v m o).n 1 + 24) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 7) := hx.g_w
  have hc5 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m ((tiX sp L i lenp nci func top g r f v m o).n 7 + 504) =
      0x0#64 := hx.mt_w
  have hc6 : bytesT8 (tiX sp L i lenp nci func top g r f v m o).m
      (16 * (tiX sp L i lenp nci func top g r f v m o).n 2 + (tiX sp L i lenp nci func top g r f v m o).n 5) =
      (tiX sp L i lenp nci func top g r f v m o).b 13 := hx.val_w
  have hf0 : 16 * (tiX sp L i lenp nci func top g r f v m o).n 2 + (tiX sp L i lenp nci func top g r f v m o).n 5 <
      (tiX sp L i lenp nci func top g r f v m o).n 6 := show 16 * i + func < top by omega
  have hg_6 := absindex_pos i hx.i_lo hx.i_hi
  have hg_2 : zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 2)) = false :=
    sge0_pos i hx.i_lo (by omega)
  have hg_5 : zopz0zI_u (BitVec.ofNat 64 (16 * (tiX sp L i lenp nci func top g r f v m o).n 2 +
      (tiX sp L i lenp nci func top g r f v m o).n 5)) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 6))
      = true := show zopz0zI_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = true by
    rw [fult (by omega) (by omega)]; simp; omega
  have hg_5' : zopz0zKzJ_u (BitVec.ofNat 64 (16 * (tiX sp L i lenp nci func top g r f v m o).n 2 +
      (tiX sp L i lenp nci func top g r f v m o).n 5)) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f v m o).n 6))
      = false := show zopz0zKzJ_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = false by
    rw [fuge (by omega) (by omega)]; simp; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80021b2c#64 (Lua.Vm.AtF.TolInt.r0 (tiX sp L i lenp nci func top g r f v m o))
      (ArmPay (tiX sp L i lenp nci func top g r f v m o).m (tiX sp L i lenp nci func top g r f v m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TolInt h acc until [0x800030a4]
  exact ⟨_, acc, h⟩

theorem pfFr_tolFr {sp : Nat} (hsp : 48 ≤ sp) : ∀ a, PfFr (sp - 48) a → TolFr sp a := by
  intro a ha
  simp only [PfFr, TolFr] at ha ⊢
  omega

/-- `luaL_tolstring`'s stores before `lua_pushfstring` (the generated `m2`):
its frame, the callees' below it. -/
theorem ti_m2 {sp L i lenp nci func top g : Nat} {r : BitVec 64} {f : AbiFrame} {v : BitVec 64} {m : Mem}
    {o : Array String} (hsp : 80 ≤ sp) :
    (∀ a, (a + 80 < sp ∨ sp ≤ a) →
      bytesT1 (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) a = bytesT1 m a) ∧
    bytesT8 (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) (sp - 8) = r ∧
    bytesT8 (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) (sp - 16) = f.s0 ∧
    bytesT8 (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) (sp - 24) = f.s1 ∧
    bytesT8 (Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o)) (sp - 32) = f.s2 := by
  simp only [Lua.Vm.AtF.TolInt.m2, tiX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [fw1_wm8]
  all_goals simp (disch := omega) only [fw8_wm8, fw8_same]

/-- **`luaL_tolstring(L, i, &l)` on an integer `v`** (lane F1-20): the digits
of `v` interned (`PfStr`, off the frames `TolFr`) and pushed (`PfPost`), `l`
their count, `getstr` of the string returned. -/
theorem tolint_sum (hM : MallocR_Statement) (hI2S : IntegerToStr_Statement) (sp L i lenp nci func top g : Nat)
    (v r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) (hx : TolIIn m sp L i lenp nci func top g v r)
    (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat) (H : HeapIx)
    (hT : NlTab m L g top (intU8 v) seed K X W cw size hash head d nuse H) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ ts M3 M H', PfStr m M3 (TolFr sp) g (intU8 v) seed K X W size hash nuse head H ts H' ∧
        PfPost M3 M (sp - 48) L g top ts ∧ PfTs M ts (intU8 v).length ∧
        wrRet r sp (ts + 24) f (writeMap8 M lenp (sdData_val (BitVec.ofNat 64 (intU8 v).length))) o c) := by
  intro c h
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hn1 := (intBytes_len v).1
  have hn2 := (intBytes_len v).2
  have hb40 : (intU8 v).length ≤ 40 := by rw [intU8_length]; omega
  obtain ⟨c1, s1, h1⟩ := ti_pre sp L i lenp nci func top g v r f m o hx c h
  obtain ⟨k2, w8, w16, w24, w32⟩ := ti_m2 (sp := sp) (L := L) (i := i) (lenp := lenp) (nci := nci) (func := func)
    (top := top) (g := g) (r := r) (f := f) (v := v) (m := m) (o := o) (by omega)
  generalize Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f v m o) = M2 at h1 k2 w8 w16 w24 w32
  have kl : ∀ a, a < 0x87800000 + 64 → bytesT1 M2 a = bytesT1 m a := fun a ha => k2 a (.inl (by omega))
  have hPf : PfIn M2 (sp - 48) L g top 0x80021c40#64 := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega
    L_al := by omega, L_he := by omega, g_lo := by omega, g_hi := by omega, t_lo := by omega, t_hi := by omega
    t_al := by omega, tL := by omega, tg := by omega, Lg := by omega
    Lg_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.g_w
    top_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.top_w
    rod := RodataRead.congr hx.rod fun a ha => kl a (by omega) }
  fcx_unfold at h1
  obtain ⟨c2, s2, ts, M3, M, H', hstr, hpost, hts, hret⟩ := pushfI_sum hM hI2S (sp - 48) L g top v 0x80021c40#64
    (tiFr L i lenp f) M2 o hPf (hx.stat.congr fun a ha => kl a (by omega)) seed K X W cw size hash head d nuse H
    (hT.congr kl) ((kl _ (by simp only [gGcstpOff]; omega)).trans hx.gcstp) hx.g_al c1
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h1.repin (by pins_of h1))
  -- the frame's words at the return: off the push and the string's writes
  have kF : ∀ a, sp - 48 ≤ a → a < sp → bytesT1 M a = bytesT1 M2 a := fun a h1 h2 =>
    (hpost.keep a (by simp only [Rng, PfFr, gTotalbytesOff, gGCdebtOff]; omega)).trans
      (hstr.stack hb40 (by omega) (by have := hT.new.bkt_he; omega) (by omega) (by simp only [PfFr]; omega))
  have hX1 : Lua.Vm.AtF.TolInt.Ok (tiX sp L i lenp nci func top g r f v M o) := by fcx_ok
  have hc7 : bytesT8 (tiX sp L i lenp nci func top g r f v M o).m ((tiX sp L i lenp nci func top g r f v M o).n 0 - 16) =
      (tiX sp L i lenp nci func top g r f v M o).b 1 :=
    show bytesT8 M (sp - 16) = f.s0 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w16
  have hc8 : bytesT8 (tiX sp L i lenp nci func top g r f v M o).m ((tiX sp L i lenp nci func top g r f v M o).n 0 - 8) =
      (tiX sp L i lenp nci func top g r f v M o).b 0 :=
    show bytesT8 M (sp - 8) = r from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w8
  have hc9 : bytesT8 (tiX sp L i lenp nci func top g r f v M o).m ((tiX sp L i lenp nci func top g r f v M o).n 0 - 24) =
      (tiX sp L i lenp nci func top g r f v M o).b 2 :=
    show bytesT8 M (sp - 24) = f.s1 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w24
  have hc10 : bytesT8 (tiX sp L i lenp nci func top g r f v M o).m ((tiX sp L i lenp nci func top g r f v M o).n 0 - 32) =
      (tiX sp L i lenp nci func top g r f v M o).b 3 :=
    show bytesT8 M (sp - 32) = f.s2 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w32
  simp only [wrRet] at hret
  have h : SegSt 0x80021c40#64 (Lua.Vm.AtF.TolInt.r3 (tiX sp L i lenp nci func top g r f v M o))
      (ArmPay (tiX sp L i lenp nci func top g r f v M o).m (tiX sp L i lenp nci func top g r f v M o).o) c2 := by
    fcx_unfold; exact hret.repin (by pins_of hret)
  have acc := s1.trans s2
  fat_run Lua.Vm.AtF.TolInt h acc until [0x80002994]
  fcx_unfold at h
  have hts1 := hts.ts_lo; have hts2 := hts.ts_hi
  obtain ⟨c3, s3, hfin⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (top := top + 16) (ts := ts)
    (len := (intU8 v).length) (r := r) f o
    ⟨by omega, hx.ra, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
    ⟨hpost.top_w, by rw [show top + 16 - 8 = top + 8 by omega]; exact hpost.tag,
      by rw [show top + 16 - 16 = top by omega]; exact hpost.val, hts.len, by omega⟩ _
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have hG : ∀ a, TolFr sp a → 0x87800000 ≤ a := fun a ha => by simp only [TolFr] at ha; omega
  have hFG : ∀ a, PfFr (sp - 48) a → TolFr sp a := pfFr_tolFr (by omega)
  have hk : ∀ a, ¬ TolFr sp a → bytesT1 M2 a = bytesT1 m a := fun a ha =>
    k2 a (by simp only [TolFr] at ha; omega)
  have hs2 := PfStr.trans hstr (fun a ha => (hT.hK a ha).2) hG hFG hk hx.g_hi hb40
  exact ⟨c3, acc.trans s3, ts, M3, M, H', hs2, hpost, hts, hfin⟩

end Lua.Vm.Sim.Kit

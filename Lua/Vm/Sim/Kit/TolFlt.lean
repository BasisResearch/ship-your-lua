import Lua.Vm.Sim.Kit.PushfF
import Lua.Vm.Sim.Kit.TolInt
import Lua.Vm.AtF.TolFlt

/-!
# `luaL_tolstring` on a float argument (lane F1-25)

`luaL_tolstring(L, i, &l)` on a float: `luaL_callmeta` (no metatable for
numbers: `G(L)->mt[LUA_TNUMBER]` NULL), `lua_type`, `lua_isinteger` (no),
`lua_tonumberx` (the double), `lua_pushfstring(L, "%f", n)` (`PushfF`), the
tail `lua_tolstring(L, -1, &l)` (`toltop_sum`). Its at-lemmas are generated
(`Lua/Vm/AtF/TolFlt.lean`): the entry and the return from `lua_pushfstring`
(`0x80021ccc`). The run's shape is `tolint_sum`'s, cut in two inside
`lua_pushfstring` at `tostringbuff`'s return (`tolflt_pre`, `tolflt_post`):
the first half a bignum computation (`BigRun`), the second `luaS_newlstr` on
the memory it leaves (`tolPost_of_split`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- **What `luaL_tolstring` needs on a float** (`LUA_VNUMFLT`, the double
`x`, `G(L)->mt[LUA_TNUMBER]`). -/
abbrev TolDIn (m : Mem) (sp L i lenp nci func top g : Nat) (x r : BitVec 64) : Prop :=
  TolVIn m sp L i lenp nci func top g 0x13#8 504 x r

/-- **`luaL_tolstring` on a float, to `lua_pushfstring`'s call.** -/
theorem tf_pre (sp L i lenp nci func top g : Nat) (x r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : TolDIn m sp L i lenp nci func top g x r) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => SegSt 0x800030a4#64 (Lua.Vm.AtF.TolFlt.r2 (tiX sp L i lenp nci func top g r f x m o))
        (ArmPay (Lua.Vm.AtF.TolFlt.m2 (tiX sp L i lenp nci func top g r f x m o)) o) c) := by
  intro c h
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.TolFlt.Ok (tiX sp L i lenp nci func top g r f x m o) := by fcx_ok
  have hc0 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m ((tiX sp L i lenp nci func top g r f x m o).n 1 + 32) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 4) := hx.ci_w
  have hc1 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m ((tiX sp L i lenp nci func top g r f x m o).n 4) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 5) := hx.func_w
  have hc2 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m ((tiX sp L i lenp nci func top g r f x m o).n 1 + 16) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 6) := hx.top_w
  have hc3 : bytesT1 (tiX sp L i lenp nci func top g r f x m o).m
      (16 * (tiX sp L i lenp nci func top g r f x m o).n 2 + (tiX sp L i lenp nci func top g r f x m o).n 5 + 8) =
      0x13#8 := hx.tag_w
  have hc4 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m ((tiX sp L i lenp nci func top g r f x m o).n 1 + 24) =
      BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 7) := hx.g_w
  have hc5 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m ((tiX sp L i lenp nci func top g r f x m o).n 7 + 504) =
      0x0#64 := hx.mt_w
  have hc6 : bytesT8 (tiX sp L i lenp nci func top g r f x m o).m
      (16 * (tiX sp L i lenp nci func top g r f x m o).n 2 + (tiX sp L i lenp nci func top g r f x m o).n 5) =
      (tiX sp L i lenp nci func top g r f x m o).b 13 := hx.val_w
  have hf0 : 16 * (tiX sp L i lenp nci func top g r f x m o).n 2 + (tiX sp L i lenp nci func top g r f x m o).n 5 <
      (tiX sp L i lenp nci func top g r f x m o).n 6 := show 16 * i + func < top by omega
  have hg_6 := absindex_pos i hx.i_lo hx.i_hi
  have hg_2 : zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 2)) = false :=
    sge0_pos i hx.i_lo (by omega)
  have hg_5 : zopz0zI_u (BitVec.ofNat 64 (16 * (tiX sp L i lenp nci func top g r f x m o).n 2 +
      (tiX sp L i lenp nci func top g r f x m o).n 5)) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 6))
      = true := show zopz0zI_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = true by
    rw [fult (by omega) (by omega)]; simp; omega
  have hg_5' : zopz0zKzJ_u (BitVec.ofNat 64 (16 * (tiX sp L i lenp nci func top g r f x m o).n 2 +
      (tiX sp L i lenp nci func top g r f x m o).n 5)) (BitVec.ofNat 64 ((tiX sp L i lenp nci func top g r f x m o).n 6))
      = false := show zopz0zKzJ_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = false by
    rw [fuge (by omega) (by omega)]; simp; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80021b2c#64 (Lua.Vm.AtF.TolFlt.r0 (tiX sp L i lenp nci func top g r f x m o))
      (ArmPay (tiX sp L i lenp nci func top g r f x m o).m (tiX sp L i lenp nci func top g r f x m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TolFlt h acc until [0x800030a4]
  exact ⟨_, acc, h⟩

/-- `luaL_tolstring`'s and its callees' frames on a float: `[sp - 16432, sp)`
(`lua_pushfstring`'s `PffFr` below `luaL_tolstring`'s 48 bytes). -/
def TfFr (sp a : Nat) : Prop := sp ≤ a + 16432 ∧ a < sp

/-- **The configurations at `tostringbuff`'s return inside `luaL_tolstring`'s
`lua_pushfstring`**, memory `M` (`tolPost_of_split`'s `Q`): `luaL_tolstring`'s
saved words, `lua_pushfstring`'s state after the cut (`PffS`), the row. -/
structure TfMid (sp L i lenp g top : Nat) (r x : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (c : Config) : Prop where
  ra : bytesT8 M (sp - 8) = r
  s0 : bytesT8 M (sp - 16) = f.s0
  s1 : bytesT8 M (sp - 24) = f.s1
  s2 : bytesT8 M (sp - 32) = f.s2
  pff : PffS M (sp - 48) L 0x80021ccc#64 x (tiFr L i lenp f)
  row : ∃ a3 a4 a5 a6 a7, SegSt 0x800115c0#64
    (Lua.Vm.AtF.PushfF.r6 (pffX2 (sp - 48) L g top (tsbBytes x).length 0x80021ccc#64 (tiFr L i lenp f) x
      a3 a4 a5 a6 a7 M o)) (ArmPay M o) c

/-- **`luaL_tolstring` on a float, to `tostringbuff`'s return** (lane F1-25):
a bignum computation (`BigRun`, off its frames `TfFr`) leaving `TfMid`. -/
theorem tolflt_pre (hF : FloatToStr_Statement) (sp L i lenp nci func top g : Nat) (x r : BitVec 64)
    (f : AbiFrame) (m : Mem) (o : Array String) (H : HeapIx) (B : Nat → Prop)
    (hx : TolDIn m sp L i lenp nci func top g x r) (hI : PffIn m H B) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ M H' B', BigRun (TfFr sp) m M H H' B B' dtoaRoom ∧ TfMid sp L i lenp g top r x f M o c) := by
  intro c h
  ti_in hx
  have hHE : heapEnd = 0x87800000 := rfl
  obtain ⟨c1, s1, h1⟩ := tf_pre sp L i lenp nci func top g x r f m o hx c h
  obtain ⟨k2, w8, w16, w24, w32⟩ := ti_m2 (sp := sp) (L := L) (i := i) (lenp := lenp) (nci := nci) (func := func)
    (top := top) (g := g) (r := r) (f := f) (v := x) (m := m) (o := o) (by omega)
  have e2 : Lua.Vm.AtF.TolFlt.m2 (tiX sp L i lenp nci func top g r f x m o) =
      Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f x m o) := rfl
  rw [e2] at h1
  generalize Lua.Vm.AtF.TolInt.m2 (tiX sp L i lenp nci func top g r f x m o) = M2 at h1 k2 w8 w16 w24 w32
  have kl : ∀ a, a < 0x87800000 + 64 → bytesT1 M2 a = bytesT1 m a := fun a ha => k2 a (.inl (by omega))
  have hBh : ∀ a, B a → a < heapEnd := fun a ha => (hI.big_in a ha).2.2
  have hPf : PfIn M2 (sp - 48) L g top 0x80021ccc#64 := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega
    L_al := by omega, L_he := by omega, g_lo := by omega, g_hi := by omega, t_lo := by omega, t_hi := by omega
    t_al := by omega, tL := by omega, tg := by omega, Lg := by omega
    Lg_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.g_w
    top_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.top_w
    rod := RodataRead.congr hx.rod fun a ha => kl a (by omega) }
  have hF2 : ∀ a, ¬ TfFr sp a → bytesT1 M2 a = bytesT1 m a := fun a ha =>
    k2 a (by simp only [TfFr, not_and, Nat.not_lt] at ha; omega)
  have hFF : ∀ a, TfFr sp a → heapEnd + 32 ≤ a := fun a ha => by simp only [TfFr] at ha; omega
  have hR2 := BigRun.ofFrame hI.heap hI.big hBh hFF hF2
  have hI2 : PffIn M2 H B :=
    ⟨hI.stat.congr fun a ha => kl a (by omega), hR2.heap, hI.room, hR2.big, hI.big_in⟩
  fcx_unfold at h1
  obtain ⟨c2, s2, M, H', B', a3, a4, a5, a6, a7, hS, hR, h2⟩ := pushfF_pre hF (sp - 48) L g top x 0x80021ccc#64
    (tiFr L i lenp f) M2 o H B hPf hI2 c1
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h1.repin (by pins_of h1))
  -- `luaL_tolstring`'s frame: off `lua_pushfstring`'s callees' frames
  have kF : ∀ a, sp - 48 ≤ a → a < sp → bytesT1 M a = bytesT1 M2 a := fun a h1 h2 => hR.keep a fun hw => by
    rcases hw with hw | hw | hw | hw
    · rcases hw with hg | ⟨-, hh, -⟩
      · have := hg.lt; have : heapStart = 0x8006ecd0 := rfl; omega
      · omega
    · have := hBh a hw; omega
    · simp only [ReentWord, symImpureData, reentResultOff, reentFreelistOff] at hw; omega
    · simp only [PffFr] at hw; omega
  have hRall : BigRun (TfFr sp) m M H H' B B' dtoaRoom := by
    have := hR2.trans (hR.mono (F' := TfFr sp) (fun a ha => by simp only [PffFr, TfFr] at ha ⊢; omega)
      (Nat.le_refl _))
    rwa [Nat.zero_add] at this
  exact ⟨c2, s1.trans s2, M, H', B', hRall,
    ⟨(bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w8,
     (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w16,
     (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w24,
     (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w32, hS, a3, a4, a5, a6, a7, h2⟩⟩

/-- **`luaL_tolstring` on a float, from `tostringbuff`'s return** (lane
F1-25): the bytes interned (found or created, `PfStr` against the memory `M`
after the cut, off the frames `TolFr`) and pushed (`PfPost`), `l` their count,
`getstr` of the string returned. The numbers of `luaL_tolstring`'s objects
are the entry's (`hx`, at any memory). -/
theorem tolflt_post (hM : MallocR_Statement) (sp L i lenp nci func top g : Nat) (x r : BitVec 64) (f : AbiFrame)
    (m0 M : Mem) (o : Array String) (hx : TolDIn m0 sp L i lenp nci func top g x r)
    (hP : PfIn M (sp - 48) L g top 0x80021ccc#64) (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8)
    (size hash head d nuse : Nat) (H : HeapIx) (hT : NlTab M L g top (tsbU8 x) seed K X W cw size hash head d nuse H)
    (hgc : bytesT1 M (g + gGcstpOff) = 0x1#8) (c : Config)
    (hm : TfMid sp L i lenp g top r x f M o c) :
    ∃ c', Steps c c' ∧ ∃ ts M3 M' H', PfStr M M3 (TolFr sp) g (tsbU8 x) seed K X W size hash nuse head H ts H' ∧
      PfPost M3 M' (sp - 48) L g top ts ∧
      wrRet r sp (ts + 24) f (writeMap8 M' lenp (sdData_val (BitVec.ofNat 64 (tsbU8 x).length))) o c' := by
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  obtain ⟨a3, a4, a5, a6, a7, h⟩ := hm.row
  have hb40 : (tsbU8 x).length ≤ 40 := by rw [tsbU8_length]; have := hm.pff.len_hi; omega
  obtain ⟨c2, s2, ts, M3, M', H', hstr, hpost, hts, hret⟩ := pushfF_post hM (sp - 48) L g top x 0x80021ccc#64
    (tiFr L i lenp f) a3 a4 a5 a6 a7 M o hP hm.pff seed K X W cw size hash head d nuse H hT hgc hx.g_al c h
  -- the frame's words at the return: off the push and the string's writes
  have kF : ∀ a, sp - 48 ≤ a → a < sp → bytesT1 M' a = bytesT1 M a := fun a h1 h2 =>
    (hpost.keep a (by simp only [Rng, PfFr, gTotalbytesOff, gGCdebtOff]; omega)).trans
      (hstr.stack hb40 (by omega) (by have := hT.new.bkt_he; omega) (by omega) (by simp only [PfFr]; omega))
  have hX1 : Lua.Vm.AtF.TolFlt.Ok (tiX sp L i lenp nci func top g r f x M' o) := by fcx_ok
  have hc7 : bytesT8 (tiX sp L i lenp nci func top g r f x M' o).m ((tiX sp L i lenp nci func top g r f x M' o).n 0 - 16) =
      (tiX sp L i lenp nci func top g r f x M' o).b 1 :=
    show bytesT8 M' (sp - 16) = f.s0 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans hm.s0
  have hc8 : bytesT8 (tiX sp L i lenp nci func top g r f x M' o).m ((tiX sp L i lenp nci func top g r f x M' o).n 0 - 8) =
      (tiX sp L i lenp nci func top g r f x M' o).b 0 :=
    show bytesT8 M' (sp - 8) = r from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans hm.ra
  have hc9 : bytesT8 (tiX sp L i lenp nci func top g r f x M' o).m ((tiX sp L i lenp nci func top g r f x M' o).n 0 - 24) =
      (tiX sp L i lenp nci func top g r f x M' o).b 2 :=
    show bytesT8 M' (sp - 24) = f.s1 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans hm.s1
  have hc10 : bytesT8 (tiX sp L i lenp nci func top g r f x M' o).m ((tiX sp L i lenp nci func top g r f x M' o).n 0 - 32) =
      (tiX sp L i lenp nci func top g r f x M' o).b 3 :=
    show bytesT8 M' (sp - 32) = f.s2 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans hm.s2
  simp only [wrRet] at hret
  have h : SegSt 0x80021ccc#64 (Lua.Vm.AtF.TolFlt.r3 (tiX sp L i lenp nci func top g r f x M' o))
      (ArmPay (tiX sp L i lenp nci func top g r f x M' o).m (tiX sp L i lenp nci func top g r f x M' o).o) c2 := by
    fcx_unfold; exact hret.repin (by pins_of hret)
  have acc := s2
  fat_run Lua.Vm.AtF.TolFlt h acc until [0x80002994]
  fcx_unfold at h
  have hts1 := hts.ts_lo; have hts2 := hts.ts_hi
  obtain ⟨c3, s3, hfin⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (top := top + 16) (ts := ts)
    (len := (tsbU8 x).length) (r := r) f o
    ⟨by omega, hx.ra, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by omega⟩
    ⟨hpost.top_w, by rw [show top + 16 - 8 = top + 8 by omega]; exact hpost.tag,
      by rw [show top + 16 - 16 = top by omega]; exact hpost.val, hts.len, by omega⟩ _
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h.repin (by pins_of h))
  have hG : ∀ a, TolFr sp a → 0x87800000 ≤ a := fun a ha => by simp only [TolFr] at ha; omega
  have hFG : ∀ a, PfFr (sp - 48) a → TolFr sp a := pfFr_tolFr (by omega)
  have hs2 := PfStr.trans hstr (fun a ha => (hT.hK a ha).2) hG hFG (fun _ _ => rfl) hx.g_hi hb40
  exact ⟨c3, acc.trans s3, ts, M3, M', H', hs2, hpost, hfin⟩

end Lua.Vm.Sim.Kit

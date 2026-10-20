import Lua.Vm.Sim.Kit.PushfP
import Lua.Vm.Sim.Kit.TolInt
import Lua.Vm.AtF.TolFn

/-!
# `luaL_tolstring` on a function argument (lane F1-24)

`luaL_tolstring(L, i, &l)` on F1's light C function `print`: `luaL_callmeta`
(no metatable for functions: `G(L)->mt[LUA_TFUNCTION]` NULL), `lua_type`,
`lua_typename` (`.rodata`'s `"function"`), `lua_topointer` (the function's
address), `lua_pushfstring(L, "%s: %p", "function", print)` (a call node:
`pushfP_sum`), the tail `lua_tolstring(L, -1, &l)` (`toltop_sum`). Its
at-lemmas are generated (`Lua/Vm/AtF/TolFn.lean`): the entry and the return
from `lua_pushfstring` (`0x80021cac`). The run's shape is `tolint_sum`'s, over
the generic entry facts `TolVIn`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- **What `luaL_tolstring` needs on `print`** (`LUA_VLCF`, the address
`0x80022f18`, `G(L)->mt[LUA_TFUNCTION]`). -/
abbrev TolFIn (m : Mem) (sp L i lenp nci func top g : Nat) (r : BitVec 64) : Prop :=
  TolVIn m sp L i lenp nci func top g 0x16#8 528 0x80022f18#64 r

/-- `lua_typename`'s table entry for `LUA_TFUNCTION` (`.rodata`). -/
theorem rod_fnName {m : Mem} (h : RodataRead m) : bytesT8 m 0x80053288 = 0x8004f290#64 := by
  rw [show (0x80053288 : Nat) = Image.rodataBase + 0x45c0 by decide, At.rod8 h _ (by decide)]; decide

/-- **`luaL_tolstring` on `print`, to `lua_pushfstring`'s call.** -/
theorem tf_pre (sp L i lenp nci func top g : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : TolFIn m sp L i lenp nci func top g r) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => SegSt 0x800030a4#64 (Lua.Vm.AtF.TolFn.r2 (tlX sp L i lenp nci func top g r f m o))
        (ArmPay (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) o) c) := by
  intro c h
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hX : Lua.Vm.AtF.TolFn.Ok (tlX sp L i lenp nci func top g r f m o) := by fcx_ok
  have hc0 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m ((tlX sp L i lenp nci func top g r f m o).n 1 + 32) =
      BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 4) := hx.ci_w
  have hc1 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m ((tlX sp L i lenp nci func top g r f m o).n 4) =
      BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 5) := hx.func_w
  have hc2 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m ((tlX sp L i lenp nci func top g r f m o).n 1 + 16) =
      BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 6) := hx.top_w
  have hc3 : bytesT1 (tlX sp L i lenp nci func top g r f m o).m
      (16 * (tlX sp L i lenp nci func top g r f m o).n 2 + (tlX sp L i lenp nci func top g r f m o).n 5 + 8) =
      0x16#8 := hx.tag_w
  have hc4 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m ((tlX sp L i lenp nci func top g r f m o).n 1 + 24) =
      BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 7) := hx.g_w
  have hc5 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m ((tlX sp L i lenp nci func top g r f m o).n 7 + 528) =
      0x0#64 := hx.mt_w
  have hc6 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m 0x80053288 = 0x8004f290#64 := rod_fnName hx.rod
  have hc7 : bytesT8 (tlX sp L i lenp nci func top g r f m o).m
      (16 * (tlX sp L i lenp nci func top g r f m o).n 2 + (tlX sp L i lenp nci func top g r f m o).n 5) =
      0x80022f18#64 := hx.val_w
  have hf0 : 16 * (tlX sp L i lenp nci func top g r f m o).n 2 + (tlX sp L i lenp nci func top g r f m o).n 5 <
      (tlX sp L i lenp nci func top g r f m o).n 6 := show 16 * i + func < top by omega
  have hg_6 := absindex_pos i hx.i_lo hx.i_hi
  have hg_2 : zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 2)) = false :=
    sge0_pos i hx.i_lo (by omega)
  have hg_5 : zopz0zI_u (BitVec.ofNat 64 (16 * (tlX sp L i lenp nci func top g r f m o).n 2 +
      (tlX sp L i lenp nci func top g r f m o).n 5)) (BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 6))
      = true := show zopz0zI_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = true by
    rw [fult (by omega) (by omega)]; simp; omega
  have hg_5' : zopz0zKzJ_u (BitVec.ofNat 64 (16 * (tlX sp L i lenp nci func top g r f m o).n 2 +
      (tlX sp L i lenp nci func top g r f m o).n 5)) (BitVec.ofNat 64 ((tlX sp L i lenp nci func top g r f m o).n 6))
      = false := show zopz0zKzJ_u (BitVec.ofNat 64 (16 * i + func)) (BitVec.ofNat 64 top) = false by
    rw [fuge (by omega) (by omega)]; simp; omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80021b2c#64 (Lua.Vm.AtF.TolFn.r0 (tlX sp L i lenp nci func top g r f m o))
      (ArmPay (tlX sp L i lenp nci func top g r f m o).m (tlX sp L i lenp nci func top g r f m o).o) c :=
    h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.TolFn h acc until [0x800030a4]
  exact ⟨_, acc, h⟩

/-- `luaL_tolstring`'s stores before `lua_pushfstring` (the generated `m2`):
its frame, the callees' below it. -/
theorem tf_m2 {sp L i lenp nci func top g : Nat} {r : BitVec 64} {f : AbiFrame} {m : Mem}
    {o : Array String} (hsp : 80 ≤ sp) :
    (∀ a, (a + 80 < sp ∨ sp ≤ a) →
      bytesT1 (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) a = bytesT1 m a) ∧
    bytesT8 (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) (sp - 8) = r ∧
    bytesT8 (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) (sp - 16) = f.s0 ∧
    bytesT8 (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) (sp - 24) = f.s1 ∧
    bytesT8 (Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o)) (sp - 32) = f.s2 := by
  simp only [Lua.Vm.AtF.TolFn.m2, tlX, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  refine ⟨fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [fw1_wm8]
  all_goals simp (disch := omega) only [fw8_wm8, fw8_same]

/-- **`luaL_tolstring(L, i, &l)` on `print`** (lane F1-24): the twenty bytes
`"function: 0x80022f18"` interned (`PfStr`, off the frames `TolFr`) and pushed
(`PfPost`), `l` their count, `getstr` of the string returned. -/
theorem tolfn_sum (hM : MallocR_Statement) (sp L i lenp nci func top g : Nat)
    (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) (hx : TolFIn m sp L i lenp nci func top g r)
    (seed : UInt32) (K X W : Nat → Prop) (cw : BitVec 8) (size hash head d nuse : Nat) (H : HeapIx)
    (hT : NlTab m L g top fnU8 seed K X W cw size hash head d nuse H) :
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 lenp⟩] sp r f) (ArmPay m o))
      (fun c => ∃ ts M3 M H', PfStr m M3 (TolFr sp) g fnU8 seed K X W size hash nuse head H ts H' ∧
        PfPost M3 M (sp - 48) L g top ts ∧ PfTs M ts fnU8.length ∧
        wrRet r sp (ts + 24) f (writeMap8 M lenp (sdData_val (BitVec.ofNat 64 fnU8.length))) o c) := by
  intro c h
  ti_in hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hb40 : fnU8.length ≤ 40 := by rw [fnU8_length]; omega
  obtain ⟨c1, s1, h1⟩ := tf_pre sp L i lenp nci func top g r f m o hx c h
  obtain ⟨k2, w8, w16, w24, w32⟩ := tf_m2 (sp := sp) (L := L) (i := i) (lenp := lenp) (nci := nci) (func := func)
    (top := top) (g := g) (r := r) (f := f) (m := m) (o := o) (by omega)
  generalize Lua.Vm.AtF.TolFn.m2 (tlX sp L i lenp nci func top g r f m o) = M2 at h1 k2 w8 w16 w24 w32
  have kl : ∀ a, a < 0x87800000 + 64 → bytesT1 M2 a = bytesT1 m a := fun a ha => k2 a (.inl (by omega))
  have hPf : PfIn M2 (sp - 48) L g top 0x80021cac#64 := {
    sp_lo := by omega, sp_hi := by omega, sp_al := by omega, ra := by decide, L_lo := by omega
    L_al := by omega, L_he := by omega, g_lo := by omega, g_hi := by omega, t_lo := by omega, t_hi := by omega
    t_al := by omega, tL := by omega, tg := by omega, Lg := by omega
    Lg_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.g_w
    top_w := (bytesT8_congrT fun j _ => kl _ (by omega)).trans hx.top_w
    rod := RodataRead.congr hx.rod fun a ha => kl a (by omega) }
  fcx_unfold at h1
  obtain ⟨c2, s2, ts, M3, M, H', hstr, hpost, hts, hret⟩ := pushfP_sum hM (sp - 48) L g top 0x80021cac#64
    (tlFr L i lenp f) M2 o hPf (hx.stat.congr fun a ha => kl a (by omega)) seed K X W cw size hash head d nuse H
    (hT.congr kl) ((kl _ (by simp only [gGcstpOff]; omega)).trans hx.gcstp) hx.g_al c1
    (by simp only [callPre, AbiFrame.pins, List.cons_append, List.nil_append]; exact h1.repin (by pins_of h1))
  -- the frame's words at the return: off the push and the string's writes
  have kF : ∀ a, sp - 48 ≤ a → a < sp → bytesT1 M a = bytesT1 M2 a := fun a h1 h2 =>
    (hpost.keep a (by simp only [Rng, PfFr, gTotalbytesOff, gGCdebtOff]; omega)).trans
      (hstr.stack hb40 (by omega) (by have := hT.new.bkt_he; omega) (by omega) (by simp only [PfFr]; omega))
  have hX1 : Lua.Vm.AtF.TolFn.Ok (tlX sp L i lenp nci func top g r f M o) := by fcx_ok
  have hc8 : bytesT8 (tlX sp L i lenp nci func top g r f M o).m ((tlX sp L i lenp nci func top g r f M o).n 0 - 16) =
      (tlX sp L i lenp nci func top g r f M o).b 1 :=
    show bytesT8 M (sp - 16) = f.s0 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w16
  have hc9 : bytesT8 (tlX sp L i lenp nci func top g r f M o).m ((tlX sp L i lenp nci func top g r f M o).n 0 - 8) =
      (tlX sp L i lenp nci func top g r f M o).b 0 :=
    show bytesT8 M (sp - 8) = r from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w8
  have hc10 : bytesT8 (tlX sp L i lenp nci func top g r f M o).m ((tlX sp L i lenp nci func top g r f M o).n 0 - 24) =
      (tlX sp L i lenp nci func top g r f M o).b 2 :=
    show bytesT8 M (sp - 24) = f.s1 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w24
  have hc11 : bytesT8 (tlX sp L i lenp nci func top g r f M o).m ((tlX sp L i lenp nci func top g r f M o).n 0 - 32) =
      (tlX sp L i lenp nci func top g r f M o).b 3 :=
    show bytesT8 M (sp - 32) = f.s2 from (bytesT8_congrT fun j _ => kF _ (by omega) (by omega)).trans w32
  have hf0 : 16 * (tlX sp L i lenp nci func top g r f M o).n 2 + (tlX sp L i lenp nci func top g r f M o).n 5 <
      (tlX sp L i lenp nci func top g r f M o).n 6 := show 16 * i + func < top by omega
  simp only [wrRet] at hret
  have h : SegSt 0x80021cac#64 (Lua.Vm.AtF.TolFn.r3 (tlX sp L i lenp nci func top g r f M o))
      (ArmPay (tlX sp L i lenp nci func top g r f M o).m (tlX sp L i lenp nci func top g r f M o).o) c2 := by
    fcx_unfold; exact hret.repin (by pins_of hret)
  have acc := s1.trans s2
  fat_run Lua.Vm.AtF.TolFn h acc until [0x80002994]
  fcx_unfold at h
  have hts1 := hts.ts_lo; have hts2 := hts.ts_hi
  obtain ⟨c3, s3, hfin⟩ := toltop_sum (sp := sp) (L := L) (lenp := lenp) (top := top + 16) (ts := ts)
    (len := fnU8.length) (r := r) f o
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

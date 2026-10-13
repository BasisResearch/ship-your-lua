import Lua.Vm.Sim.Kit.Tolstring
import Lua.Vm.Sim.Kit.Udivdi3
import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Arms.Segs.Humoddi3
import Lua.Vm.Sim.Kit.RetMem
import Lua.Vm.AtF.LuaCStep
import Lua.Vm.Arms.Segs.HluaE_setdebt

/-!
# `lua_pushstring` of a C literal (lane F1-15)

`PushLit_Statement` from its parts: `__umoddi3` (`umoddi3_sumW`, from
`udivdi3_sum`), `luaS_new` (the string cache's row: `strcmp` against its two
candidates, on a miss `strlen` and `luaS_newlstr` → `internshrstr`),
`internshrstr` (the hash loop, the chain walk with `memcmp`), `luaC_step` with
the collector stopped (`luaE_setdebt`), and `lua_pushstring` itself.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `__umoddi3` -/

/-- The C frame as the soft-int helpers' frame (`HFrame`: `sp`, `gp`, `s0`–`s11`). -/
abbrev AbiFrame.hframe (f : AbiFrame) (sp : Nat) : HFrame :=
  ⟨BitVec.ofNat 64 sp, BitVec.ofNat 64 symGlobalPointer, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8,
    f.s9, f.s10, f.s11⟩

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`__umoddi3(x, y)`** (`0x8002f77c`: `mv t0, ra`, `__udivdi3`, `mv a0, a1`,
`jr t0`): `x % y`. -/
theorem umoddi3_sumW (sp x y : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hy0 : y ≠ 0) (hy : y < 2 ^ 64) (hx : x < 2 ^ 64) (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f77c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 x⟩, ⟨Register.x11, BitVec.ofNat 64 y⟩]
        sp r f) (ArmPay m o))
      (wrRet r sp (x % y) f m o) := by
  intro c h
  have acc := Steps.refl c
  simp only [callPre, List.cons_append, List.nil_append] at h
  kit_run h acc until [0x8002f734]
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  have hd : BitVec.ofNat 64 y ≠ 0#64 := fun e => hy0 (by
    have := congrArg BitVec.toNat e
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy] at this
    exact this)
  obtain ⟨c1, s1, h1⟩ := udivdi3_sum (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) 0x8002f784#64 r
    (f.hframe sp) m o hd (by decide) _ (h.repin (by pins_of h))
  have acc := acc.trans s1
  have h := h1
  kit_run h acc
  have hm : BitVec.ofNat 64 x % BitVec.ofNat 64 y = BitVec.ofNat 64 (x % y) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_umod, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
    exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx)).symm
  rw [hm] at h
  exact ⟨_, acc, (h.at (by simpa [Vsa.Sim.sext_zero] using Vsa.Sim.ret_tgt r hr)).repin (by pins_of h)⟩

/-! ## `luaC_step` with the collector stopped -/

/-- The context of the callee rows of `lua_pushstring`'s callees: `sp`, `L`,
`g` (and more Nat atoms); `ra` and the caller's frame. -/
@[at_row] abbrev plX (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- **What `luaC_step(L)` leaves with the collector stopped**: every byte kept
but `g->totalbytes`, `g->GCdebt` (`luaE_setdebt(g, -2000)`) and its frame below
`sp`. -/
structure StepPost (m m' : Mem) (sp g : Nat) : Prop where
  keep : ∀ a, ¬ (Rng (g + gTotalbytesOff) 8 a ∨ Rng (g + gGCdebtOff) 8 a ∨ Below sp 80 a) →
    bytesT1 m' a = bytesT1 m a

/-- Where `luaC_step`'s objects lie: `sp` far above the heap, `L` and `g` in the arena. -/
structure StepCx (sp L g : Nat) (r : BitVec 64) : Prop where
  sp_lo : 0x87800000 + 16384 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 16 = 0
  ra : r.toNat % 4 = 0
  L_lo : 0x8005c6d0 ≤ L
  L_he : L + 200 ≤ 0x87800000
  L_al : L % 8 = 0
  g_lo : 0x8005c6d0 ≤ g
  g_hi : g + 1400 ≤ 0x87800000
  g_al : g % 8 = 0

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | kit_hyp
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

/-- **`luaC_step(L)` with the collector stopped** (`g->gcstp ≠ 0`): `mv a0, g`,
`luaE_setdebt(g, -2000)` (the tail jump), back at `r` with `a0 = g`. -/
theorem luaC_step_sum (sp L g : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : StepCx sp L g r) (hG : bytesT8 m (L + 24) = BitVec.ofNat 64 g)
    (hS : bytesT1 m (g + gGcstpOff) = 0x1#8) :
    Triple (SegSt 0x8000ec80#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp g f m' o c ∧ StepPost m m' sp g) := by
  intro c h
  obtain ⟨x1, x2, x3, hra, x5, x6, x7, x8, x9, x10⟩ := hx
  have hX : Lua.Vm.AtF.LuaCStep.Ok (plX [sp, L, g] r f m o) := by fcx_ok
  have x1' : 2273329152 ≤ sp := by omega
  have x9' : g + 1400 ≤ 2273312768 := by omega
  clear x1 x9
  have hc0 : bytesT8 m (L + 24) = BitVec.ofNat 64 g := hG
  have hc1 : bytesT1 m (g + 106) = 0x1#8 := hS
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x8000ec80#64 (Lua.Vm.AtF.LuaCStep.r0 (plX [sp, L, g] r f m o))
      (ArmPay (plX [sp, L, g] r f m o).m (plX [sp, L, g] r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.LuaCStep h acc until [0x80016a20]
  fcx_unfold at h
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  -- `luaE_setdebt(g, -2000)`: either side of its clamp
  kit_split h
  all_goals kit_run h acc
  all_goals
    refine ⟨_, acc, _, (h.at (Vsa.Sim.ret_tgt r hra)).repin (by pins_of h),
      ⟨fun a ha => ?_⟩⟩
    simp only [Rng, Below, gTotalbytesOff, gGCdebtOff, not_or, not_and, Nat.not_lt] at ha
    rw [show (0x010#12 : BitVec 12) = BitVec.ofNat 12 16 from rfl, show (0x018#12 : BitVec 12) = BitVec.ofNat 12 24 from rfl,
      addr_imm (by decide) (by omega), addr_imm (by decide) (by omega)]
    exact AtF.bT1_congr (by simp (disch := omega) only [getElem?_writeMap8_out])

end Lua.Vm.Sim.Kit

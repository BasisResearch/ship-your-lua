import Lua.Vm.Sim.Kit.Adjvar
import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.HeapKeep
import Lua.Vm.AtF.Lua_gettop
import Lua.Vm.AtF.Lua_settop_pop

/-!
# The Lua C API calls `luaB_print` makes itself (lane F1-11)

`lua_gettop(L)` and `lua_settop(L, -2)` (`lua_pop(L, 1)`), on a C
function's API frame (`ApiAt`: `L->ci`, `ci->func`, `L->top` `k` values above
the function, `L->tbclist` below them), from their generated at-lemmas
(`Lua/Vm/AtF/Lua_gettop.lean`, `Lua/Vm/AtF/Lua_settop_pop.lean`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- **A C function's API frame**: `L->ci = ci`, `ci->func = func`, `L->top`
`k` values above the function, `L->tbclist = tbc` below the first. -/
structure ApiAt (m : Mem) (L ci func k tbc : Nat) : Prop where
  ci_w : bytesT8 m (L + 32) = BitVec.ofNat 64 ci
  func_w : bytesT8 m ci = BitVec.ofNat 64 func
  top_w : bytesT8 m (L + 16) = BitVec.ofNat 64 (func + 16 * k + 16)
  tbc_w : bytesT8 m (L + 64) = BitVec.ofNat 64 tbc
  tbc_lt : tbc < func + 16

/-- `sext.w` of a small value. -/
theorem sext32_ofNat (x : Nat) (h : x < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 x) 31 0) = BitVec.ofNat 64 x := by
  have h2 : Sail.BitVec.extractLsb (BitVec.ofNat 64 x) 31 0 = BitVec.ofNat 32 x := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
    omega
  rw [h2]
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat]
  rw [if_neg (by simp; omega)]
  omega

/-- `lua_gettop`'s value: `(top - (func + 16)) >> 4`, `sext.w`. -/
theorem gettop_val (func k : Nat) (hk : k < 2 ^ 31) (hf : func + 16 * k + 16 < 2 ^ 63) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (shift_bits_right_arith
      (BitVec.ofNat 64 (func + 16 * k + 16) - BitVec.ofNat 64 (func + 16))
      (Sail.BitVec.extractLsb (0x04#6) 5 0)) 31 0) = BitVec.ofNat 64 k := by
  have := av_t4 (func + 16 * k + 16) (func + 16) (by omega) hf
  rw [sext64_id, sext64_id] at this
  rw [this, show (func + 16 * k + 16 - (func + 16)) / 16 = k by omega]
  exact sext32_ofNat k hk

/-- The context of a Lua API call's rows: `sp`, `L`, `ci`, `func`, `k`; `ra`
and the caller's frame. -/
@[at_row] abbrev apiX (sp L ci func k : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) : FCx :=
  FCx.mk' [sp, L, ci, func, k] [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] m o

/-- **`lua_gettop(L)`** on an API frame of `k < 2 ^ 31` values: `k`, nothing written. -/
theorem gettop_sum (sp L ci func k tbc : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hA : ApiAt m L ci func k tbc) (hk : k < 2 ^ 31) (hra : r.toNat % 4 = 0) (hhi : sp ≤ 2 ^ 32)
    (hL : 0x8005c6d0 ≤ L) (hLh : L + 256 ≤ 2 ^ 32) (hLa : L % 8 = 0) (hci : 0x8005c6d0 ≤ ci)
    (hcih : ci + 256 ≤ 2 ^ 32) (hfh : func + 16 * k + 16 ≤ 2 ^ 32) :
    Triple (SegSt 0x80001bb4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] sp r f) (ArmPay m o))
      (wrRet r sp k f m o) := by
  intro c h
  have hX : Lua.Vm.AtF.Lua_gettop.Ok (apiX sp L ci func k r f m o) := by fcx_ok
  have hc0 : bytesT8 m (L + 32) = BitVec.ofNat 64 ci := hA.ci_w
  have hc1 : bytesT8 m (L + 16) = BitVec.ofNat 64 (func + 16 * k + 16) := hA.top_w
  have hc2 : bytesT8 m ci = BitVec.ofNat 64 func := hA.func_w
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80001bb4#64 (Lua.Vm.AtF.Lua_gettop.r0 (apiX sp L ci func k r f m o))
      (ArmPay (apiX sp L ci func k r f m o).m (apiX sp L ci func k r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Lua_gettop h acc
  fcx_unfold at h
  fat_rd at h
  rw [gettop_val func k hk (by omega)] at h
  exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- A C function's return without a result (`void`): `sp`, `gp`, the
caller's frame. -/
abbrev apiRet (r : BitVec 64) (sp : Nat) (f : AbiFrame) (m : Mem) (o : Array String) : Config → Prop :=
  SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins)
    (ArmPay m o)

/-- **`lua_settop(L, -2)`** (`lua_pop(L, 1)`) on an API frame of `k + 1`
values: `L->top` lowered by one slot, nothing else written. -/
theorem settop_pop_sum (sp L ci func k tbc : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hA : ApiAt m L ci func (k + 1) tbc) (hra : r.toNat % 4 = 0) (hhi : sp ≤ 2 ^ 32)
    (hL : 0x8005c6d0 ≤ L) (hLh : L + 256 ≤ 2 ^ 32) (hLa : L % 8 = 0) (hf : 0x8005c6d0 ≤ func)
    (hfh : func + 16 * k + 32 ≤ 2 ^ 32) (hsep : ci + 8 ≤ L + 16 ∨ L + 24 ≤ ci) :
    Triple (SegSt 0x80001bd4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (2 ^ 64 - 2)⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', apiRet r sp f m' o c ∧ ApiAt m' L ci func k tbc ∧ Agree (Rng (L + 16) 8) m m') := by
  intro c h
  have htl := hA.tbc_lt
  have hX : Lua.Vm.AtF.Lua_settop_pop.Ok (apiX sp L (func + 16 * (k + 1) + 16) tbc 0 r f m o) := by
    constructor <;> (try fcx_unfold) <;> omega
  have hc0 : bytesT8 m (L + 16) = BitVec.ofNat 64 (func + 16 * (k + 1) + 16) := hA.top_w
  have hc1 : bytesT8 m (L + 64) = BitVec.ofNat 64 tbc := hA.tbc_w
  have hf0 : tbc < func + 16 * (k + 1) + 16 - 16 := by omega
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80001bd4#64 (Lua.Vm.AtF.Lua_settop_pop.r0 (apiX sp L (func + 16 * (k + 1) + 16) tbc 0 r f m o))
      (ArmPay (apiX sp L (func + 16 * (k + 1) + 16) tbc 0 r f m o).m
        (apiX sp L (func + 16 * (k + 1) + 16) tbc 0 r f m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run Lua.Vm.AtF.Lua_settop_pop h acc
  fcx_unfold at h
  refine ⟨_, acc, _, h.repin (by pins_of h), ⟨?_, ?_, ?_, ?_, hA.tbc_lt⟩, fun a ha => ?_⟩
  · rw [fw8_wm8 (by omega)]; exact hA.ci_w
  · rw [fw8_wm8 (by omega)]; exact hA.func_w
  · rw [fw8_same rfl]; congr 1
  · rw [fw8_wm8 (by omega)]; exact hA.tbc_w
  · simp only [Rng, not_and, Nat.not_lt] at ha
    exact getElem?_writeMap8_out _ _ _ _ (by omega)

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms.Segs.Hmuldi3
import Vsa.Sim.Muldi3Spec

/-!
# `__muldi3` at the Lua ELF's address: the call-node summary (M5)

`muldi3_sum`: from the helper's entry `0x8002f6c8` with `a0 = x`, `a1 = y`,
`ra = r` and the caller's frame `f` (the fetch-head registers, `s6`, `s10`),
the helper returns to `r` with `a0 = x * y`, the frame, memory and console
unchanged. The loop (`muldi3_loop`) runs the generated helper segments
(`Lua.Vm.Arms.seg_8002f6*`, `scripts/gen_lua_arms.py` `HELPERS`) under the
shift-and-add invariant `a0 + a2 * a1 = x * y`, whose arithmetic step
(`invmul_bv`) and `ret` target (`ret_tgt`) are ship-your-interpreter's
(`Vsa/Sim/Muldi3Spec.lean`, copied; ATTRIBUTION.md).

Lane float-sf3: `__muldf3` keeps `t1`, `a4`-`a7`, `t3`, `t4` live across its
`__muldi3` calls (gcc's `-fipa-ra`; `__muldi3` writes only `a0`-`a3`), so the
helper's segments carry them (`gen_lua_arms.py` `PASS_THROUGH`) and the
summary is stated with them (`TFrame`, `muldi3_sumK`); `muldi3_sum` is its
instance with those registers pinned at whatever they hold (`SegSt.pinGpr`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim
open Vsa.Machine (MState Config Steps)

local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp only [Vsa.Sim.sext_one, Vsa.Sim.shr_shamt])

theorem and_one (x : BitVec 64) (h : ¬ x &&& 1#64 = 0#64) : x &&& 1#64 = 1#64 := by
  have e : (x &&& 1#64).toNat = x.toNat % 2 := by
    rw [BitVec.toNat_and, show (1#64).toNat = 1 from rfl, Nat.and_one_is_mod]
  apply BitVec.eq_of_toNat_eq
  have : (x &&& 1#64).toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq h0)
  rw [e] at this ⊢; show _ = 1; omega

/-- The caller-saved registers a caller keeps across `__muldi3`. -/
structure TFrame where
  (t1 a4 a5 a6 a7 t3 t4 : BitVec 64)

/-- Kept registers to be read off a call site's pins (`pins_of`). -/
macro "tframe?" : term => `(TFrame.mk _ _ _ _ _ _ _)

-- `pin_gpr`: `Kit/Run.lean` (lane F1-15).

/-- The loop from its head `0x8002f6d0`, by the measure `a1`. -/
theorem muldi3_loop (x y r : BitVec 64) (f : HFrame) (t : TFrame) (m : Mem) (o : Array String) :
    ∀ n (a0 a1 a2 : BitVec 64), a1.toNat < n → a0 + a2 * a1 = x * y →
    Triple (SegSt 0x8002f6d0#64 (⟨Register.x10, a0⟩ :: ⟨Register.x11, a1⟩ :: ⟨Register.x12, a2⟩ ::
        ⟨Register.x1, r⟩ :: ⟨Register.x6, t.t1⟩ :: ⟨Register.x14, t.a4⟩ :: ⟨Register.x15, t.a5⟩ :: ⟨Register.x16, t.a6⟩ ::
        ⟨Register.x17, t.a7⟩ :: ⟨Register.x28, t.t3⟩ :: ⟨Register.x29, t.t4⟩ :: f.pins) (ArmPay m o))
      (SegSt 0x8002f6e8#64 (⟨Register.x10, x * y⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x6, t.t1⟩ :: ⟨Register.x14, t.a4⟩ :: ⟨Register.x15, t.a5⟩ :: ⟨Register.x16, t.a6⟩ ::
        ⟨Register.x17, t.a7⟩ :: ⟨Register.x28, t.t3⟩ :: ⟨Register.x29, t.t4⟩ :: f.pins) (ArmPay m o))
  | 0, _, _, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, a0, a1, a2, hn, hinv => by
    intro c h
    have acc := Steps.refl c
    have hstep := invmul_bv a2 a1
    have hlt : ∀ (e : shift_bits_right a1 (Sail.BitVec.extractLsb (0x01#6) 5 0) ≠ 0#64),
        (shift_bits_right a1 (Sail.BitVec.extractLsb (0x01#6) 5 0)).toNat < n := fun e => by
      rw [shr_shamt] at e ⊢
      have := shr_lt a1 (fun h0 => e (by rw [h0]; rfl)); omega
    by_cases hev : a1 &&& 1#64 = 0#64 <;> by_cases hz : a1 >>> (1 : Nat) = 0#64
    · kit_run h acc until [0x8002f6e8]
      rw [← hinv, hstep, hz, hev]
      exact ⟨_, acc, h.repin (by simp only [BitVec.mul_zero, BitVec.zero_mul, BitVec.add_zero]; pins_of h)⟩
    · kit_run h acc until [0x8002f6d0]
      obtain ⟨c', hs, h'⟩ := muldi3_loop x y r f t m o n a0 (shift_bits_right a1 sh1) (shift_bits_left a2 sh1)
        (hlt (by rwa [shr_shamt]))
        (by rw [shr_shamt, shl_shamt, ← hinv, hstep, hev]; simp) _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩
    · have h1 := and_one a1 hev
      kit_run h acc until [0x8002f6e8]
      rw [← hinv, hstep, hz, h1]
      exact ⟨_, acc, h.repin (by simp only [BitVec.mul_zero, BitVec.zero_add, BitVec.one_mul]; pins_of h)⟩
    · have h1 := and_one a1 hev
      kit_run h acc until [0x8002f6d0]
      obtain ⟨c', hs, h'⟩ := muldi3_loop x y r f t m o n (a0 + a2) (shift_bits_right a1 sh1)
        (shift_bits_left a2 sh1) (hlt (by rwa [shr_shamt]))
        (by rw [shr_shamt, shl_shamt, ← hinv, hstep, h1, BitVec.one_mul, BitVec.add_assoc,
          BitVec.add_comm a2]) _ (h.repin (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **`__muldi3`, the call-node summary**, with the caller's kept registers. -/
theorem muldi3_sumK (x y r : BitVec 64) (f : HFrame) (t : TFrame) (m : Mem) (o : Array String)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f6c8#64 (⟨Register.x10, x⟩ :: ⟨Register.x11, y⟩ :: ⟨Register.x1, r⟩ ::
        ⟨Register.x6, t.t1⟩ :: ⟨Register.x14, t.a4⟩ :: ⟨Register.x15, t.a5⟩ :: ⟨Register.x16, t.a6⟩ ::
        ⟨Register.x17, t.a7⟩ :: ⟨Register.x28, t.t3⟩ :: ⟨Register.x29, t.t4⟩ :: f.pins) (ArmPay m o))
      (SegSt r (⟨Register.x10, x * y⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x6, t.t1⟩ :: ⟨Register.x14, t.a4⟩ :: ⟨Register.x15, t.a5⟩ :: ⟨Register.x16, t.a6⟩ ::
        ⟨Register.x17, t.a7⟩ :: ⟨Register.x28, t.t3⟩ :: ⟨Register.x29, t.t4⟩ :: f.pins) (ArmPay m o)) := by
  intro c h
  have acc := Steps.refl c
  kit_run h acc until [0x8002f6d0]
  obtain ⟨c1, hs1, h⟩ := muldi3_loop x y r f t m o (y.toNat + 1) ((0#64) + sign_extend (0x000#12)) y
    (x + sign_extend (0x000#12)) (by omega) (by simp [Vsa.Sim.sext_zero]) _ (h.repin (by pins_of h))
  have acc := acc.trans hs1
  kit_run h acc
  exact ⟨_, acc, (h.at (Vsa.Sim.ret_tgt r hr)).repin (by pins_of h)⟩

/-- **`__muldi3`, the call-node summary.** -/
theorem muldi3_sum (x y r : BitVec 64) (f : HFrame) (m : Mem) (o : Array String)
    (hr : r.toNat % 4 = 0) :
    Triple (SegSt 0x8002f6c8#64 (⟨Register.x10, x⟩ :: ⟨Register.x11, y⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m o))
      (SegSt r (⟨Register.x10, x * y⟩ :: ⟨Register.x1, r⟩ :: f.pins) (ArmPay m o)) := by
  intro c h
  pin_gpr h 6 Register.x6
  pin_gpr h 14 Register.x14
  pin_gpr h 15 Register.x15
  pin_gpr h 16 Register.x16
  pin_gpr h 17 Register.x17
  pin_gpr h 28 Register.x28
  pin_gpr h 29 Register.x29
  obtain ⟨c', hs, h⟩ := muldi3_sumK x y r f tframe? m o hr c (h.repin (by pins_of h))
  exact ⟨c', hs, h.repin (by pins_of h)⟩

end Lua.Vm.Sim.Kit

import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Arms

/-!
# `OP_LOADNIL` by the direct kit (lane KIT-2)

`setnilvalue(s2v(ra++))` for `B + 1` registers: an inline do-while loop
(`0x8001d2a8`: `addi a5,a5,16; sb zero,-8(a5); bne a5,a4`) that stores the
nil tag of each slot. `loadnil_loop` runs it by the measure "slots left"
(the `muldi3_loop` pattern), its memory `nilMem`; the close is `Core.bleach`
with the written registers `[A, A + B]` (`Core.stack_of`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

theorem ofNat_bne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = (a != b) := by
  rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, ne_eq]
  refine ⟨fun h1 h2 => h1 (by rw [h2]), fun h1 h2 => h1 ?_⟩
  have := congrArg BitVec.toNat h2
  simpa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this

/-- `slli 40; srli 56`: the `B` field (`GETARG_B`). -/
theorem field_b_shl (x : BitVec 32) :
    shift_bits_right (shift_bits_left (sign_extend (m := 64) x) (Sail.BitVec.extractLsb (0x28#6) 5 0))
      (Sail.BitVec.extractLsb (0x38#6) 5 0) = BitVec.ofNat 64 ((x.toNat >>> 16) % 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [shift_bits_left, shift_bits_right, sign_extend, Sail.BitVec.signExtend, Sail.BitVec.extractLsb]
  simp [BitVec.toNat_signExtend, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have := x.isLt
  split <;> omega

theorem insert_addr {M : Mem} {a a' : Nat} {b : BitVec 8} (h : a = a') : M.insert a b = M.insert a' b :=
  h ▸ rfl

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [add_imm,
      ofNat_bne, BitVec.ofNat_add_ofNat])

/-- **The loop** from its head `0x8001d2a8` with `a5 = X`, `a4 = E`, `k`
slots left (`X + 16·k = E`): the tags of the `k` slots from `X + 16` are
stored nil (`sb zero, -8(a5)` after `addi a5,a5,16`, so the first store is
`X + 8`). -/
theorem loadnil_loop (w : RelPtrs) (pc : Nat) (ins : Word) (o : Array String) (E : Nat)
    (hlo : tohostAddr + 16 ≤ E) (hhi : E ≤ 2 ^ 32) :
    ∀ k (X : Nat) (M : Mem), 0 < k → X + 16 * k = E → tohostAddr + 8 ≤ X →
      Triple (SegSt 0x8001d2a8#64 (⟨Register.x15, BitVec.ofNat 64 X⟩ :: ⟨Register.x14, BitVec.ofNat 64 E⟩ ::
          armPins w pc ins) (ArmPay M o))
        (SegSt 0x8001d2b4#64 (⟨Register.x15, BitVec.ofNat 64 E⟩ :: ⟨Register.x14, BitVec.ofNat 64 E⟩ ::
          armPins w pc ins) (ArmPay (nilMem M X k) o))
  | 0, _, _, h0, _, _ => absurd h0 (Nat.lt_irrefl 0)
  | k + 1, X, M, _, hE, hX => by
    intro c h
    have acc := Steps.refl c
    have hTH : tohostAddr = 0x8005c6c0 := rfl
    by_cases hk : k = 0
    · subst hk
      have hX16 : X + 16 = E := by omega
      have hb : (X + 16 != E) = false := by simp [hX16]
      kit_run h acc until [0x8001d2b4, 0x8001d2a8]
      exact ⟨_, acc, (h.mem_eq (by simp only [nilMem]; exact insert_addr (by kit_disch))).repin (by pins_of h)⟩
    · have hX16 : X + 16 ≠ E := by omega
      have hb : (X + 16 != E) = true := by simp [hX16]
      kit_run h acc until [0x8001d2b4, 0x8001d2a8]
      obtain ⟨c', hs, h'⟩ := loadnil_loop w pc ins o E hlo hhi k (X + 16) _ (by omega) (by omega)
        (by omega) _ ((h.mem_eq (m' := M.insert (X + 8) (stData 1 (0#64))) (insert_addr (by kit_disch))).repin
          (by pins_of h))
      exact ⟨c', acc.trans hs, h'⟩

theorem sim_LOADNIL : SimArm .LOADNIL := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001d284
  simp [setNils, VState.apply, KEdge.kills, writeDefs_range', foldr_range_top] at hk htop
  subst hk
  have hB : ins.b = (ins.toNat >>> 16) % 2 ^ 8 := rfl
  kit_bound hAt (ins.a + ins.b)
  kit_run h0 acc until [0x8001d2a8]
  simp only [field_b_shl] at h0
  obtain ⟨_, hs, h0⟩ := loadnil_loop w s.pc ins _ (w.slot ins.a + 16 * (ins.b + 1)) (by kit_disch)
    (by kit_disch) (ins.b + 1) (w.slot ins.a) _ (by omega) rfl (by kit_disch) _ (h0.repin (by pins_of h0))
  have acc := acc.trans hs
  kit_run h0 acc
  refine ⟨_, acc, hc.bleach h0 (by kit_pins h0) (fun x hx _ => nilMem_out fun i hi e => hx ?_)
    (hc.stack_of (fun j => ins.a ≤ j ∧ j < ins.a + (ins.b + 1)) (fun j hj => by simp [hj])
      (fun x _ hx => nilMem_out fun i hi e => ?_) fun j v hj _ hv => ?_), h0.pcAt⟩
  · simp only [Slots, RelPtrs.slot, stackValueSize] at e ⊢; omega
  · have := hx (ins.a + i) ⟨by omega, by omega⟩; simp only [RelPtrs.slot, stackValueSize] at this e; omega
  · simp only [hj, and_self, if_true, Option.some.injEq] at hv; subst hv
    have := nilMem_tag (M := c.σ.mem) (X := w.slot ins.a) (k := ins.b + 1) (i := j - ins.a) (by omega)
    rw [show w.slot ins.a + 16 * (j - ins.a) = w.slot j by simp only [RelPtrs.slot, stackValueSize]; omega]
      at this
    rw [this]; exact .nil

end Lua.Vm.Sim.Kit

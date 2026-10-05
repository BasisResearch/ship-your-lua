import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Arms

/-!
# `OP_LOADNIL` by the direct kit (lane KIT-2; round-4 S-SCAN refactor)

`setnilvalue(s2v(ra++))` for `B + 1` registers: an inline do-while loop
(`0x8001d2a8`: `addi a5,a5,16; sb zero,-8(a5); bne a5,a4`) that stores the
nil tag of each slot. `loadnil_loop` is the loop rule `seg_loop` (M-loop)
over the iterations done; the loop's memory is a comprehension log entry
(`compMem`: "for all `i < k`, `sb zero` at `X + 8 + 16·i`"). The close is
`Core.bleach` with the written registers `[A, A + B]` (`Core.stack_of`),
read through the entry (`compMem_out`, `compMem_in`).
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

/-- The loop's head `0x8001d2a8` after `i` iterations from `a5 = X`, `a4 = E`. -/
abbrev nilSt (w : RelPtrs) (pc : Nat) (ins : Word) (o : Array String) (M : Mem) (X E i : Nat) :
    Config → Prop :=
  SegSt 0x8001d2a8#64 (⟨Register.x15, BitVec.ofNat 64 (X + 16 * i)⟩ :: ⟨Register.x14, BitVec.ofNat 64 E⟩ ::
    armPins w pc ins) (ArmPay (compMem M (X + 8) 16 (stData 1 (0#64)) i) o)

/-- **The loop** (`seg_loop`): `K` iterations from `X` to `E = X + 16·K`. -/
theorem loadnil_loop (w : RelPtrs) (pc : Nat) (ins : Word) (o : Array String) (M : Mem) (X E K : Nat)
    (hK : 0 < K) (hE : X + 16 * K = E) (hX : tohostAddr + 8 ≤ X) (hhi : E ≤ 2 ^ 32) :
    Triple (nilSt w pc ins o M X E 0) (SegSt 0x8001d2b4#64 (⟨Register.x15, BitVec.ofNat 64 E⟩ ::
      ⟨Register.x14, BitVec.ofNat 64 E⟩ :: armPins w pc ins)
        (ArmPay (compMem M (X + 8) 16 (stData 1 (0#64)) K) o)) :=
  fun c h => seg_loop (S := fun i c => i < K ∧ nilSt w pc ins o M X E i c) (fun i => K - i)
    (fun i c ⟨hi, h⟩ => by
      have acc := Steps.refl c
      have hTH : tohostAddr = 0x8005c6c0 := rfl
      dsimp only [nilSt] at h
      by_cases hk : i + 1 = K
      · have hb : (X + 16 * i + 16 != E) = false := by simp; omega
        kit_run h acc until [0x8001d2b4, 0x8001d2a8]
        exact ⟨_, acc, .inr ((h.mem_eq (by rw [← hk]; exact insert_addr (by kit_disch))).repin
          (by pins_of h))⟩
      · have hb : (X + 16 * i + 16 != E) = true := by simp; omega
        kit_run h acc until [0x8001d2b4, 0x8001d2a8]
        exact ⟨_, acc, .inl ⟨i + 1, by omega, by omega,
          (h.mem_eq (insert_addr (by kit_disch))).repin (by pins_of h)⟩⟩) 0 c ⟨hK, h⟩

theorem sim_LOADNIL : SimArm .LOADNIL := sim_arm (by decide) fun {p} hS {c s s' w ins} hA hf hop hstep => by
  kit_setup 0x8001d284
  simp [setNils, VState.apply, KEdge.kills, writeDefs_range', foldr_range_top] at hk htop
  subst hk
  have hB : ins.b = (ins.toNat >>> 16) % 2 ^ 8 := rfl
  kit_bound hAt (ins.a + ins.b)
  kit_run h0 acc until [0x8001d2a8]
  simp only [field_b_shl] at h0
  obtain ⟨_, hs, h0⟩ := loadnil_loop w s.pc ins _ _ (w.slot ins.a) _ (ins.b + 1) (by omega) rfl
    (by kit_disch) (by kit_disch) _ (h0.repin (by pins_of h0))
  have acc := acc.trans hs
  kit_run h0 acc
  refine ⟨_, acc, hc.bleach h0 (by kit_pins h0) (fun x hx _ => compMem_out fun i hi e => hx ?_)
    (hc.stack_of (fun j => ins.a ≤ j ∧ j < ins.a + (ins.b + 1)) (fun j hj => by simp [hj])
      (fun x _ hx => compMem_out fun i hi e => ?_) fun j v hj _ hv => ?_), h0.pcAt⟩
  · simp only [Slots, RelPtrs.slot, stackValueSize] at e ⊢; omega
  · have := hx (ins.a + i) ⟨by omega, by omega⟩; simp only [RelPtrs.slot, stackValueSize] at this e; omega
  · simp only [hj, and_self, if_true, Option.some.injEq] at hv; subst hv
    have := compMem_in (M := c.σ.mem) (o := w.slot ins.a + 8) (s := 16) (b := stData 1 (0#64))
      (k := ins.b + 1) (i := j - ins.a) (by omega)
    rw [show w.slot ins.a + 8 + 16 * (j - ins.a) = w.slot j + tvalueTagOff by
      simp only [RelPtrs.slot, stackValueSize, tvalueTagOff]; omega] at this
    rw [show slotTag _ (w.slot j) = BitVec.ofNat 8 vNil by simp only [slotTag, bytesT1, this]; decide]
    exact .nil

end Lua.Vm.Sim.Kit

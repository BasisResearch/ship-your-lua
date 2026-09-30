import Lua.Vm.Sim.Rel
import Lua.Vm.Sim.Bits
import Lua.Vm.Arms.Head
import Vsa.Sim.StepCount

/-!
# The dispatch lemma: from the fetch head to the arm of the opcode (A1)

`dispatch`, proved once for every opcode in the table: from `VmRelAt p c s w`
at the fetch head with the instruction `ins` at `s.pc`, the machine runs the
generated head segment `Lua.Vm.Arms.seg_8001bfe4_8001c00c` (trap check, `lw`,
bound check, the `lw` of the 4-byte table entry in `.rodata`, the `jr`) and
arrives at `armTarget ins.opNum` (`ArmAt`): the relation's `Core` unchanged,
s3 = `pc + 1`, s4 = the instruction. The side conditions of the segment are
discharged from the relation (`Core.fetch`, `Ranges`, the image's `.rodata`
via `jtWord_eq`, `armTarget_aligned`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- A tracked pin, by position in the bundle. -/
theorem pinsHold_get {σ : MState} :
    ∀ {L : List Pin}, PinsHold σ L → ∀ (i : Nat) (hi : i < L.length),
      σ.regs.get? L[i].1 = some L[i].2
  | _ :: _, h, 0, _ => h.1
  | _ :: _, h, i + 1, hi => pinsHold_get h.2 i (by simp only [List.length_cons] at hi; omega)

/-- A run that moves the pc is not empty. -/
theorem steps_lt {a b : Config} (h : Steps a b) (hne : a ≠ b) : a.steps < b.steps := by
  cases h with
  | refl => exact absurd rfl hne
  | head s r => have := s.steps_succ; have := r.steps_le; omega

/-- **The dispatch lemma.** -/
theorem dispatch {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hR : VmRelAt p c s w)
    {ins : Word} (hf : p.fetch s.pc = some ins) (hop : ins.opNum < Arms.jtEntries) :
    ∃ c', Steps c c' ∧ c.steps < c'.steps ∧ ArmAt p c' s w ins := by
  have hc := hR.core
  have hr := hc.ranges
  have hlt := fetch_lt hf
  have hN : w.code + 4 * s.pc + 4 ≤ 0x100000000 := by have := hr.code_hi; omega
  have hN' : w.code + 4 * s.pc < 2 ^ 64 := by omega
  have eN := add_imm (w.code + 4 * s.pc) 0 (by decide)
  simp only [Nat.add_zero] at eN
  have hins : bytesT4 c.σ.mem (w.code + 4 * s.pc) = ins := hc.fetch hf
  have hopc : ins.opNum = ins.toNat % 2 ^ 7 := by
    simp only [Word.opNum, Word.field, Nat.shiftRight_zero]
  have eJ := add_imm (Arms.jtBase + ins.opNum * 2 ^ 2) 0 (by decide)
  simp only [Nat.add_zero] at eJ
  have hjt : bytesT4 c.σ.mem (Arms.jtBase + 4 * ins.opNum) = jtWord ins.opNum :=
    jtWord_eq hc.image.2 hop
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hJB : Arms.jtBase = 0x8005336c := rfl
  have hJE : Arms.jtEntries = 82 := rfl
  obtain ⟨c', hs, hpost⟩ := Arms.seg_8001bfe4_8001c00c
    (0#64) (BitVec.ofNat 64 (w.code + 4 * s.pc)) (BitVec.ofNat 64 (Arms.jtEntries - 1))
    (BitVec.ofNat 64 Arms.jtBase) (BitVec.ofNat 64 w.sp) (BitVec.ofNat 64 symGlobalPointer)
    (BitVec.ofNat 64 w.L) (BitVec.ofNat 64 vNumInt) (BitVec.ofNat 64 w.ci)
    (BitVec.ofNat 64 w.base) c.σ.mem c.σ.sailOutput
    (by decide)
    (by rw [eN, BitVec.toNat_ofNat]; have := hr.code_lo; omega)
    (by rw [eN, BitVec.toNat_ofNat]; omega)
    (by rw [eN, BitVec.toNat_ofNat]; have := hr.code_lo; omega)
    (by
      rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc]
      rw [hJE] at hop ⊢
      simp only [zopz0zI_u, BitVec.toNatInt, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show ins.opNum < 2 ^ 64 by omega)]
      simp
      omega)
    (by
      rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc,
        shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, eJ, BitVec.toNat_ofNat]
      omega)
    (by
      rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc,
        shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, eJ, BitVec.toNat_ofNat]
      omega)
    (by
      rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc,
        shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, eJ, BitVec.toNat_ofNat]
      omega)
    (by
      rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc,
        shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, eJ, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show Arms.jtBase + ins.opNum * 2 ^ 2 < 2 ^ 64 by omega),
        show Arms.jtBase + ins.opNum * 2 ^ 2 = Arms.jtBase + 4 * ins.opNum by omega, hjt]
      exact armTarget_aligned _ hop)
    c ⟨hc.good, hR.pcAt,
      ⟨hc.pins.trap, hc.pins.pc, hc.pins.opMax, hc.pins.jt, hc.pins.sp, hc.pins.gp, hc.pins.L,
        hc.pins.intTag, hc.pins.ci, hc.pins.base, trivial⟩,
      hc.minstret, hc.tick, ⟨hc.image.1, rfl, rfl⟩⟩
  have hP := hpost.pins
  have hpc' : c'.σ.regs.get? Register.PC = some (armTarget ins.opNum) := by
    have h := hpost.pcAt
    rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins, opcode_mask, ← hopc,
      shl_ofNat _ _ (by decide), BitVec.ofNat_add_ofNat, eJ, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show Arms.jtBase + ins.opNum * 2 ^ 2 < 2 ^ 64 by omega),
      show Arms.jtBase + ins.opNum * 2 ^ 2 = Arms.jtBase + 4 * ins.opNum by omega, hjt] at h
    exact h
  have hs3 : c'.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1))) := by
    have h := pinsHold_get hP 2 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [add_imm _ 4 (by decide), show w.code + 4 * s.pc + 4 = w.code + 4 * (s.pc + 1) by omega] at h
    exact h
  have hs4 : c'.σ.regs.get? Register.x20 = some (sign_extend (m := 64) ins) := by
    have h := pinsHold_get hP 3 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [eN, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hN', hins] at h
    exact h
  have hpins : Pins c'.σ w s.pc :=
    ⟨pinsHold_get hP 8 (by simp), pinsHold_get hP 9 (by simp), pinsHold_get hP 10 (by simp),
      pinsHold_get hP 6 (by simp), pinsHold_get hP 11 (by simp), pinsHold_get hP 4 (by simp),
      pinsHold_get hP 12 (by simp), pinsHold_get hP 7 (by simp), pinsHold_get hP 13 (by simp),
      pinsHold_get hP 5 (by simp)⟩
  have hne : c ≠ c' := fun h => by
    have h1 := hR.pcAt
    rw [h, hpc', Option.some.injEq] at h1
    exact armTarget_ne_head _ hop h1
  exact ⟨c', hs, steps_lt hs hne,
    ⟨hc.jump hpost hpins hpost.extra.2.2 hpost.extra.2.1, hpc', hs3, hs4⟩⟩

end Lua.Vm.Sim

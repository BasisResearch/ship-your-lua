import Vsa.Sim.BlockPilot

/-!
# `RegsOk`: every GPR present, the HTIF mailbox idle

The register half of ship-your-interpreter's `VsaOk` (`VsaIris/Vsa/Instance.lean`):
all 31 general registers hold a value, and no `tohost` word is half-written
(`htif_payload_writes = 0`, what every console store needs). `MachineAt`
(`Lua/Vm/Loaded.lean`) carries it at `luaV_execute`'s entry, and `VmRel`
(`Lua/Vm/Sim/Rel.lean`) at the fetch head. The segments of the simulated arms
thread it step by step (`Lua/Vm/Arms/RegsOk.lean`, one lemma per step class).
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState)

namespace Lua.Vm

/-- **All GPRs present, HTIF mailbox idle.** -/
structure RegsOk (σ : MState) : Prop where
  gpr : ∀ n, 1 ≤ n → n ≤ 31 → (Vsa.Sim.gprGet σ n).isSome
  htifIdle : σ.regs.get? Register.htif_payload_writes = some (0#4)

/-- A register no step's bookkeeping writes (the counters, `PC`/`nextPC`, the
`minstret` flags): in the order of `Vsa.Sim.obs_*_other'`'s ladder. -/
abbrev Quiet (R : Register) : Prop :=
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
    (Register.mip == R) = false ∧ (Register.minstret == R) = false ∧
    (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
    (Register.minstret_increment == R) = false

/-- `RegsOk` across a step that keeps every quiet register present and leaves
the mailbox idle. -/
theorem RegsOk.of_step {σ σ' : MState} (h : RegsOk σ)
    (hreg : ∀ R : Register, Quiet R → (σ.regs.get? R).isSome → (σ'.regs.get? R).isSome)
    (hhtif : σ'.regs.get? Register.htif_payload_writes = some (0#4)) : RegsOk σ' := by
  refine ⟨fun n h1 h2 => ?_, hhtif⟩
  have hg := h.gpr n h1 h2
  match n, h1, h2 with
  | 1, _, _ => exact hreg Register.x1 (by decide) hg
  | 2, _, _ => exact hreg Register.x2 (by decide) hg
  | 3, _, _ => exact hreg Register.x3 (by decide) hg
  | 4, _, _ => exact hreg Register.x4 (by decide) hg
  | 5, _, _ => exact hreg Register.x5 (by decide) hg
  | 6, _, _ => exact hreg Register.x6 (by decide) hg
  | 7, _, _ => exact hreg Register.x7 (by decide) hg
  | 8, _, _ => exact hreg Register.x8 (by decide) hg
  | 9, _, _ => exact hreg Register.x9 (by decide) hg
  | 10, _, _ => exact hreg Register.x10 (by decide) hg
  | 11, _, _ => exact hreg Register.x11 (by decide) hg
  | 12, _, _ => exact hreg Register.x12 (by decide) hg
  | 13, _, _ => exact hreg Register.x13 (by decide) hg
  | 14, _, _ => exact hreg Register.x14 (by decide) hg
  | 15, _, _ => exact hreg Register.x15 (by decide) hg
  | 16, _, _ => exact hreg Register.x16 (by decide) hg
  | 17, _, _ => exact hreg Register.x17 (by decide) hg
  | 18, _, _ => exact hreg Register.x18 (by decide) hg
  | 19, _, _ => exact hreg Register.x19 (by decide) hg
  | 20, _, _ => exact hreg Register.x20 (by decide) hg
  | 21, _, _ => exact hreg Register.x21 (by decide) hg
  | 22, _, _ => exact hreg Register.x22 (by decide) hg
  | 23, _, _ => exact hreg Register.x23 (by decide) hg
  | 24, _, _ => exact hreg Register.x24 (by decide) hg
  | 25, _, _ => exact hreg Register.x25 (by decide) hg
  | 26, _, _ => exact hreg Register.x26 (by decide) hg
  | 27, _, _ => exact hreg Register.x27 (by decide) hg
  | 28, _, _ => exact hreg Register.x28 (by decide) hg
  | 29, _, _ => exact hreg Register.x29 (by decide) hg
  | 30, _, _ => exact hreg Register.x30 (by decide) hg
  | 31, _, _ => exact hreg Register.x31 (by decide) hg

end Lua.Vm

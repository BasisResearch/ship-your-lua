import Lua.Vm.Sim.Kit.Run
import Lua.Vm.Arms.Segs.Hexit
import Lua.Vm.Arms.Segs.Hcall_exitprocs
import Lua.Vm.Arms.Segs.Hretarget_lock_acquire_recursive
import Lua.Vm.Arms.Segs.Hretarget_lock_release_recursive
import Lua.Vm.Arms.Segs.HUexit
import Vsa.Sim.Generic.ExitStep

/-!
# `exit(0)` with no handler, and `_exit`'s `tohost` store (lane F1-4)

`exit(0)` (`0x8002f85c`) calls `__call_exitprocs(0, NULL)`, which takes the
(no-op) recursive lock, finds `__atexit = NULL` (`beqz` taken) and releases
the lock; with `__stdio_exit_handler = NULL` (`beqz` taken) `exit` calls
`_exit(0)`, which stores `(0 << 1) | 1` to `tohost` (`sd a5,120(a4)`): the
HTIF exit with code 0, the console unchanged (`exit_halt`,
`Vsa.Sim.stepOnce_tohost_G`, the step `Console.exit_haltFact` packages for
the Iris route). `exitOk_of_quiet` gives `ExitOk` of a complement with no
handler (the entry's, `StdioBoot`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- A `ret`'s target: the saved `ra`, aligned. -/
theorem rtgt (r : BitVec 64) (h : r.toNat % 4 = 0) : BitVec.update r 0 0#1 = r := by
  have := Vsa.Sim.ret_tgt r h; rwa [Vsa.Sim.sext_zero, BitVec.add_zero] at this

theorem bytesT8_wm8_out' {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

/-- A read of a store chain at the stored address. -/
theorem bytesT8_wm8_hitX {m : Mem} {a x : Nat} {d : BitVec 64} (h : a = x) :
    bytesT8 (writeMap8 m a (sdData_val d)) x = d := by
  subst h; rw [bytesT8_writeMap8, sdData_id]

/-- `addi rd, rs, -k`, in range. -/
theorem sl_negX {y k : Nat} (hk : 2048 ≤ k ∧ k < 4096) (hy : 4096 - k ≤ y) (hy2 : y < 2 ^ 64) :
    BitVec.ofNat 64 y + sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (y - (4096 - k)) := by
  rw [imm_neg_add y k hk.1 hk.2]
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- **`_exit`'s store halts**: at `0x8000064c` with `a4` the `auipc` base of
`tohost` and `a5 = (0 << 1) | 1`, the next step is the HTIF exit with code 0,
reporting the console so far. -/
theorem exit_halt {m : Mem} {o : Array String} {c : Config} {L : List Pin}
    (h : SegSt 0x8000064c#64 (⟨Register.x14, 0x8005c648#64⟩ :: ⟨Register.x15, 1#64⟩ :: L)
      (ArmPay m o) c) :
    ∃ σf, Vsa.Machine.Halted c 0 σf ∧ Vsa.Machine.output σf = Vsa.Machine.output c.σ := by
  obtain ⟨σ, i, u⟩ := c
  have hG := h.good
  have hpc := h.pcAt
  obtain ⟨vm, hvm⟩ := h.minstret
  have hok := h.armOk
  obtain ⟨th, hth⟩ := hG.htif_tohost
  have hx14 := h.pins.1
  have hx15 := h.pins.2.1
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Lua.Vm.Code._exit_at_8000064c
    (Lua.Vm.Code.textLoaded__exitLoaded h.armText)
  have hstep := stepOnce_tohost_G σ i u (0x8000064c#64) vm (0x06f73c23#32) (0x078#12)
    (regidx.Regidx 0x0f#5) (regidx.Regidx 0x0e#5) (0x8005c648#64) (1#64) (1#64) (0#64) th
    (0x23#8) (0x3c#8) (0xf7#8) (0x06#8) hG hpc hvm (by decide) (by decide)
    (Vsa.Sim.decodeW (w := 0x06f73c23#32) (afterPrelude σ)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.misa)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.cur_privilege)
      (by rw [get?_afterPrelude σ _ (by decide)]; exact hG.mseccfg))
    (rX_bits_x14 _ _ (by rw [get?_afterNextPC σ _ _ (by decide) (by decide)]; exact hx14))
    (rX_bits_x15 _ _ (by rw [get?_afterNextPC σ _ _ (by decide) (by decide)]; exact hx15))
    (by decide) rfl hok.htifIdle hth (by decide) (by decide) hb0 hb1 hb2 hb3
    (by decide) (by decide) (by decide)
  exact ⟨_, .mk hstep, rfl⟩

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_negX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    Nat.reduceAdd, symGlobalPointer, bytesT8_wm8_hitX, bytesT8_wm8_out', sext64_id, hat,
    hsx] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (rw [rtgt _ (by decide)]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          Nat.reduceAdd, symGlobalPointer, bytesT8_wm8_hitX, bytesT8_wm8_out', sext64_id, hat,
          hsx, Vsa.Sim.sext_zero, BitVec.add_zero]
         first | decide | (rw [rtgt _ (by decide)]; decide)))

/-- **`exit(0)` with no `atexit` handler and no stdio exit handler halts with
code 0**, the console unchanged. -/
theorem exit_run {M : Mem} {o : Array String} {c : Config}
    {q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64}
    (h : SegSt (BitVec.ofNat 64 symCExit) (exitRow q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27)
      (ArmPay M o) c)
    (hat : bytesT8 M symAtexit = 0#64) (hsx : bytesT8 M symStdioExitHandler = 0#64) :
    Vsa.Machine.Halts c (Vsa.Machine.output c.σ) 0 := by
  have acc := Steps.refl c
  have hout := h.armOut
  simp only [symAtexit, symStdioExitHandler] at hat hsx
  simp only [exitRow, symCExit] at h
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc
  have h := h.at (rtgt _ (by decide))
  kit_run h acc until [0x8000064c]
  obtain ⟨σf, hh, ho⟩ := exit_halt (L := []) (h.repin (by pins_of h))
  refine ⟨_, σf, acc, hh, ho.trans ?_⟩
  exact (output_congr (h.armOut.trans hout.symm))


/-- **`ExitOk` of a complement with no `atexit` and no stdio exit handler**,
the two words off `ExitFree`. -/
theorem exitOk_of_quiet {p : Proto} {w : RelPtrs} (hat : bytesT8 w.mo symAtexit = 0#64)
    (hsx : bytesT8 w.mo symStdioExitHandler = 0#64)
    (hout : ∀ i, i < 8 → ¬ ExitFree p w (symAtexit + i) ∧ ¬ ExitFree p w (symStdioExitHandler + i)) :
    ExitOk p w := by
  intro M o c q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 hM h
  exact exit_run h ((bytesT8_congrT fun i hi => hM _ (hout i hi).1).trans hat)
    ((bytesT8_congrT fun i hi => hM _ (hout i hi).2).trans hsx)

end Lua.Vm.Sim.Ret

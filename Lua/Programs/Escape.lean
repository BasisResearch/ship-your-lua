import Lua.StuckCases
import Lua.Theorems
import Lua.Vm.Runtime
import Lua.Programs.EscStrflt
import Lua.Programs.EscForstr
import Lua.Programs.EscUnmflt

/-!
# Supported programs whose bytecode is stuck but whose binary exits 0

Three `luac -s` chunks (`c/tests/stuck/`) that are `Supported`, whose `BcSem`
run reaches a stuck state that is not final (so they have no `BcSem`
output), and on which Lua 5.4.7 continues (`Fault.Escape`):

| program | stuck at | Lua's value | Sail run of the ELF |
|---|---|---|---|
| `s_strflt.lua`: `local x = "1.5" + 1; print(x)` | `MMBINI` (`__add`, `"1.5"`, `1`) | `2.5` | prints `2.5`, exit 0, 192,534 steps |
| `s_forstr.lua`: `for i = 1, "2" do print(i) end` | `FORPREP` (limit `"2"`) | `forlimit` coerces | prints `1`, `2`, exit 0, 186,147 steps |
| `s_unmflt.lua`: `local s = "1.5"; print(-s)` | `UNM` (`"1.5"`) | `-1.5` | prints `-1.5`, exit 0, 191,970 steps |

(`c/tests/difftest.sh c/tests/stuck/*.lua`: host `lua` and the ELF on the
Sail model agree; the seven `e_*.lua` probes there, one per error kind,
exit 2.)

So `StuckSim` (`Lua/Vm/Sim/Fold.lean`) is false for these programs, and
with it `vm_refinement_Statement luaLayout` itself:
`vm_refinement_no_clean_halt` derives from it that the ELF loaded with each
of them never halts with code 0, which the Sail runs contradict. The
statements are kept; the escapes are excluded by the named hypothesis
`NoEscape` in the corrected Layer A (`Lua/Vm/Sim/Stuck.lean`).
-/

namespace Lua.Programs

open Lua.Bytecode Lua.Vm Vsa.Machine Vsa.Densify

theorem escStrflt_supported : Supported escStrfltProto := by decide +kernel
theorem escForstr_supported : Supported escForstrProto := by decide +kernel
theorem escUnmflt_supported : Supported escUnmfltProto := by decide +kernel

theorem escStrflt_stuckRun : (stuckRun binaryHost escStrfltProto 8 State.init).isSome := by
  decide +kernel
theorem escForstr_stuckRun : (stuckRun binaryHost escForstrProto 8 State.init).isSome := by
  decide +kernel
theorem escUnmflt_stuckRun : (stuckRun binaryHost escUnmfltProto 8 State.init).isSome := by
  decide +kernel

theorem noBcSem_of_isSome {p : Proto} {n : Nat}
    (h : (stuckRun binaryHost p n State.init).isSome) : ¬ ∃ out, BcSem binaryHost p out := by
  cases hr : stuckRun binaryHost p n State.init with
  | none => rw [hr] at h; cases h
  | some s => exact noBcSem_of_stuckRun hr

theorem escStrflt_noBcSem : ¬ ∃ out, BcSem binaryHost escStrfltProto out :=
  noBcSem_of_isSome escStrflt_stuckRun
theorem escForstr_noBcSem : ¬ ∃ out, BcSem binaryHost escForstrProto out :=
  noBcSem_of_isSome escForstr_stuckRun
theorem escUnmflt_noBcSem : ¬ ∃ out, BcSem binaryHost escUnmfltProto out :=
  noBcSem_of_isSome escUnmflt_stuckRun

/-- The word of `MMBINI 0 1 6 0` (`__add`), `s_strflt`'s instruction 3. -/
abbrev mmbiniW : Word := 0x0680002f#32

/-- The kernel of `s_strflt`'s instruction 3: `MMBINI` after `ADDI` fell
through. -/
def escStrfltK : Kernel Value :=
  (opKernel escStrfltProto 3 mmbiniW .MMBINI).get (by decide +kernel)

/-- `MMBINI`'s operands (`R[0]`, the immediate `1`). -/
def escStrfltOs : List Opnd := flip false (.reg 0) (immB mmbiniW)

/-- **`"1.5" + 1` reaches an escaping stuck state** (`¬ NoEscape`): the run
stops at `MMBINI` with `R[0] = "1.5"`, the fault is `δ (.tm .add)` on
`["1.5", 1]`, and it is a `Fault.Escape`. -/
theorem escStrflt_escapes : ¬ NoEscape binaryHost escStrfltProto := by
  intro hNE
  cases hr : stuckRun binaryHost escStrfltProto 8 State.init with
  | none => have := escStrflt_stuckRun; rw [hr] at this; cases this
  | some s =>
    have hpc : (stuckRun binaryHost escStrfltProto 8 State.init).map VState.pc = some 3 := by
      decide +kernel
    have hrd : (stuckRun binaryHost escStrfltProto 8 State.init).map
        (fun s => [0].mapM s.regs) = some (some [.str [49, 46, 53]]) := by decide +kernel
    rw [hr] at hpc hrd
    simp only [Option.map_some, Option.some.injEq] at hpc hrd
    have hreads : escStrfltK.reads = [0] := by decide +kernel
    refine hNE s mmbiniW .MMBINI escStrfltK [.str [49, 46, 53]] (.prim (.tm .add) escStrfltOs)
      (stuckRun_sound hr).steps
      ⟨by rw [hpc]; decide +kernel, by decide +kernel, by rw [hpc]; exact (Option.some_get _).symm,
        by rw [hreads]; exact hrd, Option.isNone_iff_eq_none.1 (by decide +kernel),
        show δ _ _ = none by decide +kernel, by decide +kernel,
        show escStrfltK.reads = _ by rw [hreads]; decide +kernel⟩ ?_
    exact rfl

/-- **What Layer A says about a supported program with no `BcSem` output**:
its binary never halts with code 0. -/
theorem vm_refinement_no_clean_halt (H : vm_refinement_Statement luaLayout) {p : Proto}
    (hS : Supported p) (hno : ¬ ∃ out, BcSem binaryHost p out) {c : Config}
    (hL : VmLoaded luaLayout p (fillZero c)) (out : String) : ¬ Halts c out 0 :=
  fun h => hno ⟨out, ((H p c hS hL).1 out).2 h⟩

/-- **The obstruction**: `vm_refinement_Statement luaLayout` implies that
the ELF running `"1.5" + 1` never exits 0. The Sail model's run of
`c/tests/stuck/s_strflt.lua` exits 0 (printing `2.5`). -/
theorem escStrflt_obstruction (H : vm_refinement_Statement luaLayout) {c : Config}
    (hL : VmLoaded luaLayout escStrfltProto (fillZero c)) (out : String) : ¬ Halts c out 0 :=
  vm_refinement_no_clean_halt H escStrflt_supported escStrflt_noBcSem hL out

theorem escForstr_obstruction (H : vm_refinement_Statement luaLayout) {c : Config}
    (hL : VmLoaded luaLayout escForstrProto (fillZero c)) (out : String) : ¬ Halts c out 0 :=
  vm_refinement_no_clean_halt H escForstr_supported escForstr_noBcSem hL out

theorem escUnmflt_obstruction (H : vm_refinement_Statement luaLayout) {c : Config}
    (hL : VmLoaded luaLayout escUnmfltProto (fillZero c)) (out : String) : ¬ Halts c out 0 :=
  vm_refinement_no_clean_halt H escUnmflt_supported escUnmflt_noBcSem hL out

end Lua.Programs

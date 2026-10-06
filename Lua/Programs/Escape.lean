import Lua.StuckCases
import Lua.Theorems
import Lua.Vm.Runtime
import Lua.Programs.EscStrflt
import Lua.Programs.EscForstr
import Lua.Programs.EscUnmflt

/-!
# The former escapes: three programs with floats and string coercion

Three `luac -s` chunks (`c/tests/stuck/`) on which the integer-only `δ` was
stuck while Lua 5.4.7 continues (lane F1-5, `abstractions/ledger/f1-lane-5.md`).
With floats and string coercion in `δ` (FLOAT-DESIGN.md S1) each has a
`BcSem` output, and it is what the ELF prints on the Sail model:

| program | `δ` now | `BcSem` output | Sail run of the ELF |
|---|---|---|---|
| `s_strflt.lua`: `local x = "1.5" + 1; print(x)` | `MMBINI` (`__add`): `lstrlib.c` `arith` → `luaO_rawarith` | `2.5` | prints `2.5`, exit 0 |
| `s_forstr.lua`: `for i = 1, "2" do print(i) end` | `FORPREP`: `forlimit` coerces `"2"` | `1`, `2` | prints `1`, `2`, exit 0 |
| `s_unmflt.lua`: `local s = "1.5"; print(-s)` | `UNM` (`__unm`): `arith_unm` | `-1.5` | prints `-1.5`, exit 0 |

(`c/tests/difftest.sh c/tests/stuck/s_*.lua`.) Each is `Supported`, and no
supported program escapes (`noEscape_of_supported`), so `NoEscape` is no
longer a hypothesis of Layer A (`Lua/Vm/Sim/Stuck.lean`).
-/

namespace Lua.Programs

open Lua.Bytecode Lua.Vm Vsa.Machine Vsa.Densify

theorem escStrflt_supported : Supported escStrfltProto := by decide +kernel
theorem escForstr_supported : Supported escForstrProto := by decide +kernel
theorem escUnmflt_supported : Supported escUnmfltProto := by decide +kernel

/-- **`"1.5" + 1` prints `2.5`** (the string library's `__add`). -/
theorem escStrflt_bcSem : BcSem binaryHost escStrfltProto "2.5\n" :=
  bcSem_of_run (n := 20) (by decide +kernel)

/-- **`for i = 1, "2"` runs twice** (`forlimit` coerces the limit). -/
theorem escForstr_bcSem : BcSem binaryHost escForstrProto "1\n2\n" :=
  bcSem_of_run (n := 40) (by decide +kernel)

/-- **`-"1.5"` prints `-1.5`** (the string library's `__unm`). -/
theorem escUnmflt_bcSem : BcSem binaryHost escUnmfltProto "-1.5\n" :=
  bcSem_of_run (n := 20) (by decide +kernel)

theorem escStrflt_noEscape : NoEscape binaryHost escStrfltProto :=
  noEscape_of_supported escStrflt_supported
theorem escForstr_noEscape : NoEscape binaryHost escForstrProto :=
  noEscape_of_supported escForstr_supported
theorem escUnmflt_noEscape : NoEscape binaryHost escUnmfltProto :=
  noEscape_of_supported escUnmflt_supported

theorem noBcSem_of_isSome {p : Proto} {n : Nat}
    (h : (stuckRun binaryHost p n State.init).isSome) : ¬ ∃ out, BcSem binaryHost p out := by
  cases hr : stuckRun binaryHost p n State.init with
  | none => rw [hr] at h; cases h
  | some s => exact noBcSem_of_stuckRun hr

/-- **What Layer A says about a supported program with no `BcSem` output**:
its binary never halts with code 0. -/
theorem vm_refinement_no_clean_halt (H : vm_refinement_Statement luaLayout) {p : Proto}
    (hS : Supported p) (hno : ¬ ∃ out, BcSem binaryHost p out) {c : Config}
    (hL : VmLoaded luaLayout p (fillZero c)) (out : String) : ¬ Halts c out 0 :=
  fun h => hno ⟨out, ((H p c hS hL).1 out).2 h⟩

/-- **What Layer A says about the former escapes**: the ELF running `"1.5" +
1` halts with code 0 exactly when the output is `2.5\n`. -/
theorem escStrflt_layerA (H : vm_refinement_Statement luaLayout) {c : Config}
    (hL : VmLoaded luaLayout escStrfltProto (fillZero c)) (out : String) :
    Halts c out 0 ↔ out = "2.5\n" :=
  ⟨fun h => BcSem.deterministic (((H _ c escStrflt_supported hL).1 out).2 h) escStrflt_bcSem,
    fun h => h ▸ ((H _ c escStrflt_supported hL).1 _).1 escStrflt_bcSem⟩

end Lua.Programs

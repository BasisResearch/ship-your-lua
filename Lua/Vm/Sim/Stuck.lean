import Lua.Vm.Sim.Fold
import Lua.StuckCases

/-!
# The stuck clause: Lua errors, and Layer A from them

`StuckSim` (`Lua/Vm/Sim/Fold.lean`) asks, at every reachable stuck non-final
state, that the machine diverge or halt with a nonzero code (`StuckOut`; the
output before the halt is unconstrained, and `FoldSim.stuckOut` needs no
more). `stuck_cases` (`Lua/StuckCases.lean`) enumerates those states as
`StuckAt … φ` for a failing `Fault` `φ`, and splits them:

* **escapes** (`Fault.Escape`, exact since floats and string coercion are in
  `δ`): only a stuck `OP_FORLOOP`, where `lvm.c` continues on whatever the
  loop's registers hold; a supported program never reaches one
  (`noEscape_of_supported`, by the loop check `loopsOk`);
* **errors** (the rest): Lua raises an error from the C function
  `Fault.site` names. The machine obligation is `ErrorSim`, one field per
  site: from `VmRel` at such a state, `StuckOut`. Every site ends in
  `luaG_errormsg` → `luaD_throw` → `longjmp` → `luaD_rawrunprotected`'s
  return → `lua_pcallk` returns `LUA_ERRRUN` → `main` prints `lua: <msg>` to
  stderr and returns 2 → `exit(2)` → `_exit`'s `tohost` store.

So `StuckSim` follows from `ErrorSim` (`stuckSim_of_error`), and Layer A
from `OpenArms`, `FloatArms` and `ErrorSim` (`vm_refinement_of_error`), with
no `NoEscape` hypothesis. `StuckSimNE` and `vm_refinement_ne_Statement` (the
lane-5 route under `NoEscape`) remain, now with `NoEscape` derived.
-/

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout Vsa.Sim
open Vsa.Machine (Config)

/-- **The error clause at one site**: at a reachable state that is stuck at
a non-escaping fault whose error `site` raises, the machine diverges or halts
with a nonzero code. -/
def ErrorSimAt (e : ErrSite) : Prop :=
  ∀ p c s w o K vs φ, Supported p → Reach p s → VmRel p c s → StuckAt p s w o K vs φ →
    ¬ φ.Escape vs → φ.site vs = e → StuckOut c

/-- **The machine side of the Lua errors**, one obligation per raising C
function (`ErrSite`). Each is the arm's path to the call of that function
(the at-lemma route, as the arms' step paths), then the shared tail
`luaG_errormsg` → `luaD_throw` → … → `_exit` with code 2. -/
structure ErrorSim : Prop where
  /-- `luaG_runerror` (0x800092cc): `n%0`, `n//0`, `'for' step is zero` -/
  runerror : ErrorSimAt .runerror
  /-- `luaG_opinterror` (0x80009414) via `luaT_trybinTM` (0x800194f4) -/
  opinterror : ErrorSimAt .opinterror
  /-- `luaG_tointerror` (0x80009468) via `luaT_trybinTM` -/
  tointerror : ErrorSimAt .tointerror
  /-- `luaL_error` (0x800207a4) from `lstrlib.c`'s `trymt`, through the
  string metamethod call (`luaT_trybinTM` → `luaT_callTMres` → `luaD_call`) -/
  strarith : ErrorSimAt .strarith
  /-- `luaG_typeerror` (0x80009398) via `luaV_objlen` (0x8001bae0) -/
  typeerror : ErrorSimAt .typeerror
  /-- `luaG_ordererror` (0x800094c0) via `luaT_callorderTM` (0x800196c4) or
  `luaT_callorderiTM` (0x80019738) -/
  ordererror : ErrorSimAt .ordererror
  /-- `luaG_concaterror` (0x800093e4) via `luaT_tryconcatTM` (0x800195f4) -/
  concaterror : ErrorSimAt .concaterror
  /-- `luaG_forerror` (0x80009438) from `forprep` -/
  forerror : ErrorSimAt .forerror
  /-- `luaG_callerror` (0x80009530) via `luaD_precall` → `luaD_tryfuncTM` -/
  callerror : ErrorSimAt .callerror

theorem ErrorSim.at (h : ErrorSim) : ∀ e, ErrorSimAt e
  | .runerror => h.runerror
  | .opinterror => h.opinterror
  | .tointerror => h.tointerror
  | .strarith => h.strarith
  | .typeerror => h.typeerror
  | .ordererror => h.ordererror
  | .concaterror => h.concaterror
  | .forerror => h.forerror
  | .callerror => h.callerror

/-- **The stuck clause without escapes.** -/
def StuckSimNE : Prop :=
  ∀ p c s, Supported p → NoEscape binaryHost p → Reach p s → VmRel p c s → ¬ Final p s →
    Stuck p s → StuckOut c

/-- **`StuckSimNE` from the error sites** (`stuck_cases`). -/
theorem stuckSimNE_of_error (h : ErrorSim) : StuckSimNE := by
  intro p c s hS hNE hs hR hnf hst
  obtain ⟨w, o, K, vs, φ, hA⟩ := stuck_cases hS hs hnf hst
  exact h.at _ p c s w o K vs φ hS hs hR hA (hNE s w o K vs φ hs hA) rfl

/-- `StuckSim` is `StuckSimNE` where no program escapes. -/
theorem stuckSim_of_NE (h : StuckSimNE) (hall : ∀ p, Supported p → NoEscape binaryHost p) :
    StuckSim :=
  fun p c s hS hs hR hnf hst => h p c s hS (hall p hS) hs hR hnf hst

/-- **The stuck clause from the error sites**: no supported program escapes
(`noEscape_of_supported`). -/
theorem stuckSim_of_error (h : ErrorSim) : StuckSim :=
  stuckSim_of_NE (stuckSimNE_of_error h) fun _ hS => noEscape_of_supported hS

/-- **Layer A from the open premises and the error sites** (no `NoEscape`). -/
theorem vm_refinement_of_error (arms : OpenArms) (farms : FloatArms) (err : ErrorSim) :
    vm_refinement_Statement luaLayout :=
  vm_refinement_of_open arms farms finalSim (stuckSim_of_error err)

/-! ## Layer A without escapes -/

/-- Loaded at the VM cut point, supported, and without escapes. -/
def VmLoadedNE (p : Proto) (c : Config) : Prop :=
  Supported p ∧ NoEscape binaryHost p ∧ VmLoaded luaLayout p c

/-- **Layer A's obligation without escapes.** -/
abbrev VmSimNE : Prop := Refine.Sim (fun p out => BcSem binaryHost p out) VmLoadedNE

/-- **Layer A without escapes**: `vm_refinement_Statement luaLayout` for the
supported programs none of whose reachable stuck states escapes. -/
def vm_refinement_ne_Statement : Prop :=
  ∀ p c, Supported p → NoEscape binaryHost p → VmLoaded luaLayout p (Vsa.Densify.fillZero c) →
    (∀ out, BcSem binaryHost p out ↔ Vsa.Machine.Halts c out 0) ∧
    (Vsa.Machine.Diverges c → ¬ ∃ out, BcSem binaryHost p out)

/-- **`VmSimNE` from the arms** (the fold, `foldSim_of_arms`). -/
theorem vmSimNE_of_arms (arms : ∀ o ∈ armOps, SimArm o) (entry : EntrySim)
    (vararg : VarargSim) (final : FinalSim) (stuck : StuckSimNE) : VmSimNE :=
  fold_sim (R := FoldRel) (fun _ _ ⟨hS, _, hL⟩ => foldRel_entry entry hS hL)
    (fun p _ ⟨hS, hNE, _⟩ => foldSim_of_arms arms vararg final hS fun c s hs hR hnf hno =>
      stuck p c s hS hNE hs hR hnf hno)

theorem vm_refinement_ne_of_sim (H : VmSimNE) : vm_refinement_ne_Statement := by
  intro p c hS hNE hL
  obtain ⟨h1, h2⟩ := Refine.refinement H p (Vsa.Densify.fillZero c) ⟨hS, hNE, hL⟩
  refine ⟨fun out => (h1 out).trans (Vsa.Densify.halts_fillZero c out 0).symm, fun hd => h2 ?_⟩
  exact (Vsa.Densify.diverges_fillZero c).1 hd

/-- **Layer A without escapes from the open premises**: the open arms, the
return chain and the error sites. -/
theorem vm_refinement_ne_of_open (arms : OpenArms) (farms : FloatArms) (final : FinalSim)
    (err : ErrorSim) : vm_refinement_ne_Statement :=
  vm_refinement_ne_of_sim
    (vmSimNE_of_arms (armTable arms farms) entrySim Kit.varargSim final (stuckSimNE_of_error err))

/-- **Layer A without escapes, `FinalSim` discharged** (`finalSim`, lane F1-4). -/
theorem vm_refinement_ne_of_open' (arms : OpenArms) (farms : FloatArms) (err : ErrorSim) :
    vm_refinement_ne_Statement :=
  vm_refinement_ne_of_open arms farms finalSim err

/-- **`NoEscape` is derived**: Layer A without escapes is Layer A. -/
theorem vm_refinement_of_ne (h : vm_refinement_ne_Statement) : vm_refinement_Statement luaLayout :=
  fun p c hS hL => h p c hS (noEscape_of_supported hS) hL

end Lua.Vm.Sim

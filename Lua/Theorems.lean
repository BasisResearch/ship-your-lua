import Lua.Refinement
import Lua.Fragment
import Lua.Vm.Loaded
import Lua.Vm.Host
import Lua.Ast.Semantics
import Vsa.Densify

/-!
# The theorem statements: Layer A, Layer B, and their composition

None of the three headline theorems is proved yet. Each is stated as a
`def …_Statement : Prop` (never a `sorry`, never an axiom), with the
obligation that would prove it packaged as a structure. What *is* proved
here is everything around them:

* `vm_refinement_of_sim` — Layer A follows from the forward simulation
  `VmSim` (the refinement pattern plus `fillZero` densification);
* `endToEnd_of_layers` — the composed theorem follows from the two layers;
* `compile_refinement_of_tv` — Layer B for a compiler relation follows from
  per-program translation validation plus determinism.

PHASES.md lists the owners and exit criteria of each obligation.

```
LuaSem s out  ↔  BcSem (compile s) out  ↔  Halts c out 0
   (Layer B: compile_refinement)   (Layer A: vm_refinement)
```
-/

namespace Lua

open Vsa.Machine Vsa.Densify Lua.Bytecode Lua.Vm Lua.Ast

/-! ## Layer A: the `luaV_execute` binary refines `BcSem` -/

/-- A program is loaded at the VM cut point: F1-supported, and the
configuration is at `luaV_execute`'s entry with its `Proto` in memory. -/
def VmLoadedSupported (Lay : VmLayout) (p : Proto) (c : Config) : Prop :=
  Supported p ∧ VmLoaded Lay p c

/-- **Layer A obligation** (forward simulation, ∀ programs): what
`InterpSim` is for ship-your-interpreter. Discharged opcode by opcode by
simulation lemmas about the compiled `luaV_execute` arms (and their callees)
against `Step`, by induction on `Steps`. -/
abbrev VmSim (Lay : VmLayout) : Prop :=
  Refine.Sim (fun p out => BcSem binaryHost p out) (VmLoadedSupported Lay)

/-- **Layer A** (`vm_refinement`): for every F1-supported `Proto` `p` and
every configuration whose zero-fill is at `luaV_execute`'s entry running
`p`: the clean halts are exactly `BcSem`'s outputs, and divergence means no
output. -/
def vm_refinement_Statement (Lay : VmLayout) : Prop :=
  ∀ p c, Supported p → VmLoaded Lay p (fillZero c) →
    (∀ out, BcSem binaryHost p out ↔ Halts c out 0) ∧
    (Diverges c → ¬ ∃ out, BcSem binaryHost p out)

/-- Layer A from its obligation (proved). -/
theorem vm_refinement_of_sim {Lay : VmLayout} (H : VmSim Lay) : vm_refinement_Statement Lay := by
  intro p c hs hL
  obtain ⟨h1, h2⟩ := Refine.refinement H p (fillZero c) ⟨hs, hL⟩
  refine ⟨fun out => (h1 out).trans (halts_fillZero c out 0).symm, fun hd => h2 ?_⟩
  exact (diverges_fillZero c).1 hd

/-! ## Layer B: bytecode refines the source semantics -/

/-- **Layer B** (`compile_refinement`), for a compiler relation `Compiles`
(`Compiles s p`: `p` is the main function `luac` produces for `s`). A
supported source compiles to a supported `Proto` with the same behaviours.

Instances, in order (PHASES.md): per-program translation validation of the
host `luac`'s output (`compile_refinement_of_tv`); a Lean model of
`lparser`/`lcode` with a compiler-correctness proof; the compiled
`lparser`/`lcode` in the ELF refining that model. -/
def compile_refinement_Statement (Compiles : Chunk → Proto → Prop) : Prop :=
  ∀ s p, Compiles s p → AstSupported s →
    Supported p ∧ ∀ out, LuaSem binaryHost s out ↔ BcSem binaryHost p out

/-- Translation-validation obligations for a compiler relation: supported
output, the same output on termination in each direction. -/
structure CompileTV (Compiles : Chunk → Proto → Prop) : Prop where
  supported : ∀ s p, Compiles s p → AstSupported s → Supported p
  forward : ∀ s p out, Compiles s p → AstSupported s → LuaSem binaryHost s out →
    BcSem binaryHost p out
  backward : ∀ s p out, Compiles s p → AstSupported s → BcSem binaryHost p out →
    LuaSem binaryHost s out

/-- Layer B from its obligations (proved). -/
theorem compile_refinement_of_tv {Compiles : Chunk → Proto → Prop} (H : CompileTV Compiles) :
    compile_refinement_Statement Compiles := fun s p hc hs =>
  ⟨H.supported s p hc hs, fun out => ⟨H.forward s p out hc hs, H.backward s p out hc hs⟩⟩

/-! ## The composed theorem -/

/-- **`endToEnd_lua`**: for every supported Lua chunk `s`, its compiled
main function `p`, and every configuration at `luaV_execute`'s entry running
`p`: the machine halts cleanly printing `out` iff `s` does, and divergence
means no output. -/
def endToEnd_lua_Statement (Lay : VmLayout) (Compiles : Chunk → Proto → Prop) : Prop :=
  ∀ s p c, Compiles s p → AstSupported s → VmLoaded Lay p (fillZero c) →
    (∀ out, LuaSem binaryHost s out ↔ Halts c out 0) ∧
    (Diverges c → ¬ ∃ out, LuaSem binaryHost s out)

/-- **Composition** (proved): Layer A and Layer B give the end-to-end
theorem. -/
theorem endToEnd_of_layers {Lay : VmLayout} {Compiles : Chunk → Proto → Prop}
    (hA : vm_refinement_Statement Lay) (hB : compile_refinement_Statement Compiles) :
    endToEnd_lua_Statement Lay Compiles := by
  intro s p c hc hs hL
  obtain ⟨hsup, hB'⟩ := hB s p hc hs
  obtain ⟨hA1, hA2⟩ := hA p c hsup hL
  exact ⟨fun out => (hB' out).trans (hA1 out),
    fun hd ⟨out, h⟩ => hA2 hd ⟨out, (hB' out).1 h⟩⟩

/-- The end-to-end theorem from the three obligations (proved). -/
theorem endToEnd_of_obligations {Lay : VmLayout} {Compiles : Chunk → Proto → Prop}
    (hA : VmSim Lay) (hB : CompileTV Compiles) : endToEnd_lua_Statement Lay Compiles :=
  endToEnd_of_layers (vm_refinement_of_sim hA) (compile_refinement_of_tv hB)

end Lua

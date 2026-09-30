import Vsa.Triple
import Vsa.Sim.GoodState

/-!
# The RISC-V ABI callee-saved register set

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

namespace Vsa.Alloc

open Vsa.Machine Vsa.Logic Vsa.Sim
open LeanRV64DExecutable

/-! ### From `Vsa.Alloc` -/

/-- Registers a call must preserve per the RISC-V ABI: `sp`, `gp`, `tp`,
`s0–s11` — plus the machine-control registers no C function touches. The
allocator contract's frame is stated over exactly these (caller-saved
registers are forfeit across the call). -/
def AbiPreserved : Register → Bool
  | .x2 | .x3 | .x4 | .x8 | .x9 => true
  | .x18 | .x19 | .x20 | .x21 | .x22 | .x23 | .x24 | .x25 | .x26 | .x27 => true
  | _ => false

end Vsa.Alloc

namespace Vsa.Sim

open LeanRV64DExecutable
open Vsa.Alloc

/-! ### From `Vsa.Sim.InterpEntry` -/

/-- Register set preserved across `eval_expr` for the ghost frame: the RISC-V
callee-saved set (`AbiPreserved`) plus the machine-noise registers (PC/nextPC/
minstret/…). An `abbrev` so `by decide` can synthesize `Decidable` and the frame
helpers destructure it (M3 rule). -/
abbrev AbiPreservedNoise (R : Register) : Prop :=
  AbiPreserved R = true ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

end Vsa.Sim

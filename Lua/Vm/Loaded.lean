import Lua.Vm.Repr
import Lua.Vm.Image
import Vsa.Sim.GoodState
import Vsa.Sim.BlockPilot
import Vsa.Sim.Code.FixedImage

/-!
# `VmLoaded`: the machine at `luaV_execute`'s entry with a loaded `Proto`

The Layer A cut point, the analogue of ship-your-interpreter's
`Loaded interpRunLayout` at `interp_run` (`Vsa/Refinement.lean`,
`Vsa/Sim/LayoutInstance.lean`): the configuration is at `luaV_execute(L, ci)`
for the main closure of `p`, with

* the machine in its good state (`Vsa.Sim.GoodState`, whose `tohost` is the
  Lua image's, `tohostAddr_eq_symTohost`),
* `pc = luaV_execute`, `a0 = L`, `a1 = ci` (the RISC-V ABI),
* the exact `.text` and `.rodata` bytes of `c/lua-riscv-htif.elf`
  (`Lua/Vm/Image.lean`; the same bytes for every program, link.ld),
* the Lua-side data `VmEntryData` (`Lua/Vm/Repr.lean`): the `CallInfo`, the
  closure, `ProtoRepr` of `p`, `_ENV.print`, the stopped collector,
* and the rest of the runtime (`VmLayout.runtimeReady`): the C stack and
  return address into `ccall`, the dlmalloc heap in canonical shape, newlib's
  stdout `FILE`, the `lua_longjmp` chain, and every byte the run may touch
  being present. Its concrete instance is Phase A0's first deliverable
  (PHASES.md), generated like `InterpRunReadyFacts` and witnessed on real
  boot traces by the boot-witness generator.
-/

namespace Lua.Vm

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1
open Vsa.Machine (MState Config)
open Vsa.Sim (gprGet)

/-- The copied layer's `tohost` is the Lua image's: `Vsa.Sim.GoodState` pins
`htif_tohost_base` to `Vsa.Sim.tohostAddr`, which is the generated
`Layout.symTohost`, so every copied RAM-read lemma stated
against `tohostAddr` applies to the Lua ELF as is. When the ELF is
regenerated and `tohost` moves, this `rfl` fails until `Vsa.Sim.tohostAddr`
(`Vsa/Sim/InitValues.lean`, the only place the number is written) follows. -/
theorem tohostAddr_eq_symTohost : Vsa.Sim.tohostAddr = Layout.symTohost := rfl

/-- The runtime facts outside the VM's own data that `luaV_execute`'s
callees rely on (C stack, heap, stdio, error-recovery chain). Abstract here;
instantiated by `luaLayout` (`Lua/Vm/Runtime.lean`). -/
structure VmLayout where
  runtimeReady : Config → (L ci : Nat) → Prop

/-- Registers and immutable image at `luaV_execute`'s entry. -/
structure MachineAt (c : Config) (L ci : Nat) : Prop where
  good : Vsa.Sim.GoodState c.σ
  pc : c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 Layout.symLuaVExecute)
  a0 : gprGet c.σ 10 = some (BitVec.ofNat 64 L)
  a1 : gprGet c.σ 11 = some (BitVec.ofNat 64 ci)
  text : Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize Image.textByte c.σ.mem
  rodata : Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte c.σ.mem

/-- **`VmLoaded Lay p c`**: `c` is at `luaV_execute`'s entry running the
main closure of `p`. -/
def VmLoaded (Lay : VmLayout) (p : Lua.Bytecode.Proto) (c : Config) : Prop :=
  ∃ L ci e, MachineAt c L ci ∧ VmEntryData c.σ.mem L ci p e ∧ Lay.runtimeReady c L ci

end Lua.Vm

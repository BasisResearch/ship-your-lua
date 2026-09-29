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

* the machine in its good state (`LuaGoodState`: `Vsa.Sim.GoodState` with the
  Lua image's `tohost`, see below),
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
open Vsa.Sim (initMisa initMstatus initPmpcfg initPmpaddr initPmaRegions gprGet)

/-- `Vsa.Sim.GoodState` (copied field for field) with the HTIF mailbox at the
Lua image's `tohost` (`0x80048400`) instead of the WHILE image's
`Vsa.Sim.tohostAddr` (`0x8001ad00`). Retargeting the copied RAM-read
lemmas, which are stated against `tohostAddr`, is Phase A0 work. -/
-- discipline: allow(R7-conj-tower-def) the `∃ v` presence fields are Vsa.Sim.GoodState's, copied verbatim; retired in PHASES A0.1
structure LuaGoodState (σ : MState) : Prop where
  cur_privilege :
    σ.regs.get? Register.cur_privilege = some Privilege.Machine
  misa : σ.regs.get? Register.misa = some initMisa
  mstatus : σ.regs.get? Register.mstatus = some initMstatus
  mie : σ.regs.get? Register.mie = some (0#64)
  mseccfg : σ.regs.get? Register.mseccfg = some (0#64)
  satp : σ.regs.get? Register.satp = some (0#64)
  mtvec : σ.regs.get? Register.mtvec = some (0#64)
  mideleg : σ.regs.get? Register.mideleg = some (0#64)
  medeleg : σ.regs.get? Register.medeleg = some (0#64)
  hart_state : σ.regs.get? Register.hart_state = some (HartState.HART_ACTIVE ())
  htif_done : σ.regs.get? Register.htif_done = some false
  htif_tohost :
    ∃ v, σ.regs.get? Register.htif_tohost = some v
  htif_tohost_base :
    σ.regs.get? Register.htif_tohost_base =
      some (some (BitVec.ofNat 64 Layout.symTohost) : RegisterType Register.htif_tohost_base)
  elp : σ.regs.get? Register.elp = some (0#1)
  pmpcfg_n : σ.regs.get? Register.pmpcfg_n = some initPmpcfg
  pmpaddr_n : σ.regs.get? Register.pmpaddr_n = some initPmpaddr
  pma_regions : σ.regs.get? Register.pma_regions = some initPmaRegions
  menvcfg : σ.regs.get? Register.menvcfg = some (0#64)
  mcountinhibit : σ.regs.get? Register.mcountinhibit = some (0#32)
  mcyclecfg : σ.regs.get? Register.mcyclecfg = some (0#64)
  minstretcfg : σ.regs.get? Register.minstretcfg = some (0#64)
  -- present-but-unpinned: written by the machine (tick_clock, postlude)
  -- or read with an irrelevant value on the hot path.
  mip : ∃ v, σ.regs.get? Register.mip = some v
  sig_meip : ∃ v, σ.regs.get? Register.sig_meip = some v
  sig_seip : ∃ v, σ.regs.get? Register.sig_seip = some v
  mtime : ∃ v, σ.regs.get? Register.mtime = some v
  mtimecmp : ∃ v, σ.regs.get? Register.mtimecmp = some v
  minstret : ∃ v, σ.regs.get? Register.minstret = some v
  minstret_increment : ∃ v, σ.regs.get? Register.minstret_increment = some v
  mcycle : ∃ v, σ.regs.get? Register.mcycle = some v
  nextPC : ∃ v, σ.regs.get? Register.nextPC = some v

/-- The runtime facts outside the VM's own data that `luaV_execute`'s
callees rely on (C stack, heap, stdio, error-recovery chain). Abstract here;
instantiated in Phase A0. -/
structure VmLayout where
  runtimeReady : Config → (L ci : Nat) → Prop

/-- Registers and immutable image at `luaV_execute`'s entry. -/
structure MachineAt (c : Config) (L ci : Nat) : Prop where
  good : LuaGoodState c.σ
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

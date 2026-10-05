import Lua.Vm.Boot.Check

/-!
# `VmLoaded luaLayout` from the per-structure checks (PHASES A0.6)

`vmLoaded_of_checks` assembles `VmLoaded luaLayout p (fillZero ⟨σ, tick, steps⟩)`
for every machine state `σ` whose registers are the traced ones (`EntryRegs`)
and whose memory agrees with a byte view wherever the view has a byte
(`PartialView σ.mem v`), from the Bool checks of `Lua/Vm/Boot/Check.lean` at
that view. The register file is not built here: `EntryRegs` names the
control registers (`GoodState`), `pc`, the HTIF mailbox and the traced GPRs,
which is what the trace fixes. A program's witness
(`Lua/Vm/Boot/Witness/<Prog>.lean`) instantiates it with
`v = bootView chunk runs`, whose `PartialView` of the boot memory
`bootMem chunk log` is `bootMem_get` under the chunked `LogOk log runs`.
-/

namespace Lua.Vm.Boot

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Lua.Vm Lua.Vm.Layout Lua.Bytecode
open Vsa.Machine (MState Config)
open Vsa.Sim (gprGet)

/-- **The traced registers at `luaV_execute`'s entry.** -/
structure EntryRegs (σ : MState) (gprs : List (Nat × BitVec 64)) : Prop where
  /-- the control registers the Sail model consults (reset values, no traps) -/
  good : Vsa.Sim.GoodState σ
  pc : σ.regs.get? Register.PC = some (BitVec.ofNat 64 symLuaVExecute)
  /-- no `tohost` word half-written (`scripts/gen_lua_boot_witness.py` `check_regs`) -/
  htifIdle : σ.regs.get? Register.htif_payload_writes = some (0#4)
  /-- `x1 … x31` as traced -/
  gpr : ∀ r ∈ gprs, gprGet σ r.1 = some r.2

theorem _root_.Vsa.Sim.GoodState.setMem {σ : MState} (h : Vsa.Sim.GoodState σ)
    (m : Std.ExtHashMap Nat (BitVec 8)) : Vsa.Sim.GoodState { σ with mem := m } := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _⟩ := h
  constructor <;> assumption

theorem gprGet_setMem (σ : MState) (m : Std.ExtHashMap Nat (BitVec 8)) (n : Nat) :
    gprGet { σ with mem := m } n = gprGet σ n := rfl

/-- The register facts `MachineAt` and `CStackAt` need, from the traced GPRs. -/
def gprsCheck (gprs : List (Nat × BitVec 64)) (L ci : Nat) : Bool :=
  (List.range 31).all (fun i => gprs.any (·.1 == i + 1)) &&
  calleeSavedRegs.all (fun r => gprs.any (·.1 == r)) &&
  gprs.contains (10, BitVec.ofNat 64 L) && gprs.contains (11, BitVec.ofNat 64 ci) &&
  gprs.contains (2, BitVec.ofNat 64 RuntimeData.spEntry) &&
  gprs.contains (1, BitVec.ofNat 64 RuntimeData.retCcall) &&
  gprs.contains (3, BitVec.ofNat 64 symGlobalPointer)

/-- What `gprsCheck` gives. -/
structure GprFacts (σ : MState) (L ci : Nat) : Prop where
  all : ∀ n, 1 ≤ n → n ≤ 31 → (gprGet σ n).isSome
  callee_saved : ∀ r ∈ calleeSavedRegs, (gprGet σ r).isSome = true
  a0 : gprGet σ 10 = some (BitVec.ofNat 64 L)
  a1 : gprGet σ 11 = some (BitVec.ofNat 64 ci)
  sp : gprGet σ 2 = some (BitVec.ofNat 64 RuntimeData.spEntry)
  ra : gprGet σ 1 = some (BitVec.ofNat 64 RuntimeData.retCcall)
  gp : gprGet σ 3 = some (BitVec.ofNat 64 symGlobalPointer)

theorem gprsCheck_sound {σ : MState} {gprs : List (Nat × BitVec 64)} {L ci : Nat}
    (E : EntryRegs σ gprs) (hc : gprsCheck gprs L ci = true) : GprFacts σ L ci := by
  simp only [gprsCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range,
    beq_iff_eq, List.contains_iff_mem] at hc
  obtain ⟨⟨⟨⟨⟨⟨hall, hcs⟩, h10⟩, h11⟩, h2⟩, h1⟩, h3⟩ := hc
  have some_of : ∀ n, (∃ r, r ∈ gprs ∧ r.1 = n) → (gprGet σ n).isSome = true := by
    rintro n ⟨r, hr, rfl⟩
    rw [E.gpr r hr]; rfl
  exact
    { all := fun n h1 h31 => some_of n (by
        obtain ⟨r, hr, he⟩ := hall (n - 1) (by omega)
        exact ⟨r, hr, by omega⟩)
      callee_saved := fun r hr => some_of r (hcs r hr)
      a0 := E.gpr _ h10
      a1 := E.gpr _ h11
      sp := E.gpr _ h2
      ra := E.gpr _ h1
      gp := E.gpr _ h3 }

/-- **The runtime at the entry** (`RuntimeReadyAt`, the witnessed
`luaRuntimeReady`) from the traced registers, an empty console, a tick below
2, memory agreeing with the view and the passing `RtChecks`. -/
theorem runtimeReadyAt_of_checks {σ : MState} {gprs : List (Nat × BitVec 64)} {v : View}
    {L ci : Nat} {w : RtPtrs} (E : EntryRegs σ gprs) (hout : Vsa.Machine.output σ = "")
    (hv : PartialView σ.mem v) {tick : Nat} (htick : tick < 2) (steps : Nat)
    (hregs : gprsCheck gprs L ci = true) (hrt : RtChecks v L ci w) :
    RuntimeReadyAt (Vsa.Densify.fillZero ⟨σ, tick, steps⟩) L ci w := by
  have hv' : PartialView (Vsa.Densify.fillZeroMem σ.mem) v :=
    fun k b hk => Vsa.Densify.fillZeroMem_some (hv k b hk)
  have hg := gprsCheck_sound E hregs
  exact
      { harness := ⟨htick, hout⟩
        cstack :=
          { sp := hg.sp
            ra := hg.ra
            gp := hg.gp
            callee_saved := hg.callee_saved
            callers := hv'.segsAt hrt.callers
            dense := fun a h1 h2 => by
              show (Vsa.Densify.fillZeroMem σ.mem)[a]?.isSome = true
              rw [Vsa.Densify.fillZeroMem_ram _ h1 h2]; rfl }
        error_jmp := errorJmpCheck_sound hv' hrt.errorJmp
        stdio := stdioCheck_sound hv' hrt.stdio
        memfs := memfsCheck_sound hv' hrt.memfs
        heap := heapAt_of_check hv' hrt.heap
        lua := luaStateCheck_sound hv' hrt.lua
        top := hv'.reads hrt.top (by mem_tac)
        regions := regionsCheck_sound hv' hrt.regions
        interned := internedCheck_sound hv' hrt.interned
        kowned := kownedCheck_sound hv' hrt.kowned }

/-- **The assembly.** The traced registers, an empty console, a tick below 2,
memory agreeing with the view `bootView chunk runs`, and the passing checks at
that view give `VmLoaded luaLayout p` at the zero fill. -/
theorem vmLoaded_of_checks {σ : MState} {gprs : List (Nat × BitVec 64)} {chunk : Nat}
    {runs : RunTree} {L ci : Nat} {p : Proto} {e : EntryPtrs} {slot : PrintSlot} {w : RtPtrs}
    (E : EntryRegs σ gprs) (hout : Vsa.Machine.output σ = "")
    (hv : PartialView σ.mem (bootView chunk runs)) {tick : Nat} (htick : tick < 2) (steps : Nat)
    (hregs : gprsCheck gprs L ci = true)
    (himg : runsAvoid runs Image.textBase (Image.rodataBase + Image.rodataSize) = true)
    (hentry : entryCheck (bootView chunk runs) L ci p e slot = true)
    (hrt : RtChecks (bootView chunk runs) L ci w) :
    VmLoaded luaLayout p (Vsa.Densify.fillZero ⟨σ, tick, steps⟩) := by
  have hv' : PartialView (Vsa.Densify.fillZeroMem σ.mem) (bootView chunk runs) :=
    fun k b hk => Vsa.Densify.fillZeroMem_some (hv k b hk)
  have hg := gprsCheck_sound E hregs
  refine ⟨L, ci, e, ?_, entryCheck_sound hv' hentry, show luaRuntimeReady _ L ci from
    ⟨w, runtimeReadyAt_of_checks E hout hv htick steps hregs hrt⟩⟩
  exact
    { good := E.good.setMem _
      pc := E.pc
      a0 := hg.a0
      a1 := hg.a1
      regs := ⟨hg.all, E.htifIdle⟩
      text := text_of_view hv' himg
      rodata := rodata_of_view hv' himg }

/-- The boot memory itself: `bootMem chunk log` reads as `bootView chunk runs`
everywhere under `LogOk log runs` (`bootMem_get`). -/
theorem vmLoaded_of_boot {σ : MState} {gprs : List (Nat × BitVec 64)} {chunk : Nat}
    {log : PackedLog} {runs : RunTree} {L ci : Nat} {p : Proto} {e : EntryPtrs} {slot : PrintSlot}
    {w : RtPtrs} (hlog : LogOk log runs) (E : EntryRegs σ gprs) (hmem : σ.mem = bootMem chunk log)
    (hout : Vsa.Machine.output σ = "") {tick : Nat} (htick : tick < 2) (steps : Nat)
    (hregs : gprsCheck gprs L ci = true)
    (himg : runsAvoid runs Image.textBase (Image.rodataBase + Image.rodataSize) = true)
    (hentry : entryCheck (bootView chunk runs) L ci p e slot = true)
    (hrt : RtChecks (bootView chunk runs) L ci w) :
    VmLoaded luaLayout p (Vsa.Densify.fillZero ⟨σ, tick, steps⟩) :=
  vmLoaded_of_checks E hout (hmem ▸ (bootMem_get hlog).partial) htick steps hregs himg hentry hrt

end Lua.Vm.Boot

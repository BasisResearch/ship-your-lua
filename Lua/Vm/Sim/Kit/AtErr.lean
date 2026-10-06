import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.DivLib
import Lua.Vm.At.Idiv
import Lua.Vm.At.Idivk
import Lua.Vm.At.Mod
import Lua.Vm.At.Modk
import Lua.Vm.At.Forprep
import Lua.Vm.LayoutErr

/-!
# Error paths on the location-list route: an arm's run into an error exit

At a stuck state whose fault is a Lua error (`Lua/StuckCases.lean`) the arm
does not reach the fetch head: it calls an error exit (`luaG_runerror`, …,
`l_noret`). `gen_lua_at.py` walks those paths too (a path ends at the entry
of an `ERRS` function), so an error path is `at_err NS`: the arm's entry as a
row, `at_run NS` (which stops at an error entry, `errEntryPcs`), and the pc of
the final row. The kernel is not run (there is no step): the path's facts
are the machine's (`Q`), and `kit_setup_err` is `kit_setup` without the
kernel's forward evaluation.

Proved here: the `n // 0` and `n % 0` paths of `OP_IDIV`, `OP_IDIVK`, `OP_MOD`,
`OP_MODK`, and `'for' step is zero` of `OP_FORPREP`, each into
`luaG_runerror` (`symLuaGRunerror`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps StepsN)

/-- The error entries of `at_run` are the ELF's (`Lua/Vm/LayoutErr.lean`). -/
theorem errEntryPcs_eq : errEntryPcs = [symLuaGRunerror, symLuaGForerror, symLuaGOpinterror,
    symLuaGTointerror, symLuaGTypeerror, symLuaGOrdererror, symLuaGConcaterror,
    symLuaGCallerror] := rfl

/-- The machine is at the entry of the function at `f`. -/
def ErrAt (f : Nat) (c : Config) : Prop := c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 f)

/-- **An arm's run into an error exit** under a case condition `Q`: from the
arm's entry (`ArmAt`, after dispatch) the machine reaches the entry of `f`. -/
def ArmErr (o : OpCode) (Q : Proto → Config → State → RelPtrs → Word → Prop) (f : Nat) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s : State} {w : RelPtrs} {ins : Word},
    ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Q p c s w ins →
      ∃ c', Steps c c' ∧ ErrAt f c'

set_option hygiene false in
/-- **`kit_setup_err pc`**: `kit_setup` without the kernel (no step): the
relation's facts, the register bound `htop`, the arm's entry `h0` at `pc`. -/
macro "kit_setup_err " pc:num : tactic => `(tactic| (
  have hc := hA.core
  have hr := hc.ranges
  have htop := supported_regTop hS hf
  simp [regTop, kernel, hop, opKernel, arithRR, arithRK, opArith, forprepK, Kernel.regTop,
    Opnd.ports, Option.map] at htop
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hr.base_lo; have := hr.base_hi; have := hr.base_al; have := hr.ci_lo
  have := hr.ci_hi; have := hr.code_hi; have := hr.code_lo; have := fetch_lt hf
  have := ins.isLt; have := hr.L_lo; have := hr.ci_sep; have := hr.L_sep; have := hr.ci_top
  have := hr.L_top; have := hr.slots_top; have := hr.sp_eq; have := hr.L_al; have := hr.ci_al
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame] at *
  have h0 := hA.seg (pc := BitVec.ofNat 64 $pc) (by rw [opNum_of_op? hop]; decide)
  have acc := Steps.refl c))

set_option hygiene false in
/-- **`at_err NS`**: after `kit_setup_err`, the run by the at-lemmas of `NS`
into an error exit, and its pc. -/
macro "at_err " ns:ident : tactic => `(tactic| (
  have hX : Cx.Ok ⟨p, c, s, w, ins⟩ := ⟨hc, hf⟩
  have h0 : At ⟨p, c, s, w, ins⟩ _ (headRow ⟨p, c, s, w, ins⟩) [] c := h0
  try simp only [stackValueSize] at *
  at_run $ns h0 acc
  exact ⟨_, acc, h0.pcAt⟩))

/-- A division path by zero (`DivPath` with the divisor `0`). -/
abbrev DivZero (B : Proto → Config → State → RelPtrs → Word → Prop) (dv : RelPtrs → Word → Nat) :
    Proto → Config → State → RelPtrs → Word → Prop :=
  DivPath B dv fun _ y => y = 0#64

/-- A `K` operand's path: `K[C]` exists (the kernel's `kval`), and `Q`. -/
def WithK (Q : Proto → Config → State → RelPtrs → Word → Prop) (p : Proto) (c : Config)
    (s : State) (w : RelPtrs) (ins : Word) : Prop :=
  (kval p ins.c).isSome = true ∧ Q p c s w ins

/-- `forprep`'s integer case with a zero step: `init` and `step` integers,
`step = 0`. -/
def FpZero (_p : Proto) (c : Config) (_s : State) (w : RelPtrs) (ins : Word) : Prop :=
  slotTag c.σ.mem (w.slot ins.a) = BitVec.ofNat 8 vNumInt ∧
    slotTag c.σ.mem (w.slot (ins.a + 2)) = BitVec.ofNat 8 vNumInt ∧
    slotVal c.σ.mem (w.slot (ins.a + 2)) = 0#64

set_option hygiene false in
/-- **`div_err pc NS`**: a division arm's `n = 0` path (`R[C]`): both
operands integers (the tags `hB`, `hC`), the divisor `hz`, then `at_err`. -/
local macro "div_err " pc:num ns:ident : tactic => `(tactic| (
  rintro p hS c s w ins hA hf hop ⟨hI, hz⟩
  simp only [dvR, dvK] at hz
  kit_setup_err $pc
  kit_bound hAt ins.a; kit_bound hBt ins.b; kit_bound hCt ins.c
  have hB := hI.1; have hC := hI.2
  at_err $ns))

set_option hygiene false in
/-- **`divk_err pc NS`**: `div_err` with `K[C]`: its bounds and its slot's
facts (`kitk_const`'s, from `kval` instead of the kernel). -/
local macro "divk_err " pc:num ns:ident : tactic => `(tactic| (
  rintro p hS c s w ins hA hf hop ⟨hkv', hI, hz⟩
  simp only [dvR, dvK] at hz
  kit_setup_err $pc
  obtain ⟨y, hkv⟩ := Option.isSome_iff_exists.1 hkv'
  simp [hkv, opArith, Kernel.regTop, Opnd.ports] at htop
  have hKc := kval_lt hkv
  have hklo := hr.k_lo; have hkhi := hr.k_hi; have hkal := hr.k_al
  simp only [Word.c, Word.field, Nat.shiftRight_eq_div_pow, stackValueSize] at hKc hkhi
  kit_bound hAt ins.a; kit_bound hBt ins.b
  have hB := hI.1; have hC := hI.2
  at_err $ns))

set_option hygiene false in
/-- **`fp_err`**: `forprep`'s zero step. -/
local macro "fp_err" : tactic => `(tactic| (
  rintro p hS c s w ins hA hf hop ⟨hTi, hTs, hz⟩
  kit_setup_err 0x8001c0f8
  at_err Lua.Vm.At.FORPREP))

/-- `OP_IDIV` with `R[C] = 0`: `luaV_idiv`'s `luaG_runerror(L, "attempt to perform 'n//0'")`. -/
theorem idiv_err : ArmErr .IDIV (DivZero BothInt dvR) symLuaGRunerror := by
  div_err 0x8001deac Lua.Vm.At.IDIV

/-- `OP_MOD` with `R[C] = 0`: `luaV_mod`'s `'n%%0'`. -/
theorem mod_err : ArmErr .MOD (DivZero BothInt dvR) symLuaGRunerror := by
  div_err 0x8001dc58 Lua.Vm.At.MOD

/-- `OP_IDIVK` with `K[C] = 0`. -/
theorem idivk_err : ArmErr .IDIVK (WithK (DivZero BothIntK dvK)) symLuaGRunerror := by
  divk_err 0x8001d768 Lua.Vm.At.IDIVK

/-- `OP_MODK` with `K[C] = 0`. -/
theorem modk_err : ArmErr .MODK (WithK (DivZero BothIntK dvK)) symLuaGRunerror := by
  divk_err 0x8001dad0 Lua.Vm.At.MODK

/-- `forprep`'s integer case with a zero step: `luaG_runerror(L, "'for' step is zero")`
(before the limit is looked at). -/
theorem forprep_err : ArmErr .FORPREP FpZero symLuaGRunerror := by
  fp_err

end Lua.Vm.Sim.At

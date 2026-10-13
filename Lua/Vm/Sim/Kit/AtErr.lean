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

/-- **What an arm's error path writes** before it calls the exit:
`savestate`'s `L->top` and `ci->u.l.savedpc`, and spills into `luaV_execute`'s
C frame below its saved registers (`16(sp)` … `71(sp)`; `forprep`'s float
path spills its control values there). -/
def ErrW (w : RelPtrs) (a : Nat) : Prop :=
  (w.L + stateTopOff ≤ a ∧ a < w.L + stateTopOff + 8) ∨
    (w.ci + ciSavedpcOff ≤ a ∧ a < w.ci + ciSavedpcOff + 8) ∨ (w.sp + 16 ≤ a ∧ a < w.sp + 72)

/-- The exit's entry pins: `a0 = L`, `a1` the message's address, `luaV_execute`'s
`sp`, `gp`. -/
abbrev errPins (w : RelPtrs) (msg : Nat) : List Pin :=
  [⟨Register.x10, BitVec.ofNat 64 w.L⟩, ⟨Register.x11, BitVec.ofNat 64 msg⟩,
   ⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩]

/-- **The machine at an error exit's entry, from an arm's path**, for the
arm context `X` (whose `Core` holds at `X.c`) and a memory `M`: the call's
pins (`errPins`), `M` equal to the arm's entry memory off `ErrW`, and
`savestate`'s two words: `L->top = ci->top` and `ci->u.l.savedpc` past the
instruction. -/
structure ErrInM (X : Cx) (f msg : Nat) (M : Mem) (c : Config) : Prop where
  seg : SegSt (BitVec.ofNat 64 f) (errPins X.w msg) (ArmPay M X.c.σ.sailOutput) c
  keep : ∀ a, ¬ ErrW X.w a → bytesT1 M a = bytesT1 X.c.σ.mem a
  top : bytesT8 M (X.w.L + stateTopOff) = bytesT8 X.c.σ.mem (X.w.ci + ciTopOff)
  savedpc : bytesT8 M (X.w.ci + ciSavedpcOff) = BitVec.ofNat 64 (X.w.code + 4 * (X.s.pc + 1))

-- discipline: allow(R7-conj-tower-def) one existential over the memory; the
-- body is the named-field structure `ErrInM`
/-- **`ErrInM` for some memory.** -/
def ErrIn (X : Cx) (f msg : Nat) (c : Config) : Prop := ∃ M, ErrInM X f msg M c

theorem ErrIn.at {X : Cx} {f msg : Nat} {c : Config} (h : ErrIn X f msg c) : ErrAt f c :=
  let ⟨_, hM⟩ := h; hM.seg.pcAt

/-- **An arm's run into an error exit** under a case condition `Q`: from the
arm's entry (`ArmAt`, after dispatch) the machine reaches the entry of `f`
with the message `msg` (`ErrIn`). -/
def ArmErr (o : OpCode) (Q : Proto → Config → State → RelPtrs → Word → Prop) (f msg : Nat) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s : State} {w : RelPtrs} {ins : Word},
    ArmAt p c s w ins → p.fetch s.pc = some ins → ins.op? = some o → Q p c s w ins →
      ∃ c', Steps c c' ∧ ErrIn ⟨p, c, s, w, ins⟩ f msg c'

/-- A store of the path lies in `P`. -/
def Ent.In (X : Cx) (P : Nat → Prop) : Ent → Prop
  | .sd a _ => ∀ i, i < 8 → P (a.den X + i)
  | .sb a _ => P (a.den X)
  | .clob a n _ => ∀ i, i < n → P (a.den X + i)

/-- **A path's memory off its stores' region** is the entry memory. -/
theorem Log.den_out (X : Cx) (P : Nat → Prop) :
    ∀ (M : List Ent), (∀ e ∈ M, Ent.In X P e) → ∀ a, ¬ P a → bytesT1 (Log.den X M) a = bytesT1 X.c.σ.mem a
  | [], _, _, _ => rfl
  | e :: M, h, a, ha => by
    have ih := Log.den_out X P M (fun e he => h e (List.mem_cons_of_mem _ he)) a ha
    have he := h e List.mem_cons_self
    simp only [Log.den]
    rw [← ih]
    cases e with
    | sd b v =>
      refine ld1_wm8 ?_
      unfold Sep; refine Classical.byContradiction fun hc => ha ?_
      have := he (a - b.den X) (by omega)
      rwa [show b.den X + (a - b.den X) = a by omega] at this
    | sb b v =>
      refine ld1_ins ?_
      unfold Sep; refine Classical.byContradiction fun hc => ha ?_
      rwa [show a = b.den X by omega]
    | clob b n f =>
      refine ld1_patch ?_
      unfold Sep; refine Classical.byContradiction fun hc => ha ?_
      have := he (a - b.den X) (by omega)
      rwa [show b.den X + (a - b.den X) = a by omega] at this

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

theorem rd8_hit {m : Mem} {a x : Nat} {d : BitVec 64} (h : a = x) :
    bytesT8 (writeMap8 m a (sdData_val d)) x = d := by
  rw [ld8_wm8_same h.symm, sdData_id]

theorem rd8_out {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x := ld8_wm8 h

/-- **`err_rd8`**: a word of a path's memory read through its stores (the
hit and the misses by `omega` over the context's ranges). -/
macro "err_rd8" : tactic => `(tactic| (
  simp only [Log.den, Ent.app, Aff.den, Aff.sum, Atom.den, Loc.den, Fld.den, stateTopOff,
    ciSavedpcOff, ciTopOff, Nat.add_zero, Nat.sub_zero, Nat.one_mul, Nat.zero_add]
  repeat' first
    | with_reducible refine (rd8_out (by omega)).trans ?_
    | with_reducible refine (rd8_hit (by omega)).trans ?_
  with_reducible rfl))

set_option hygiene false in
/-- **`at_err NS`**: after `kit_setup_err`, the run by the at-lemmas of `NS`
into an error exit, and the exit's entry (`ErrIn`): the pins off the last
row, the memory off the path's log (`Log.den_out`, `err_rd8`). -/
macro "at_err " ns:ident : tactic => `(tactic| (
  have hX : Cx.Ok ⟨p, c, s, w, ins⟩ := ⟨hc, hf⟩
  have h0 : At ⟨p, c, s, w, ins⟩ _ (headRow ⟨p, c, s, w, ins⟩) [] c := h0
  try simp only [stackValueSize] at *
  at_run $ns h0 acc
  have hE : SegSt _ _ _ _ := h0
  have hLci := hr.L_sep_ci
  simp only [stateSize, ciSize] at hLci
  refine ⟨_, acc, _, Vsa.Sim.SegSt.repin hE (by pins_of hE), ?_, ?_, ?_⟩
  · refine Log.den_out _ _ _ ?_
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      intro i hi <;> simp only [Ent.In, ErrW, Aff.den, Aff.sum, Atom.den, stateTopOff,
        ciSavedpcOff] <;> omega
  · err_rd8
  · err_rd8))

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
theorem idiv_err : ArmErr .IDIV (DivZero BothInt dvR) symLuaGRunerror msgIdiv0 := by
  div_err 0x8001deac Lua.Vm.At.IDIV

/-- `OP_MOD` with `R[C] = 0`: `luaV_mod`'s `'n%%0'`. -/
theorem mod_err : ArmErr .MOD (DivZero BothInt dvR) symLuaGRunerror msgMod0 := by
  div_err 0x8001dc58 Lua.Vm.At.MOD

/-- `OP_IDIVK` with `K[C] = 0`. -/
theorem idivk_err : ArmErr .IDIVK (WithK (DivZero BothIntK dvK)) symLuaGRunerror msgIdiv0 := by
  divk_err 0x8001d768 Lua.Vm.At.IDIVK

/-- `OP_MODK` with `K[C] = 0`. -/
theorem modk_err : ArmErr .MODK (WithK (DivZero BothIntK dvK)) symLuaGRunerror msgMod0 := by
  divk_err 0x8001dad0 Lua.Vm.At.MODK

/-- `forprep`'s integer case with a zero step: `luaG_runerror(L, "'for' step is zero")`
(before the limit is looked at). -/
theorem forprep_err : ArmErr .FORPREP FpZero symLuaGRunerror msgForZero := by
  fp_err

end Lua.Vm.Sim.At

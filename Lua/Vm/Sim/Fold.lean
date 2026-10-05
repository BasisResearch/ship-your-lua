import Lua.Vm.Sim
import Lua.Vm.Sim.Kit
import Lua.Theorems

/-!
# The `VmSim` fold: Layer A from its arms (A1)

`VmSim luaLayout` (`Lua/Theorems.lean`) is `Refine.Sim`: `term_sim` (every
`BcSem` output is a clean halt) and `stuck_sim` (a program with no `BcSem`
output diverges or halts with a nonzero code). Both follow from five clauses
about `VmRel`, by induction on the bytecode run (`fold_sim`, over any
relation: `FoldSim`):

* **entry** (`EntrySim`): `luaV_execute`'s prologue reaches the fetch head in
  `VmRel … State.init`, with the entry-only facts `FreshAt` (`L->top = func + 1`
  and the stack room `luaT_adjustvarargs` checks);
* **arms**: every opcode with a kernel but `VARARGPREP` has its `SimArm`
  (`armOps`); the proved ones are the table `armTable`, the open ones the
  named premises of `OpenArms`;
* **`VARARGPREP`** (`VarargSim`): only at the entry state. `SimArm .VARARGPREP`
  is not the right obligation: `luaT_adjustvarargs` reads `L->top`, which
  `VmRel` leaves free (`Scratch`), so from a general `VmRel` state it moves
  `ci->func` by an unknown amount (or grows the stack). The kernel admits the
  opcode only at pc 0 with `A = 0`, and `supportedB` rejects every edge into
  pc 0 (`DefInit.pc_pos`), so the one reachable state at a `VARARGPREP` is the
  entry state (`reach_pc_zero`);
* **final** (`FinalSim`): at a reachable `Final` state the machine halts with
  code 0 and console `s.out` (the `RETURN*` chain; `vmRel_final_Statement`
  implies it, `finalSim_of_statement`);
* **stuck** (`StuckSim`): at a reachable state that is not final and has no
  step (an error of `δ`: `luaG_opinterror`, `luaG_forerror`, …), the machine
  diverges or halts with a nonzero code (`StuckOut`).

The machine's determinism turns `term_sim`/`stuck_sim` into the refinement
(`Refine.refinement`). `fillZero` enters only in `vm_refinement_of_sim` (the
theorem is about `c`, `VmLoaded` about `fillZero c`); `Supported` enters
through `VmLoadedSupported` and every clause's hypothesis.
-/

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout Vsa.Sim
open Vsa.Machine (Config)

/-! ## Machine runs -/

section Runs
open Vsa.Machine

/-- **The outcome `stuck_sim` asks for**: divergence, or a halt with a nonzero
code. -/
def StuckOut (c : Config) : Prop := Diverges c ∨ ∃ out e, Halts c out e ∧ e ≠ 0

/-- **A non-empty run** from `c` into `R · s'`. -/
def RunsTo (R : Config → State → Prop) (c : Config) (s' : State) : Prop :=
  ∃ c' n, 0 < n ∧ StepsN n c c' ∧ R c' s'

/-- **A run** (possibly empty) from `c` into `R · s`. -/
def Reaches (R : Config → State → Prop) (c : Config) (s : State) : Prop :=
  ∃ c', Steps c c' ∧ R c' s

/-- A counted run has every shorter prefix. -/
theorem StepsN.prefix : ∀ {m n : Nat} {a b : Config}, StepsN m a b → n ≤ m → ∃ c, StepsN n a c
  | _, 0, a, _, _, _ => ⟨a, .zero a⟩
  | _, _ + 1, _, _, .zero _, h => absurd h (by omega)
  | _, n + 1, _, _, .succ s h, hle => by
    obtain ⟨c, hc⟩ := StepsN.prefix h (n := n) (by omega)
    exact ⟨c, .succ s hc⟩

/-- Halting is closed under running backwards. -/
theorem Halts.of_steps {a b : Config} {out : String} {e : Nat} (h : Steps a b)
    (hb : Halts b out e) : Halts a out e := by
  obtain ⟨c', σf, hs, hh, ho⟩ := hb
  exact ⟨c', σf, h.trans hs, hh, ho⟩

/-- Divergence is closed under running backwards. -/
theorem Diverges.of_steps {a b : Config} (h : Steps a b) (hb : Diverges b) : Diverges a := by
  obtain ⟨k, hk⟩ := h.toN
  intro n
  by_cases hn : n ≤ k
  · exact StepsN.prefix hk hn
  · obtain ⟨c, hc⟩ := hb (n - k)
    exact ⟨c, by have := hk.trans_add hc; rwa [Nat.add_sub_cancel' (by omega)] at this⟩

theorem StuckOut.of_steps {a b : Config} (h : Steps a b) (hb : StuckOut b) : StuckOut a :=
  hb.imp (Diverges.of_steps h) fun ⟨out, e, hh, he⟩ => ⟨out, e, Halts.of_steps h hh, he⟩

end Runs

/-! ## Bytecode runs -/

section Bc
variable {H : Host} {p : Proto}

/-- A bytecode run extends by one step at its end. -/
theorem bcSteps_snoc {a b c : State} (h : Bytecode.Steps H p a b) (hs : Step H p b c) :
    Bytecode.Steps H p a c := by
  induction h with
  | refl => exact .head hs (.refl _)
  | head s _ ih => exact .head s (ih hs)

/-- A supported run that moved is past pc 0. -/
theorem bcSteps_pc_pos (hS : Supported p) {a b : State} (h : Bytecode.Steps H p a b) :
    a = b ∨ 0 < b.pc := by
  induction h with
  | refl => exact .inl rfl
  | head s _ ih =>
    rcases ih with rfl | h
    · exact .inr (hS.defInit.pc_pos s)
    · exact .inr h

/-- **The one reachable state at pc 0 is the entry state** (`DefInit.pc_pos`). -/
theorem reach_pc_zero (hS : Supported p) {s : State} (h : Bytecode.Steps H p State.init s)
    (h0 : s.pc = 0) : s = State.init := by
  rcases bcSteps_pc_pos hS h with h | h
  · exact h.symm
  · omega

end Bc

/-! ## The generic fold -/

/-- `s` is reachable from the entry state. -/
def Reach (p : Proto) (s : State) : Prop := Bytecode.Steps binaryHost p State.init s

/-- `s` has no step. -/
def Stuck (p : Proto) (s : State) : Prop := ∀ s', ¬ Step binaryHost p s s'

/-- **The clauses of a simulation of `p`'s bytecode by the machine**, for a
relation `R` between configurations and bytecode states, at reachable
states. -/
structure FoldSim (p : Proto) (R : Config → State → Prop) : Prop where
  step : ∀ c s s', Reach p s → R c s → Step binaryHost p s s' → RunsTo R c s'
  final : ∀ c s, Reach p s → R c s → Final p s → Vsa.Machine.Halts c s.out 0
  stuck : ∀ c s, Reach p s → R c s → ¬ Final p s → Stuck p s → StuckOut c

section Fold
variable {p : Proto} {R : Config → State → Prop}

/-- Every reachable state is simulated. -/
theorem FoldSim.reach (hF : FoldSim p R) {c : Config} (hc : R c State.init) {s : State}
    (hs : Reach p s) : Reaches R c s := by
  suffices ∀ a, Bytecode.Steps binaryHost p a s → Reach p a → ∀ c, R c a → Reaches R c s from
    this _ hs (.refl _) c hc
  clear hs hc
  intro a h
  induction h with
  | refl => exact fun _ c hc => ⟨c, .refl _, hc⟩
  | head st _ ih =>
    intro ha c hc
    obtain ⟨c₁, n, -, hn, h₁⟩ := hF.step _ _ _ ha hc st
    obtain ⟨c', hs', h'⟩ := ih (bcSteps_snoc ha st) c₁ h₁
    exact ⟨c', hn.toSteps.trans hs', h'⟩

/-- If no reachable state is stuck, every related reachable state diverges. -/
theorem FoldSim.diverges (hF : FoldSim p R) (hall : ∀ s, Reach p s → ¬ Stuck p s)
    {c : Config} {s : State} (hs : Reach p s) (hc : R c s) : Vsa.Machine.Diverges c := by
  intro n
  induction n using Nat.strongRecOn generalizing c s with
  | ind n ih =>
    obtain ⟨s', st⟩ := Classical.not_forall_not.1 (hall s hs)
    obtain ⟨c₁, m, hm, h₁, hR⟩ := hF.step _ _ _ hs hc st
    by_cases hnm : n ≤ m
    · exact StepsN.prefix h₁ hnm
    · obtain ⟨c', hc'⟩ := ih (n - m) (by omega) (bcSteps_snoc hs st) hR
      exact ⟨c', by have := h₁.trans_add hc'; rwa [Nat.add_sub_cancel' (by omega)] at this⟩

/-- **`term_sim` from the clauses.** -/
theorem FoldSim.term (hF : FoldSim p R) {c : Config} (h₀ : Reaches R c State.init)
    {out : String} (hb : BcSem binaryHost p out) : Vsa.Machine.Halts c out 0 := by
  obtain ⟨c₀, h₀, hc⟩ := h₀
  obtain ⟨s, hs, hf, rfl⟩ := hb
  obtain ⟨c', hc', hR⟩ := hF.reach hc hs
  exact Halts.of_steps (h₀.trans hc') (hF.final _ _ hs hR hf)

/-- **`stuck_sim` from the clauses.** -/
theorem FoldSim.stuckOut (hF : FoldSim p R) {c : Config} (h₀ : Reaches R c State.init)
    (hno : ¬ ∃ out, BcSem binaryHost p out) : StuckOut c := by
  obtain ⟨c₀, h₀, hc⟩ := h₀
  refine StuckOut.of_steps h₀ ?_
  by_cases hstuck : ∃ s, Reach p s ∧ Stuck p s
  · obtain ⟨s, hs, hno'⟩ := hstuck
    have hnf : ¬ Final p s := fun hf => hno ⟨s.out, s, hs, hf, rfl⟩
    obtain ⟨c', hc', hR⟩ := hF.reach hc hs
    exact StuckOut.of_steps hc' (hF.stuck _ _ hs hR hnf hno')
  · exact .inl (hF.diverges (fun s hs h => hstuck ⟨s, hs, h⟩) (.refl _) hc)

end Fold

/-- **The generic fold**: a forward simulation for every program, from an
entry run into the relation and the clauses. -/
theorem fold_sim {Loaded : Proto → Config → Prop} {R : Proto → Config → State → Prop}
    (entry : ∀ p c, Loaded p c → Reaches (R p) c State.init)
    (clauses : ∀ p c, Loaded p c → FoldSim p (R p)) :
    Refine.Sim (fun p out => BcSem binaryHost p out) Loaded where
  term_sim p c _out hL hb := (clauses p c hL).term (entry p c hL) hb
  stuck_sim p c hL hno := (clauses p c hL).stuckOut (entry p c hL) hno

/-! ## The opcodes with a kernel -/

/-- **Every opcode `opKernel` gives a kernel** (the F1 rules). -/
def kernelOps : List OpCode :=
  [.MOVE, .LOADI, .LOADK, .LOADFALSE, .LFALSESKIP, .LOADTRUE, .LOADNIL, .GETTABUP,
   .ADD, .SUB, .MUL, .MOD, .IDIV, .BAND, .BOR, .BXOR, .SHL, .SHR,
   .ADDK, .SUBK, .MULK, .MODK, .IDIVK, .BANDK, .BORK, .BXORK, .ADDI, .SHRI, .SHLI,
   .MMBIN, .MMBINI, .MMBINK, .UNM, .BNOT, .NOT, .LEN, .CONCAT, .JMP,
   .EQ, .EQK, .EQI, .LT, .LE, .LTI, .LEI, .GTI, .GEI, .TEST, .TESTSET,
   .FORPREP, .FORLOOP, .CALL, .VARARGPREP]

/-- The opcodes whose arm is a `SimArm` from any `VmRel` state: all of
`kernelOps` but `VARARGPREP` (`VarargSim`). -/
def armOps : List OpCode := kernelOps.erase .VARARGPREP

theorem mem_kernelOps {p : Proto} {pc : Nat} {w : Word} {o : OpCode} {K : Kernel Value}
    (h : opKernel p pc w o = some K) : o ∈ kernelOps := by
  cases o <;> simp [kernelOps] <;> simp [opKernel] at h

theorem varargprep_pc {p : Proto} {pc : Nat} {w : Word} {K : Kernel Value}
    (h : opKernel p pc w .VARARGPREP = some K) : pc = 0 := by
  simp only [opKernel] at h
  split at h
  · rename_i hc; exact hc.1
  · cases h

/-- **The opcode of a step**: the fetched instruction decodes to an opcode
with a kernel. -/
structure StepOp (p : Proto) (s : State) (ins : Word) (o : OpCode) : Prop where
  fetch : p.fetch s.pc = some ins
  op : ins.op? = some o
  mem : o ∈ kernelOps
  /-- `VARARGPREP` has a kernel only at pc 0 -/
  vararg : o = .VARARGPREP → s.pc = 0

theorem stepOp {H : Host} {p : Proto} {s s' : State} (h : Step H p s s') :
    ∃ ins o, StepOp p s ins o := by
  obtain ⟨hK, -, -, -⟩ := h
  obtain ⟨ins, hf, hk⟩ := Option.bind_eq_some_iff.1 hK
  obtain ⟨o, ho, hK'⟩ := Option.bind_eq_some_iff.1 hk
  exact ⟨ins, o, hf, ho, mem_kernelOps hK', fun e => varargprep_pc (e ▸ hK')⟩

/-! ## The clauses at `luaLayout` -/

/-- **The entry-only facts** at the fetch head, for pointers `w`:
`luaT_adjustvarargs` (`OP_VARARGPREP` at pc 0) reads `L->top`, which `VmRel`
leaves free (`Scratch`), and compares `L->stack_last - L->top` with
`maxstacksize + 1` (`luaD_checkstack`, else `luaD_growstack`). -/
structure FreshAt (p : Proto) (c : Config) (w : RelPtrs) : Prop where
  /-- `L->top = func + 1` (`RuntimeReadyAt.top`): no arguments -/
  top : bytesT8 c.σ.mem (w.L + stateTopOff) = BitVec.ofNat 64 (w.func + stackValueSize)
  /-- `L->stack_last - L->top > maxstacksize + 1` slots: no `luaD_growstack` -/
  room : w.func + stackValueSize * (p.maxstacksize + 3) ≤ w.rt.stackLast

/-- **At the fetch head with the entry-only facts**, for some pointers. -/
def FreshRel (p : Proto) (c : Config) (s : State) : Prop :=
  ∃ w, VmRelAt p c s w ∧ FreshAt p c w

/-- **The entry clause**: the prologue reaches the fetch head in `VmRel` with
the entry state, and the entry-only facts hold. (`vmRel_entry` proves the
`VmRel` part.) -/
def EntrySim : Prop :=
  ∀ p c, Supported p → VmLoaded luaLayout p c → Reaches (FreshRel p) c State.init

/-- **The `VARARGPREP` clause**: at the entry state (the only reachable state at
a `VARARGPREP`, `reach_pc_zero`), `luaT_adjustvarargs` moves `ci->func` one
slot up and the machine is back at the fetch head with the successor
(`VmRel` at the new `func`). -/
def VarargSim : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {w : RelPtrs}, VmRelAt p c State.init w →
    FreshAt p c w → ∀ {ins : Word} {s' : State}, p.fetch 0 = some ins →
    ins.op? = some .VARARGPREP → Step binaryHost p State.init s' → RunsTo (VmRel p) c s'

/-- **The `Final` clause** at reachable states (`RETURN*`; implied by
`vmRel_final_Statement`, `finalSim_of_statement`). -/
def FinalSim : Prop :=
  ∀ p c s, Supported p → Reach p s → VmRel p c s → Final p s → Vsa.Machine.Halts c s.out 0

theorem finalSim_of_statement (h : vmRel_final_Statement) : FinalSim :=
  fun p c s hS _ hR hf => h p c s hS hR hf

/-- **The stuck clause**: at a reachable state that is not final and has no
step (`δ` undefined: `luaG_opinterror`, `luaG_forerror`, `luaG_typeerror`,
`luaG_ordererror`, the `MMBIN*` metamethod miss, a call of a non-`print`
value), the machine diverges or halts with a nonzero code (`luaD_throw` →
`longjmp` → `lua_pcallk` returns an error → `main` exits nonzero). -/
def StuckSim : Prop :=
  ∀ p c s, Supported p → Reach p s → VmRel p c s → ¬ Final p s → Stuck p s → StuckOut c

/-- The relation of the fold: `VmRel`, and at pc 0 (only the entry state) the
entry-only facts. -/
def FoldRel (p : Proto) (c : Config) (s : State) : Prop :=
  VmRel p c s ∧ (s.pc = 0 → FreshRel p c s)

theorem foldRel_of_step {p : Proto} (hS : Supported p) {c : Config} {s s' : State}
    (st : Step binaryHost p s s') (h : RunsTo (VmRel p) c s') : RunsTo (FoldRel p) c s' :=
  let ⟨c', n, hn, hN, hR⟩ := h
  ⟨c', n, hn, hN, hR, fun h0 => absurd h0 (Nat.pos_iff_ne_zero.1 (hS.defInit.pc_pos st))⟩

/-- **`VmSim` from the arms** (the fold). -/
theorem vmSim_of_arms (arms : ∀ o ∈ armOps, SimArm o) (entry : EntrySim) (vararg : VarargSim)
    (final : FinalSim) (stuck : StuckSim) : VmSim luaLayout := by
  refine fold_sim (R := FoldRel) (fun p c ⟨hS, hL⟩ => ?_) (fun p c ⟨hS, _⟩ => ?_)
  · obtain ⟨c', hc, w, hR, hF⟩ := entry p c hS hL
    exact ⟨c', hc, ⟨w, hR⟩, fun _ => ⟨w, hR, hF⟩⟩
  · refine ⟨fun c s s' hs ⟨hR, hE⟩ st => ?_, fun c s hs hR hf => final p c s hS hs hR.1 hf,
      fun c s hs hR hnf hno => stuck p c s hS hs hR.1 hnf hno⟩
    obtain ⟨ins, o, ho⟩ := stepOp st
    by_cases hv : o = .VARARGPREP
    · subst hv
      have h0 := ho.vararg rfl
      obtain rfl := reach_pc_zero hS hs h0
      obtain ⟨w, hRw, hF⟩ := hE h0
      exact foldRel_of_step hS st (vararg hS hRw hF ho.fetch ho.op st)
    · exact foldRel_of_step hS st
        (arms o ((List.mem_erase_of_ne hv).2 ho.mem) hS hR ho.fetch ho.op st)


/-! ## The arm table -/

/-- **The open arms**, one named premise per opcode of `armOps` without a
proof. `EQK` and `LE` are open only on the path their partial proofs leave
(`Kit.sim_EQK_of_long`: two long strings; `Kit.sim_LE_of_str`: two strings). -/
structure OpenArms : Prop where
  /-- `_ENV.print` (`luaV_fastget` on the `_ENV` table, `luaH_getshortstr`) -/
  GETTABUP : SimArm .GETTABUP
  /-- the shifts (`luaV_shiftl`'s shift-amount branches) -/
  SHL : SimArm .SHL
  SHR : SimArm .SHR
  SHRI : SimArm .SHRI
  SHLI : SimArm .SHLI
  /-- `luaV_idiv` with `K[C]` (`__divdi3`, as `At.sim_IDIV`) -/
  IDIVK : SimArm .IDIVK
  /-- `op_bitwiseK` (an integer `K[C]`, `bitwiseRK`) -/
  BANDK : SimArm .BANDK
  BORK : SimArm .BORK
  BXORK : SimArm .BXORK
  /-- `luaT_trybinTM`: the string coercions of `δ (.tm o)` -/
  MMBIN : SimArm .MMBIN
  MMBINI : SimArm .MMBINI
  MMBINK : SimArm .MMBINK
  /-- `luaV_arith`/`luaT_trybinTM` on a numeric string -/
  UNM : SimArm .UNM
  /-- `luaV_objlen` on a string -/
  LEN : SimArm .LEN
  /-- `luaV_concat` (string creation: `Strs.own` grows) -/
  CONCAT : SimArm .CONCAT
  /-- `print`: `luaD_precall` → `luaB_print` → … → HTIF (stack reallocation) -/
  CALL : SimArm .CALL
  /-- `OP_EQK` on two long strings (`luaS_eqlngstr` with `K[B]`) -/
  EQK_long : ArmBody .EQK fun p c s w ins => ¬ Kit.EqkShort p c s w ins
  /-- `OP_LE` on two strings (`l_strcmp`'s answer observed by `slti a0,1`) -/
  LE_str : ArmBody .LE BothStrAB

/-- **The arm table**: the proved arms and the open premises cover `armOps`. -/
theorem armTable (h : OpenArms) : ∀ o ∈ armOps, SimArm o := by
  intro o ho
  cases o
  case MOVE => exact @sim_MOVE
  case LOADI => exact @sim_LOADI
  case LOADK => exact @sim_LOADK
  case LOADFALSE => exact @sim_LOADFALSE
  case LFALSESKIP => exact @sim_LFALSESKIP
  case LOADTRUE => exact @sim_LOADTRUE
  case LOADNIL => exact Kit.sim_LOADNIL
  case GETTABUP => exact h.GETTABUP
  case ADD => exact @sim_ADD
  case SUB => exact @sim_SUB
  case MUL => exact Kit.sim_MUL
  case MOD => exact Kit.sim_MOD
  case IDIV => exact At.sim_IDIV
  case BAND => exact @sim_BAND
  case BOR => exact @sim_BOR
  case BXOR => exact @sim_BXOR
  case SHL => exact h.SHL
  case SHR => exact h.SHR
  case ADDK => exact @sim_ADDK
  case SUBK => exact @sim_SUBK
  case MULK => exact Kit.sim_MULK
  case MODK => exact At.sim_MODK
  case IDIVK => exact h.IDIVK
  case BANDK => exact h.BANDK
  case BORK => exact h.BORK
  case BXORK => exact h.BXORK
  case ADDI => exact @sim_ADDI
  case SHRI => exact h.SHRI
  case SHLI => exact h.SHLI
  case MMBIN => exact h.MMBIN
  case MMBINI => exact h.MMBINI
  case MMBINK => exact h.MMBINK
  case UNM => exact h.UNM
  case BNOT => exact @sim_BNOT
  case NOT => exact @sim_NOT
  case LEN => exact h.LEN
  case CONCAT => exact h.CONCAT
  case JMP => exact @sim_JMP
  case EQ => exact Kit.sim_EQ
  case EQK => exact Kit.sim_EQK_of_long h.EQK_long
  case EQI => exact @sim_EQI
  case LT => exact Kit.sim_LT
  case LE => exact Kit.sim_LE_of_str h.LE_str
  case LTI => exact @sim_LTI
  case LEI => exact @sim_LEI
  case GTI => exact @sim_GTI
  case GEI => exact @sim_GEI
  case TEST => exact @sim_TEST
  case TESTSET => exact @sim_TESTSET
  case FORPREP => exact At.sim_FORPREP
  case FORLOOP => exact @sim_FORLOOP
  case CALL => exact h.CALL
  all_goals simp [armOps, kernelOps] at ho

/-- **`VmSim luaLayout` from the open premises**: the proved arms are
discharged; what is left is exactly the open arms (`OpenArms`), the entry-only
facts (`EntrySim`), `VARARGPREP` (`VarargSim`), the return chain (`FinalSim`)
and the error paths (`StuckSim`). -/
theorem vmSim_of_open (arms : OpenArms) (entry : EntrySim) (vararg : VarargSim)
    (final : FinalSim) (stuck : StuckSim) : VmSim luaLayout :=
  vmSim_of_arms (armTable arms) entry vararg final stuck

/-- **Layer A from the open premises** (`vm_refinement_of_sim`). -/
theorem vm_refinement_of_open (arms : OpenArms) (entry : EntrySim) (vararg : VarargSim)
    (final : FinalSim) (stuck : StuckSim) : vm_refinement_Statement luaLayout :=
  vm_refinement_of_sim (vmSim_of_open arms entry vararg final stuck)

end Lua.Vm.Sim

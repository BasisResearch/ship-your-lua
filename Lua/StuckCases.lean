import Lua.FragmentSound

/-!
# The stuck states of supported programs (`stuck_cases`)

`StuckSim` (`Lua/Vm/Sim/Fold.lean`) is about the reachable states of a
`Supported` program that are not `Final` and have no `Step`. This file
enumerates them from the kernel table alone, with no per-opcode argument
beyond one lemma per `lvm.c` combinator:

* **reads are defined** (`reach_regs`): at a reachable state every register
  in the definite-initialisation mask holds a value. The only kernel fact
  this needs is `Kernel.Wf` (the body picks an existing edge and gives every
  def port a value), proved per combinator and read off the table
  (`opKernel_wf`);
* so a stuck state's kernel exists (`Supported`: every non-`RETURN*`
  instruction has one), its read ports are defined, and its **body fails**
  on their values;
* **the faults** (`body_fault`): a body fails only at a `δ` primitive (`n%0`
  and `n//0`, `MMBIN*`'s metamethod, `UNM`, `BNOT`, `LEN`, `CONCAT`, the
  order tests), `FORPREP`, `FORLOOP` or `CALL` (`Fault`, `Fault.ops`). `MOVE`,
  the loads, `GETTABUP`, `JMP`, `EQ*`, `TEST*`, `NOT`, `LOADNIL` and
  `VARARGPREP` never get stuck.

`stuck_cases` packages this: every reachable stuck non-final state is a
`StuckAt` with a failing `Fault`.

**Not every fault is a Lua error.** The kernel is stuck wherever F1 has no
value for the result, and in three families Lua 5.4.7 (with the default
string coercion, `LUA_NOCVTS2N` unset) continues instead (`Fault.Escape`, a
conservative superset):

* string arithmetic whose operand is a float numeral (`"1.5" + 1`,
  `lstrlib.c` `arith` → `lua_arith` gives `2.5`), and `-"1.5"`;
* a numeric `for` whose control values are numerals but not all integers
  (`for i = 1, "2"`: `forlimit` → `luaV_tointeger` coerces the string; a
  string `init`/`step` takes `forprep`'s float loop);
* `OP_FORLOOP` on a non-integer internal register (only hand-written
  bytecode: `lvm.c` reads `ivalue` without a tag test, or takes
  `floatforloop`).

`Lua/Programs/Escape.lean` gives three `Supported` programs (from `luac`)
that reach such a state, and `c/tests/stuck/` their runs on the Sail model
(exit 0). The rest (`¬ Fault.Escape`) are Lua errors, each raised from the
C function `Fault.site` names; all of them reach `luaG_errormsg` →
`luaD_throw`.
-/

namespace Lua.Bytecode

/-! ## Kernel well-formedness -/

/-- **A well-formed kernel**: whatever its body chooses is an existing edge,
and every def port of that edge gets a value. -/
def Kernel.Wf {V : Type} (K : Kernel V) : Prop :=
  ∀ vs o, K.body vs = some o → ∃ e, K.edges[o.edge]? = some e ∧ e.defs.length ≤ o.vals.length

/-- Close a `Kernel.Wf` case whose body gave `some out`. -/
local macro "wf_done" : tactic =>
  `(tactic| (simp only [Option.some.injEq] at *; subst_vars; exact ⟨_, rfl, by simp⟩))

section Wf
variable {p : Proto} {pc : Nat} {w : Word}

theorem wf_setR (a next : Nat) (os : List Opnd) (f : List Value → Option Value) :
    (setR a next os f).Wf := by
  intro vs o h
  simp only [setR, Option.map_eq_some_iff] at h
  obtain ⟨v, -, rfl⟩ := h
  exact ⟨_, rfl, by simp⟩

theorem wf_setNils (a n next : Nat) : (setNils a n next).Wf := by
  intro vs o h
  simp only [setNils, Option.some.injEq] at h
  subst h
  exact ⟨_, rfl, by simp⟩

theorem wf_jump (t : Nat) : (jump t).Wf := by
  intro vs o h
  simp only [jump, Option.some.injEq] at h
  subst h
  exact ⟨_, rfl, by simp⟩

theorem wf_opArith (a : Nat) (b : BinOp) (os : List Opnd) : (opArith pc a b os).Wf := by
  intro vs o h
  simp only [opArith] at h
  split at h
  · split at h
    · wf_done
    · wf_done
    · cases h
  · wf_done

theorem wf_mmbin {tm : Nat} {os : List Opnd} {K : Kernel Value} (h : mmbin p pc tm os = some K) :
    K.Wf := by
  unfold mmbin at h
  split at h
  · cases h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨_, -, _, -, rfl⟩ := h
    exact wf_setR _ _ _ _

theorem wf_docondjump {k : Bool} {os : List Opnd} {test : List Value → Option Value}
    {K : Kernel Value} (h : docondjump p pc k os test = some K) : K.Wf := by
  simp only [docondjump, Option.map_eq_some_iff] at h
  obtain ⟨t, -, rfl⟩ := h
  intro vs o h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c, -, rfl⟩ := h
  by_cases hc : (!c.isFalse) = k <;> simp [hc]

theorem wf_testsetK (t : Nat) : (testsetK pc w t).Wf := by
  intro vs o h
  simp only [testsetK] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    split <;> exact ⟨_, rfl, by simp⟩
  · cases h

theorem wf_forprepK : (forprepK pc w).Wf := by
  intro vs o h
  simp only [forprepK] at h
  split at h
  · split at h
    · cases h
    · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.1 h
      split
      · split <;> exact ⟨_, rfl, by simp⟩
      · exact ⟨_, rfl, by simp⟩
  · split at h
    · split at h
      · cases h
      · split at h
        · split at h <;> wf_done
        · split at h <;> wf_done
    · cases h
  · cases h

theorem wf_forloopK (t : Nat) : (forloopK pc w t).Wf := by
  intro vs o h
  simp only [forloopK] at h
  split at h
  · split at h
    · wf_done
    · split at h
      · wf_done
      · cases h
  · split at h
    · split at h <;> wf_done
    · split at h <;> wf_done
  · cases h

theorem wf_callK : (callK p pc w).Wf := by
  intro vs o h
  simp only [callK] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, by simp⟩
  · cases h

theorem wf_concatK : (concatK pc w).Wf := by
  intro vs o h
  simp only [concatK, Option.map_eq_some_iff] at h
  obtain ⟨v, -, rfl⟩ := h
  exact ⟨_, rfl, by simp⟩

/-- **Every kernel of the table is well-formed.** -/
theorem opKernel_wf {o : OpCode} {K : Kernel Value} (h : opKernel p pc w o = some K) : K.Wf := by
  cases o
  case MOVE | LOADI | LOADF | LOADFALSE | LFALSESKIP | LOADTRUE | UNM | BNOT | NOT | LEN =>
    simp only [opKernel, move, Option.some.injEq] at h; subst h; exact wf_setR _ _ _ _
  case LOADNIL => simp only [opKernel, Option.some.injEq] at h; subst h; exact wf_setNils _ _ _
  case ADDI | SHRI | SHLI | ADD | SUB | MUL | MOD | IDIV | BAND | BOR | BXOR | SHL | SHR | DIV | POW =>
    simp only [opKernel, arithRR, Option.some.injEq] at h; subst h; exact wf_opArith _ _ _
  case LOADK =>
    simp only [opKernel, move, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_setR _ _ _ _
  case ADDK | SUBK | MULK | MODK | IDIVK | DIVK | POWK =>
    simp only [opKernel, arithRK, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_opArith _ _ _
  case JMP =>
    simp only [opKernel, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_jump _
  case TESTSET =>
    simp only [opKernel, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_testsetK _
  case FORLOOP =>
    simp only [opKernel, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_forloopK _
  case BANDK | BORK | BXORK =>
    simp only [opKernel, bitwiseRK] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact wf_opArith _ _ _
    · cases h
  case MMBIN | MMBINI => exact wf_mmbin h
  case MMBINK => exact let ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h; wf_mmbin h
  case EQ | EQI | LT | LE | LTI | LEI | GTI | GEI | TEST => exact wf_docondjump h
  case EQK => exact let ⟨_, _, h⟩ := Option.bind_eq_some_iff.1 h; wf_docondjump h
  case FORPREP => simp only [opKernel, Option.some.injEq] at h; subst h; exact wf_forprepK
  case GETTABUP =>
    simp only [opKernel] at h
    split at h
    · simp only [move, Option.some.injEq] at h; subst h; exact wf_setR _ _ _ _
    · cases h
  case CONCAT =>
    simp only [opKernel] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact wf_concatK
    · cases h
  case CALL =>
    simp only [opKernel] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact wf_callK
    · cases h
  case VARARGPREP =>
    simp only [opKernel] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h; exact wf_jump _
    · cases h
  all_goals simp [opKernel] at h

end Wf

/-! ## Reachable states have their read ports defined -/

theorem writeDefs_isSome {V : Type} {j : Nat} :
    ∀ {ds : List Nat} {vs : List V} {ρ : Nat → Option V}, j ∈ ds → ds.length ≤ vs.length →
      (writeDefs ds vs ρ j).isSome
  | [], _, _, h, _ => by cases h
  | d :: ds, vs, ρ, h, hl => by
    simp only [writeDefs]
    split
    · cases vs with
      | nil => simp at hl
      | cons v vs => rfl
    · rename_i hj
      cases vs with
      | nil => simp at hl
      | cons v vs =>
        exact writeDefs_isSome ((List.mem_cons.1 h).resolve_left hj)
          (by simp only [List.length_cons, List.tail_cons] at hl ⊢; omega)

/-- The registers of the definite-initialisation mask at `s.pc` hold values. -/
def RegsDef (p : Proto) (s : State) : Prop :=
  ∀ j, (defMask p s.pc).testBit j = true → (s.regs j).isSome

theorem kernelAt_wf {p : Proto} {pc : Nat} {K : Kernel Value} (h : kernelAt p pc = some K) :
    K.Wf := by
  obtain ⟨w, -, hk⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨o, -, hK⟩ := Option.bind_eq_some_iff.1 hk
  exact opKernel_wf hK

theorem RegsDef.step {H : Host} {p : Proto} (hS : Supported p) {s s' : State}
    (hd : RegsDef p s) (h : Step H p s s') : RegsDef p s' := by
  obtain ⟨hK, hvs, ho, he⟩ := h
  rename_i K vs o e
  intro j hj
  have hs := hS.defInit.cert.stable _ _ hK e (List.mem_of_getElem? he) j hj
  by_cases hdj : j ∈ e.defs
  · obtain ⟨e', he', hl⟩ := kernelAt_wf hK vs o ho
    rw [he] at he'
    cases he'
    exact writeDefs_isSome hdj hl
  · obtain ⟨hm, hk⟩ := hs.resolve_right hdj
    rw [apply_regs_frame _ _ _ hdj]
    simp only [hk, ↓reduceIte]
    exact hd j hm

/-- **At a reachable state the masked registers hold values.** -/
theorem reach_regs {H : Host} {p : Proto} (hS : Supported p) {s : State}
    (h : Steps H p State.init s) : RegsDef p s := by
  suffices ∀ a, Steps H p a s → RegsDef p a → RegsDef p s from
    this _ h fun j hj => by
      simp only [State.init, hS.defInit.entry, Nat.zero_testBit] at hj; cases hj
  clear h
  intro a h
  induction h with
  | refl => exact id
  | head st _ ih => exact fun ha => ih (ha.step hS st)

theorem mapM_some {V : Type} {f : Nat → Option V} :
    ∀ {l : List Nat}, (∀ r ∈ l, (f r).isSome) → ∃ vs, l.mapM f = some vs ∧ vs.length = l.length
  | [], _ => ⟨[], rfl, rfl⟩
  | r :: l, h => by
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (h r List.mem_cons_self)
    obtain ⟨vs, hvs, hl⟩ := mapM_some (l := l) fun r' hr' => h r' (List.mem_cons_of_mem _ hr')
    exact ⟨v :: vs, by simp [List.mapM_cons, hv, hvs], by simp [hl]⟩

/-! ## The faults -/

/-- **The operation a stuck kernel fails at.** Its operands are the values
of the kernel's read ports (`vs`), filled with the instruction's immediates
for a `δ` primitive (`Opnd.fill os vs`). -/
inductive Fault where
  /-- a `δ` primitive on the operands `os` (`setR`, `op_arith`, `MMBIN*`, the
  order tests) -/
  | prim (f : Prim) (os : List Opnd)
  /-- `luaV_concat` on the read values -/
  | concat
  /-- `forprep` on (`init`, `limit`, `step`) -/
  | forprep
  /-- `OP_FORLOOP` on (index, count, step) -/
  | forloop
  /-- `OP_CALL` of the first read value -/
  | call

/-- The fault happens on the read values `vs`: the kernel's computation fails
(read off the kernel terms, not restated). -/
def Fault.Fails : Fault → List Value → Prop
  | .prim f os, vs => δ f (Opnd.fill os vs) = none
  | .concat, vs => δ .concat vs = none
  | .forprep, vs => (forprepK 0 0).body vs = none
  | .forloop, vs => (forloopK 0 0 0).body vs = none
  | .call, vs => vs.head? ≠ some (.builtin .print)

/-- The opcodes whose kernel can fail with a fault of this family. -/
def Fault.ops : Fault → List OpCode
  | .prim (.arith _) _ => [.MOD, .IDIV, .MODK, .IDIVK]
  | .prim (.tm _) _ => [.MMBIN, .MMBINI, .MMBINK]
  | .prim .unm _ => [.UNM]
  | .prim .bnot _ => [.BNOT]
  | .prim .len _ => [.LEN]
  | .prim .lt _ => [.LT, .LTI, .GTI]
  | .prim .le _ => [.LE, .LEI, .GEI]
  | .prim _ _ => []
  | .concat => [.CONCAT]
  | .forprep => [.FORPREP]
  | .forloop => [.FORLOOP]
  | .call => [.CALL]

/-- A primitive fault's operands are the kernel's read ports. -/
def Fault.PortsOf (K : Kernel Value) : Fault → Prop
  | .prim _ os => K.reads = Opnd.ports os
  | _ => True

section Faults
variable {p : Proto} {pc : Nat} {w : Word}

theorem fill_length : ∀ {os : List Opnd} {vs : List Value}, vs.length = (Opnd.ports os).length →
    (Opnd.fill os vs).length = os.length
  | [], _, _ => rfl
  | .imm _ :: os, vs, h => by simp only [Opnd.fill, List.length_cons, fill_length (os := os) h]
  | .reg _ :: os, [], h => by simp [Opnd.ports] at h
  | .reg _ :: os, _ :: vs, h => by
    simp only [Opnd.ports, List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [Opnd.fill, List.length_cons, fill_length h]

/-- A `setR` body fails only where its function does. -/
theorem setR_none {a next : Nat} {os : List Opnd} {f : List Value → Option Value}
    {vs : List Value} (h : (setR a next os f).body vs = none) : f (Opnd.fill os vs) = none := by
  simpa [setR] using h

/-- `op_arith`'s fault: `luaV_mod`/`luaV_idiv` by zero. -/
theorem opArith_fault {a : Nat} {b : BinOp} {os : List Opnd} {vs : List Value}
    (h : (opArith pc a b os).body vs = none) :
    (Fault.prim (.arith b) os).Fails vs ∧ (b = .mod ∨ b = .idiv) := by
  simp only [opArith] at h
  split at h
  · rename_i x y hf
    split at h
    · cases h
    · cases h
    · rename_i hr
      refine ⟨by simp only [Fault.Fails, hf, δ, hr, resVal], ?_⟩
      simp only [fastArith] at hr
      split at hr
      · have := Lua.Num.rawArith_err hr
        cases b <;> simp_all [BinOp.toOp]
      · cases hr
  · cases h

/-- A conditional jump fails only at its test. -/
theorem docondjump_none {k : Bool} {os : List Opnd} {test : List Value → Option Value}
    {K : Kernel Value} (hK : docondjump p pc k os test = some K) {vs : List Value}
    (h : K.body vs = none) : test (Opnd.fill os vs) = none ∧ K.reads = Opnd.ports os := by
  simp only [docondjump, Option.map_eq_some_iff] at hK
  obtain ⟨t, -, rfl⟩ := hK
  simpa using h

theorem mmbin_none {tm : Nat} {os : List Opnd} {K : Kernel Value} (hK : mmbin p pc tm os = some K)
    {vs : List Value} (h : K.body vs = none) :
    ∃ b, δ (.tm b) (Opnd.fill os vs) = none ∧ K.reads = Opnd.ports os := by
  unfold mmbin at hK
  split at hK
  · cases hK
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at hK
    obtain ⟨_, -, b, -, rfl⟩ := hK
    exact ⟨b, setR_none h, rfl⟩

/-- A one-operand `setR` whose function is `List.head?` does not fail. -/
theorem head_fill {x : Opnd} {vs : List Value} (hl : vs.length = (Opnd.ports [x]).length) :
    (List.head? (Opnd.fill [x] vs)).isSome := by
  match h : Opnd.fill [x] vs, fill_length hl with
  | [v], _ => simp

/-- `δ .eq` does not fail on two operands. -/
theorem eq_fill {x y : Opnd} {vs : List Value} (hl : vs.length = (Opnd.ports [x, y]).length) :
    (δ .eq (Opnd.fill [x, y] vs)).isSome := by
  match h : Opnd.fill [x, y] vs, fill_length hl with
  | [a, b], _ => simp [δ]

/-- **The faults of the table**: a kernel's body fails on read values only at
one of `Fault`'s operations, of an opcode `Fault.ops` lists. -/
theorem body_fault {o : OpCode} {K : Kernel Value} {vs : List Value}
    (hK : opKernel p pc w o = some K) (hl : vs.length = K.reads.length)
    (hb : K.body vs = none) : ∃ φ : Fault, φ.Fails vs ∧ o ∈ φ.ops ∧ φ.PortsOf K := by
  cases o
  case MOVE | LOADI | LOADF | LOADFALSE | LFALSESKIP | LOADTRUE =>
    simp only [opKernel, move, Option.some.injEq] at hK; subst hK
    have := head_fill (by simpa [setR] using hl)
    rw [setR_none hb] at this; cases this
  case UNM =>
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    exact ⟨.prim .unm _, setR_none hb, by simp [Fault.ops], rfl⟩
  case BNOT =>
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    exact ⟨.prim .bnot _, setR_none hb, by simp [Fault.ops], rfl⟩
  case LEN =>
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    exact ⟨.prim .len _, setR_none hb, by simp [Fault.ops], rfl⟩
  case NOT =>
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    have := setR_none hb
    match h : Opnd.fill [.reg w.b] vs, fill_length (os := [.reg w.b]) (by simpa [setR] using hl) with
    | [v], _ => rw [h] at this; simp [δ] at this
  case LOADNIL => simp only [opKernel, Option.some.injEq] at hK; subst hK; simp [setNils] at hb
  case ADDI | SHRI | SHLI | ADD | SUB | MUL | MOD | IDIV | BAND | BOR | BXOR | SHL | SHR | DIV | POW =>
    simp only [opKernel, arithRR, Option.some.injEq] at hK; subst hK
    obtain ⟨hF, hb'⟩ := opArith_fault hb
    first
      | (simp at hb'; done)
      | exact ⟨_, hF, by simp [Fault.ops], rfl⟩
  case ADDK | SUBK | MULK | MODK | IDIVK | DIVK | POWK =>
    simp only [opKernel, arithRK, Option.map_eq_some_iff] at hK
    obtain ⟨_, -, rfl⟩ := hK
    obtain ⟨hF, hb'⟩ := opArith_fault hb
    first
      | (simp at hb'; done)
      | exact ⟨_, hF, by simp [Fault.ops], rfl⟩
  case BANDK | BORK | BXORK =>
    simp only [opKernel, bitwiseRK] at hK
    split at hK
    · simp only [Option.some.injEq] at hK; subst hK
      obtain ⟨-, hb'⟩ := opArith_fault hb
      simp at hb'
    · cases hK
  case LOADK =>
    simp only [opKernel, move, Option.map_eq_some_iff] at hK
    obtain ⟨_, -, rfl⟩ := hK
    simp [setR, Opnd.fill] at hb
  case JMP =>
    simp only [opKernel, Option.map_eq_some_iff] at hK
    obtain ⟨_, -, rfl⟩ := hK
    simp [jump] at hb
  case TESTSET =>
    simp only [opKernel, Option.map_eq_some_iff] at hK
    obtain ⟨_, -, rfl⟩ := hK
    match vs, (by simpa [testsetK] using hl : vs.length = 1) with
    | [v], _ => simp [testsetK] at hb
  case FORLOOP =>
    simp only [opKernel, Option.map_eq_some_iff] at hK
    obtain ⟨_, -, rfl⟩ := hK
    exact ⟨.forloop, hb, by simp [Fault.ops], trivial⟩
  case FORPREP =>
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    exact ⟨.forprep, hb, by simp [Fault.ops], trivial⟩
  case MMBIN | MMBINI =>
    obtain ⟨b, hδ, hr⟩ := mmbin_none hK hb
    exact ⟨.prim (.tm b) _, hδ, by simp [Fault.ops], hr⟩
  case MMBINK =>
    obtain ⟨_, -, hK⟩ := Option.bind_eq_some_iff.1 hK
    obtain ⟨b, hδ, hr⟩ := mmbin_none hK hb
    exact ⟨.prim (.tm b) _, hδ, by simp [Fault.ops], hr⟩
  case EQ | EQI =>
    obtain ⟨hδ, hr⟩ := docondjump_none hK hb
    have := eq_fill (hr ▸ hl)
    rw [hδ] at this; cases this
  case EQK =>
    obtain ⟨_, -, hK⟩ := Option.bind_eq_some_iff.1 hK
    obtain ⟨hδ, hr⟩ := docondjump_none hK hb
    have := eq_fill (hr ▸ hl)
    rw [hδ] at this; cases this
  case LT | LTI | GTI =>
    exact ⟨.prim .lt _, (docondjump_none hK hb).1, by simp [Fault.ops], (docondjump_none hK hb).2⟩
  case LE | LEI | GEI =>
    exact ⟨.prim .le _, (docondjump_none hK hb).1, by simp [Fault.ops], (docondjump_none hK hb).2⟩
  case TEST =>
    obtain ⟨hδ, hr⟩ := docondjump_none hK hb
    have := head_fill (hr ▸ hl)
    rw [hδ] at this; cases this
  case GETTABUP =>
    simp only [opKernel] at hK
    split at hK
    · simp only [move, Option.some.injEq] at hK; subst hK
      simp [setR, Opnd.fill] at hb
    · cases hK
  case CONCAT =>
    simp only [opKernel] at hK
    split at hK
    · simp only [Option.some.injEq] at hK; subst hK
      exact ⟨.concat, show δ .concat vs = none by simpa [concatK] using hb,
        by simp [Fault.ops], trivial⟩
    · cases hK
  case CALL =>
    simp only [opKernel] at hK
    split at hK
    · rename_i hbc
      simp only [Option.some.injEq] at hK; subst hK
      have hl' : vs.length = w.b := by simpa [callK] using hl
      match vs, hl' with
      | f :: args, _ =>
        refine ⟨.call, fun hf => ?_, by simp [Fault.ops], trivial⟩
        simp only [List.head?_cons, Option.some.injEq] at hf
        subst hf
        simp [callK] at hb
      | [], h => exact absurd h.symm hbc.1
    · cases hK
  case VARARGPREP =>
    simp only [opKernel] at hK
    split at hK
    · simp only [Option.some.injEq] at hK; subst hK
      simp [jump] at hb
    · cases hK
  all_goals simp [opKernel] at hK

end Faults

/-! ## The enumeration -/

/-- **A stuck state of a supported program**: the instruction `w` with opcode
`o`, its kernel `K`, the read values `vs`, on which the body fails at the
fault `φ`. -/
structure StuckAt (p : Proto) (s : State) (w : Word) (o : OpCode) (K : Kernel Value)
    (vs : List Value) (φ : Fault) : Prop where
  fetch : p.fetch s.pc = some w
  op : w.op? = some o
  kernel : opKernel p s.pc w o = some K
  /-- every read port holds a value (`reach_regs`) -/
  reads : K.reads.mapM s.regs = some vs
  body : K.body vs = none
  fails : φ.Fails vs
  /-- `o` is one of the opcodes that can fail at `φ` -/
  mem : o ∈ φ.ops
  /-- a primitive's operands are the read ports -/
  ports : φ.PortsOf K

theorem steps_pc_lt {H : Host} {p : Proto} (hS : Supported p) {a b : State}
    (h : Steps H p a b) (ha : a.pc < p.code.length) : b.pc < p.code.length := by
  induction h with
  | refl => exact ha
  | head st _ ih => exact ih (hS.defInit.pc_lt st)

/-- An instruction without a kernel in a supported program is a `RETURN*`. -/
theorem final_of_no_kernel {p : Proto} (hS : Supported p) {s : State} {w : Word}
    (hw : p.fetch s.pc = some w) (hk : kernel p s.pc w = none) : Final p s := by
  have he := hS.defInit.total _ w hw
  unfold edges at he
  simp only [hw, hk] at he
  split at he
  · rename_i hn
    unfold noSucc at hn
    split at hn
    · rename_i o ho; exact .ret hw ho (Or.inl rfl)
    · rename_i o ho; exact .ret hw ho (Or.inr (Or.inl rfl))
    · rename_i o ho; exact .ret hw ho (Or.inr (Or.inr rfl))
    · cases hn
  · exact absurd rfl he

/-- **`stuck_cases`**: every reachable state of a supported program that is
not final and has no step is a `StuckAt`: the instruction has a kernel, its
read ports are defined, and its body fails at one of the faults. -/
theorem stuck_cases {H : Host} {p : Proto} {s : State} (hS : Supported p)
    (h : Steps H p State.init s) (hnf : ¬ Final p s) (hst : ∀ s', ¬ Step H p s s') :
    ∃ w o K vs φ, StuckAt p s w o K vs φ := by
  have hlt := steps_pc_lt hS h hS.defInit.pos
  have hw : p.fetch s.pc = some p.code[s.pc] := List.getElem?_eq_getElem hlt
  generalize p.code[s.pc] = w at hw
  cases hk : kernel p s.pc w with
  | none => exact absurd (final_of_no_kernel hS hw hk) hnf
  | some K =>
    obtain ⟨o, ho, hK⟩ := Option.bind_eq_some_iff.1 hk
    have hKa : kernelAt p s.pc = some K := by simp only [kernelAt, hw, Option.bind_some, hk]
    obtain ⟨vs, hvs, hl⟩ := mapM_some (f := s.regs) (l := K.reads) fun r hr =>
      reach_regs hS h r (hS.defInit.cert.reads _ _ hKa r hr)
    cases hb : K.body vs with
    | some out =>
      obtain ⟨e, he, -⟩ := opKernel_wf hK vs out hb
      exact absurd (KStep.run hKa hvs hb he) (hst _)
    | none =>
      obtain ⟨φ, hF, hm, hp⟩ := body_fault hK hl hb
      exact ⟨_, o, K, vs, φ, hw, ho, hK, hvs, hb, hF, hm, hp⟩

/-! ## A loop's internal registers (`loopsOk`)

`OP_FORLOOP` reads its count, limit and index with `ivalue`/`fltvalue` and
no tag test (`lvm.c:1784-1801`, `floatforloop`), so its kernel has a step
only when `R[A..A+2]` hold what `FORPREP`/`FORLOOP` store: three integers or
three floats (`LoopTriple`). `loopsOk` (`Supported`) makes that an invariant
of every reachable state inside the loop (`loop_inv`): only `FORPREP` enters
the range, and nothing strictly inside writes the three registers. -/

/-- What `FORPREP`/`FORLOOP` leave in `R[A..A+2]`: three integers (index,
count, step) or three floats (index, limit, step). -/
inductive LoopTriple : Option Value → Option Value → Option Value → Prop where
  | int (i n st : BitVec 64) : LoopTriple (some (.int i)) (some (.int n)) (some (.int st))
  | flt (i : Float.Model) (ni : Bool) (l : Float.Model) (nl : Bool) (st : Float.Model) (ns : Bool) :
      LoopTriple (some (.flt i ni)) (some (.flt l nl)) (some (.flt st ns))

theorem mapM_three {V : Type} {f : Nat → Option V} {a b c : Nat} {vs : List V}
    (h : [a, b, c].mapM f = some vs) : ∃ x y z, f a = some x ∧ f b = some y ∧ f c = some z ∧
      vs = [x, y, z] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, ⟨y, hy, _, ⟨z, hz, _, rfl, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨x, y, z, hx, hy, hz, rfl⟩

/-- The `FORLOOP` kernel steps on a loop triple. -/
theorem forloop_body_some {pc t : Nat} {w : Word} {x y z : Value}
    (h : LoopTriple (some x) (some y) (some z)) : ((forloopK pc w t).body [x, y, z]).isSome := by
  cases h with
  | int i n st => unfold forloopK; dsimp only; split <;> rfl
  | flt i ni l nl st ns => unfold forloopK; dsimp only; split <;> (split <;> rfl)

section Loop
variable {p : Proto}

/-- The kernel at a fetched instruction. -/
theorem kernelAt_of {pc : Nat} {w : Word} {o : OpCode} (hf : p.fetch pc = some w)
    (ho : w.op? = some o) : kernelAt p pc = opKernel p pc w o := by
  simp only [kernelAt, hf, Option.bind_some, kernel, ho]

/-- `writeDefs` at a def port: the value listed for its first occurrence. -/
theorem writeDefs_cons_self {V : Type} {d : Nat} {ds : List Nat} {v : V} {vs : List V}
    {ρ : Nat → Option V} : writeDefs (d :: ds) (v :: vs) ρ d = some v := by
  simp [writeDefs]

theorem writeDefs_cons_ne {V : Type} {d j : Nat} {ds : List Nat} {vs : List V}
    {ρ : Nat → Option V} (h : j ≠ d) : writeDefs (d :: ds) vs ρ j = writeDefs ds vs.tail ρ j := by
  simp [writeDefs, h]

/-- An edge with no kill ports leaves a non-def register as it was. -/
theorem apply_nokill {line : List Value → String} {s : State} {e : KEdge} {o : Out Value} {j : Nat}
    (hk : e.killN = 0) (hd : j ∉ e.defs) : (s.apply line e o).regs j = s.regs j := by
  rw [apply_regs_frame _ _ _ hd]
  have : ¬ e.kills j := by simp only [KEdge.kills, hk]; omega
  simp [this]

/-- **The loop check, unfolded** for the `FORLOOP` `w` at `f` with head `q`. -/
structure LoopFacts (p : Proto) (f : Nat) (w : Word) (q : Nat) : Prop where
  /-- the head is `FORPREP` with the same `A`, skipping to `f + 1` -/
  head : ∃ w', p.fetch q = some w' ∧ w'.op? = some .FORPREP ∧ w'.a = w.a ∧ w'.bx + 1 = w.bx
  q_eq : q + w.bx = f
  pos : 1 ≤ w.bx
  /-- inside `(q, f)`, no edge defines or kills `R[A..A+2]` -/
  inside : ∀ pc K, q < pc → pc < f → kernelAt p pc = some K → ∀ e ∈ K.edges, e.avoids w.a = true
  /-- outside `[q, f]`, no edge enters `(q, f]` -/
  outside : ∀ pc K, (pc < q ∨ f < pc) → kernelAt p pc = some K → ∀ e ∈ K.edges,
    ¬ (q < e.tgt ∧ e.tgt ≤ f)

theorem loopFacts {f : Nat} {w : Word} {q : Nat} (h : loopOk p f w = true)
    (hq : loopHead p f w = some q) : LoopFacts p f w q := by
  unfold loopHead at hq
  split at hq
  · rename_i hb
    split at hq
    · rename_i w' hw'
      split at hq
      · rename_i hc
        cases hq
        unfold loopOk at h
        rw [show loopHead p f w = some (f - w.bx) by
          unfold loopHead; simp only [hb, and_self, ↓reduceIte, hw', hc]] at h
        have hall := List.all_eq_true.1 h
        refine ⟨⟨w', hw', hc.1, hc.2.1, hc.2.2⟩, by omega, hb.1, ?_, ?_⟩
        · intro pc K h1 h2 hK e he
          obtain ⟨w'', hw'', hk⟩ := Option.bind_eq_some_iff.1 hK
          have := hall pc (List.mem_range.2 (List.getElem?_eq_some_iff.1 hw'').1)
          simp only [hw'', hk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, decide_eq_false_iff_not] at this
          exact List.all_eq_true.1 (this.1.resolve_left (by omega)) e he
        · intro pc K h1 hK e he
          obtain ⟨w'', hw'', hk⟩ := Option.bind_eq_some_iff.1 hK
          have := hall pc (List.mem_range.2 (List.getElem?_eq_some_iff.1 hw'').1)
          simp only [hw'', hk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
            Bool.not_true, decide_eq_false_iff_not] at this
          have := List.all_eq_true.1 (this.2.resolve_left (by omega)) e he
          simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at this
          exact this
      · cases hq
    · cases hq
  · cases hq

/-- A `FORPREP` step into its loop body, along the edge `e`: the integer
loop (edge 0: the count replaces the limit) or the float loop (edge 2: four
floats). -/
inductive PrepInto (pc : Nat) (w : Word) (vs : List Value) (o : Out Value) : KEdge → Prop where
  | int {i st n : BitVec 64} {l : Value} : vs = [.int i, l, .int st] → o.vals = [.int i, .int n] →
      PrepInto pc w vs o { tgt := pc + 1, defs := [w.a + 3, w.a + 1] }
  | flt {fi fl fs : Float.Model} {ni nl ns : Bool} :
      o.vals = [.flt fi ni, .flt fl nl, .flt fs ns, .flt fi ni] →
      PrepInto pc w vs o { tgt := pc + 1, defs := [w.a, w.a + 1, w.a + 2, w.a + 3] }

theorem forprep_into {pc : Nat} {w : Word} {vs : List Value} {o : Out Value} {e : KEdge}
    (hb : (forprepK pc w).body vs = some o) (he : (forprepK pc w).edges[o.edge]? = some e)
    (ht : e.tgt ≤ pc + w.bx + 1) : PrepInto pc w vs o e := by
  simp only [forprepK] at hb
  split at hb
  · split at hb
    · cases hb
    · obtain ⟨r, -, rfl⟩ := Option.map_eq_some_iff.1 hb
      split at he
      · split at he
        · simp only [forprepK, List.getElem?_cons_zero, Option.some.injEq] at he
          subst he
          exact .int rfl rfl
        · simp only [forprepK, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at he
          subst he; simp only at ht; omega
      · simp only [forprepK, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at he
        subst he; simp only at ht; omega
  · split at hb
    · split at hb
      · cases hb
      · split at hb <;> split at hb <;> simp only [Option.some.injEq] at hb <;> subst hb <;>
          simp only [forprepK, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.some.injEq] at he
        all_goals first
          | (subst he; exact .flt rfl)
          | (subst he; simp only at ht; omega)
    · cases hb
  · cases hb

/-- A `FORLOOP` step back into its loop body, along the edge `e`: the
integer loop (edge 1) or the float loop (edge 2). -/
inductive LoopInto (t : Nat) (w : Word) (vs : List Value) (o : Out Value) : KEdge → Prop where
  | int {i n st : BitVec 64} : vs = [.int i, .int n, .int st] →
      o.vals = [.int (n - 1), .int (i + st), .int (i + st)] →
      LoopInto t w vs o { tgt := t, defs := [w.a + 1, w.a, w.a + 3] }
  | flt {i l st : Float.Model} {ni nl ns : Bool} : vs = [.flt i ni, .flt l nl, .flt st ns] →
      o.vals = [.ofFloat (Float.Model.add i st), .ofFloat (Float.Model.add i st)] →
      LoopInto t w vs o { tgt := t, defs := [w.a, w.a + 3] }

theorem forloop_into {pc t : Nat} {w : Word} {vs : List Value} {o : Out Value} {e : KEdge}
    (hb : (forloopK pc w t).body vs = some o) (he : (forloopK pc w t).edges[o.edge]? = some e)
    (ht : e.tgt ≠ pc + 1) : LoopInto t w vs o e := by
  simp only [forloopK] at hb
  split at hb
  · split at hb
    · simp only [Option.some.injEq] at hb
      subst hb
      simp only [forloopK, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he; simp only at ht; omega
    · split at hb
      · simp only [Option.some.injEq] at hb
        subst hb
        simp only [forloopK, List.getElem?_cons_succ, List.getElem?_cons_zero,
          Option.some.injEq] at he
        subst he
        exact .int rfl rfl
      · cases hb
  · split at hb <;> split at hb <;> simp only [Option.some.injEq] at hb <;> subst hb <;>
      simp only [forloopK, List.getElem?_cons_succ, List.getElem?_cons_zero,
        Option.some.injEq] at he
    all_goals first
      | (subst he; exact .flt rfl rfl)
      | (subst he; simp only at ht; omega)
  · cases hb

/-- The loop invariant: at every state inside the range `(q, f]` of a
checked loop, the internal registers hold a loop triple. -/
def LoopInv (p : Proto) (s : State) : Prop :=
  ∀ f w q, p.fetch f = some w → w.op? = some .FORLOOP → loopHead p f w = some q →
    q < s.pc → s.pc ≤ f → LoopTriple (s.regs w.a) (s.regs (w.a + 1)) (s.regs (w.a + 2))

theorem loopInv_step {H : Host} (hS : Supported p) {s s' : State} (h : Step H p s s')
    (hI : LoopInv p s) : LoopInv p s' := by
  intro f w q hf ho hq h1 h2
  have hok : loopOk p f w = true := by
    have := List.all_eq_true.1 hS.2 f (List.mem_range.2 (List.getElem?_eq_some_iff.1 hf).1)
    simpa [hf, ho] using this
  have hL := loopFacts hok hq
  obtain ⟨hK, hvs, hb, he⟩ := h
  rename_i K vs o e
  have hem : e ∈ K.edges := List.mem_of_getElem? he
  -- `s'.pc = e.tgt`
  show LoopTriple ((s.apply (printLine H) e o).regs w.a) ((s.apply (printLine H) e o).regs (w.a + 1))
    ((s.apply (printLine H) e o).regs (w.a + 2))
  change q < e.tgt at h1
  change e.tgt ≤ f at h2
  rcases Nat.lt_or_ge s.pc q with hlt | hge
  · exact absurd ⟨h1, h2⟩ (hL.outside _ _ (.inl hlt) hK e hem)
  rcases Nat.lt_or_ge f s.pc with hgt | hle
  · exact absurd ⟨h1, h2⟩ (hL.outside _ _ (.inr hgt) hK e hem)
  rcases Nat.eq_or_lt_of_le hge with heq | hgt'
  · -- at the head `FORPREP`
    obtain ⟨w', hw', ho', ha, hbx⟩ := hL.head
    have hqf := hL.q_eq
    rw [← heq, kernelAt_of hw' ho'] at hK
    simp only [opKernel, Option.some.injEq] at hK
    subst hK
    rcases forprep_into hb he (by omega) with ⟨rfl, hv⟩ | ⟨hv⟩
    · rename_i i st n l
      obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := mapM_three hvs
      simp only [List.cons.injEq, and_true] at hxyz
      obtain ⟨rfl, rfl, rfl⟩ := hxyz
      rw [← ha]
      have e1 : (s.apply (printLine H) { tgt := q + 1, defs := [w'.a + 3, w'.a + 1] } o).regs w'.a = some (.int i) := by
        rw [apply_nokill rfl (by simp)]; exact hx
      have e2 : (s.apply (printLine H) { tgt := q + 1, defs := [w'.a + 3, w'.a + 1] } o).regs (w'.a + 1) = some (.int n) := by
        simp only [VState.apply, hv, writeDefs_cons_ne (show w'.a + 1 ≠ w'.a + 3 by omega)]
        simp [writeDefs]
      have e3 : (s.apply (printLine H) { tgt := q + 1, defs := [w'.a + 3, w'.a + 1] } o).regs (w'.a + 2) = some (.int st) := by
        rw [apply_nokill rfl (by simp)]; exact hz
      rw [e1, e2, e3]; exact .int _ _ _
    · rename_i fi fl fs ni nl ns
      rw [← ha]
      have e0 : ∀ j k, k < 4 → j = w'.a + k →
          (s.apply (printLine H) { tgt := q + 1, defs := [w'.a, w'.a + 1, w'.a + 2, w'.a + 3] } o).regs j =
            [Value.flt fi ni, .flt fl nl, .flt fs ns, .flt fi ni][k]? := by
        intro j k hk hj; subst hj
        simp only [VState.apply, hv]
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3) with rfl | rfl | rfl | rfl <;> simp [writeDefs]
      rw [e0 w'.a 0 (by omega) (by omega), e0 (w'.a + 1) 1 (by omega) rfl,
        e0 (w'.a + 2) 2 (by omega) rfl]
      exact .flt _ _ _ _ _ _
  rcases Nat.eq_or_lt_of_le hle with heq | hlt'
  · -- at the `FORLOOP` itself
    rw [heq, kernelAt_of hf ho] at hK
    simp only [opKernel, Option.map_eq_some_iff] at hK
    obtain ⟨t, -, rfl⟩ := hK
    rcases forloop_into hb he (by omega) with ⟨rfl, hv⟩ | ⟨rfl, hv⟩
    · rename_i i n st
      obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := mapM_three hvs
      simp only [List.cons.injEq, and_true] at hxyz
      obtain ⟨rfl, rfl, rfl⟩ := hxyz
      have e1 : (s.apply (printLine H) { tgt := t, defs := [w.a + 1, w.a, w.a + 3] } o).regs w.a = some (.int (i + st)) := by
        simp only [VState.apply, hv, writeDefs_cons_ne (show w.a ≠ w.a + 1 by omega)]
        simp [writeDefs]
      have e2 : (s.apply (printLine H) { tgt := t, defs := [w.a + 1, w.a, w.a + 3] } o).regs (w.a + 1) = some (.int (n - 1)) := by
        simp only [VState.apply, hv]; simp [writeDefs]
      have e3 : (s.apply (printLine H) { tgt := t, defs := [w.a + 1, w.a, w.a + 3] } o).regs (w.a + 2) = some (.int st) := by
        rw [apply_nokill rfl (by simp)]; exact hz
      rw [e1, e2, e3]; exact .int _ _ _
    · rename_i i l st ni nl ns
      obtain ⟨x, y, z, hx, hy, hz, hxyz⟩ := mapM_three hvs
      simp only [List.cons.injEq, and_true] at hxyz
      obtain ⟨rfl, rfl, rfl⟩ := hxyz
      have e1 : (s.apply (printLine H) { tgt := t, defs := [w.a, w.a + 3] } o).regs w.a =
          some (.ofFloat (Float.Model.add i st)) := by
        simp only [VState.apply, hv]; simp [writeDefs]
      have e2 : (s.apply (printLine H) { tgt := t, defs := [w.a, w.a + 3] } o).regs (w.a + 1) = some (.flt l nl) := by
        rw [apply_nokill rfl (by simp)]; exact hy
      have e3 : (s.apply (printLine H) { tgt := t, defs := [w.a, w.a + 3] } o).regs (w.a + 2) = some (.flt st ns) := by
        rw [apply_nokill rfl (by simp)]; exact hz
      rw [e1, e2, e3]; exact .flt _ _ _ _ _ _
  · -- strictly inside: the three registers are untouched
    have hav := hL.inside _ _ hgt' hlt' hK e hem
    simp only [KEdge.avoids, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hav
    have hkeep : ∀ j, w.a ≤ j → j < w.a + 3 → (s.apply (printLine H) e o).regs j = s.regs j := by
      intro j hj1 hj2
      have hd : j ∉ e.defs := fun hm => by have := hav.1 j hm; omega
      rw [apply_regs_frame _ _ _ hd]
      have : ¬ e.kills j := by simp only [KEdge.kills]; omega
      simp [this]
    rw [hkeep _ (by omega) (by omega), hkeep _ (by omega) (by omega), hkeep _ (by omega) (by omega)]
    exact hI f w q hf ho hq hgt' (by omega)

/-- **The loop invariant holds at every reachable state.** -/
theorem loop_inv {H : Host} (hS : Supported p) {s : State} (h : Steps H p State.init s) :
    LoopInv p s := by
  suffices ∀ a, Steps H p a s → LoopInv p a → LoopInv p s from
    this _ h fun _ _ _ _ _ _ h0 _ => absurd h0 (Nat.not_lt_zero _)
  intro a hs
  clear h
  induction hs with
  | refl => exact id
  | head st _ ih => exact fun ha => ih (loopInv_step hS st ha)

/-- **A reachable `FORLOOP` has a step**: its internal registers hold a loop
triple (`loop_inv`). -/
theorem forloop_regs {H : Host} (hS : Supported p) {s : State} (h : Steps H p State.init s)
    {w : Word} (hf : p.fetch s.pc = some w) (ho : w.op? = some .FORLOOP) :
    LoopTriple (s.regs w.a) (s.regs (w.a + 1)) (s.regs (w.a + 2)) := by
  have hok : loopOk p s.pc w = true := by
    have := List.all_eq_true.1 hS.2 s.pc (List.mem_range.2 (List.getElem?_eq_some_iff.1 hf).1)
    simpa [hf, ho] using this
  cases hq : loopHead p s.pc w with
  | none => simp [loopOk, hq] at hok
  | some q =>
    have hL := loopFacts hok hq
    exact loop_inv hS h s.pc w q hf ho hq (by have := hL.q_eq; have := hL.pos; omega) (Nat.le_refl _)

end Loop

/-! ## Lua errors and escapes -/

/-- A number (`ttisnumber`). -/
def Value.isNum : Value → Bool
  | .int _ | .flt _ _ => true
  | _ => false

def Value.isStr : Value → Bool
  | .str _ => true
  | _ => false

/-- `forprep`'s integer loop with a zero step (`'for' step is zero`, checked
before the limit). -/
def zeroStep : Value → Value → Bool
  | .int _, .int c => c == 0
  | _, _ => false

/-- **The faults where Lua 5.4.7 continues** (exact). With floats and string
coercion in `δ` (`LUA_NOCVTS2N` unset), every failing primitive, `CONCAT`,
`FORPREP` and `CALL` is a Lua error (`Fault.site`); only `OP_FORLOOP` never
raises: `lvm.c` reads the count and index with `ivalue` and no tag test, or
takes `floatforloop`, whatever the registers hold. A supported program never
reaches a stuck `FORLOOP` (`forloop_regs`), so it never escapes
(`noEscape_of_supported`). -/
def Fault.Escape : Fault → List Value → Prop
  | .forloop, _ => True
  | _, _ => False

/-- **The C function a Lua error is raised from.** Every one ends in
`luaG_errormsg` → `luaD_throw` → `longjmp` into `luaD_rawrunprotected`;
`lua_pcallk` returns `LUA_ERRRUN` and `main` returns 2 after printing the
message to stderr (`c/src/main.c`). -/
inductive ErrSite where
  /-- `luaG_runerror`: `luaV_mod`'s `'n%%0'`, `luaV_idiv`'s `'n//0'`,
  `forprep`'s `'for' step is zero` -/
  | runerror
  /-- `luaG_opinterror` (via `luaT_trybinTM`): arithmetic or bitwise on a
  non-number -/
  | opinterror
  /-- `luaG_tointerror` (via `luaT_trybinTM`): a bitwise metamethod event on
  two numbers (a float without an integer value, or `MMBIN*` reached by a
  jump) -/
  | tointerror
  /-- string arithmetic: `luaL_error` in `lstrlib.c` `trymt` (an operand that
  is not a number or numeral), or `luaV_mod`/`luaV_idiv` by zero inside the
  string metamethod (`luaG_runerror`) -/
  | strarith
  /-- `luaG_typeerror` (via `luaV_objlen`): `#` of a non-string -/
  | typeerror
  /-- `luaG_ordererror` (via `luaT_callorderTM`/`luaT_callorderiTM`) -/
  | ordererror
  /-- `luaG_concaterror` (via `luaT_tryconcatTM`) -/
  | concaterror
  /-- `luaG_forerror`: a `for` value that is not a number -/
  | forerror
  /-- `luaG_callerror` (via `luaD_tryfuncTM`): a call of a non-function -/
  | callerror
  deriving DecidableEq, Repr

/-- Where Lua raises the error of a non-escaping fault. -/
def Fault.site : Fault → List Value → ErrSite
  | .prim (.arith _) _, _ => .runerror
  | .prim (.tm b) os, vs =>
    match Opnd.fill os vs with
    | [x, y] =>
      if b.strMeta && (x.isStr || y.isStr) then .strarith
      else if !b.strMeta && x.isNum && y.isNum then .tointerror
      else .opinterror
    | _ => .opinterror
  | .prim .len _, _ => .typeerror
  | .prim .lt _, _ | .prim .le _, _ => .ordererror
  | .prim _ _, _ => .opinterror
  | .concat, _ => .concaterror
  | .forprep, vs =>
    match vs with
    | [i, _, st] => if zeroStep i st then .runerror else .forerror
    | _ => .forerror
  | .forloop, _ => .runerror
  | .call, _ => .callerror

/-- **No reachable stuck state of `p` escapes**: every one is a Lua error. -/
def NoEscape (H : Host) (p : Proto) : Prop :=
  ∀ s w o K vs φ, Steps H p State.init s → StuckAt p s w o K vs φ → ¬ φ.Escape vs

/-- **A supported program never escapes**: its only escaping fault is a
stuck `FORLOOP`, and the loop check keeps every reachable `FORLOOP`'s
registers a loop triple, on which the kernel steps. -/
theorem noEscape_of_supported {H : Host} {p : Proto} (hS : Supported p) : NoEscape H p := by
  intro s w o K vs φ hs hA hesc
  cases φ <;> simp only [Fault.Escape] at hesc
  have ho : o = .FORLOOP := by simpa [Fault.ops] using hA.mem
  subst ho
  have hK := hA.kernel
  simp only [opKernel, Option.map_eq_some_iff] at hK
  obtain ⟨t, -, rfl⟩ := hK
  have hT := forloop_regs hS hs hA.fetch hA.op
  obtain ⟨x, y, z, hx, hy, hz, rfl⟩ := mapM_three hA.reads
  rw [hx, hy, hz] at hT
  have := forloop_body_some (pc := s.pc) (w := w) (t := t) hT
  rw [hA.body] at this
  cases this

/-! ## Runs to a stuck state -/

/-- Run until a stuck state that is not final, within `fuel` steps. -/
def stuckRun (H : Host) (p : Proto) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    if final? p s then none
    else
      match step? H p s with
      | some s' => stuckRun H p n s'
      | none => some s

theorem final?_complete {p : Proto} {s : State} (h : Final p s) : final? p s = true := by
  obtain ⟨hw, ho, hor⟩ := h
  rcases hor with rfl | rfl | rfl <;> simp [final?, hw, ho]

/-- **A run from `a` to a stuck state `s`**: `s` is reached, stuck and not
final, and no run from `a` reaches a final state. -/
structure RunsStuck (H : Host) (p : Proto) (a s : State) : Prop where
  steps : Steps H p a s
  not_final : ¬ Final p s
  stuck : ∀ s', ¬ Step H p s s'
  never_final : ∀ t, Steps H p a t → ¬ Final p t

/-- **`stuckRun` is sound** (`Step` is deterministic). -/
theorem stuckRun_sound {H : Host} {p : Proto} :
    ∀ {n : Nat} {a s : State}, stuckRun H p n a = some s → RunsStuck H p a s
  | 0, _, _, h => by cases h
  | n + 1, a, s, h => by
    unfold stuckRun at h
    split at h
    · cases h
    · rename_i hf
      have hnf : ¬ Final p a := fun h' => hf (final?_complete h')
      split at h
      · rename_i a' ha'
        obtain ⟨hs, hns, hst, hall⟩ := stuckRun_sound h
        refine ⟨.head (step?_sound ha') hs, hns, hst, fun t ht => ?_⟩
        cases ht with
        | refl => exact hnf
        | head st rest =>
          rw [step?_complete st] at ha'
          cases ha'
          exact hall t rest
      · rename_i ha'
        cases h
        have hst : ∀ s', ¬ Step H p a s' := fun s' st => by
          rw [step?_complete st] at ha'; cases ha'
        refine ⟨.refl _, hnf, hst, fun t ht => ?_⟩
        cases ht with
        | refl => exact hnf
        | head st _ => exact absurd st (hst _)

/-- A program whose run gets stuck has no `BcSem` output. -/
theorem noBcSem_of_stuckRun {H : Host} {p : Proto} {n : Nat} {s : State}
    (h : stuckRun H p n State.init = some s) : ¬ ∃ out, BcSem H p out := fun ⟨_, t, ht, hf, _⟩ =>
  (stuckRun_sound h).never_final t ht hf

end Lua.Bytecode

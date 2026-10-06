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
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨v, -, rfl⟩ := h
    exact ⟨_, rfl, by simp⟩
  · simp only [Option.some.injEq] at h
    subst h
    exact ⟨_, rfl, by simp⟩

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
    · simp only [Option.some.injEq] at h
      subst h
      split <;> exact ⟨_, rfl, by simp⟩
  · cases h

theorem wf_forloopK (t : Nat) : (forloopK pc w t).Wf := by
  intro vs o h
  simp only [forloopK] at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, by simp⟩
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact ⟨_, rfl, by simp⟩
      · cases h
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
  case MOVE | LOADI | LOADFALSE | LFALSESKIP | LOADTRUE | UNM | BNOT | NOT | LEN =>
    simp only [opKernel, move, Option.some.injEq] at h; subst h; exact wf_setR _ _ _ _
  case LOADNIL => simp only [opKernel, Option.some.injEq] at h; subst h; exact wf_setNils _ _ _
  case ADDI | SHRI | SHLI | ADD | SUB | MUL | MOD | IDIV | BAND | BOR | BXOR | SHL | SHR =>
    simp only [opKernel, arithRR, Option.some.injEq] at h; subst h; exact wf_opArith _ _ _
  case LOADK =>
    simp only [opKernel, move, Option.map_eq_some_iff] at h
    obtain ⟨_, -, rfl⟩ := h; exact wf_setR _ _ _ _
  case ADDK | SUBK | MULK | MODK | IDIVK =>
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
    simp only [Option.map_eq_none_iff] at h
    refine ⟨by simp only [Fault.Fails, hf]; exact h, ?_⟩
    cases b <;> simp [δ, BinOp.int] at h ⊢
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
  case MOVE | LOADI | LOADFALSE | LFALSESKIP | LOADTRUE =>
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
  case ADDI | SHRI | SHLI | ADD | SUB | MUL | MOD | IDIV | BAND | BOR | BXOR | SHL | SHR =>
    simp only [opKernel, arithRR, Option.some.injEq] at hK; subst hK
    obtain ⟨hF, hb'⟩ := opArith_fault hb
    first
      | (simp at hb'; done)
      | exact ⟨_, hF, by simp [Fault.ops], rfl⟩
  case ADDK | SUBK | MULK | MODK | IDIVK =>
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

/-! ## Lua errors and escapes -/

/-- An integer or a string: what Lua's string-to-number coercion
(`l_strton`, `lstrlib.c` `tonum`) might accept. -/
def Value.numLike : Value → Bool
  | .int _ | .str _ => true
  | _ => false

def Value.isStr : Value → Bool
  | .str _ => true
  | _ => false

/-- `forprep`'s integer loop with a zero step (`'for' step is zero`, checked
before the limit). -/
def zeroStep : Value → Value → Bool
  | .int _, .int c => c == 0
  | _, _ => false

/-- **The faults where Lua 5.4.7 may continue** (a conservative superset;
`LUA_NOCVTS2N` is unset, so strings coerce to numbers):

* string arithmetic (`lstrlib.c` `arith`): both operands numbers or strings,
  one a string; a float numeral gives a float (`"1.5" + 1`);
* `-s` on a string (`arith_unm`; `-"1.5"` is `-1.5`);
* `forprep` on numbers and strings but not the zero-step case: a string limit
  is coerced by `forlimit` (`luaV_tointeger`), a string `init`/`step` takes
  the float loop;
* `OP_FORLOOP`: `lvm.c` reads the count and index with `ivalue` and no tag
  test, or takes `floatforloop` (never an error; unreachable from `luac`
  output, which never writes a loop's internal registers).

A non-numeral string (`"x" + 1`) is a Lua error that this predicate still
counts as an escape. -/
def Fault.Escape : Fault → List Value → Prop
  | .prim (.tm b) os, vs =>
    match Opnd.fill os vs with
    | [x, y] => b.strMeta && (x.isStr || y.isStr) && x.numLike && y.numLike
    | _ => False
  | .prim .unm os, vs =>
    match Opnd.fill os vs with
    | [x] => x.isStr
    | _ => False
  | .forprep, vs =>
    match vs with
    | [i, l, st] => i.numLike && l.numLike && st.numLike && !zeroStep i st
    | _ => False
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
  two numbers (`MMBIN*` reached by a jump, not a fall-through) -/
  | tointerror
  /-- `luaL_error` in `lstrlib.c` `trymt`: string arithmetic with an operand
  that is not a number -/
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
      else if !b.strMeta && !x.isStr && !y.isStr && x.numLike && y.numLike then .tointerror
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

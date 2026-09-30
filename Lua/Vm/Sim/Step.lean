import Lua.FragmentSound

/-!
# The bytecode side of an arm simulation, per kernel combinator (A1)

A `Step` is `KStep` over the kernel table (`Lua/Bytecode/Kernel.lean`), so
what a step does is read off the opcode's kernel term. These lemmas invert a
step once per lvm.c-macro combinator of `Lua/Bytecode/Semantics.lean`, not
per opcode:

* `step_setR`: `R[a] := f(operands)` (`MOVE`, `LOADI`, `LOADK`, `LOADFALSE`,
  `LOADTRUE`, `GETTABUP`, `UNM`, `BNOT`, `NOT`, `LEN`, …);
* `step_jump`: an unconditional jump (`JMP`, `VARARGPREP`).

`supported_regTop` is the frame bound `supportedB` checks: every register an
instruction touches is below `maxstacksize`.
-/

namespace Lua.Vm.Sim

open Lua.Bytecode

variable {H : Host} {p : Proto}

/-- A step whose kernel is `setR a next os f` writes `R[a]` and nothing else. -/
theorem step_setR {s s' : State} {a next : Nat} {os : List Opnd} {f : List Value → Option Value}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (setR a next os f)) :
    ∃ vs v, (Opnd.ports os).mapM s.regs = some vs ∧ f (Opnd.fill os vs) = some v ∧
      s' = ⟨next, fun j => if j = a then some v else s.regs j, s.out⟩ := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o e
  cases hK.symm.trans hK'
  simp only [setR, Option.map_eq_some_iff] at ho
  obtain ⟨v, hv, rfl⟩ := ho
  simp only [setR, List.getElem?_cons_zero, Option.some.injEq] at he hvs
  subst he
  refine ⟨vs, v, hvs, hv, ?_⟩
  simp only [VState.apply, writeDefs, KEdge.kills]
  congr 1

/-- A step whose kernel is `jump t` only moves the pc. -/
theorem step_jump {s s' : State} {t : Nat}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (jump t)) :
    s' = ⟨t, s.regs, s.out⟩ := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o e
  cases hK.symm.trans hK'
  simp only [jump, Option.some.injEq] at ho
  subst ho
  simp only [jump, List.getElem?_cons_zero, Option.some.injEq] at he
  subst he
  simp only [VState.apply, writeDefs, KEdge.kills]
  congr 1

theorem opcode_table : ∀ n, n < 128 → ((OpCode.ofNat? n).all fun o => n == o.toNat) = true := by
  decide +kernel

/-- The decoded opcode determines the opcode field. -/
theorem opNum_of_op? {w : Word} {o : OpCode} (h : w.op? = some o) : w.opNum = o.toNat := by
  have hlt : w.opNum < 128 := Nat.mod_lt _ (by decide)
  have := opcode_table _ hlt
  simp only [Word.op?] at h
  rw [h] at this
  simpa using this

/-- `Supported`: every instruction's registers fit the frame. -/
theorem supported_regTop (hS : Supported p) {pc : Nat} {w : Word} (hf : p.fetch pc = some w) :
    regTop p pc w ≤ p.maxstacksize := by
  unfold Supported supportedB at hS
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hS
  obtain ⟨_, h⟩ := hS
  split at h
  · cases h
  · simp only [Bool.and_eq_true] at h
    have := List.all_eq_true.1 h.1 pc (List.mem_range.2 (fetch_lt hf))
    rw [hf] at this
    exact of_decide_eq_true this

end Lua.Vm.Sim

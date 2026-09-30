import Lua.Vm.Sim.Step

/-!
# Kernel inversions of the branching combinators (A1)

The companions of `step_setR`/`step_jump` (`Lua/Vm/Sim/Step.lean`) for the
combinators whose kernel has two edges, once per `lvm.c` macro:

* `step_opArith`: `op_arith` on two operands, the integer edge (`R[a] :=
  x op y`, `pc + 2`) or the fall-through to `MMBIN` (`pc + 1`);
* `step_condjump`: `docondjump`, the skip (`pc + 2`) or the next jump;
* `step_forloop`: `OP_FORLOOP`'s integer loop, the exit or the jump back
  writing count, index and control variable.
-/

namespace Lua.Vm.Sim

open Lua.Bytecode

variable {H : Host} {p : Proto}

/-- `R[a]` updated. -/
abbrev upd (regs : Nat → Option Value) (a : Nat) (v : Value) : Nat → Option Value :=
  fun j => if j = a then some v else regs j

/-- A step whose kernel is `opArith pc a o [x, y]`: both operands integers
and the result written with `pc + 2`, or not both integers and nothing
changed but `pc + 1`. -/
theorem step_opArith {s s' : State} {a : Nat} {o : BinOp} {os : List Opnd}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (opArith s.pc a o os)) :
    ∃ vs, (Opnd.ports os).mapM s.regs = some vs ∧
      ((∃ x y v, Opnd.fill os vs = [.int x, .int y] ∧ o.int x y = some v ∧
          s' = ⟨s.pc + 2, upd s.regs a (.int v), s.out⟩) ∨
       ((∀ x y, Opnd.fill os vs ≠ [.int x, .int y]) ∧ s' = ⟨s.pc + 1, s.regs, s.out⟩)) := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o' e
  cases hK.symm.trans hK'
  refine ⟨vs, hvs, ?_⟩
  simp only [opArith] at ho he
  split at ho
  · rename_i x y hfill
    left
    simp only [δ, Option.map_map, Option.map_eq_some_iff] at ho
    obtain ⟨v, hv, rfl⟩ := ho
    simp only [Function.comp, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    refine ⟨x, y, v, hfill, hv, ?_⟩
    simp only [VState.apply, writeDefs, KEdge.kills]
    congr 1
  · rename_i hne
    right
    simp only [Option.some.injEq] at ho
    subst ho
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    refine ⟨fun x y hxy => hne x y hxy, ?_⟩
    simp only [VState.apply, writeDefs, KEdge.kills]
    congr 1

/-- A step at a `docondjump` kernel whose next jump targets `t`: the test's
value `c`; the jump is taken iff `c`'s truth is `k`. -/
theorem step_condjump {s s' : State} {k : Bool} {os : List Opnd}
    {test : List Value → Option Value} {t : Nat}
    (h : Step H p s s') (hK : kernelAt p s.pc = docondjump p s.pc k os test)
    (ht : nextJump p s.pc = some t) :
    ∃ vs c, (Opnd.ports os).mapM s.regs = some vs ∧ test (Opnd.fill os vs) = some c ∧
      s' = ⟨if (!c.isFalse) = k then t else s.pc + 2, s.regs, s.out⟩ := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K' vs o e
  rw [hK, docondjump, ht] at hK'
  simp only [Option.map_some, Option.some.injEq] at hK'
  subst hK'
  simp only [Option.map_eq_some_iff] at ho
  obtain ⟨c, hc, rfl⟩ := ho
  refine ⟨vs, c, hvs, hc, ?_⟩
  split at he <;> rename_i hck <;>
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he <;>
    subst he <;> simp only [VState.apply, writeDefs, KEdge.kills, hck, ite_true, ite_false] <;>
    congr 1

/-- The test of `EQ`/`EQK`/`EQI` on an integer. -/
theorem cond_int (x y : BitVec 64) :
    (!(Value.bool (decide (Value.int x = Value.int y))).isFalse) = decide (x = y) := by
  by_cases h : x = y <;> simp [h, Value.isFalse]

/-- The test of an ordering (`δ .lt`/`.le` gives a boolean). -/
theorem cond_bool (b : Bool) : (!(Value.bool b).isFalse) = b := by
  cases b <;> rfl

/-- ... and on anything else. -/
theorem cond_nonint {v : Value} (h : ∀ i, v ≠ .int i) (y : BitVec 64) :
    (!(Value.bool (decide (v = Value.int y))).isFalse) = false := by
  simp [h y, Value.isFalse]

/-- A backward jump `pc - k`. -/
theorem jumpTo_neg {b k t : Nat} (h : jumpTo b (-(k : Int)) = some t) : k ≤ b ∧ t = b - k := by
  unfold jumpTo at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; omega
  · cases h

/-- A forward jump `pc + off`. -/
theorem jumpTo_eq {b t : Nat} {off : Int} (h : jumpTo b off = some t) :
    0 ≤ (b : Int) + off ∧ (t : Int) = b + off := by
  unfold jumpTo at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; omega
  · cases h

theorem mapM1 {f : Nat → Option Value} {a : Nat} {vs : List Value}
    (h : [a].mapM f = some vs) : ∃ x, f a = some x ∧ vs = [x] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, rfl, rfl⟩ := h
  exact ⟨x, hx, rfl⟩

theorem mapM2 {f : Nat → Option Value} {a b : Nat} {vs : List Value}
    (h : [a, b].mapM f = some vs) : ∃ x y, f a = some x ∧ f b = some y ∧ vs = [x, y] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, ⟨y, hy, _, rfl, rfl⟩, rfl⟩ := h
  exact ⟨x, y, hx, hy, rfl⟩

theorem mapM3 {f : Nat → Option Value} {a b c : Nat} {vs : List Value}
    (h : [a, b, c].mapM f = some vs) : ∃ x y z, f a = some x ∧ f b = some y ∧ f c = some z ∧
      vs = [x, y, z] := by
  simp only [List.mapM_cons, List.mapM_nil, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨x, hx, _, ⟨y, hy, _, ⟨z, hz, _, rfl, rfl⟩, rfl⟩, rfl⟩ := h
  exact ⟨x, y, z, hx, hy, hz, rfl⟩

/-- A step whose kernel is `forloopK pc w t`: the count `n`, the step and the
index are read; count 0 exits to `pc + 1`, otherwise the index is an integer
and count−1, index+step and the control variable are written, jumping to
`t`. -/
theorem step_forloop {s s' : State} {w : Word} {t : Nat}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (forloopK s.pc w t)) :
    ∃ i n st, s.regs w.a = some i ∧ s.regs (w.a + 1) = some (.int n) ∧
      s.regs (w.a + 2) = some (.int st) ∧
      ((n = 0 ∧ s' = ⟨s.pc + 1, s.regs, s.out⟩) ∨
       (n ≠ 0 ∧ ∃ x, i = .int x ∧
         s' = ⟨t, upd (upd (upd s.regs (w.a + 3) (.int (x + st))) w.a (.int (x + st)))
           (w.a + 1) (.int (n - 1)), s.out⟩)) := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o e
  cases hK.symm.trans hK'
  obtain ⟨i, n', st', hi, hn, hst, rfl⟩ := mapM3 hvs
  simp only [forloopK] at ho he
  split at ho
  · rename_i n st heq
    simp only [List.cons.injEq] at heq
    obtain ⟨hii, rfl, rfl, -⟩ := heq
    subst hii
    refine ⟨i, n, st, hi, hn, hst, ?_⟩
    split at ho
    · rename_i hn0
      left
      simp only [Option.some.injEq] at ho
      subst ho
      simp only [List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      refine ⟨hn0, ?_⟩
      simp only [VState.apply, writeDefs, KEdge.kills]
      congr 1
    · rename_i hn0
      right
      cases i with
      | int x =>
        simp only [Option.some.injEq] at ho
        subst ho
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        refine ⟨hn0, x, rfl, ?_⟩
        simp only [VState.apply, writeDefs, KEdge.kills, List.head?, List.tail]
        congr 1
      | _ => simp at ho
  · cases ho

end Lua.Vm.Sim

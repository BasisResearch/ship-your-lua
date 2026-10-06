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

/-! ## Float operands

The arms proved before floats were in `δ` cover the states where no operand
is a float; the float paths are the named premises `FloatArms`
(`Lua/Vm/Sim/Fold.lean`). These predicates name the split. -/

/-- `v` is not a float. -/
def _root_.Lua.Bytecode.Value.NotFlt (v : Value) : Prop := ∀ x n, v ≠ .flt x n

/-- Register `r` holds a float. -/
def FltReg (s : State) (r : Nat) : Prop := ∃ x n, s.regs r = some (.flt x n)

/-- The constant `K[i]` is a float. -/
def FltK (p : Proto) (i : Nat) : Prop := ∃ x n, kval p i = some (.flt x n)

theorem notFlt_of_reg {s : State} {r : Nat} {v : Value} (h : ¬ FltReg s r)
    (hv : s.regs r = some v) : v.NotFlt := fun x n e => h ⟨x, n, e ▸ hv⟩

theorem notFlt_of_k {i : Nat} {v : Value} (h : ¬ FltK p i) (hv : kval p i = some v) :
    v.NotFlt := fun x n e => h ⟨x, n, e ▸ hv⟩

theorem notFlt_int (i : BitVec 64) : (Value.int i).NotFlt := fun _ _ e => by cases e

/-! The float paths of an arm, by its operands (`FloatArms`). -/

/-- `R[B]` or `R[C]` is a float (`op_arith`, `op_bitwise`). -/
abbrev FltBC (_p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.b ∨ FltReg s ins.c
/-- `R[B]` or `K[C]` is a float (`op_arithK`). -/
abbrev FltBK (p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.b ∨ FltK p ins.c
/-- `R[B]` is a float (`op_arithI`, `OP_SHRI`/`OP_SHLI`, `op_bitwiseK`, `OP_UNM`, `OP_BNOT`). -/
abbrev FltB (_p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.b
/-- `R[A]` is a float (`OP_EQI`, `op_orderI`). -/
abbrev FltA (_p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.a
/-- `R[A]` or `R[B]` is a float (`OP_EQ`, `op_order`). -/
abbrev FltAB (_p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.a ∨ FltReg s ins.b
/-- `R[A]` or `K[B]` is a float (`OP_EQK`). -/
abbrev FltAKb (p : Proto) (s : State) (ins : Word) : Prop := FltReg s ins.a ∨ FltK p ins.b
/-- The step `R[A+2]` is a float (`OP_FORLOOP`'s float loop, `floatforloop`). -/
abbrev FltStep (_p : Proto) (s : State) (ins : Word) : Prop := FltReg s (ins.a + 2)
/-- Not all of `init`, `limit`, `step` are integers (`forprep`'s coerced limit
or its float loop). -/
abbrev ForCoerce (_p : Proto) (s : State) (ins : Word) : Prop :=
  ¬ ((∃ i, s.regs ins.a = some (.int i)) ∧ (∃ l, s.regs (ins.a + 1) = some (.int l)) ∧
    ∃ st, s.regs (ins.a + 2) = some (.int st))

/-- Off floats, raw equality is structural. -/
theorem _root_.Lua.Bytecode.Value.rawEq_of_notFlt {x y : Value} (hx : x.NotFlt) (hy : y.NotFlt) :
    x.rawEq y = decide (x = y) := by
  cases x <;> cases y <;> first | rfl | exact absurd rfl (hx _ _) | exact absurd rfl (hy _ _)

/-- The fast path's error: two integers, the divisor zero. -/
theorem fastArith_err {o : BinOp} {x y : Value} (h : fastArith o x y = .err) :
    ∃ i, x = .int i ∧ y = .int 0 := by
  unfold fastArith at h
  split at h
  · rename_i a b ha hb
    obtain ⟨i, rfl, rfl⟩ := Lua.Num.rawArith_err_int h
    cases x <;> simp [Value.toNum?] at ha <;> cases y <;> simp [Value.toNum?] at hb
    exact ⟨i, by rw [ha], by rw [hb]; rfl⟩
  · cases h

/-- `forlimit` on an integer limit is the limit. -/
@[simp] theorem forLimit_int (l st : BitVec 64) : forLimit (.int l) st = some (some l) := rfl

/-- No operand of `os` is a float. -/
def NoFlt (s : State) (os : List Opnd) : Prop :=
  ∀ vs, (Opnd.ports os).mapM s.regs = some vs → ∀ v ∈ Opnd.fill os vs, v.NotFlt

theorem noFlt_rr {s : State} {b c : Nat} (hb : ¬ FltReg s b) (hc : ¬ FltReg s c) :
    NoFlt s [.reg b, .reg c] := fun vs hvs v hv => by
  simp only [Opnd.ports, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hvs
  obtain ⟨x, hx, _, ⟨y, hy, _, rfl, rfl⟩, rfl⟩ := hvs
  simp only [Opnd.fill, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact notFlt_of_reg hb hx
  · exact notFlt_of_reg hc hy

theorem noFlt_ri {s : State} {b : Nat} {y : Value} (hb : ¬ FltReg s b) (hy : y.NotFlt) :
    NoFlt s [.reg b, .imm y] := fun vs hvs v hv => by
  simp only [Opnd.ports, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hvs
  obtain ⟨x, hx, _, rfl, rfl⟩ := hvs
  simp only [Opnd.fill, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact notFlt_of_reg hb hx
  · exact hy

theorem noFlt_ir {s : State} {b : Nat} {y : Value} (hb : ¬ FltReg s b) (hy : y.NotFlt) :
    NoFlt s [.imm y, .reg b] := fun vs hvs v hv => by
  simp only [Opnd.ports, List.mapM_cons, List.mapM_nil, Option.bind_eq_bind,
    Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hvs
  obtain ⟨x, hx, _, rfl, rfl⟩ := hvs
  simp only [Opnd.fill, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hy
  · exact notFlt_of_reg hb hx

/-- The integer operators (all but `/` and `^`). -/
def _root_.Lua.Bytecode.BinOp.isInt : BinOp → Bool
  | .add | .sub | .mul | .mod | .idiv | .band | .bor | .bxor | .shl | .shr => true
  | .pow | .div => false

/-- **The fast path on two integers** is the integer operation. -/
theorem fastArith_int {o : BinOp} (hio : o.isInt = true) (x y : BitVec 64) :
    fastArith o (.int x) (.int y) = Lua.Num.Res.ofInt (o.int x y) := by
  cases o <;> first
    | rfl
    | simp [BinOp.isInt] at hio

/-! The fast path on two integers, per integer operator (simp lemmas: the
kit's forward kernel evaluation reads `R[A]`'s value off them). -/

@[simp] theorem fastArith_add (x y : BitVec 64) :
    fastArith .add (.int x) (.int y) = .val (.int (x + y)) := rfl
@[simp] theorem fastArith_sub (x y : BitVec 64) :
    fastArith .sub (.int x) (.int y) = .val (.int (x - y)) := rfl
@[simp] theorem fastArith_mul (x y : BitVec 64) :
    fastArith .mul (.int x) (.int y) = .val (.int (x * y)) := rfl
@[simp] theorem fastArith_mod (x y : BitVec 64) :
    fastArith .mod (.int x) (.int y) = Lua.Num.Res.ofInt (imod x y) := rfl
@[simp] theorem fastArith_idiv (x y : BitVec 64) :
    fastArith .idiv (.int x) (.int y) = Lua.Num.Res.ofInt (idiv x y) := rfl
@[simp] theorem fastArith_band (x y : BitVec 64) :
    fastArith .band (.int x) (.int y) = .val (.int (x &&& y)) := rfl
@[simp] theorem fastArith_bor (x y : BitVec 64) :
    fastArith .bor (.int x) (.int y) = .val (.int (x ||| y)) := rfl
@[simp] theorem fastArith_bxor (x y : BitVec 64) :
    fastArith .bxor (.int x) (.int y) = .val (.int (x ^^^ y)) := rfl
@[simp] theorem fastArith_shl (x y : BitVec 64) :
    fastArith .shl (.int x) (.int y) = .val (.int (shiftl x y)) := rfl
@[simp] theorem fastArith_shr (x y : BitVec 64) :
    fastArith .shr (.int x) (.int y) = .val (.int (shiftr x y)) := rfl

@[simp] theorem Res.ofInt_some (i : BitVec 64) : Lua.Num.Res.ofInt (some i) = .val (.int i) := rfl
@[simp] theorem Res.ofInt_none : Lua.Num.Res.ofInt none = .err := rfl
@[simp] theorem Value.ofNum_int (i : BitVec 64) : Value.ofNum (.int i) = .int i := rfl

/-- **The fast path off floats**: unless both operands are integers, a
non-float pair falls through to `MMBIN*`. -/
theorem fastArith_fail {o : BinOp} {x y : Value} (hx : x.NotFlt) (hy : y.NotFlt)
    (h : ∀ a b, [x, y] ≠ [.int a, .int b]) : fastArith o x y = .fail := by
  unfold fastArith
  cases x with
  | int a =>
    cases y with
    | int b => exact absurd rfl (h a b)
    | flt => exact absurd rfl (hy _ _)
    | _ => rfl
  | flt => exact absurd rfl (hx _ _)
  | _ => rfl

/-- `R[a]` updated. -/
abbrev upd (regs : Nat → Option Value) (a : Nat) (v : Value) : Nat → Option Value :=
  fun j => if j = a then some v else regs j

/-- A step whose kernel is `opArith pc a o [x, y]` of an integer operator,
with no float operand (`NoFlt`): both operands integers and the result
written with `pc + 2`, or not both integers and nothing changed but
`pc + 1`. -/
theorem step_opArith {s s' : State} {a : Nat} {o : BinOp} {os : List Opnd}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (opArith s.pc a o os)) (hnf : NoFlt s os)
    (hio : o.isInt = true := by decide) :
    ∃ vs, (Opnd.ports os).mapM s.regs = some vs ∧
      ((∃ x y v, Opnd.fill os vs = [.int x, .int y] ∧ o.int x y = some v ∧
          s' = ⟨s.pc + 2, upd s.regs a (.int v), s.out⟩) ∨
       ((∀ x y, Opnd.fill os vs ≠ [.int x, .int y]) ∧ s' = ⟨s.pc + 1, s.regs, s.out⟩)) := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o' e
  cases hK.symm.trans hK'
  refine ⟨vs, hvs, ?_⟩
  have hnf' := hnf vs hvs
  simp only [opArith] at ho he
  split at ho
  · rename_i x y hfill
    rw [hfill] at hnf'
    have hx := hnf' x (by simp)
    have hy := hnf' y (by simp)
    by_cases hii : ∃ a b, [x, y] = [Value.int a, .int b]
    · obtain ⟨a, b, hab⟩ := hii
      simp only [List.cons.injEq, and_true] at hab
      obtain ⟨rfl, rfl⟩ := hab
      left
      rw [fastArith_int hio] at ho
      cases hv : o.int a b with
      | none => simp [hv, Lua.Num.Res.ofInt] at ho
      | some v =>
        simp only [hv, Lua.Num.Res.ofInt, Option.some.injEq] at ho
        subst ho
        simp only [List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        refine ⟨a, b, v, hfill, hv, ?_⟩
        simp only [VState.apply, writeDefs, KEdge.kills, Value.ofNum]
        congr 1
    · right
      rw [fastArith_fail hx hy (fun a b h => hii ⟨a, b, h⟩)] at ho
      simp only [Option.some.injEq] at ho
      subst ho
      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he
      subst he
      refine ⟨fun a b hab => hii ⟨a, b, hfill ▸ hab⟩, ?_⟩
      simp only [VState.apply, writeDefs, KEdge.kills]
      congr 1
  · rename_i hne
    right
    simp only [Option.some.injEq] at ho
    subst ho
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    refine ⟨fun x y hxy => hne _ _ hxy, ?_⟩
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
    (!(Value.bool ((Value.int x).rawEq (Value.int y))).isFalse) = decide (x = y) := by
  by_cases h : x = y <;> simp [h, Value.isFalse, Value.rawEq]

/-- The test of an ordering (`δ .lt`/`.le` gives a boolean). -/
theorem cond_bool (b : Bool) : (!(Value.bool b).isFalse) = b := by
  cases b <;> rfl

/-- ... and on anything else but a float. -/
theorem cond_nonint {v : Value} (h : ∀ i, v ≠ .int i) (hf : v.NotFlt) (y : BitVec 64) :
    (!(Value.bool (v.rawEq (Value.int y))).isFalse) = false := by
  cases v with
  | int i => exact absurd rfl (h i)
  | flt x n => exact absurd rfl (hf x n)
  | _ => simp [Value.isFalse, Value.rawEq]

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

/-- A step at `OP_TESTSET` (`testsetK`): `R[B]` is `v`; if its falsity is
`k`, skip (`pc + 2`), else `R[A] := v` and jump to `t`. -/
theorem step_testset {s s' : State} {w : Word} {t : Nat}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (testsetK s.pc w t)) :
    -- discipline: allow(R7-conj-tower-def) a kernel inversion's conclusion (one per combinator, each consumed at once by `obtain` in the generated arms), not a post/entry predicate
    ∃ v, s.regs w.b = some v ∧
      ((v.isFalse = w.k ∧ s' = ⟨s.pc + 2, s.regs, s.out⟩) ∨
       (¬ v.isFalse = w.k ∧ s' = ⟨t, upd s.regs w.a v, s.out⟩)) := by
  obtain ⟨hK', hvs, ho, he⟩ := h
  rename_i K vs o e
  cases hK.symm.trans hK'
  obtain ⟨v, hv, rfl⟩ := mapM1 hvs
  refine ⟨v, hv, ?_⟩
  simp only [testsetK, Option.some.injEq] at ho
  subst ho
  by_cases hk : v.isFalse = w.k
  · left
    simp only [testsetK, hk, ite_true, List.getElem?_cons_zero, Option.some.injEq] at he
    subst he
    exact ⟨hk, by simp [VState.apply, writeDefs, KEdge.kills, hk]⟩
  · right
    simp only [testsetK, hk, ite_false, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at he
    subst he
    refine ⟨hk, ?_⟩
    simp [VState.apply, writeDefs, KEdge.kills, hk]

/-- A step whose kernel is `forloopK pc w t`, on an integer loop (the step
`R[A+2]` is not a float: the float loop is `FloatArms.FORLOOP`): the count
`n`, the step and the index are read; count 0 exits to `pc + 1`, otherwise
the index is an integer and count−1, index+step and the control variable are
written, jumping to `t`. -/
theorem step_forloop {s s' : State} {w : Word} {t : Nat}
    (h : Step H p s s') (hK : kernelAt p s.pc = some (forloopK s.pc w t))
    (hnf : ¬ FltReg s (w.a + 2)) :
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
  · rename_i i' ni l nl st'' ns heq
    simp only [List.cons.injEq] at heq
    obtain ⟨-, -, rfl, -⟩ := heq
    exact absurd ⟨_, _, hst⟩ hnf
  · cases ho

end Lua.Vm.Sim

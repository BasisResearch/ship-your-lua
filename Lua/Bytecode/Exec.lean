import Lua.Bytecode.Semantics

/-!
# An executable stepper for F1, sound for `Step`

`step?` computes one F1 step and `run` iterates it to a `Final` state. They
are *not* the semantics: `BcSem` is the inductive relation. They exist so
that the kernel can build `BcSem` derivations for concrete programs
(`Lua/Programs/Validation.lean`): `run_sound` turns a successful run into
`Steps` plus `Final`. `step?` may be stricter than `Step` (it is only
required to be sound, not complete).
-/

namespace Lua.Bytecode

/-- The second operand of an arithmetic instruction. -/
def arithOperand (p : Proto) (s : State) (w : Word) : ArithShape → Option (BitVec 64)
  | .rr => match s.regs w.c with | .int y => some y | _ => none
  | .rk => match p.const w.c with | some (.int y) => some y | _ => none
  | .ri => some (BitVec.ofInt 64 w.sc)

/-- One arithmetic instruction (`op_arith*`). -/
def arithStep? (p : Proto) (s : State) (w : Word) (o : OpCode) : Option State :=
  match intArith o, arithShape o with
  | some f, some sh =>
    match s.regs w.b with
    | .int x =>
      match arithOperand p s w sh with
      | some y => (f x y).map fun r => (s.set w.a (.int r)).goto (s.pc + 2)
      | none => none
    | _ => none
  | _, _ => none

/-- One F1 step, computed. -/
def step? (H : Host) (p : Proto) (s : State) : Option State :=
  match p.fetch s.pc with
  | none => none
  | some w =>
    match w.op? with
    | none => none
    | some o =>
      match o with
      | .MOVE => some ((s.set w.a (s.regs w.b)).goto (s.pc + 1))
      | .LOADI => some ((s.set w.a (.int (BitVec.ofInt 64 w.sbx))).goto (s.pc + 1))
      | .LOADK =>
        match p.const w.bx with
        | some c => (c.toValue?).map fun v => (s.set w.a v).goto (s.pc + 1)
        | none => none
      | .LOADFALSE => some ((s.set w.a (.bool false)).goto (s.pc + 1))
      | .LFALSESKIP => some ((s.set w.a (.bool false)).goto (s.pc + 2))
      | .LOADTRUE => some ((s.set w.a (.bool true)).goto (s.pc + 1))
      | .LOADNIL => some ((s.setNils w.a (w.b + 1)).goto (s.pc + 1))
      | .GETTABUP =>
        if w.b = 0 ∧ p.const w.c = some (.str printKey) then
          some ((s.set w.a (.builtin .print)).goto (s.pc + 1))
        else none
      | .UNM =>
        match s.regs w.b with
        | .int x => some ((s.set w.a (.int (0 - x))).goto (s.pc + 1))
        | _ => none
      | .BNOT =>
        match s.regs w.b with
        | .int x => some ((s.set w.a (.int (~~~x))).goto (s.pc + 1))
        | _ => none
      | .NOT => some ((s.set w.a (.bool (s.regs w.b).isFalse)).goto (s.pc + 1))
      | .JMP => (jumpTo (s.pc + 1) w.sj).map s.goto
      | .EQ => (condJump p s.pc (decide (s.regs w.a = s.regs w.b)) w.k).map s.goto
      | .EQK =>
        match p.const w.b with
        | some c =>
          match c.toValue? with
          | some v => (condJump p s.pc (decide (s.regs w.a = v)) w.k).map s.goto
          | none => none
        | none => none
      | .EQI =>
        (condJump p s.pc (decide (s.regs w.a = .int (BitVec.ofInt 64 w.sb))) w.k).map s.goto
      | .LT | .LE =>
        match intCmp o, s.regs w.a, s.regs w.b with
        | some f, .int x, .int y => (condJump p s.pc (f x y) w.k).map s.goto
        | _, _, _ => none
      | .LTI | .LEI | .GTI | .GEI =>
        match intCmp o, s.regs w.a with
        | some f, .int x => (condJump p s.pc (f x (BitVec.ofInt 64 w.sb)) w.k).map s.goto
        | _, _ => none
      | .TEST => (condJump p s.pc (!(s.regs w.a).isFalse) w.k).map s.goto
      | .TESTSET =>
        if (s.regs w.b).isFalse = w.k then some (s.goto (s.pc + 2))
        else
          match p.fetch (s.pc + 1) with
          | some ni => (jumpTo (s.pc + 2) ni.sj).map fun t => (s.set w.a (s.regs w.b)).goto t
          | none => none
      | .FORPREP =>
        match s.regs w.a, s.regs (w.a + 1), s.regs (w.a + 2) with
        | .int i, .int _, .int st =>
          if st = 0 then none else
          match s.regs (w.a + 1) with
          | .int l =>
            match forCount i l st with
            | some n => some (((s.set (w.a + 3) (.int i)).set (w.a + 1) (.int n)).goto (s.pc + 1))
            | none => some ((s.set (w.a + 3) (.int i)).goto (s.pc + 1 + w.bx + 1))
          | _ => none
        | _, _, _ => none
      | .FORLOOP =>
        match s.regs (w.a + 1), s.regs w.a, s.regs (w.a + 2) with
        | .int n, .int i, .int st =>
          if n = 0 then some (s.goto (s.pc + 1)) else
          (jumpTo (s.pc + 1) (-(w.bx : Int))).map fun t =>
            (((s.set (w.a + 1) (.int (n - 1))).set w.a (.int (i + st))).set (w.a + 3)
              (.int (i + st))).goto t
        | _, _, _ => none
      | .CALL =>
        if s.regs w.a = .builtin .print ∧ w.b ≠ 0 ∧ w.c ≠ 0 then
          some (((s.emit (printLine H (s.args (w.a + 1) (w.b - 1)))).setNils w.a (w.c - 1)).goto
            (s.pc + 1))
        else none
      | .VARARGPREP => some (s.goto (s.pc + 1))
      | o => arithStep? p s w o

/-- Is `s` at a `RETURN*`? -/
def final? (p : Proto) (s : State) : Bool :=
  match p.fetch s.pc with
  | some w =>
    match w.op? with
    | some .RETURN | some .RETURN0 | some .RETURN1 => true
    | _ => false
  | none => false

/-- Run to a `Final` state within `fuel` steps. -/
def run (H : Host) (p : Proto) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    if final? p s then some s
    else
      match step? H p s with
      | some s' => run H p n s'
      | none => none

section Soundness
variable {H : Host} {p : Proto}

theorem arithStep?_sound {s s' : State} {w : Word} {o : OpCode}
    (hw : p.fetch s.pc = some w) (ho : w.op? = some o)
    (h : arithStep? p s w o = some s') : Step H p s s' := by
  unfold arithStep? at h
  split at h
  · rename_i f sh hf hsh
    split at h
    · rename_i x hx
      split at h
      · rename_i y hy
        cases hr : f x y with
        | none => simp [hr] at h
        | some r =>
          simp only [hr, Option.map_some, Option.some.injEq] at h
          subst h
          refine Step.arith hw ho hf hsh hx ?_ hr
          cases sh with
          | rr =>
            simp only [arithOperand] at hy
            split at hy
            · rename_i y' hy'; cases hy; exact hy'
            · cases hy
          | rk =>
            simp only [arithOperand] at hy
            split at hy
            · rename_i y' hy'; cases hy; exact hy'
            · cases hy
          | ri => simp only [arithOperand, Option.some.injEq] at hy; exact hy.symm
      · cases h
    · cases h
  · cases h

theorem map_goto_eq {s s' : State} {o : Option Nat} (h : o.map s.goto = some s') :
    ∃ t, o = some t ∧ s' = s.goto t := by
  cases o with
  | none => cases h
  | some t => exact ⟨t, rfl, (Option.some.inj h).symm⟩

/-- `step?` is sound for `Step`. -/
theorem step?_sound {s s' : State} (h : step? H p s = some s') : Step H p s s' := by
  unfold step? at h
  split at h
  · cases h
  · rename_i w hw
    split at h
    · cases h
    · rename_i o ho
      cases o
      all_goals first
        | exact arithStep?_sound hw ho h
        | skip
      all_goals (try simp only at h)
      -- the remaining cases, one per rule
      case MOVE => cases h; exact Step.move hw ho
      case LOADI => cases h; exact Step.loadi hw ho
      case LOADK =>
        split at h
        · rename_i c hc
          cases hv : c.toValue? with
          | none => simp [hv] at h
          | some v =>
            simp only [hv, Option.map_some, Option.some.injEq] at h
            subst h; exact Step.loadk hw ho hc hv
        · cases h
      case LOADFALSE => cases h; exact Step.loadfalse hw ho
      case LFALSESKIP => cases h; exact Step.lfalseskip hw ho
      case LOADTRUE => cases h; exact Step.loadtrue hw ho
      case LOADNIL => cases h; exact Step.loadnil hw ho
      case GETTABUP =>
        split at h
        · rename_i hc; cases h; exact Step.gettabupPrint hw ho hc.1 hc.2
        · cases h
      case UNM =>
        split at h
        · rename_i x hx; cases h; exact Step.unm hw ho hx
        · cases h
      case BNOT =>
        split at h
        · rename_i x hx; cases h; exact Step.bnot hw ho hx
        · cases h
      case NOT => cases h; exact Step.not hw ho
      case JMP =>
        obtain ⟨t, ht, rfl⟩ := map_goto_eq h; exact Step.jmp hw ho ht
      case EQ =>
        obtain ⟨t, ht, rfl⟩ := map_goto_eq h; exact Step.eq hw ho ht
      case EQK =>
        split at h
        · rename_i c hc
          split at h
          · rename_i v hv
            obtain ⟨t, ht, rfl⟩ := map_goto_eq h; exact Step.eqk hw ho hc hv ht
          · cases h
        · cases h
      case EQI =>
        obtain ⟨t, ht, rfl⟩ := map_goto_eq h; exact Step.eqi hw ho ht
      case LT =>
        split at h
        · rename_i f x y hf hx hy
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRR hw ho (Or.inl rfl) hf hx hy ht
        · cases h
      case LE =>
        split at h
        · rename_i f x y hf hx hy
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRR hw ho (Or.inr rfl) hf hx hy ht
        · cases h
      case LTI =>
        split at h
        · rename_i f x hf hx
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRI hw ho (Or.inl rfl) hf hx ht
        · cases h
      case LEI =>
        split at h
        · rename_i f x hf hx
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRI hw ho (Or.inr (Or.inl rfl)) hf hx ht
        · cases h
      case GTI =>
        split at h
        · rename_i f x hf hx
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRI hw ho (Or.inr (Or.inr (Or.inl rfl))) hf hx ht
        · cases h
      case GEI =>
        split at h
        · rename_i f x hf hx
          obtain ⟨t, ht, rfl⟩ := map_goto_eq h
          exact Step.cmpRI hw ho (Or.inr (Or.inr (Or.inr rfl))) hf hx ht
        · cases h
      case TEST =>
        obtain ⟨t, ht, rfl⟩ := map_goto_eq h; exact Step.test hw ho ht
      case TESTSET =>
        split at h
        · rename_i hk; cases h; exact Step.testsetSkip hw ho hk
        · rename_i hk
          split at h
          · rename_i ni hni
            cases hj : jumpTo (s.pc + 2) ni.sj with
            | none => simp [hj] at h
            | some t =>
              simp only [hj, Option.map_some, Option.some.injEq] at h
              subst h; exact Step.testsetJump hw ho hk hni hj
          · cases h
      case FORPREP =>
        split at h
        · rename_i i l0 st hi hl0 hst
          split at h
          · cases h
          · rename_i hst0
            split at h
            · rename_i l hl
              split at h
              · rename_i n hn
                cases h; exact Step.forprepEnter hw ho hi hl hst hst0 hn
              · rename_i hn
                cases h; exact Step.forprepSkip hw ho hi hl hst hst0 hn
            · cases h
        · cases h
      case FORLOOP =>
        split at h
        · rename_i n i st hn hi hst
          split at h
          · rename_i hn0
            subst hn0; cases h; exact Step.forloopDone hw ho hn ⟨st, hst⟩
          · rename_i hn0
            cases hj : jumpTo (s.pc + 1) (-(w.bx : Int)) with
            | none => simp [hj] at h
            | some t =>
              simp only [hj, Option.map_some, Option.some.injEq] at h
              subst h; exact Step.forloopAgain hw ho hn hn0 hi hst hj
        · cases h
      case CALL =>
        split at h
        · rename_i hc; cases h; exact Step.callPrint hw ho hc.1 hc.2.1 hc.2.2
        · cases h
      case VARARGPREP => cases h; exact Step.varargprep hw ho
      all_goals first
        | (unfold arithStep? at h; simp [intArith] at h)
        | skip

theorem final?_sound {s : State} (h : final? p s = true) : Final p s := by
  unfold final? at h
  split at h
  · rename_i w hw
    split at h
    · rename_i ho; exact Final.ret hw ho (Or.inl rfl)
    · rename_i ho; exact Final.ret hw ho (Or.inr (Or.inl rfl))
    · rename_i ho; exact Final.ret hw ho (Or.inr (Or.inr rfl))
    · cases h
  · cases h

/-- A successful run is a `Steps` derivation to a `Final` state. -/
theorem run_sound : ∀ {n : Nat} {s s' : State}, run H p n s = some s' →
    Steps H p s s' ∧ Final p s'
  | 0, _, _, h => by cases h
  | n + 1, s, s', h => by
    unfold run at h
    split at h
    · rename_i hf; cases h; exact ⟨Steps.refl s, final?_sound hf⟩
    · split at h
      · rename_i s₁ h₁
        obtain ⟨hs, hfin⟩ := run_sound h
        exact ⟨Steps.head (step?_sound h₁) hs, hfin⟩
      · cases h

/-- **Validation route**: a run that ends printing `out` is a `BcSem`
derivation. -/
theorem bcSem_of_run {n : Nat} {out : String}
    (h : ((run H p n State.init).map State.out) = some out) : BcSem H p out := by
  cases hr : run H p n State.init with
  | none => simp [hr] at h
  | some s =>
    simp only [hr, Option.map_some, Option.some.injEq] at h
    obtain ⟨hs, hf⟩ := run_sound hr
    exact ⟨s, hs, hf, h⟩

end Soundness

end Lua.Bytecode

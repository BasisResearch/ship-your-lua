import Lua.Vm.Sim.Kit.AtFlt
import Lua.Vm.Sim.Kit.AtJoinRow

/-!
# Float arms by pair atoms, Boolean forks and join cuts (round 5, A-JOIN)

An arm's float path is run once, forward, and split only where the machine
forks:

* **Boolean forks** (`at_walk`, `at_step1`). The at-lemmas are chained by
  row as `at_run` does, but a guard over a soft-float answer (a location
  `.fn f<k>` or a join `.fn j<k>`) is never closed by trial: the run splits
  on the very `Bool` the branch reads (`hf_<pc> : G = true` / `= false`,
  two goals) and each side takes its lemma by `assumption`. The prefix the
  sides share runs once; nothing splits the kernel before the run.
* **Join cuts** (`Kit/AtJoinRow.lean`, generator `JOINS`). Where the two
  sides meet, the join lemma moves each to the one join row; the tail is
  one set of lemmas.
* **Pair atoms and the leaf** (`at_atoms`, `at_leaf`). At the fetch head,
  the kernel's outcome is split (`split at hk`) and the wrong side refuted:
  the path's fork facts and the kernel's test are rewritten to functions of
  `Float.Model.compare x y` (the routines' specifications, `F64`'s bridge,
  the payload models), every comparison is keyed by its unordered pair of
  model values (`model_cmp_swap` orients it as the kernel first names it),
  the atoms are generalised and one closed `decide` over the `≤ 4^k`
  answers refutes it. The machine's idioms (`slti`, `blez`, `not; srli`,
  …) are evaluated by that `decide` on the four answers, never by a bridge
  lemma per idiom.
* **Per-operand views** (`flt_reg_q`, `flt_reg`): a register the operand
  predicate names a float, or one the kernel's float clause inverts to a
  float, gives its tag and payload model (`hta`, `hxm`, accumulated).
* **`sgnBound`**: the C idiom `luai_numlt(0, step) ? R(a, b) : R(b, a)`
  shared by `floatforloop` and `forprep` (`forloopK`, `forprepK`'s float
  clauses are it by `rfl`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.At

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout Lua.Num

/-! ## Pair atoms -/

/-- **The orientation of a pair atom**: one comparison per unordered pair. -/
theorem model_cmp_swap (x y : Float.Model) :
    Float.Model.compare y x = (Float.Model.compare x y).map Ordering.swap := by
  have h := F64.compare_swap x.toBits.toBitVec y.toBits.toBitVec
  rwa [F64.compare_eq_model, F64.compare_eq_model, toModel_toBits, toModel_toBits] at h

theorem model_lt_cmp (x y : Float.Model) :
    Float.Model.lt x y = (Float.Model.compare x y == some .lt) := by
  have h := F64.lt_eq_model x.toBits.toBitVec y.toBits.toBitVec
  rw [toModel_toBits, toModel_toBits] at h
  rw [← h, F64.lt, F64.compare_eq_model, toModel_toBits, toModel_toBits]

theorem model_le_cmp (x y : Float.Model) :
    Float.Model.le x y = (Float.Model.compare x y).any (·.isLE) := by
  have h := F64.le_eq_model x.toBits.toBitVec y.toBits.toBitVec
  rw [toModel_toBits, toModel_toBits] at h
  rw [← h, F64.le, F64.compare_eq_model, toModel_toBits, toModel_toBits]

theorem model_beq_cmp (x y : Float.Model) :
    Float.Model.beq x y = (Float.Model.compare x y == some .eq) := by
  have h := F64.eq_eq_model x.toBits.toBitVec y.toBits.toBitVec
  rw [toModel_toBits, toModel_toBits] at h
  rw [← h, F64.eq, F64.compare_eq_model, toModel_toBits, toModel_toBits]

/-- A computed sum's model (`__adddf3`'s specification read back). -/
theorem toModel_add (a b : BitVec 64) :
    F64.toModel (F64.add a b) = Float.Model.add (F64.toModel a) (F64.toModel b) := by
  rw [F64.add_eq_model, toModel_toBits]

/-- **The answers of one atom are four**: `decide` over them. -/
instance decForallAtom (P : Option Ordering → Prop) [DecidablePred P] : Decidable (∀ o, P o) :=
  decidable_of_iff (P none ∧ P (some .lt) ∧ P (some .eq) ∧ P (some .gt))
    ⟨fun ⟨a, b, c, d⟩ o => by rcases o with _ | _ | _ | _ <;> assumption,
     fun h => ⟨h _, h _, h _, h _⟩⟩

/-! ## The signed bound -/

/-- **`luai_numlt(0, step) ? R(a, b) : R(b, a)`**: `floatforloop`'s and
`forprep`'s float skeleton. -/
def sgnBound (R : Float.Model → Float.Model → Bool) (st a b : Float.Model) : Bool :=
  if Float.Model.lt Lua.Num.zero st then R a b else R b a

theorem forloop_sgnBound (st idx l : Float.Model) :
    (if Float.Model.lt Lua.Num.zero st then Float.Model.le idx l else Float.Model.le l idx) =
      sgnBound Float.Model.le st idx l := rfl

theorem forprep_sgnBound (fs fl fi : Float.Model) :
    (if Float.Model.lt Lua.Num.zero fs then Float.Model.lt fl fi else Float.Model.lt fi fl) =
      sgnBound Float.Model.lt fs fl fi := rfl

/-- **`sgnBound` on its two pair atoms** `{0, st}` and `{a, b}`, for a
relation that reads one answer (`lt`, `le`). -/
theorem sgnBound_atoms (R : Float.Model → Float.Model → Bool) (ρ : Option Ordering → Bool)
    (hR : ∀ x y, R x y = ρ (Float.Model.compare x y)) (st a b : Float.Model) :
    sgnBound R st a b = if (Float.Model.compare Lua.Num.zero st == some .lt) = true
      then ρ (Float.Model.compare a b) else ρ ((Float.Model.compare a b).map Ordering.swap) := by
  simp only [sgnBound, model_lt_cmp, hR, model_cmp_swap a b]

/-! ## Per-operand views -/

set_option hygiene false in
/-- The accumulators of the views (`hta`: tags, `hxm`: payload models). -/
macro "flt_views" : tactic => `(tactic| (
  have hta : True := trivial
  have hxm : True := trivial))

set_option hygiene false in
/-- **`flt_reg_q x j, hT`**: register `j`, a float by the operand predicate
(`hT : FltReg s j`): its tag and model join `hta`, `hxm`. -/
macro "flt_reg_q " x:ident j:term "," hq:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  obtain ⟨$x, _, hst⟩ := $hq
  rw [hst] at hr; cases hr
  obtain ⟨hta', hxm', -⟩ := hv.flt_parts
  have hta := And.intro hta' hta
  have hxm := And.intro hxm' hxm
  clear hta' hxm'))

set_option hygiene false in
/-- **`flt_reg_s j, hT`**: `flt_reg_q`, the value substituted by its view
(`.flt (F64.toModel x) x.msb`, `x` the payload): the kernel then reads the
payloads themselves. -/
macro "flt_reg_s " j:term "," hq:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  obtain ⟨_, _, hst⟩ := $hq
  rw [hst] at hr; cases hr
  obtain ⟨hta', rfl, rfl⟩ := hv.flt_parts
  have hta := And.intro hta' hta
  clear hta'))

set_option hygiene false in
/-- **`flt_reg x j`**: register `j`, a float by the kernel's float clause
(every other value refuted by `hk`). -/
macro "flt_reg " x:ident j:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  rcases v with _ | _ | _ | ⟨$x, _⟩ | _ | _ <;> simp at hk
  obtain ⟨hta', hxm', -⟩ := hv.flt_parts
  have hta := And.intro hta' hta
  have hxm := And.intro hxm' hxm
  clear hta' hxm'))

set_option hygiene false in
/-- **`flt_reg2 x j, y k`**: two registers the kernel's float clause inverts
together (its match tests them in turn). -/
macro "flt_reg2 " x:ident j:term "," y:ident k:term : tactic => `(tactic| (
  kit_reg hr v hv $j
  kit_reg hr' v' hv' $k
  rcases v with _ | _ | _ | ⟨$x, _⟩ | _ | _ <;> rcases v' with _ | _ | _ | ⟨$y, _⟩ | _ | _ <;>
    simp at hk ⊢
  obtain ⟨hta', hxm', -⟩ := hv.flt_parts
  obtain ⟨hta'', hxm'', -⟩ := hv'.flt_parts
  have hta := And.intro hta' (And.intro hta'' hta)
  have hxm := And.intro hxm' (And.intro hxm'' hxm)
  clear hta' hxm' hta'' hxm''))

/-- **The per-operand view of a number operand** (`tonumberns`, `op_arithf`'s
per-operand conversion): a float (its model), an integer (its payload), or no
number. The third component is uniform (`True` but for no number), so one
`rcases` pattern names it in every class. -/
theorem _root_.Lua.Vm.Sim.ValRepr.numView {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {v : Value}
    (h : ValRepr mo ι t x v) :
    (v = .flt (F64.toModel x) x.msb ∧ t = BitVec.ofNat 8 vNumFlt ∧ True) ∨
    (v = .int x ∧ t = BitVec.ofNat 8 vNumInt ∧ True) ∨
    (v.toNum? = none ∧ t ≠ BitVec.ofNat 8 vNumInt ∧ t ≠ BitVec.ofNat 8 19) := by
  cases h with
  | flt => exact .inl ⟨rfl, rfl, trivial⟩
  | int => exact .inr (.inl ⟨rfl, rfl, trivial⟩)
  | str => exact .inr (.inr ⟨rfl, by rcases strTag_cases _ with e | e <;> rw [e] <;> decide,
      by rcases strTag_cases _ with e | e <;> rw [e] <;> decide⟩)
  | _ => exact .inr (.inr ⟨rfl, by decide, by decide⟩)

set_option hygiene false in
/-- **`num_reg j, hn`**: register `j` by its per-operand view, three goals
(float, integer, no number: `hn : v.toNum? = none`, else `True`). -/
macro "num_reg " j:term "," hn:ident : tactic => `(tactic| (
  kit_reg hr v hv $j
  rcases hv.numView with ⟨rfl, htn, $hn⟩ | ⟨rfl, htn, $hn⟩ | ⟨$hn, htn, htn'⟩))

set_option hygiene false in
/-- A stored float computed by the soft-float call nodes (`luai_numsub`,
`luai_numadd`, the conversions `__floatdidf`): its bits are the kernel's
value's, through `F64`'s bridges. -/
macro_rules
  | `(tactic| at_new_ext) => `(tactic| (
      refine ValRepr.ofFloat_of (by decide) ?_
      simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec, Lua.Vm.Fn.Subdf3.S,
        Lua.Vm.Fn.Adddf3.S, Lua.Vm.Fn.Floatdidf.S, F64.sub_eq_model, F64.add_eq_model, toModel_toBits,
        toModel_ofInt, ofI, hxm, true_and, and_true]
      done))

/-- Two tags compared (`beq a4, a2`: `R[C]`'s tag against `R[B]`'s). -/
theorem zext_byte_beq (a b : BitVec 8) :
    (zero_extend (m := 64) (a : BitVec (8 * 1)) == zero_extend (m := 64) (b : BitVec (8 * 1))) =
      decide (a = b) := by
  have key : ∀ x : BitVec 8, (zero_extend (m := 64) (x : BitVec (8 * 1))).toNat = x.toNat := by
    intro x
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, BitVec.zeroExtend_eq_setWidth]
    have := x.isLt; omega
  by_cases h : a = b
  · subst h; simp
  · have hne : zero_extend (m := 64) (a : BitVec (8 * 1)) ≠ zero_extend (m := 64) (b : BitVec (8 * 1)) :=
      fun he => h (BitVec.eq_of_toNat_eq (by have := congrArg BitVec.toNat he; rwa [key, key] at this))
    simp [h, hne]

open Lean Elab Tactic Meta in
/-- **`at_tags`**: a tag guard from the views' tag facts (whatever their
names): the operands' tags, a tag against a literal or another tag. -/
elab "at_tags" : tactic => withMainContext do
  let mut facts : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  for d in (← getLCtx) do
    if d.isImplementationDetail || d.userName.hasMacroScopes then continue
    let t ← instantiateMVars d.type
    unless ← Meta.isProp t do continue
    unless (t.find? fun e => e.isConstOf ``slotTag).isSome do continue
    if (t.find? fun e => e.isConstOf ``Vsa.Sim.SegSt).isSome then continue
    facts := facts.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):term))
  evalTactic (← `(tactic| simp only [Loc.den, Fld.den, Nat.add_zero, zext_byte_beq, bne,
      zext_beq_lit _ 19 (by decide), zext_beq_lit _ vNumInt (by decide), vNumFlt, true_and, and_true,
      decide_eq_true_eq, decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false', $facts,*]))
  unless (← getUnsolvedGoals).isEmpty do evalTactic (← `(tactic| decide))

/-- The tag guards of the per-operand views, tried first. -/
macro_rules | `(tactic| at_hyp) => `(tactic| at_tags)

/-- A stored float tag over an entry payload (`setfltvalue` of a register's own
float, `forprep`'s float loop). -/
theorem _root_.Lua.Vm.Sim.ValRepr.flt_lit {mo : Mem} {ι : Strs} {x : BitVec 64} :
    ValRepr mo ι (stData 1 (0x13#64 : BitVec 64)) x (.flt (F64.toModel x) x.msb) := by
  rw [show stData 1 (0x13#64 : BitVec 64) = BitVec.ofNat 8 vNumFlt by decide]; exact .flt

macro_rules | `(tactic| at_new_ext) => `(tactic| exact ValRepr.flt_lit)

/-! ## The run: Boolean forks -/

open Lean Elab Tactic Meta

/-- The lemmas that may start at `pc`: `at_run`'s and the join lemmas. -/
def atCandsJ (ns : Name) (pc : Nat) (ret : Option Nat) : MetaM (List Name) := do
  let mut out ← atCands ns pc ret
  for k in ["", "_1", "_2", "_3", "_4", "_5"] do
    let n := ns ++ Name.mkSimple s!"join_{hex8 pc}{k}"
    if (← getEnv).contains n then out := out ++ [n]
  return out

/-- A guard over a soft-float answer or a join (`Loc.fn`): a fork. -/
def isForkGuard (t : Expr) : Bool := (t.find? fun e => e.isConstOf ``Loc.fn).isSome

/-- The arguments of an at-lemma for `at_step1`: a fork's guard only by
`assumption` (the split put it in context), the rest as `at_run`'s. -/
def atWalkArgs (n : Name) : TermElabM (Array Term) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    let mut args : Array Term := #[]
    for x in xs do
      let t ← inferType x
      let d ← x.fvarId!.getDecl
      unless d.binderInfo.isExplicit do continue
      let nm := d.userName.toString
      if nm == "hX" then args := args.push (mkIdent `hX)
      else if ← Meta.isProp t then
        if nm.startsWith "hg" && isForkGuard t then args := args.push (← `((by assumption)))
        else args := args.push (← `((by at_hyp)))
      else args := args.push (← `(_))
    return args

/-- The fork guard of an at-lemma at the context `X`, if it has one. -/
def forkGuard? (n : Name) (X : Expr) : MetaM (Option Expr) := do
  let ci ← getConstInfo n
  forallTelescope ci.type fun xs _ => do
    for x in xs do
      let d ← x.fvarId!.getDecl
      if d.userName.toString.startsWith "hg" then
        let t ← inferType x
        if isForkGuard t then return some (t.replaceFVar xs[0]! X)
    return none

/-- **`at_step1 ns h acc`**: one at-lemma of `ns` from `h : At X pc …`
(fork guards from context only), or, at a fork, the split on its `Bool`
(`hf_<pc>`). Fails at the fetch head or an error exit's entry. -/
elab "at_step1 " ns:ident h:ident acc:ident : tactic => withMainContext do
  let some ld := (← getLCtx).findFromUserName? h.getId | throwError "at_step1: no {h}"
  let ty ← instantiateMVars ld.type
  let some pc ← atPc ty | throwError "at_step1: no pc"
  if pc == 0x8001bfe4 || errEntryPcs.contains pc then throwError "at_step1: at the head"
  let ret ← atRet ty
  let key ← atKey ty
  let X := ty.getAppArgs[0]!
  let cands ← (← atCandsJ ns.getId pc ret).filterM fun n => return (← lemmaKey n) == key
  for n in cands do
    let s ← saveState
    let ok ← tryCatchRuntimeEx (do
        let args ← Tactic.runTermElab (atWalkArgs n)
        let lem ← `($(mkIdent n) $args*)
        withoutRecover <| Term.withoutErrToSorry <| evalTactic (← `(tactic|
          obtain ⟨_, $acc, $h⟩ := At.run $acc $h $lem))
        pure true)
      (fun _ => pure false)
    if ok then return
    s.restore
  for n in cands do
    if let some g ← forkGuard? n X then
      let some (_, lhs, _) := g.eq? | continue
      let stx ← Term.exprToSyntax lhs
      let hn := mkIdent (Name.mkSimple s!"hf_{hex8 pc}")
      evalTactic (← `(tactic| rcases Bool.eq_false_or_eq_true $stx with $hn:ident | $hn:ident))
      return
  throwError "at_step1: nothing applies at 0x{hex8 pc}"

set_option hygiene false in
/-- **`at_walk NS`**: after the arm's setup, the run from the entry to the
fetch head (or an error exit) in every machine path, split at the forks. -/
macro "at_walk " ns:ident : tactic => `(tactic| (
  have hX : Cx.Ok ⟨p, c, s, w, ins⟩ := ⟨hc, hf⟩
  have h0 : At ⟨p, c, s, w, ins⟩ _ (headRow ⟨p, c, s, w, ins⟩) [] c := h0
  have e : True := trivial  -- the float closers' kernel facts: none here (no kernel split)
  have hnj : True := trivial
  try simp only [stackValueSize] at *
  repeat' at_step1 $ns h0 acc))

/-! ## The leaf: one closed `decide` over the pair atoms -/

/-- The `Float.Model.compare` terms of `e`, in order. -/
partial def cmpTerms (e : Expr) (acc : Array (Expr × Expr) := #[]) : Array (Expr × Expr) :=
  let acc := if e.isAppOfArity ``Float.Model.compare 2 then acc.push (e.appFn!.appArg!, e.appArg!) else acc
  match e with
  | .app f a => cmpTerms a (cmpTerms f acc)
  | .lam _ t b _ | .forallE _ t b _ => cmpTerms b (cmpTerms t acc)
  | .letE _ t v b _ => cmpTerms b (cmpTerms v (cmpTerms t acc))
  | .mdata _ b | .proj _ _ b => cmpTerms b acc
  | _ => acc

/-- **`at_atoms`**: refute the leaf (`False`) from the fork facts `hf_*` and
the kernel's test `hq`: each rewritten to the pair atoms, generalised, one
`decide`. -/
elab "at_atoms" : tactic => withMainContext do
  -- the fork facts and the kernel's tests (`hf_*`, `hq`, shadowed ones
  -- too), renamed apart
  let mut hs : Array Name := #[]
  let mut ms : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[]
  let mut g ← getMainGoal
  let mut i := 0
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    let nm := d.userName.toString
    if nm.startsWith "hf_" || nm.startsWith "hq" then
      let n := Name.mkSimple s!"hpc_{i}"
      i := i + 1
      g ← g.rename d.fvarId n
      hs := hs.push n
    -- the payload models (`hxm`'s conjuncts)
    if nm == "hxm" then ms := ms.push (← `(Lean.Parser.Tactic.simpLemma| $(mkIdent d.userName):term))
  replaceMainGoal [g]
  let hids := hs.map mkIdent
  evalTactic (← `(tactic| simp (disch := assumption) only [Loc.den, Fld.den, Nat.add_zero, at_fspec,
      Lua.Vm.Fn.Gedf2.S, Lua.Vm.Fn.Ledf2.S, Lua.Vm.Fn.Eqdf2.S, Lua.Vm.Fn.Adddf3.S, F64.eq,
      F64.compare_eq_model, toModel_add, toModel_toBits, toModel_zero, model_lt_cmp, model_le_cmp,
      model_beq_cmp, sgnBound, true_and, and_true, Bool.not_eq_true, $ms,*] at $hids*))
  if (← getUnsolvedGoals).isEmpty then return
  withMainContext do
    -- the pair atoms: the kernel's test (`hq`) names the orientation first
    let lctx ← getLCtx
    let mut order : Array (Expr × Expr) := #[]
    for nm in hs.reverse do
      let some d := lctx.findFromUserName? nm | continue
      order := order ++ cmpTerms (← instantiateMVars d.type)
    let mut keys : Array (Expr × Expr) := #[]
    let mut swaps : Array (Expr × Expr) := #[]
    for (a, b) in order do
      if keys.any (fun (x, y) => x == a && y == b) then continue
      if keys.any (fun (x, y) => x == b && y == a) then
        unless swaps.any (fun (x, y) => x == a && y == b) do swaps := swaps.push (a, b)
        continue
      keys := keys.push (a, b)
    for (a, b) in swaps do
      let sa ← Term.exprToSyntax a
      let sb ← Term.exprToSyntax b
      evalTactic (← `(tactic| simp only [model_cmp_swap $sb $sa] at $hids*))
    let mut os : Array Ident := #[]
    for (a, b) in keys do
      let o := mkIdent (← mkFreshUserName `o)
      os := os.push o
      let sa ← Term.exprToSyntax a
      let sb ← Term.exprToSyntax b
      evalTactic (← `(tactic| generalize Float.Model.compare $sa $sb = $o:ident at $hids*))
    evalTactic (← `(tactic| revert $hids*))
    evalTactic (← `(tactic| revert $os*))
    evalTactic (← `(tactic| decide))

set_option hygiene false in
/-- **`at_leaf NS`**: at the fetch head, the kernel's outcome: the side of
its test the path's atoms refute is closed by `at_atoms`, the other by the
close (`at_close`). -/
macro "at_leaf " ns:ident : tactic => `(tactic| (
  repeat' (split at hk <;> rename_i hq)
  all_goals first
  | (simp at hk; done)
  | (exfalso; at_atoms)
  | (simp [VState.apply, writeDefs, KEdge.kills] at hk
     subst hk
     at_close $ns h0 acc)
  | at_close $ns h0 acc))

end Lua.Vm.Sim.At

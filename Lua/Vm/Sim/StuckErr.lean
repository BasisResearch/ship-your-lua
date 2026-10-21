import Lua.Vm.Sim.Stuck
import Lua.Vm.Sim.Kit.AtErr
import Lua.Vm.Sim.Kit.ErrTail
import Lua.Vm.Sim.Kit.Unwind

/-!
# The error sites: the arms' paths, the heads, and the shared tail

The site `ErrSite.runerror` collects the stuck states of `n % 0`, `n // 0`
(`OP_MOD`, `OP_IDIV`, `OP_MODK`, `OP_IDIVK`) and `'for' step is zero`
(`OP_FORPREP`, integer or float loop). For each, the machine runs from the
fetch head through dispatch and the arm's error path (`Kit/AtErr.lean`, the
generated at-lemmas) to the entry of `luaG_runerror` with the message in
`a1` (`ErrIn`). What remains is that entry's summary, `ThrowFrom
symLuaGRunerror msg` (`Kit/ErrTail.lean`): `luaG_runerror` formats the
message (`RunerrorHead_Statement`) and calls `luaG_errormsg`, the shared
tail: the throw (`Kit.throw_land`, proved) and the unwind to `exit(2)`
(`Kit.Unwind_Statement`).

`runerrorSim : RunerrorThrow → FpFltZero_Statement → ErrorSimAt .runerror`;
every other site is its head into the shared tail (`SiteHead_Statement`,
`errorSimAt_of_head`); `ErrorSimRest` is what is left of `ErrorSim`
(`vm_refinement_of_open'`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.At Lua.Vm.Sim.Kit
open Vsa.Machine (Config Steps)

/-- **An error state by an arm's error path**: dispatch, the arm's run into
`f` (`ArmErr`), then `f`'s throw obligation. -/
theorem stuckOut_of_armErr {o : OpCode} {Q : Proto → Config → State → RelPtrs → Word → Prop}
    {f msg : Nat} (ho : o.toNat < Arms.jtEntries) (hE : ArmErr o Q f msg) (hT : ThrowFrom f msg)
    {p : Proto} {c : Config} {s : State} {ins : Word} (hS : Supported p) (hs : Reach p s)
    (hR : VmRel p c s) (hf : p.fetch s.pc = some ins) (hop : ins.op? = some o)
    (hq : ∀ c' w, ArmAt p c' s w ins → Q p c' s w ins) : StuckOut c := by
  obtain ⟨w, hRw⟩ := hR
  obtain ⟨c1, hs1, -, hA⟩ := dispatch hRw hf (by rw [opNum_of_op? hop]; exact ho)
  obtain ⟨c2, hs2, hE2⟩ := hE hS hA hf hop (hq c1 w hA)
  exact StuckOut.of_steps (hs1.trans hs2) (hT ⟨p, c1, s, w, ins⟩ c2 hS hs hA.core hE2)

/-- `op_arith`'s failing body: two integers and `luaV_mod`/`luaV_idiv` by zero. -/
theorem opArith_zero {pc a : Nat} {b : BinOp} {x y : Opnd} {vs : List Value}
    (h : (opArith pc a b [x, y]).body vs = none) :
    ∃ i, Opnd.fill [x, y] vs = [.int i, .int 0] := by
  simp only [opArith] at h
  split at h
  · rename_i x y hf
    split at h
    · cases h
    · cases h
    · rename_i he
      obtain ⟨i, rfl, rfl⟩ := fastArith_err he
      exact ⟨i, hf⟩
  · cases h

/-- A register the kernel reads is in the frame (`Supported`'s `regTop`). -/
theorem reads_lt {p : Proto} (hS : Supported p) {pc : Nat} {w : Word} {o : OpCode}
    {K : Kernel Value} (hf : p.fetch pc = some w) (hop : w.op? = some o)
    (hK : opKernel p pc w o = some K) {r : Nat} (hr : r ∈ K.reads) : r < p.maxstacksize := by
  have htop := supported_regTop hS hf
  simp only [regTop, kernel, hop, Option.bind_some, hK, Option.map_some, Option.getD_some] at htop
  refine Nat.lt_of_lt_of_le ?_ htop
  unfold Kernel.regTop
  have h1 : ∀ l : List Nat, r ∈ l → r < l.foldr (fun r m => max (r + 1) m) 0 := by
    intro l hl
    induction l with
    | nil => cases hl
    | cons a l ih =>
      rcases List.mem_cons.1 hl with rfl | hl
      · simp only [List.foldr_cons]; omega
      · simp only [List.foldr_cons]; have := ih hl; omega
  have h2 : ∀ (es : List KEdge) (z : Nat),
      z ≤ es.foldr (fun e m => max (max (e.defs.foldr (fun r m => max (r + 1) m) 0)
        (e.killLo + e.killN)) m) z := by
    intro es z
    induction es with
    | nil => exact Nat.le_refl _
    | cons e es ih => simp only [List.foldr_cons]; omega
  exact Nat.lt_of_lt_of_le (h1 _ hr) (h2 _ _)

/-- A read register's value is represented in its slot. -/
theorem slot_of_read {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word}
    (hA : ArmAt p c s w ins) (hS : Supported p) {o : OpCode} {K : Kernel Value}
    (hf : p.fetch s.pc = some ins) (hop : ins.op? = some o) (hK : opKernel p s.pc ins o = some K)
    {r : Nat} (hr : r ∈ K.reads) {v : Value} (hv : s.regs r = some v) :
    ValRepr w.mo w.ι (slotTag c.σ.mem (w.slot r)) (slotVal c.σ.mem (w.slot r)) v :=
  hA.core.stack r v (reads_lt hS hf hop hK hr) hv

/-- The error path of an `op_arith` arm by zero, from its stuck state (`R[C]`). -/
theorem divR_q {p : Proto} (hS : Supported p) {s : State} {ins : Word} {o : OpCode} {b : BinOp}
    {vs : List Value} (hf : p.fetch s.pc = some ins) (hop : ins.op? = some o)
    (hK : opKernel p s.pc ins o = some (opArith s.pc ins.a b [.reg ins.b, .reg ins.c]))
    (hvs : (opArith s.pc ins.a b [.reg ins.b, .reg ins.c]).reads.mapM s.regs = some vs)
    (hb : (opArith s.pc ins.a b [.reg ins.b, .reg ins.c]).body vs = none) :
    ∀ c' w, ArmAt p c' s w ins → DivZero BothInt dvR p c' s w ins := by
  intro c' w hA
  obtain ⟨i, hfill⟩ := opArith_zero hb
  simp only [opArith, Opnd.ports, List.mapM_cons, List.mapM_nil] at hvs
  cases hrb : s.regs ins.b <;> cases hrc : s.regs ins.c <;> simp [hrb, hrc] at hvs
  subst hvs
  simp only [Opnd.fill, List.cons.injEq, and_true] at hfill
  obtain ⟨rfl, rfl⟩ := hfill
  have hB := (slot_of_read hA hS hf hop hK (by simp [opArith, Opnd.ports]) hrb).tag_of_int
  have hC := (slot_of_read hA hS hf hop hK (by simp [opArith, Opnd.ports]) hrc).tag_of_int
  exact ⟨⟨hB.1, hC.1⟩, hC.2⟩

/-- The same with the divisor `K[C]`. -/
theorem divK_q {p : Proto} (hS : Supported p) {s : State} {ins : Word} {o : OpCode} {b : BinOp}
    {vs : List Value} {v : Value} (hf : p.fetch s.pc = some ins) (hop : ins.op? = some o)
    (hkv : kval p ins.c = some v)
    (hK : opKernel p s.pc ins o = some (opArith s.pc ins.a b [.reg ins.b, .imm v]))
    (hvs : (opArith s.pc ins.a b [.reg ins.b, .imm v]).reads.mapM s.regs = some vs)
    (hb : (opArith s.pc ins.a b [.reg ins.b, .imm v]).body vs = none) :
    ∀ c' w, ArmAt p c' s w ins →
      WithK (DivZero BothIntK dvK) p c' s w ins := by
  intro c' w hA
  obtain ⟨i, hfill⟩ := opArith_zero hb
  simp only [opArith, Opnd.ports, List.mapM_cons, List.mapM_nil] at hvs
  cases hrb : s.regs ins.b <;> simp [hrb] at hvs
  subst hvs
  simp only [Opnd.fill, List.cons.injEq, and_true] at hfill
  obtain ⟨rfl, rfl⟩ := hfill
  have hB := (slot_of_read hA hS hf hop hK (by simp [opArith, Opnd.ports]) hrb).tag_of_int
  have hC := (hA.core.kconst hkv).tag_of_int
  exact ⟨by simp [hkv], ⟨hB.1, hC.1⟩, hC.2⟩

/-- `forprep`'s integer zero step, from its stuck state. -/
theorem forprep_q {p : Proto} (hS : Supported p) {s : State} {ins : Word} {vs : List Value}
    (hf : p.fetch s.pc = some ins) (hop : ins.op? = some .FORPREP)
    (hvs : (forprepK s.pc ins).reads.mapM s.regs = some vs)
    (hz : ∀ i l st, vs = [i, l, st] → zeroStep i st = true) :
    ∀ c' w, ArmAt p c' s w ins → FpZero p c' s w ins := by
  intro c' w hA
  have hK : opKernel p s.pc ins .FORPREP = some (forprepK s.pc ins) := rfl
  simp only [forprepK, List.mapM_cons, List.mapM_nil] at hvs
  cases h1 : s.regs ins.a <;> cases h2 : s.regs (ins.a + 1) <;> cases h3 : s.regs (ins.a + 2) <;>
    simp [h1, h2, h3] at hvs
  subst hvs
  rename_i i _ st
  have hz := hz _ _ _ rfl
  cases i <;> cases st <;> simp [zeroStep] at hz
  subst hz
  have hI := (slot_of_read hA hS hf hop hK (by simp [forprepK]) h1).tag_of_int
  have hT := (slot_of_read hA hS hf hop hK (by simp [forprepK]) h3).tag_of_int
  exact ⟨hI.1, hT.1, hT.2⟩

/-- `forprep`'s float zero step at the arm's entry: the three control values,
`fltZeroStep` (the float loop, `'for' step is zero`). -/
def FpFltZ (_p : Proto) (_c : Config) (s : State) (_w : RelPtrs) (ins : Word) : Prop :=
  ∃ i l st, s.regs ins.a = some i ∧ s.regs (ins.a + 1) = some l ∧ s.regs (ins.a + 2) = some st ∧
    fltZeroStep i l st = true

/-- **Open: `forprep`'s float zero step's arm path** into `luaG_runerror`
with `'for' step is zero` (after `forprep`'s conversions: `luaV_tonumber_`
for a control value that is not a float, `__eqdf2` against `0.0`). The
three-float case is on the at-lemma route (`Lua/Vm/At/ForprepF.lean` reaches
`0x800092cc` with the message, its log inside `ErrW`); the coerced classes
call `luaV_tonumber_` (`FpCoerce_Statement`'s call node). -/
def FpFltZero_Statement : Prop := ArmErr .FORPREP FpFltZ symLuaGRunerror msgForZero

/-- `forprep`'s site: a `luaG_runerror` site that is not the integer zero
step is the float one. -/
theorem fltZero_of_site {pc : Nat} {ins : Word} {s : State} {vs : List Value}
    (hvs : (forprepK pc ins).reads.mapM s.regs = some vs) (hsite : Fault.site .forprep vs = .runerror)
    (hz : ¬ ∀ i l st, vs = [i, l, st] → zeroStep i st = true) :
    ∀ p c' w, FpFltZ p c' s w ins := by
  intro p c' w
  simp only [forprepK, List.mapM_cons, List.mapM_nil] at hvs
  cases h1 : s.regs ins.a <;> cases h2 : s.regs (ins.a + 1) <;> cases h3 : s.regs (ins.a + 2) <;>
    simp [h1, h2, h3] at hvs
  subst hvs
  rename_i i l st
  refine ⟨i, l, st, h1, h2, h3, ?_⟩
  have hz' : zeroStep i st = false := by
    cases e : zeroStep i st
    · rfl
    · exact absurd (fun i' l' st' h => by simp only [List.cons.injEq] at h; obtain ⟨rfl, -, rfl, -⟩ := h; exact e) hz
  simp only [Fault.site, hz', Bool.false_or] at hsite
  split at hsite
  · assumption
  · cases hsite

/-- **`luaG_runerror`'s error states, from its throw obligation.** -/
theorem runerrorSim (hT : RunerrorThrow) (hFz : FpFltZero_Statement) :
    ErrorSimAt .runerror := by
  intro p c s w o K vs φ hS hs hR hA hne hsite
  have hf := hA.fetch; have hop := hA.op; have hK := hA.kernel
  cases φ with
  | prim f os =>
    cases f
    case arith b =>
      have hm := hA.mem
      simp only [Fault.ops, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · simp only [opKernel, arithRR, Option.some.injEq] at hK; subst hK
        exact stuckOut_of_armErr (by decide) mod_err (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
          (divR_q hS hf hop hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRR, Option.some.injEq] at hK; subst hK
        exact stuckOut_of_armErr (by decide) idiv_err (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
          (divR_q hS hf hop hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRK, Option.map_eq_some_iff] at hK
        obtain ⟨v, hkv, rfl⟩ := hK
        exact stuckOut_of_armErr (by decide) modk_err (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
          (divK_q hS hf hop hkv hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRK, Option.map_eq_some_iff] at hK
        obtain ⟨v, hkv, rfl⟩ := hK
        exact stuckOut_of_armErr (by decide) idivk_err (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
          (divK_q hS hf hop hkv hA.kernel hA.reads hA.body)
    case tm b =>
      simp only [Fault.site] at hsite
      split at hsite
      · split at hsite
        · cases hsite
        · split at hsite <;> cases hsite
      · cases hsite
    all_goals (simp only [Fault.site] at hsite; (repeat' split at hsite) <;> cases hsite)
  | concat => simp [Fault.site] at hsite
  | call => simp [Fault.site] at hsite
  | forloop => exact absurd trivial hne
  | forprep =>
    have hm := hA.mem
    simp only [Fault.ops, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    by_cases hz : ∀ i l st, vs = [i, l, st] → zeroStep i st = true
    · exact stuckOut_of_armErr (by decide) forprep_err (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
        (forprep_q hS hf hop hA.reads hz)
    · exact stuckOut_of_armErr (by decide) hFz (hT _ (by simp [runerrMsgs])) hS hs hR hf hop
        (fun c' w' _ => fltZero_of_site hA.reads hsite hz p c' w')

/-- **Open: an error site's head**: from the relation at a stuck state the
site `e` raises, the machine reaches `luaG_errormsg` with the formatted
message pushed (`Kit.ErrMsgIn`, relative to the fetch head's context): the
arm's path to its helper (`luaT_trybinTM`, `luaV_objlen`,
`luaT_callorderTM`/`luaT_callorderiTM`, `luaV_concat` → `luaT_tryconcatTM`,
`forprep`'s `luaV_tonumber_`, `luaD_precall` → `luaD_tryfuncTM`), the
helper on the failing operands (no metamethod: the basic types' metatables
are `NULL`, the string metatable has no bitwise or order events), the
`luaG_*error` call (`varinfo`, `luaG_typeerror`, `luaG_runerror`'s
formatting; `lstrlib.c`'s `trymt` → `luaL_error` → `lua_error`). -/
def SiteHead_Statement (e : ErrSite) : Prop :=
  ∀ p c s w ins o K vs φ, Supported p → Reach p s → VmRelAt p c s w → StuckAt p s ins o K vs φ →
    ¬ φ.Escape vs → φ.site vs = e → ∃ c', Steps c c' ∧ Kit.ErrMsgIn ⟨p, c, s, w, ins⟩ c'

/-- **A site from its head and the shared tail.** -/
theorem errorSimAt_of_head {e : ErrSite} (hH : SiteHead_Statement e) (hT : Kit.ErrorTail_Statement) :
    ErrorSimAt e := by
  intro p c s ins o K vs φ hS hs ⟨w, hR⟩ hA hne hsite
  obtain ⟨c', hst, hM⟩ := hH p c s w ins o K vs φ hS hs hR hA hne hsite
  exact StuckOut.of_steps hst (hT ⟨p, c, s, w, ins⟩ c' hS hs hR.core hM)

/-- **What is left of `ErrorSim`** (lane F1-16): every site ends in the
shared tail from `luaG_errormsg` (`Kit.ErrorTail_Statement`), whose throw is
proved (`Kit.throw_land`) and whose unwind is `unwind`. `luaG_runerror`'s
sites have their arm paths proved (`runerrorSim`) but the float zero step's
(`fpFltZero`) and its formatting is `runerrorHead`; each other site is its
head into the tail (`SiteHead_Statement`). -/
structure ErrorSimRest : Prop where
  /-- `luaG_runerror`'s formatting (0x800092cc to `luaG_errormsg`), per message -/
  runerrorHead : ∀ msg ∈ runerrMsgs, Kit.RunerrorHead_Statement symLuaGRunerror msg
  /-- the tail after the throw: `luaD_pcall`'s error branch → `main`'s
  `fprintf(stderr)` (lane F1-26: `exit(2)` after it proved, `Kit.unwind_of`) -/
  unwind : Kit.UnwindRest
  /-- `forprep`'s float zero step's arm path -/
  fpFltZero : FpFltZero_Statement
  opinterror : SiteHead_Statement .opinterror
  tointerror : SiteHead_Statement .tointerror
  strarith : SiteHead_Statement .strarith
  typeerror : SiteHead_Statement .typeerror
  ordererror : SiteHead_Statement .ordererror
  concaterror : SiteHead_Statement .concaterror
  forerror : SiteHead_Statement .forerror
  callerror : SiteHead_Statement .callerror

/-- The shared tail of `ErrorSimRest`. -/
theorem ErrorSimRest.tail (h : ErrorSimRest) : Kit.ErrorTail_Statement :=
  Kit.errorTail_of_unwind (Kit.unwind_of h.unwind)

theorem errorSim_of_rest (h : ErrorSimRest) : ErrorSim :=
  ⟨runerrorSim (fun msg hm => Kit.throwFrom_of (h.runerrorHead msg hm) h.tail) h.fpFltZero,
    errorSimAt_of_head h.opinterror h.tail, errorSimAt_of_head h.tointerror h.tail,
    errorSimAt_of_head h.strarith h.tail, errorSimAt_of_head h.typeerror h.tail,
    errorSimAt_of_head h.ordererror h.tail, errorSimAt_of_head h.concaterror h.tail,
    errorSimAt_of_head h.forerror h.tail, errorSimAt_of_head h.callerror h.tail⟩

/-- **Layer A without escapes, from what is open**: the open arms, the
float paths, the return chain, and `ErrorSimRest`. -/
theorem vm_refinement_ne_of_rest (arms : OpenArms) (farms : FloatArms) (final : FinalSim)
    (err : ErrorSimRest) : vm_refinement_ne_Statement :=
  vm_refinement_ne_of_open arms farms final (errorSim_of_rest err)

/-- **Layer A without escapes, from what is open**, `FinalSim` discharged
(`finalSim`, lane F1-4): the open arms, the float paths and `ErrorSimRest`. -/
theorem vm_refinement_ne_of_rest' (arms : OpenArms) (farms : FloatArms) (err : ErrorSimRest) :
    vm_refinement_ne_Statement :=
  vm_refinement_ne_of_rest arms farms finalSim err

/-- **Layer A from what is open** (FLOAT-DESIGN.md S2: no `NoEscape`): the
open arms, the float paths and `ErrorSimRest`; the entry, `VARARGPREP`,
`FinalSim`, the proved arms and `luaG_runerror`'s arm paths are discharged. -/
theorem vm_refinement_of_open' (arms : OpenArms) (farms : FloatArms) (err : ErrorSimRest) :
    vm_refinement_Statement luaLayout :=
  vm_refinement_of_error arms farms (errorSim_of_rest err)

end Lua.Vm.Sim

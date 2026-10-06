import Lua.Vm.Sim.Stuck
import Lua.Vm.Sim.Kit.AtErr

/-!
# `luaG_runerror`'s error states: the arms' paths, and the throw obligation

The site `ErrSite.runerror` collects the stuck states of `n % 0`, `n // 0`
(`OP_MOD`, `OP_IDIV`, `OP_MODK`, `OP_IDIVK`) and `'for' step is zero`
(`OP_FORPREP`). For each, the machine runs from the fetch head through
dispatch and the arm's error path (`Kit/AtErr.lean`, the generated at-lemmas)
to the entry of `luaG_runerror`. What remains is that entry's summary,
`ThrowFrom symLuaGRunerror`: `luaG_runerror` formats the message
(`luaO_pushvfstring`, `luaG_addinfo`) and calls `luaG_errormsg` →
`luaD_throw` → `longjmp`; `lua_pcallk` returns `LUA_ERRRUN`, and `main`
prints the message to stderr and returns 2 (`c/src/main.c`), so `exit(2)`.

`runerrorSim : ThrowFrom symLuaGRunerror → ErrorSimAt .runerror`, and
`ErrorSimRest`, what is left of `ErrorSim` (`vm_refinement_ne_of_rest`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout Lua.Vm.Sim.At Lua.Vm.Sim.Kit
open Vsa.Machine (Config Steps)

/-- **The throw obligation at the error exit `f`** (keyed by its entry pc): a
run from a related reachable state that arrives at `f`'s entry diverges or
halts with a nonzero code. `f` does not return; its summary is the error
path `luaG_errormsg` → `luaD_throw` → `longjmp` → `luaD_rawrunprotected`
returns → `lua_pcallk` returns `LUA_ERRRUN` → `main` returns 2 → `exit(2)`. -/
def ThrowFrom (f : Nat) : Prop :=
  ∀ p c s c', Supported p → Reach p s → VmRel p c s → Steps c c' → ErrAt f c' → StuckOut c'

/-- **An error state by an arm's error path**: dispatch, the arm's run into
`f` (`ArmErr`), then `f`'s throw obligation. -/
theorem stuckOut_of_armErr {o : OpCode} {Q : Proto → Config → State → RelPtrs → Word → Prop}
    {f : Nat} (ho : o.toNat < Arms.jtEntries) (hE : ArmErr o Q f) (hT : ThrowFrom f)
    {p : Proto} {c : Config} {s : State} {ins : Word} (hS : Supported p) (hs : Reach p s)
    (hR : VmRel p c s) (hf : p.fetch s.pc = some ins) (hop : ins.op? = some o)
    (hq : ∀ c' w, ArmAt p c' s w ins → Q p c' s w ins) : StuckOut c := by
  obtain ⟨w, hRw⟩ := hR
  obtain ⟨c1, hs1, -, hA⟩ := dispatch hRw hf (by rw [opNum_of_op? hop]; exact ho)
  obtain ⟨c2, hs2, hE2⟩ := hE hS hA hf hop (hq c1 w hA)
  exact StuckOut.of_steps (hs1.trans hs2) (hT p c s c2 hS hs ⟨w, hRw⟩ (hs1.trans hs2) hE2)

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

/-- `forprep`'s zero step, from its stuck state. -/
theorem forprep_q {p : Proto} (hS : Supported p) {s : State} {ins : Word} {vs : List Value}
    (hf : p.fetch s.pc = some ins) (hop : ins.op? = some .FORPREP)
    (hvs : (forprepK s.pc ins).reads.mapM s.regs = some vs)
    (hz : Fault.site .forprep vs = .runerror) :
    ∀ c' w, ArmAt p c' s w ins → FpZero p c' s w ins := by
  intro c' w hA
  have hK : opKernel p s.pc ins .FORPREP = some (forprepK s.pc ins) := rfl
  simp only [forprepK, List.mapM_cons, List.mapM_nil] at hvs
  cases h1 : s.regs ins.a <;> cases h2 : s.regs (ins.a + 1) <;> cases h3 : s.regs (ins.a + 2) <;>
    simp [h1, h2, h3] at hvs
  subst hvs
  rename_i i _ st
  simp only [Fault.site] at hz
  cases i <;> cases st <;> simp [zeroStep] at hz
  subst hz
  have hI := (slot_of_read hA hS hf hop hK (by simp [forprepK]) h1).tag_of_int
  have hT := (slot_of_read hA hS hf hop hK (by simp [forprepK]) h3).tag_of_int
  exact ⟨hI.1, hT.1, hT.2⟩

/-- **`luaG_runerror`'s error states, from its throw obligation.** -/
theorem runerrorSim (hT : ThrowFrom symLuaGRunerror) : ErrorSimAt .runerror := by
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
        exact stuckOut_of_armErr (by decide) mod_err hT hS hs hR hf hop
          (divR_q hS hf hop hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRR, Option.some.injEq] at hK; subst hK
        exact stuckOut_of_armErr (by decide) idiv_err hT hS hs hR hf hop
          (divR_q hS hf hop hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRK, Option.map_eq_some_iff] at hK
        obtain ⟨v, hkv, rfl⟩ := hK
        exact stuckOut_of_armErr (by decide) modk_err hT hS hs hR hf hop
          (divK_q hS hf hop hkv hA.kernel hA.reads hA.body)
      · simp only [opKernel, arithRK, Option.map_eq_some_iff] at hK
        obtain ⟨v, hkv, rfl⟩ := hK
        exact stuckOut_of_armErr (by decide) idivk_err hT hS hs hR hf hop
          (divK_q hS hf hop hkv hA.kernel hA.reads hA.body)
    case tm b =>
      simp only [Fault.site] at hsite
      split at hsite
      · split at hsite
        · cases hsite
        · split at hsite <;> cases hsite
      · cases hsite
    all_goals simp [Fault.site] at hsite
  | concat => simp [Fault.site] at hsite
  | call => simp [Fault.site] at hsite
  | forloop => exact absurd trivial hne
  | forprep =>
    have hm := hA.mem
    simp only [Fault.ops, List.mem_cons, List.not_mem_nil, or_false] at hm
    subst hm
    simp only [opKernel, Option.some.injEq] at hK; subst hK
    exact stuckOut_of_armErr (by decide) forprep_err hT hS hs hR hf hop
      (forprep_q hS hf hop hA.reads hsite)

/-- **What is left of `ErrorSim`**: `luaG_runerror`'s throw obligation (its
error states' arm paths are proved, `runerrorSim`), and the other sites,
whose arms reach the error through a helper that may also return
(`luaT_trybinTM`, `luaV_objlen`, `luaT_callorderTM`, `luaV_concat`,
`luaD_precall`, `luaV_tonumber_`). -/
structure ErrorSimRest : Prop where
  /-- `luaG_runerror` (0x800092cc) never returns, and the error exits 2 -/
  runerror : ThrowFrom symLuaGRunerror
  opinterror : ErrorSimAt .opinterror
  tointerror : ErrorSimAt .tointerror
  strarith : ErrorSimAt .strarith
  typeerror : ErrorSimAt .typeerror
  ordererror : ErrorSimAt .ordererror
  concaterror : ErrorSimAt .concaterror
  forerror : ErrorSimAt .forerror
  callerror : ErrorSimAt .callerror

theorem errorSim_of_rest (h : ErrorSimRest) : ErrorSim :=
  ⟨runerrorSim h.runerror, h.opinterror, h.tointerror, h.strarith, h.typeerror, h.ordererror,
    h.concaterror, h.forerror, h.callerror⟩

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

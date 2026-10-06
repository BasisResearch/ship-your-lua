import Lua.Vm.Sim.Entry

/-!
# `OP_VARARGPREP` at the entry: the facts the arm reads (A1)

Every main chunk `luac` emits starts with `VARARGPREP 0`, which runs
`luaT_adjustvarargs(L, 0, ci, cl->p)`: with `L->top = ci->func + 1` (no
arguments) it sets `ci->u.l.nextraargs = 0`, copies the function's `TValue` one
slot up (`L->top++`), checks the stack room for `maxstacksize + 1` slots
(`luaD_checkstack`, which would call `luaD_growstack`), and moves `ci->func`
and `ci->top` one slot up; `luaV_execute` then reloads `base` (`updatebase`).

`VmRel` leaves `L->top` free (it is `Scratch`), so the arm is simulated only at
the entry state (`Lua.Vm.Sim.VarargSim`), from the facts `FreshAt` collects:

* the machine words the arm and its callee read: `L->top`, `8(sp)` (the
  closure `luaV_execute` saved), `cl->p`, `p->maxstacksize`, the function's
  slot, `L->stack_last`, `ci->func`, `ci->top`;
* the stack room (`VmEntryData.vararg_room`);
* the old slot 0's bytes as the complement holds them (it leaves the window);
* **the relation after the move** (`post`): the complement and ranges at the
  memory `varargMem` the stores leave, for the moved pointers
  (`RelPtrs.vmoved`), from the entry contract's `RuntimeReadyAt.vararg` and
  `VmEntryData.vararg_proto` by `relParts`, as at the entry.

`entry_fresh` proves them at the fetch head the prologue reaches.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (Config)

/-- **The relation's pointers after `OP_VARARGPREP`**: `ci->func` one slot up,
the complement the stores leave (`varargMem`), the moved witness, strings `ι`. -/
def RelPtrs.vmoved (w : RelPtrs) (ι : Strs) : RelPtrs :=
  ⟨w.L, w.ci, w.func + stackValueSize, w.pa, w.code, w.k, w.sp, varargMem w.mo w.ci w.rt, ι,
    w.rt.vmoved⟩

/-- **The entry-only facts** at the fetch head, for pointers `w` (the
module docstring). -/
structure FreshAt (p : Proto) (c : Config) (w : RelPtrs) : Prop where
  /-- `L->top = func + 1` (`RuntimeReadyAt.top`): no arguments -/
  top : bytesT8 c.σ.mem (w.L + stateTopOff) = BitVec.ofNat 64 (w.func + stackValueSize)
  /-- `L->stack_last - L->top > maxstacksize + 1` slots: no `luaD_growstack` -/
  room : w.func + stackValueSize * (3 + p.maxstacksize) ≤ w.rt.stackLast
  /-- the old slot 0 (which leaves the window) as the complement holds it -/
  pad : ∀ a, w.func + stackValueSize ≤ a → a < w.func + 2 * stackValueSize →
    bytesT1 c.σ.mem a = bytesT1 w.mo a
  /-- `8(sp)`: the closure the prologue saved -/
  clslot : bytesT8 c.σ.mem (w.sp + 8) = BitVec.ofNat 64 w.rt.cl
  /-- `cl->p` -/
  clp : bytesT8 c.σ.mem (w.rt.cl + lclosureProtoOff) = BitVec.ofNat 64 w.pa
  /-- `p->maxstacksize` -/
  msz : bytesT1 c.σ.mem (w.pa + protoMaxstacksizeOff) = BitVec.ofNat 8 p.maxstacksize
  /-- the function's slot: the closure and `LUA_VLCL` -/
  slot_val : bytesT8 c.σ.mem (w.func + tvalueValOff) = BitVec.ofNat 64 w.rt.cl
  slot_tag : bytesT1 c.σ.mem (w.func + tvalueTagOff) = BitVec.ofNat 8 vLcl
  /-- `L->stack_last`, `ci->func`, `ci->top` -/
  stack_last : bytesT8 c.σ.mem (w.L + stateStackLastOff) = BitVec.ofNat 64 w.rt.stackLast
  ci_func : bytesT8 c.σ.mem (w.ci + ciFuncOff) = BitVec.ofNat 64 w.func
  ci_top : bytesT8 c.σ.mem (w.ci + ciTopOff) = BitVec.ofNat 64 w.rt.ciTop
  rt_func : w.rt.func = w.func
  rt_proto : w.rt.proto = w.pa
  /-- `p->maxstacksize` lies outside the `CallInfo` (the `savedpc` and
  `nextraargs` stores miss it) -/
  pa_sep : w.pa + protoMaxstacksizeOff < w.ci ∨ w.ci + ciSize ≤ w.pa + protoMaxstacksizeOff
  /-- where the objects lie (`luaRuntimeReady`'s regions, in the complement) -/
  regions : VmRegionsAt w.mo w.L w.ci w.rt
  /-- the relation after the move: its complement and ranges -/
  post : ∃ ι, RelParts p (w.vmoved ι)

theorem AgreeOut.bytesT1 {m' m : Mem} {lo hi : Nat} (h : AgreeOut m' m lo hi) {a : Nat}
    (ha : a < lo ∨ hi ≤ a) : bytesT1 m' a = bytesT1 m a := by
  show (m'[a]?).getD 0 = (m[a]?).getD 0
  rw [h a ha]

/-- `varargMemV` keeps the image (`.text`, `.rodata` lie below every stored byte). -/
theorem FixedBytesLoaded.vararg {base size : Nat} {byte : Nat → BitVec 8} {m : Mem}
    (h : Vsa.Sim.Code.FixedBytesLoaded base size byte m) (hb : base + size ≤ tohostAddr)
    {ci func cl top : Nat} (hci : tohostAddr ≤ ci) (hf : tohostAddr ≤ func) :
    Vsa.Sim.Code.FixedBytesLoaded base size byte (varargMemV m ci func cl top) :=
  Vsa.Sim.Code.FixedBytesLoaded.transport h fun a _ h2 => varargMemV_out m ci func cl top (by
    simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff]
    omega)

/-- `FreshAt` reads the configuration only through its memory. -/
theorem FreshAt.of_mem {p : Proto} {c c' : Config} {w : RelPtrs} (h : FreshAt p c w)
    (hm : c'.σ.mem = c.σ.mem) : FreshAt p c' w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  rw [← hm] at h1 h3 h4 h5 h6 h7 h8 h9 h10 h11
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem rd8_insert_self (m : Mem) (x : Nat) (b : BitVec 8) : rd8 (m.insert x b) x = some b.toNat := by
  simp [rd8, rdLE]

theorem rd8_lt {m : Mem} {a v : Nat} (h : rd8 m a = some v) : v < 256 := by
  simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero] at h
  cases hb : m[a]? with
  | none => rw [hb] at h; cases h
  | some b =>
    rw [hb] at h
    simp at h
    have := b.isLt; omega

/-- **A framed prototype does not read the frame**: if `ProtoRepr` holds in
every memory agreeing with `m` off `VarargDirty`, then `p->maxstacksize` lies
off it (else a memory with that byte changed would break it). -/
theorem maxstack_not_dirty {m : Mem} {ci func pa code : Nat} {p : Proto}
    (h : ∀ m' : Mem, (∀ a, ¬ VarargDirty ci func a → m'[a]? = m[a]?) → ProtoAt m' pa p code) :
    ¬ VarargDirty ci func (pa + protoMaxstacksizeOff) := by
  intro hd
  have h1 := (h m (fun _ _ => rfl)).proto.maxstack
  have hlt := rd8_lt h1
  have h2 := (h (m.insert (pa + protoMaxstacksizeOff) (BitVec.ofNat 8 (p.maxstacksize + 1)))
    (fun a ha => by
      rw [Std.ExtHashMap.getElem?_insert, if_neg (by
        simp only [beq_iff_eq]; intro e; exact ha (e ▸ hd))])).proto.maxstack
  rw [rd8_insert_self, Option.some.injEq, BitVec.toNat_ofNat] at h2
  omega

/-- **The entry-only facts hold at the fetch head the prologue reaches.** -/
theorem entry_fresh {p : Proto} {c : Config} (hL : VmLoaded luaLayout p c) :
    ∃ c' w, Vsa.Machine.Steps c c' ∧ VmRelAt p c' State.init w ∧ FreshAt p c' w := by
  obtain ⟨c', w, e, h⟩ := entry_at hL
  have hE := h.entry
  have hRt := h.ready
  have hrg := hRt.regions
  have hr := h.rel.core.ranges
  have hroom := cstack_room
  have hsthi := hrg.stack_hi
  have hLhi := hrg.L_hi
  have hcihi := hrg.ci_hi
  have hclhi := hrg.cl_hi
  have hprhi := hrg.proto_hi
  have hfits := hE.frame_fits
  have hvr := hE.vararg_room
  have hsle := hRt.lua.stack_le
  have hag := h.agree
  obtain ⟨L, ci, func, pa, code, k, sp, mo, ι, rt⟩ := w
  obtain ⟨efunc, ecl, epa, ecode, esl, hmo, hsp, hrf, hrp, hrk⟩ :
      e.func = func ∧ e.cl = rt.cl ∧ e.pa = pa ∧ e.code = code ∧ e.stackLast = rt.stackLast ∧
      mo = c.σ.mem ∧ sp = RuntimeData.spEntry - execFrame ∧ rt.func = func ∧ rt.proto = pa ∧
      k = rt.k :=
    ⟨h.efunc, h.ecl, h.epa, h.ecode, h.esl, h.mo, h.sp, h.rt_func, h.rt_proto, h.rt_k⟩
  simp only at hE hRt hrg hr h hsthi hLhi hcihi hclhi hprhi hsle ⊢
  subst efunc epa ecode hmo hsp hrk
  rw [esl] at hfits hvr
  rw [hrf] at hsle
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hbase := hr.base_lo
  have hcilo := hr.ci_lo
  simp only [RelPtrs.base, stackValueSize, symHeapEnd, cStackBudget, RuntimeData.spEntry,
    execFrame] at hbase hcilo hroom hsthi
  simp only [RelPtrs.base, stackValueSize, symHeapEnd, stateSize, ciSize, lclosureUpvalsOff,
    protoCodeOff, cStackBudget, RuntimeData.spEntry, execFrame] at hLhi hcihi hclhi hprhi hfits hvr
  -- every word read lies in the heap, below the prologue's C frame
  have out8 : ∀ a, a + 8 ≤ 0x87fffe20 - 176 → bytesT8 c'.σ.mem a = bytesT8 c.σ.mem a :=
    fun a ha => hag.bytesT8 (by simp only [RuntimeData.spEntry, execFrame]; omega)
  have out1 : ∀ a, a < 0x87fffe20 - 176 → bytesT1 c'.σ.mem a = bytesT1 c.σ.mem a :=
    fun a ha => hag.bytesT1 (by simp only [RuntimeData.spEntry, execFrame]; omega)
  refine ⟨c', _, h.steps, h.rel,
    { top := ?_, room := ?_, pad := ?_, clslot := h.clslot, clp := ?_, msz := ?_, slot_val := ?_,
      slot_tag := ?_, stack_last := ?_, ci_func := ?_, ci_top := ?_, rt_func := hrf,
      rt_proto := hrp, pa_sep := ?_, regions := hRt.regions, post := ?_ }⟩
  · rw [out8 _ (by simp only [stateTopOff]; omega), bytesT8_of_rd64 hRt.top, hrf]
  · simp only [stackValueSize]; omega
  · intro a h1 h2
    rw [out1 _ (by simp only [stackValueSize] at h1 h2; omega)]
  · rw [out8 _ (by simp only [lclosureProtoOff]; omega), ← ecl, bytesT8_of_rd64 hE.cl_proto]
  · rw [out1 _ (by simp only [protoMaxstacksizeOff]; omega), bytesT1_of_rd8 hE.proto.maxstack]
  · rw [out8 _ (by simp only [tvalueValOff]; omega), ← ecl, bytesT8_of_rd64 hE.func_val]
  · rw [out1 _ (by simp only [tvalueTagOff]; omega)]
    exact bytesT1_of_rd8 hE.func_tag
  · rw [out8 _ (by simp only [stateStackLastOff]; omega), ← esl, bytesT8_of_rd64 hE.stack_last]
  · rw [out8 _ (by simp only [ciFuncOff]; omega), bytesT8_of_rd64 hE.ci_func]
  · rw [out8 _ (by simp only [ciTopOff]; omega), bytesT8_of_rd64 hRt.lua.ci_top]
  · have := maxstack_not_dirty hE.vararg_proto
    simp only [VarargDirty, ciSize, not_or, not_and, Nat.not_lt] at this
    simp only [ciSize]; omega
  · -- the relation after the stores, by `relParts` at `varargMem`
    have hdirty : ∀ a, ¬ VarargDirty ci e.func a →
        (varargMem c.σ.mem ci rt)[a]? = c.σ.mem[a]? := fun a ha => by
      simp only [varargMem]; rw [hrf]; exact varargMemV_out _ _ _ _ _ ha
    obtain ⟨ι', hP⟩ := relParts (L := L) (ci := ci) (sp := RuntimeData.spEntry - execFrame)
      (func := e.func + stackValueSize)
      (FixedBytesLoaded.vararg h.rel.core.comp.text Arms.text_below_tohost (by omega)
        (by rw [hrf]; omega))
      (FixedBytesLoaded.vararg h.rel.core.comp.rodata rodata_below_tohost (by omega)
        (by rw [hrf]; omega))
      (hE.vararg_proto _ hdirty) hRt.vararg (by simp only [RtPtrs.vmoved]; rw [hrf]) hrp rfl
      (by simp only [RtPtrs.vmoved, stackValueSize]; omega)
      (callers_congr hRt.cstack.callers fun a h1 h2 => hdirty a (by
        simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff, RuntimeData.spEntry] at h1 ⊢
        omega))
      (fun a ha => by
        have := callerLSlots_above a ha
        rw [bytesT8_congr fun i hi => hdirty _ (by
          simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff, RuntimeData.spEntry] at this ⊢
          omega)]
        exact bytesT8_of_rd64 (hRt.callerL a ha))
      ((rdLE_congr fun i hi => hdirty _ (by
        have b1 := hrg.ci_lo; have b2 := hrg.stack_lo
        simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff, symAtexit, symEnd] at b1 b2 ⊢
        omega)).trans hRt.stdio.atexit)
      ((rdLE_congr fun i hi => hdirty _ (by
        have b1 := hrg.ci_lo; have b2 := hrg.stack_lo
        simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff, symStdioExitHandler,
          symEnd] at b1 b2 ⊢
        omega)).trans hRt.stdio.exit_handler)
      (f0 := e.func) (Nat.le_add_right _ _) (by
        have h := envMem_of_entry hE hdirty (k := rt.k) (by
          have := hRt.vararg.regions.kArr
          simp only [RtPtrs.vmoved] at this; rw [hrp] at this; exact this)
        rw [ecl, esl] at h
        exact h)
    exact ⟨ι', hP⟩

/-- **The `VARARGPREP` clause**: at the entry state (the only reachable state at
a `VARARGPREP`, `reach_pc_zero`), `luaT_adjustvarargs` moves `ci->func` one
slot up and the machine is back at the fetch head with the successor
(`VmRel` at the new `func`). -/
def VarargSim : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {w : RelPtrs}, VmRelAt p c State.init w →
    FreshAt p c w → ∀ {ins : Word} {s' : State}, p.fetch 0 = some ins →
    ins.op? = some .VARARGPREP → Step binaryHost p State.init s' →
      ∃ c' n, 0 < n ∧ Vsa.Machine.StepsN n c c' ∧ VmRel p c' s'

end Lua.Vm.Sim

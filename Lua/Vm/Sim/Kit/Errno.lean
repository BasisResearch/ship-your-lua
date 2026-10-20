import Lua.Vm.Sim.Kit.CallClose

/-!
# `errno` changed by an arm (lane F1-F7)

libm's `fmod` stores `EDOM` to `errno` (`_REENT->_errno`, the first word of
`_impure_data`: `ErrnoW`) on its domain error, which `OP_MOD`/`OP_MODK`
reach for `x % 0.0` (Lua 5.4's `luai_nummod` calls `fmod` with `y = 0`; the
result is NaN, no error). The word lies outside the window, so the arm
changes the complement there. The relation after the arm is at the pointers
`w.after (errnoMo w.mo m) w.ι w.rt`: the complement with `errno` taken from
the final memory `m` (`errnoMo`), everything else the old one.

* `Complement.errno`: the complement survives, since nothing it states reads
  `errno`. Its region facts are the `CALL` invariant's (`CallInvAt`): the
  objects frozen on `F`, `FL` (in chunks in use or below `tohost`), the
  stdio state on `StdioFoot` (which excludes the allocator's words, `errno`
  among them), the heap on `HeapReads`; `exit` finds `errno` free
  (`ExitFree`).
* `Core.errnoF`: `Core.bleachF` with the final memory free at `errno` too.
* `AtFinE`, `AtFinE.close`: the fetch head's close (`AtFin`, `AtFin.close`)
  for a path that may store `errno`, at the pointers after it.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- `errno`'s address. -/
abbrev errnoA : Nat := symImpureData + reentErrnoOff

theorem errnoA_eq : errnoA = 0x8005d1b8 := rfl

/-- A byte at or above the heap is not `errno`. -/
theorem notErrno_of_heap {a : Nat} (h : heapStart ≤ a) : ¬ ErrnoW a := fun he => by
  simp only [ErrnoW, heapStart, symEnd, symImpureData, reentErrnoOff] at he h; omega

/-- A byte below `tohost` is not `errno`. -/
theorem notErrno_of_low {a : Nat} (h : a < symTohost) : ¬ ErrnoW a := fun he => by
  simp only [ErrnoW, symTohost, symImpureData, reentErrnoOff] at he h; omega

/-- (lane F1-19) A locale word is not `errno`. -/
theorem notErrno_of_locale {a : Nat} (h : (0x80000000 ≤ a ∧ a < symTohost) ∨ LocaleW a) : ¬ ErrnoW a :=
  fun he => by
  simp only [ErrnoW, LocaleW, symTohost, symImpurePtr, symImpureData, reentErrnoOff] at he h; omega

/-- (lane F1-19) A word of `_REENT`'s `_dtoa_r` state is not `errno`. -/
theorem notErrno_of_reent {a : Nat} (h : ReentWord a) : ¬ ErrnoW a := fun he => by
  simp only [ErrnoW, ReentWord, symImpureData, reentErrnoOff, reentResultOff, reentFreelistOff] at he h; omega

/-- **The complement with `errno` from `m`** (the zero fill: every RAM byte present). -/
noncomputable def errnoMo (mo m : Mem) : Mem := fillZeroMem (memPatch mo m errnoA 4)

theorem errnoMo_out {mo m : Mem} {a : Nat} (ha : ¬ ErrnoW a) : bytesT1 (errnoMo mo m) a = bytesT1 mo a := by
  unfold errnoMo
  rw [bytesT1_fill, bytesT1_memPatch_out (by simp only [ErrnoW, errnoA] at ha ⊢; omega)]

theorem errnoMo_in {mo m : Mem} {a : Nat} (ha : ErrnoW a) : bytesT1 (errnoMo mo m) a = bytesT1 m a := by
  unfold errnoMo
  simp only [ErrnoW, errnoA] at ha
  simp only [bytesT1_fill, bytesT1, getElem?_memPatch, if_pos (show errnoA ≤ a ∧ a < errnoA + 4 from ha)]

/-- The relation's pointers after an `errno` store. -/
noncomputable abbrev _root_.Lua.Vm.Sim.RelPtrs.errno (w : RelPtrs) (m : Mem) : RelPtrs :=
  w.after (errnoMo w.mo m) w.ι w.rt

section
variable {p : Proto} {w : RelPtrs}

/-- The frozen objects at the pointers after an `errno` store. -/
theorem _root_.Lua.Vm.Sim.StatFacts.errno {M : Mem} (h : StatFacts p w M) (m : Mem) :
    StatFacts p (w.errno m) M :=
  ⟨h.rodata, h.proto, h.proto_code, h.strs, fun ts ho => (h.env ts ho).mono fun _ _ hr => hr.after _ _ _,
    ⟨h.lua.hookmask, h.lua.errfunc, h.lua.nCcalls, h.lua.openupval, h.lua.tbclist, h.lua.stack,
    h.lua.stack_last, h.lua.g, h.lua.mt_nil, h.lua.mt_boolean, h.lua.mt_number, h.lua.errjmp, h.lua.frealloc,
    h.lua.gcstp, h.lua.mt_fn⟩, h.locale⟩

/-- The owned strings at the complement after an `errno` store. -/
theorem _root_.Lua.Vm.Sim.Complement.errno_strs (hc : Complement p w) (M : Mem) :
    ∀ ts s, w.ι.own ts s → TStringRepr (errnoMo w.mo M) ts s := by
  obtain ⟨ph, F, FL, ls, hI⟩ := hc.call
  refine (hI.stat (memPatch w.mo M errnoA 4) fun a ha => bytesT1_memPatch_out ?_).strs
  have := (hI.stat_in a ha).elim (fun hk => notErrno_of_heap hk.lo) notErrno_of_locale
  simp only [ErrnoW, errnoA] at this ⊢; omega

/-- A value's representation at the complement after an `errno` store. -/
theorem _root_.Lua.Vm.Sim.ValRepr.errno (hc : Complement p w) (M : Mem) {t : BitVec 8} {x : BitVec 64}
    {v : Value} (h : ValRepr w.mo w.ι t x v) : ValRepr (errnoMo w.mo M) w.ι t x v :=
  h.transfer (hc.errno_strs M)

/-- **The complement survives an `errno` store.** -/
theorem _root_.Lua.Vm.Sim.Complement.errno (hc : Complement p w) (hr : Ranges p w) (M : Mem) :
    Complement p (w.errno M) := by
  obtain ⟨ph, F, FL, ls, hI⟩ := hc.call
  have hd := hI.dense
  have hB : heapStart = 0x8006ecd0 := rfl
  have nK : ∀ {a}, Kept w.rt.hix ph a → ¬ ErrnoW a := fun hk => notErrno_of_heap hk.lo
  have ag : ∀ a, ¬ ErrnoW a → bytesT1 (errnoMo w.mo M) a = bytesT1 w.mo a := fun a ha => errnoMo_out ha
  -- the patched memory before its fill
  have agP : ∀ a, ¬ ErrnoW a → bytesT1 (memPatch w.mo M errnoA 4) a = bytesT1 w.mo a := fun a ha =>
    bytesT1_memPatch_out (by simp only [ErrnoW, errnoA] at ha ⊢; omega)
  have rdT : ∀ a n, 0x80000000 ≤ a → a + n ≤ 0x88000000 → (∀ j, j < n → ¬ ErrnoW (a + j)) →
      rdLE (errnoMo w.mo M) a n = rdLE w.mo a n := fun a n h1 h2 hj =>
    rdLE_fill hd h1 h2 fun j hj' => agP _ (hj j hj')
  have nF : ∀ a, F a → ¬ ErrnoW a := fun a ha =>
    (hI.stat_in a ha).elim nK notErrno_of_locale
  have nFL : ∀ a, FL a → ¬ ErrnoW a := fun a ha => nK (hI.lits_in a ha)
  have SF : StatFacts p w (errnoMo w.mo M) := hI.stat _ fun a ha => agP a (nF a ha)
  have hL : heapStart ≤ w.L := (hI.L_in w.L (Nat.le_refl _) (by simp only [stateSize]; omega)).lo
  have hci : heapStart ≤ w.ci := (hI.ci_in w.ci (Nat.le_refl _) (by simp only [ciSize]; omega)).lo
  have hcit := hr.ci_top; have hLt := hr.L_top
  have e1 : ciSize = 64 := rfl
  have e2 : stateSize = 200 := rfl
  have e3 : RuntimeData.spEntry - cStackBudget = 0x87fefe20 := rfl
  rw [e1, e3] at hcit; rw [e2, e3] at hLt
  have footE : ∀ a, StdioFoot a → ¬ ErrnoW a := fun a hf he => hf.2 (by
    simp only [ErrnoW, symImpureData, reentErrnoOff] at he
    exact .inl ⟨by omega, by omega⟩)
  have bufE : ∀ a, ph.Buf a → ¬ ErrnoW a := by
    intro a hb'
    cases hI.io with
    | up _ _ hb _ => simp only [StdoutPh.Buf, Rng] at hb'; have := hb.lo; exact notErrno_of_heap (by omega)
    | boot => simp only [StdoutPh.Buf] at hb'
    | fresh => simp only [StdoutPh.Buf] at hb'
  -- reads of the `CallInfo`, the `lua_State` and the C stack
  have ciRd : ∀ o n, o + n ≤ 64 → rdLE (errnoMo w.mo M) (w.ci + o) n = rdLE w.mo (w.ci + o) n :=
    fun o n h => rdT _ _ (by omega) (by omega) fun j _ => notErrno_of_heap (by omega)
  have LRd : ∀ o n, o + n ≤ 200 → rdLE (errnoMo w.mo M) (w.L + o) n = rdLE w.mo (w.L + o) n :=
    fun o n h => rdT _ _ (by omega) (by omega) fun j _ => notErrno_of_heap (by omega)
  have upRd : ∀ a n, 0x87fefe20 ≤ a → a + n ≤ 0x88000000 →
      rdLE (errnoMo w.mo M) a n = rdLE w.mo a n := fun a n h1 h2 =>
    rdT _ _ (by omega) h2 fun j _ => notErrno_of_heap (by omega)
  have hlua := hc.runtime.lua
  have SFc := SF.lua
  refine
    { text := fun o ho => fillZeroMem_some (by
        have := Arms.text_below_tohost
        have hTH : tohostAddr = 0x8005c6c0 := rfl
        rw [getElem?_memPatch_out (by simp only [errnoA, symImpureData, reentErrnoOff]; omega)]
        exact hc.text o ho)
      rodata := SF.rodata
      proto := SF.proto
      proto_code := SF.proto_code
      code_word := fun i ins hf => by
        obtain ⟨hsz, hwords⟩ := SF.proto.code SF.proto_code
        obtain ⟨hlt, hi⟩ := List.getElem?_eq_some_iff.1 hf
        show bytesT4 (errnoMo w.mo M) (w.code + 4 * i) = ins
        rw [bytesT4_of_rd32 (hwords i hlt), hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      func_word := (bytesT8_congrT fun j _ => ag _ (notErrno_of_heap (by simp only [ciFuncOff]; omega))).trans
        hc.func_word
      trap_word := (bytesT4_congrT fun j _ => ag _ (notErrno_of_heap (by simp only [ciTrapOff]; omega))).trans
        hc.trap_word
      runtime := ⟨hc.runtime.func, ?_, ?_, ?_⟩
      kconst := fun i v hv => ?_
      own := fun ts s ho => by
        obtain ⟨cc, hcc⟩ := hc.own ts s ho
        exact ⟨cc, hcc.walk, hcc.inuse, hcc.lo, hcc.hi, hcc.out⟩
      callers := fun sg hs i hi => ?_
      callerL := fun a ha => ?_
      exit := fun M' o c q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 hM h =>
        hc.exit M' o c q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27
          (fun a ha => (hM a ha).trans (ag a fun he => ha (.inr (.inr (.inr (.inr he)))))) h
      env := fun ts ho => (SF.env ts ho).mono fun _ _ hr' => hr'.after _ _ _
      call := ⟨ph, F, FL, ls, ?_⟩ }
  · -- the Lua state
    refine ⟨SFc.hookmask, (ciRd ciTrapOff 4 (by decide)).trans hlua.trap, SFc.errfunc,
      SFc.nCcalls, SFc.openupval, SFc.tbclist, SFc.stack, SFc.stack_last,
      (ciRd ciFuncOff 8 (by decide)).trans hlua.func, hlua.stack_le,
      (ciRd ciTopOff 8 (by decide)).trans hlua.ci_top, hlua.ci_top_le,
      (ciRd ciCallstatusOff 2 (by decide)).trans hlua.callstatus,
      (ciRd ciNresultsOff 2 (by decide)).trans hlua.nresults,
      (ciRd ciPreviousOff 8 (by decide)).trans hlua.previous, ?_, SFc.g, SFc.mt_nil, SFc.mt_boolean,
      SFc.mt_number, (LRd stateCiOff 8 (by decide)).trans hlua.lci⟩
    have e := ciRd ciNextOff 8 (by decide)
    rcases hlua.next with h0 | ⟨nci, hn, hN⟩
    · exact .inl (e.trans h0)
    · refine .inr ⟨nci, e.trans hn, hN.lo, hN.hi, hN.al, ?_⟩
      have := hN.lo; have := hN.hi
      simp only [symEnd, ciPreviousOff, ciSize, RuntimeData.spEntry, cStackBudget] at *
      exact (rdT _ _ (by omega) (by omega) fun j _ => notErrno_of_heap (by omega)).trans hN.previous
  · -- the heap
    exact hc.runtime.heap.ofTotal fun a hr' _ => agP a fun he => by
      simp only [HeapReads, ErrnoW, symImpureData, reentErrnoOff, heapStart, symEnd, heapEnd, symMallocAv,
        symMallocSbrkBase, symBrk, symMallocTopPad, symMallocMaxSbrked, symMallocMallinfo] at hr' he
      omega
  · -- the error handler (`L->errorJmp`, the `lua_longjmp` on the C stack)
    have he := hc.runtime.error_jmp
    have hj : RuntimeData.ljAddr = 0x87fffe60 := rfl
    exact ⟨SFc.errjmp, (upRd _ 8 (by simp only [ljPreviousOff]; omega) (by simp only [ljPreviousOff]; omega)).trans he.previous,
      (upRd _ 8 (by simp only [ljBOff, RuntimeData.jbRa]; omega) (by simp only [ljBOff, RuntimeData.jbRa]; omega)).trans he.ret,
      (upRd _ 8 (by simp only [ljBOff, RuntimeData.jbSp]; omega) (by simp only [ljBOff, RuntimeData.jbSp]; omega)).trans he.sp,
      fun i hi => by
        rw [show rd64 (errnoMo w.mo M) _ = rd64 w.mo _ from
          upRd _ 8 (by simp only [ljBOff, RuntimeData.jbS0]; omega) (by simp only [ljBOff, RuntimeData.jbS0]; omega)]
        exact he.saved i hi⟩
  · -- the constants
    have hk := hc.kconst i v hv
    have hi : i < p.k.length := by
      simp only [kval, Proto.const, Option.bind_eq_some_iff] at hv
      obtain ⟨_, hc', _⟩ := hv
      exact (List.getElem?_eq_some_iff.1 hc').1
    have kb : ∀ j, j < 16 → bytesT1 (errnoMo w.mo M) (w.k + stackValueSize * i + j) =
        bytesT1 w.mo (w.k + stackValueSize * i + j) := fun j hj =>
      ag _ (nF _ (by
        have := hI.kslots (tvalueSize * i + j) (by simp only [tvalueSize] at *; omega)
        simp only [stackValueSize, tvalueSize] at this ⊢; rwa [Nat.add_assoc]))
    have et : slotTag (errnoMo w.mo M) (w.k + stackValueSize * i) = slotTag w.mo (w.k + stackValueSize * i) :=
      kb tvalueTagOff (by decide)
    have ev : slotVal (errnoMo w.mo M) (w.k + stackValueSize * i) = slotVal w.mo (w.k + stackValueSize * i) :=
      bytesT8_congrT fun j hj => by
        simpa only [Nat.add_assoc] using kb (tvalueValOff + j) (by simp only [tvalueValOff]; omega)
    show ValRepr (errnoMo w.mo M) w.ι (slotTag (errnoMo w.mo M) (w.k + stackValueSize * i))
      (slotVal (errnoMo w.mo M) (w.k + stackValueSize * i)) v
    rw [et, ev]; exact hk.transfer SF.strs
  · -- the caller frames
    obtain ⟨hlo, hhi⟩ := callerFrames_above sg hs
    have hb := hc.callers sg hs i hi
    have hsp : RuntimeData.spEntry = 0x87fffe20 := rfl
    show (errnoMo w.mo M)[sg.1 + i]? = _
    unfold errnoMo
    rw [fill_get _ (a := sg.1 + i) (by omega) (by omega), agP _ (notErrno_of_heap (by omega))]
    simp only [bytesT1, hb, Option.getD_some]
  · have := callerLSlots_above a ha
    have hsp : RuntimeData.spEntry = 0x87fffe20 := rfl
    exact (bytesT8_congrT fun j _ => ag _ (notErrno_of_heap (by omega))).trans (hc.callerL a ha)
  · -- the `CALL` invariant
    have hP := hI.cells
    exact
      { dense := fun a h1 h2 => by
          show (errnoMo w.mo M)[a]?.isSome = true
          unfold errnoMo; rw [fill_get _ h1 (by omega)]; rfl
        io := hI.io.congrA (fun a ha => ag a (ha.elim (footE a) (bufE a)))
          (fun hn => hI.io.room hn) (fun _ h => h)
        pend := hI.pend
        cells := ⟨(bytesT8_congrT fun j _ => ag _ (fun he => by
              simp only [ErrnoW, symImpureData, reentErrnoOff] at he; omega)).trans hP.impure,
            (bytesT8_congrT fun j _ => ag _ (fun he => by
              simp only [ErrnoW, symImpureData, reentErrnoOff] at he; omega)).trans hP.stdout,
            by rw [bytesAt_congr fun j _ => ag _ (fun he => by
              simp only [ErrnoW, symImpureData, reentErrnoOff] at he; omega)]; exact hP.tab,
            by rw [bytesAt_congr fun j _ => ag _ (fun he => by
              simp only [ErrnoW, symImpureData, reentErrnoOff] at he; omega)]; exact hP.nl⟩
        room := fun hh => hI.room (hh.imp id fun h0 => (ciRd ciNextOff 8 (by decide)).symm.trans h0)
        atexit := (bytesT8_congrT fun j _ => ag _ (fun he => by
            simp only [ErrnoW, symImpureData, reentErrnoOff, symAtexit] at he; omega)).trans hI.atexit
        stat := (hI.stat.trans fun a ha => ag a (nF a ha)).conseq fun _ h => h.errno M
        stat_in := hI.stat_in
        stat_apart := hI.stat_apart
        fits := hI.fits
        growFree := hI.growFree
        g_al := hI.g_al
        kslots := hI.kslots
        lits := hI.lits.trans fun a ha => ag a (nFL a ha)
        lits_in := hI.lits_in
        lits_apart := hI.lits_apart
        lit_strs := hI.lit_strs
        marks := hI.marks
        lit_marks := hI.lit_marks
        cache := hI.cache.congr fun a h1 h2 => ag a (nK (hI.g_in a (by omega) h2))
        L_in := hI.L_in
        g_in := hI.g_in
        ci_in := hI.ci_in
        stack_in := hI.stack_in
        nci := fun n hn h0 => by
          have h := hI.nci n ((ciRd ciNextOff 8 (by decide)).symm.trans hn) h0
          exact ⟨h.kept, h.foot, h.L, h.g, h.ci, h.stack, h.lits⟩
        objs := ⟨hI.objs.g_L, hI.objs.g_ci, hI.objs.g_stack, hI.objs.ci_stack, hI.objs.lit_L,
          hI.objs.lit_g, hI.objs.lit_ci, hI.objs.lit_stack, hI.objs.L_stack⟩
        alloc := by
          obtain ⟨B, hA⟩ := hI.alloc
          -- (lane F1-19) the `CALL` invariant's `X` reads only `ci->next`
          have hX : ∀ a, CallX0 (w.errno M) F a → CallX0 w F a := fun a h => by
            rcases h with h | h | h | h | h | ⟨n, hn, h0, h1⟩ | h
            · exact .inl h
            · exact .inr (.inl h)
            · exact .inr (.inr (.inl h))
            · exact .inr (.inr (.inr (.inl h)))
            · exact .inr (.inr (.inr (.inr (.inl h))))
            · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨n, (ciRd ciNextOff 8 (by decide)).symm.trans hn, h0, h1⟩)))))
            · exact .inr (.inr (.inr (.inr (.inr (.inr h)))))
          exact .intro B ⟨(hA.strt.trans fun a ha => ag a (nFL a ha)).conseq fun M' hM rt hrt =>
              (hM rt hrt).weaken (fun _ h => h) (fun a _ h => h.imp (hX a) id) fun _ _ h => h,
            hA.big.trans fun a ha => ag a (ha.elim (fun hb => nK (hA.big_in a hb)) notErrno_of_reent),
            hA.big_in, fun a hb hx => hA.big_x a hb (hX a hx), hA.big_fl, hA.big_lit⟩ }

end

end Lua.Vm.Sim.Kit

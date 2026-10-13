import Lua.Vm.Sim.Kit.Precall
import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Sim.Kit.Multi
import Lua.Vm.Arms.Segs.G13
import Lua.Vm.Arms.Segs.G14

/-!
# `OP_CALL print`: the arm around `luaD_precall` (lane F1-12)
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (Config Steps StepsN)

/-- `OP_CALL`'s edge (`callK`): the `C - 1` results, the frame above them killed. -/
abbrev callEdge (p : Proto) (pc : Nat) (ins : Word) : KEdge :=
  { tgt := pc + 1, defs := List.range' ins.a (ins.c - 1), killLo := ins.a + ins.c - 1,
    killN := p.maxstacksize - (ins.a + ins.c - 1) }

/-- **`OP_CALL`'s step**: `print` with `B - 1` arguments, the `C - 1`
results nil, the frame above them killed, the line printed. -/
theorem call_step {p : Proto} {s s' : State} {ins : Word} (hf : p.fetch s.pc = some ins)
    (hop : ins.op? = some .CALL) (h : Step binaryHost p s s') :
    ∃ args, ins.b ≠ 0 ∧ ins.c ≠ 0 ∧
      (List.range' ins.a ins.b).mapM s.regs = some (.builtin .print :: args) ∧
      s' = ⟨s.pc + 1, writeDefs (List.range' ins.a (ins.c - 1)) (List.replicate (ins.c - 1) .nil)
        (fun j => if (callEdge p s.pc ins).kills j then none else s.regs j),
        s.out ++ printLine binaryHost args⟩ := by
  have hk := (kstep_iff _ _).1 h
  by_cases hbc : ins.b ≠ 0 ∧ ins.c ≠ 0
  · rcases hv : (List.range' ins.a ins.b).mapM s.regs with _ | vs
    · simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
    · match vs, hv with
      | .builtin .print :: args, hv =>
        simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
        exact ⟨args, hbc.1, hbc.2, rfl, hk.symm⟩
      | [], hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
      | .nil :: _, hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
      | .bool _ :: _, hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
      | .int _ :: _, hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
      | .flt _ _ :: _, hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
      | .str _ :: _, hv => simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, callK, hbc, hv] at hk
  · simp [kstep, decide?, kernelAt, hf, kernel, hop, opKernel, hbc] at hk

/-! ## The arm's premise: `luaD_precall` on `print`, in the relation's terms -/

/-- The relation's pointers after a call: a new complement, strings and runtime. -/
abbrev _root_.Lua.Vm.Sim.RelPtrs.after (w : RelPtrs) (mo : Mem) (ι : Strs) (rt : RtPtrs) : RelPtrs :=
  ⟨w.L, w.ci, w.func, w.pa, w.code, w.k, w.sp, mo, ι, rt⟩

/-- **The memory at `OP_CALL`'s `jal luaD_precall`**: the head's, with
`L->top = ra + B` and `ci->u.l.savedpc` (both `Scratch`). -/
abbrev callMem (m : Mem) (w : RelPtrs) (pc : Nat) (ins : Word) : Mem :=
  writeMap8 (writeMap8 m (w.L + stateTopOff) (sdData_val (BitVec.ofNat 64 (w.slot ins.a + 16 * ins.b))))
    (w.ci + ciSavedpcOff) (sdData_val (BitVec.ofNat 64 (w.code + 4 * (pc + 1))))

/-- **What `print` leaves for the relation** (`m0` the head's memory, `m'`
the memory at the return, `out` the console's new bytes, `w'` the relation's
pointers after the call): the line printed, the complement of the memory at
the return, the C frame of `luaV_execute` and the registers below `R[A]`
kept, the results nil, `ci->u.l.trap = 0`, every register's representation
carried over. -/
structure CallOut (p : Proto) (w : RelPtrs) (m0 : Mem) (ins : Word) (args : List Value) (m' : Mem)
    (out : List (BitVec 8)) (w' : RelPtrs) : Prop where
  line : charsOf out = printLine binaryHost args
  comp : Complement p w'
  frame : ∀ a, ¬ Win p w a → bytesT1 m' a = bytesT1 w'.mo a
  above : ∀ a, w.sp ≤ a → bytesT1 m' a = bytesT1 m0 a
  below : ∀ a, w.base ≤ a → a < w.slot ins.a → bytesT1 m' a = bytesT1 m0 a
  nil : ∀ j, ins.a ≤ j → j < ins.a + ins.c - 1 → slotTag m' (w.slot j) = BitVec.ofNat 8 vNil
  trap : bytesT4 m' (w.ci + ciTrapOff) = 0#32
  vrepr : ∀ t x v, ValRepr w.mo w.ι t x v → ValRepr w'.mo w'.ι t x v
  /-- the closure `luaV_execute` saved at `8(sp)` (`Core.clptr`) -/
  cl : w'.rt.cl = w.rt.cl

/-- **Named premise: `luaD_precall` on `print` from `OP_CALL`**, on states
with the invariant `I`: from the `jal` (`L`, `ra = R[A]`, `C - 1`), back at
`0x8001c7d8` with `0` and the frame, the console gaining the line, the
relation's facts for the memory it leaves (`CallOut`, at the same pointers)
and `I` again. Supplied by `luaD_precall`'s C path (`precall_reuse`,
`precall_ext`), `luaB_print` (`print_sum`), `luaD_poscall` and the relation
facts. -/
def PrintCall_Statement (I : Proto → RelPtrs → Prop) : Prop :=
  ∀ {p : Proto} {c : Config} {s : State} {w : RelPtrs} {ins : Word} {args : List Value}
    (f : AbiFrame) (o : Array String),
    Supported p → VmRelAt p c s w → I p w → p.fetch s.pc = some ins → ins.op? = some .CALL →
    ins.b ≠ 0 → ins.c ≠ 0 → (List.range' ins.a ins.b).mapM s.regs = some (.builtin .print :: args) →
    Triple (SegSt 0x8000aab4#64 (callPre [⟨Register.x10, BitVec.ofNat 64 w.L⟩,
        ⟨Register.x11, BitVec.ofNat 64 (w.slot ins.a)⟩, ⟨Register.x12, BitVec.ofNat 64 (ins.c - 1)⟩]
        w.sp 0x8001c7d8#64 f) (ArmPay (callMem c.σ.mem w s.pc ins) o))
      (fun c' => ∃ m' out mo ι rt, wrRet 0x8001c7d8#64 w.sp 0 f m' (pushes o out) c' ∧
        CallOut p w c.σ.mem ins args m' out (w.after mo ι rt) ∧ I p (w.after mo ι rt))

/-- **An arm's simulation on the states with an invariant `I`** of the
relation's pointers, which it keeps. -/
def SimArmInv (o : OpCode) (I : Proto → RelPtrs → Prop) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State} {w : RelPtrs}, VmRelAt p c s w → I p w →
    ∀ {ins : Word}, p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      ∃ c' n w', 0 < n ∧ StepsN n c c' ∧ VmRelAt p c' s' w' ∧ I p w'

/-- The ranges at the pointers after a call (the window is the pointers'). -/
theorem _root_.Lua.Vm.Sim.Ranges.after {p : Proto} {w : RelPtrs} (hr : Ranges p w) (mo : Mem) (ι : Strs)
    (rt : RtPtrs) : Ranges p (w.after mo ι rt) :=
  ⟨hr.sp_eq, hr.base_lo, hr.base_hi, hr.base_al, hr.code_lo, hr.code_hi, hr.ci_lo, hr.ci_hi,
    hr.L_lo, hr.code_out, hr.ci_out, hr.k_lo, hr.k_hi, hr.k_al, hr.k_out, hr.frame_sep, hr.k_sep,
    hr.ci_sep, hr.L_sep, hr.ci_top, hr.L_top, hr.slots_top, hr.L_al, hr.ci_al, hr.L_sep_ci,
    hr.k_top⟩

/-- `R[A]`'s address (`RA(i)`: `srliw 7`, `zext.b`, `slli 4`, `add base`). -/
theorem call_ra (base : Nat) (ins : Word) :
    BitVec.ofNat 64 base + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0) (0x07#5))) &&&
      sign_extend (m := 64) (0x0ff#12)) (Sail.BitVec.extractLsb (0x04#6) 5 0)
      = BitVec.ofNat 64 (base + 16 * ins.a) := slot_addr base 7 ins (by decide) (by decide)

/-- `L->top = ra + B` (`slli 4`, `add`). -/
theorem call_top (base : Nat) (ins : Word) :
    BitVec.ofNat 64 base + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0) (0x07#5))) &&&
      sign_extend (m := 64) (0x0ff#12)) (Sail.BitVec.extractLsb (0x04#6) 5 0) +
    shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0) (0x10#5))) &&&
      sign_extend (m := 64) (0x0ff#12)) (Sail.BitVec.extractLsb (0x04#6) 5 0)
      = BitVec.ofNat 64 (base + 16 * ins.a + 16 * ins.b) := by
  rw [call_ra, extract_sext, field8 ins 16 (by decide) (by decide), shl_ofNat _ 4 (by decide),
    BitVec.ofNat_add_ofNat]
  simp only [Word.b, Word.field]; congr 1; omega

/-- `nresults = C - 1` (`srliw 24`, `addiw -1`). -/
theorem call_nres (ins : Word) (hc : ins.c ≠ 0) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0) (0x18#5))) + sign_extend (m := 64) (0xfff#12))
      31 0) = BitVec.ofNat 64 (ins.c - 1) := by
  rw [extract_sext, sext_shr ins 24 (by decide) (by decide)]
  have hlt : ins.toNat >>> 24 < 256 := by
    rw [Nat.shiftRight_eq_div_pow]; have := ins.isLt; omega
  have hcv : ins.c = ins.toNat >>> 24 := by
    simp only [Word.c, Word.field]; omega
  have e : BitVec.ofNat 64 (ins.toNat >>> 24) + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 (ins.c - 1) := by
    apply BitVec.eq_of_toNat_eq
    have h1 : (sign_extend (m := 64) (0xfff#12)).toNat = 2 ^ 64 - 1 := by decide
    rw [BitVec.toNat_add, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  rw [e]; exact sext32_ofNat _ (by omega)

set_option hygiene false in
local macro_rules | `(tactic| kit_guard_ext) => `(tactic| first | exact hgB | decide)

/-- **`OP_CALL print` on the states with the invariant `I`**, from
`luaD_precall`'s summary in the relation's terms (`PrintCall_Statement I`):
dispatch, the arm's `L->top = ra + B` and `savepc`, the `jal`, the summary,
the `beqz` on its `0` (a C call), `updatetrap` and the jump back to the
fetch head; the relation at the summary's pointers. -/
theorem sim_CALL_of {I : Proto → RelPtrs → Prop} (hP : PrintCall_Statement I) : SimArmInv .CALL I := by
  intro p hS c s s' w hR hI ins hf hop hstep
  obtain ⟨args, hb, hcc, hargs, rfl⟩ := call_step hf hop hstep
  have hnum := opNum_of_op? hop
  obtain ⟨c1, hs1, hlt1, hA, hm1⟩ := dispatchM hR hf (by rw [hnum]; decide)
  have hc := hA.core
  have hr := hc.ranges
  have htop := supported_regTop hS hf
  simp [regTop, kernel, hop, opKernel, Kernel.regTop, callK, hb, hcc] at htop
  have hb1 : ins.a + ins.b ≤ p.maxstacksize := by
    obtain ⟨b', hb'⟩ : ∃ b', ins.b = b' + 1 := ⟨ins.b - 1, by omega⟩
    have := foldr_range_top b' ins.a
    rw [hb'] at htop; omega
  have hc1 : ins.a + ins.c - 1 ≤ p.maxstacksize := by omega
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hr.base_lo; have := hr.base_hi; have := hr.base_al; have := hr.ci_lo
  have := hr.ci_hi; have := hr.code_hi; have := hr.code_lo; have := fetch_lt hf
  have := ins.isLt; have := hr.L_lo; have := hr.ci_sep; have := hr.L_sep; have := hr.ci_top
  have := hr.L_top; have := hr.slots_top; have := hr.sp_eq; have := hr.L_al; have := hr.ci_al
  have := hr.frame_sep
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame] at *
  have h0 := hA.seg (pc := 0x8001c79c#64) (by rw [hnum]; decide)
  have acc := Steps.refl c1
  have hgB : (((sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) ins) 31 0)
      (0x10#5))) &&& sign_extend (m := 64) (0x0ff#12)) == (0#64)) = false := by
    rw [extract_sext, field8 ins 16 (by decide) (by decide)]
    simp only [beq_eq_false_iff_ne, ne_eq]
    intro e; have := congrArg BitVec.toNat e
    simp only [Word.b, Word.field] at hb
    simp only [BitVec.toNat_ofNat] at this; omega
  simp only [armPins] at h0
  kit_run h0 acc until [0x8000aab4]
  -- at `luaD_precall`'s entry
  obtain ⟨t22, h0⟩ := h0.pin22
  obtain ⟨t26, h0⟩ := h0.pin26
  rw [call_top, call_nres ins hcc, call_ra, add_imm _ 0 (by decide), add_imm _ 16 (by decide),
    add_imm _ 32 (by decide), BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.add_zero,
    Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h0
  let f : AbiFrame := ⟨BitVec.ofNat 64 w.L, BitVec.ofNat 64 (Arms.jtEntries - 1), BitVec.ofNat 64 vNumInt,
    BitVec.ofNat 64 (w.code + 4 * (s.pc + 1)), sign_extend (m := 64) ins, 0#64, t22, BitVec.ofNat 64 w.ci,
    BitVec.ofNat 64 Arms.jtBase, BitVec.ofNat 64 w.base, t26, BitVec.ofNat 64 (w.code + 4 * s.pc)⟩
  obtain ⟨c3, s3, m', out, mo, ι, rt, hret, hout, hI'⟩ :=
    hP f c1.σ.sailOutput hS hR hI hf hop hb hcc hargs _ ((h0.repin (by
      simp only [callPre, f, AbiFrame.pins, List.cons_append, List.nil_append, RelPtrs.slot]
      pins_of h0)).mem_eq (by rw [hm1]; simp only [callMem, RelPtrs.slot, stateTopOff, ciSavedpcOff, stackValueSize]))
  have acc := acc.trans s3
  simp only [wrRet, f, AbiFrame.pins] at hret
  kit_run hret acc
  -- back at the fetch head
  rename_i c4
  have hm4 := hret.armMem
  have ho4 := hret.armOut
  have e40 : (BitVec.ofNat 64 w.ci + sign_extend (m := 64) (0x028#12)).toNat = w.ci + ciTrapOff := by
    rw [add_imm _ 40 (by decide), BitVec.toNat_ofNat]; simp only [ciTrapOff]; omega
  have hz : sign_extend (m := 64) (Sail.BitVec.extractLsb (sign_extend (m := 64) (0#32 : BitVec (8 * 4)) +
      sign_extend (m := 64) (0x000#12)) 31 0) = 0#64 := by decide
  rw [e40, hout.trap, hz, add_imm _ 0 (by decide), Nat.add_zero] at hret
  have hst4 : c.steps < c4.steps := Nat.lt_of_lt_of_le hlt1 acc.steps_le
  have ab8 : ∀ a, w.sp ≤ a → bytesT8 c4.σ.mem a = bytesT8 c1.σ.mem a := fun a ha => by
    rw [hm4, hm1]; exact bytesT8_congrT fun i _ => hout.above _ (by omega)
  refine ⟨c4, c4.steps - c.steps, w.after mo ι rt, by omega, (hs1.trans acc).toN_of_stepsField,
    ⟨?_, hret.pcAt⟩, hI'⟩
  refine
    { good := hret.good
      minstret := hret.minstret
      tick := hret.tick
      pins := ⟨by pin_of hret, by pin_of hret, by pin_of hret, by pin_of hret, by pin_of hret,
        by pin_of hret, by pin_of hret, by pin_of hret, by pin_of hret, by pin_of hret⟩
      out := ?_
      ok := hret.armOk
      text := hret.armText
      frame := fun a ha => by rw [hm4]; exact hout.frame a ha
      kptr := by
        show bytesT8 c4.σ.mem w.sp = BitVec.ofNat 64 w.k; exact (ab8 _ (Nat.le_refl _)).trans hc.kptr
      clptr := by
        show bytesT8 c4.σ.mem (w.sp + 8) = BitVec.ofNat 64 rt.cl
        rw [show rt.cl = w.rt.cl from hout.cl]; exact (ab8 _ (by omega)).trans hc.clptr
      stack := ?_
      comp := hout.comp
      ranges := hr.after mo ι rt
      saved := ⟨by show bytesT8 c4.σ.mem (w.sp + 168) = _; exact (ab8 _ (by omega)).trans hc.saved.ra,
        by show bytesT8 c4.σ.mem (w.sp + 160) = _; exact (ab8 _ (by omega)).trans hc.saved.s0,
        fun rv hrv => by
          have := savedOff_mem rv hrv
          show bytesT8 c4.σ.mem (w.sp + savedOff rv.1) = _
          exact (ab8 _ (by omega)).trans (hc.saved.s rv hrv)⟩ }
  · show String.join c4.σ.sailOutput.toList = _
    rw [ho4, output_pushes, hout.line]
    exact congrArg (· ++ printLine binaryHost args) hc.out
  · intro j v hj hv
    show ValRepr mo ι (slotTag c4.σ.mem (w.slot j)) (slotVal c4.σ.mem (w.slot j)) v
    simp only [writeDefs_range'] at hv
    by_cases h1 : ins.a ≤ j ∧ j < ins.a + (ins.c - 1)
    · simp only [h1, and_self, ite_true, Option.some.injEq] at hv
      subst hv
      rw [hm4, hout.nil j h1.1 (by omega)]
      exact .nil
    · simp only [h1, KEdge.kills] at hv
      by_cases h2 : ins.a + ins.c - 1 ≤ j ∧ j < ins.a + ins.c - 1 + (p.maxstacksize - (ins.a + ins.c - 1))
      · simp [h2] at hv
      · simp only [h2, ite_false] at hv
        have hja : j < ins.a := by omega
        have hv0 := hc.stack j v hj hv
        have et : slotTag c4.σ.mem (w.slot j) = slotTag c1.σ.mem (w.slot j) := by
          simp only [slotTag, tvalueTagOff, RelPtrs.slot, stackValueSize]
          rw [hm4, hm1]; exact hout.below _ (by omega) (by simp only [RelPtrs.slot, stackValueSize]; omega)
        have ev : slotVal c4.σ.mem (w.slot j) = slotVal c1.σ.mem (w.slot j) := by
          simp only [slotVal, tvalueValOff, RelPtrs.slot, stackValueSize, Nat.add_zero]
          rw [hm4, hm1]
          exact bytesT8_congrT fun i _ => hout.below _ (by omega)
            (by simp only [RelPtrs.slot, stackValueSize]; omega)
        rw [et, ev]
        exact hout.vrepr _ _ _ hv0

end Lua.Vm.Sim.Kit

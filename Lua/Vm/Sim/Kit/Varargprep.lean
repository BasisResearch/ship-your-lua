import Lua.Vm.Sim.Kit.Adjvar
import Lua.Vm.Arms.Segs.G20
import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Sim.Vararg

/-!
# `OP_VARARGPREP` at the entry (lane F1-3)

The arm at `0x8001ccc8` is `ProtectNT(luaT_adjustvarargs(L, A, ci, cl->p))`
(`savepc`, the call) then `updatetrap` and, `trap = 0`, `updatebase`:

* `vp1` (`seg_8001ccc8_8001cce8`): `ld a5,8(sp)` (the closure the prologue
  saved), `a1 = A = 0`, `a3 = cl->p`, `sd s3,32(s7)` (`savedpc`), `jal`;
* the call node `Kit.adjvar_sum`;
* `vp2` (`seg_8001cce8_8001ccf4_t`): `lw a5,40(s7)` (`ci->u.l.trap = 0`), the
  hook call not taken;
* `vp3` (`seg_8001ccf8_8001cd08`): `base = ci->func + 1` reloaded from the
  moved `ci->func`, `pc` from `s3`, back to the fetch head.

Each is its own declaration. The close `vclose` re-establishes `VmRel` at the
moved pointers `w.vmoved ι` (`Lua/Vm/Sim/Vararg.lean`): their complement and
ranges are the entry contract's (`FreshAt.post`); the memory outside the new
window is that complement (`vmem_frame`: the stored bytes are `varargMem`'s,
the old slot 0 leaves the window with the bytes the complement holds).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- The caller's frame across the call: the fetch-head registers after
dispatch at pc 0 (`armPins`). -/
def vpFrame (w : RelPtrs) (ins : Word) : KFrame :=
  ⟨BitVec.ofNat 64 symGlobalPointer, BitVec.ofNat 64 w.L, BitVec.ofNat 64 (Arms.jtEntries - 1),
    BitVec.ofNat 64 vNumInt, BitVec.ofNat 64 (w.code + 4 * (0 + 1)), sign_extend (m := 64) ins,
    0#64, BitVec.ofNat 64 w.ci, BitVec.ofNat 64 Arms.jtBase, BitVec.ofNat 64 w.base,
    BitVec.ofNat 64 (w.code + 4 * 0)⟩

/-- The memory at the call: `savepc`. -/
abbrev vpM0 (m : Mem) (w : RelPtrs) : Mem :=
  writeMap8 m (w.ci + 32) (sdData_val (BitVec.ofNat 64 (w.code + 4 * (0 + 1))))

set_option hygiene false in
/-- The relation's address facts, for `kit_disch`. -/
macro "vp_facts " hr:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hr).base_lo; have := ($hr).base_hi; have := ($hr).base_al; have := ($hr).ci_lo
  have := ($hr).ci_hi; have := ($hr).code_hi; have := ($hr).code_lo; have := ($hr).L_lo
  have := ($hr).ci_sep; have := ($hr).L_sep; have := ($hr).ci_top; have := ($hr).L_top
  have := ($hr).slots_top; have := ($hr).sp_eq; have := ($hr).L_al; have := ($hr).ci_al
  have := ($hr).L_sep_ci
  simp only [stackValueSize, ciSize, stateSize, RuntimeData.spEntry, cStackBudget, execFrame,
    RelPtrs.base] at *))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_side_pre) => `(tactic| simp only [e1, sext64_id] at *)

/-- **The arm up to the call**: the closure from `8(sp)`, `cl->p`, `A = 0`,
`savepc`. -/
theorem vp1 {p : Proto} {w : RelPtrs} {ins : Word} {m : Mem} {o : Array String}
    (hr : Ranges p w) (ha : ins.a = 0)
    (hcl : bytesT8 m (w.sp + 8) = BitVec.ofNat 64 w.rt.cl)
    (hclp : bytesT8 m (w.rt.cl + lclosureProtoOff) = BitVec.ofNat 64 w.pa)
    (hcl1 : symEnd ≤ w.rt.cl) (hcl2 : w.rt.cl + lclosureUpvalsOff ≤ symHeapEnd) :
    Triple (SegSt 0x8001ccc8#64 (armPins w 0 ins) (ArmPay m o))
      (SegSt 0x800197f0#64 (⟨Register.x10, BitVec.ofNat 64 w.L⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 w.ci⟩ :: ⟨Register.x2, BitVec.ofNat 64 w.sp⟩ ::
        ⟨Register.x11, 0#64⟩ :: ⟨Register.x1, 0x8001cce8#64⟩ ::
        ⟨Register.x13, BitVec.ofNat 64 w.pa⟩ :: (vpFrame w ins).pins) (ArmPay (vpM0 m w) o)) := by
  intro c h
  have acc := Steps.refl c
  vp_facts hr
  simp only [symEnd, symHeapEnd, lclosureUpvalsOff, lclosureProtoOff] at hcl1 hcl2 hclp
  have e1 : bytesT8 m (BitVec.ofNat 64 w.sp + sign_extend (m := 64) (8#12)).toNat =
      BitVec.ofNat 64 w.rt.cl := by
    rw [add_imm _ 8 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hcl
  simp only [armPins, vpFrame, KFrame.pins] at h ⊢
  kit_run h acc until [0x800197f0]
  have e2 : bytesT8 m (BitVec.ofNat 64 w.rt.cl + sign_extend (m := 64) (24#12)).toNat =
      BitVec.ofNat 64 w.pa := by
    rw [add_imm _ 24 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hclp
  have e3 : (BitVec.ofNat 64 w.ci + sign_extend (m := 64) (32#12)).toNat = w.ci + 32 := by
    kit_disch
  have e4 : (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb
      (sign_extend (m := 64) ins) 31 0) (0x07#5))) &&& sign_extend (m := 64) (0x0ff#12) = 0#64 := by
    rw [extract_sext, field8 _ 7 (by decide) (by decide)]
    have : (ins.toNat >>> 7) % 2 ^ 8 = 0 := ha
    rw [this]
  simp only [e1, sext64_id, e2, e3, e4, Vsa.Sim.sext_zero, BitVec.add_zero] at h
  refine ⟨_, acc, Vsa.Sim.SegSt.repin h ?_⟩
  pins_of h

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [e5]; decide))

/-- **The trap reload**: `ci->u.l.trap = 0`, no hook call. -/
theorem vp2 {p : Proto} {w : RelPtrs} {ins : Word} {M : Mem} {o : Array String}
    (hr : Ranges p w) (htrap : bytesT4 M (w.ci + ciTrapOff) = 0) :
    Triple (SegSt 0x8001cce8#64 (⟨Register.x2, BitVec.ofNat 64 w.sp⟩ :: (vpFrame w ins).pins)
        (ArmPay M o))
      (SegSt 0x8001ccf8#64 (⟨Register.x2, BitVec.ofNat 64 w.sp⟩ :: (vpFrame w ins).pins)
        (ArmPay M o)) := by
  intro c h
  have acc := Steps.refl c
  vp_facts hr
  have e5 : bytesT4 M (BitVec.ofNat 64 w.ci + sign_extend (m := 64) (40#12)).toNat = 0#32 := by
    rw [add_imm _ 40 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact htrap
  simp only [vpFrame, KFrame.pins] at h ⊢
  kit_run h acc until [0x8001ccf8]
  simp only [e5] at h
  have e6 : sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (0#32 : BitVec (8 * 4))) +
      sign_extend (m := 64) (0#12)) 31 0) = (0#64 : BitVec 64) := by decide
  simp only [e6] at h
  refine ⟨_, acc, Vsa.Sim.SegSt.repin h ?_⟩
  pins_of h

/-- The fetch-head registers at the moved pointers (`RelPtrs.vmoved`), pc 1. -/
abbrev vpHead (w : RelPtrs) : List Pin :=
  [⟨Register.x25, BitVec.ofNat 64 (w.base + stackValueSize)⟩,
    ⟨Register.x27, BitVec.ofNat 64 (w.code + 4 * (0 + 1))⟩,
    ⟨Register.x2, BitVec.ofNat 64 w.sp⟩, ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩,
    ⟨Register.x8, BitVec.ofNat 64 w.L⟩, ⟨Register.x9, BitVec.ofNat 64 (Arms.jtEntries - 1)⟩,
    ⟨Register.x18, BitVec.ofNat 64 vNumInt⟩, ⟨Register.x21, 0#64⟩,
    ⟨Register.x23, BitVec.ofNat 64 w.ci⟩, ⟨Register.x24, BitVec.ofNat 64 Arms.jtBase⟩]

/-- **`updatebase`**: `base` from the moved `ci->func`, `pc` from `s3`. -/
theorem vp3 {p : Proto} {w : RelPtrs} {ins : Word} {M : Mem} {o : Array String}
    (hr : Ranges p w) (hfn : bytesT8 M w.ci = BitVec.ofNat 64 (w.func + stackValueSize)) :
    Triple (SegSt 0x8001ccf8#64 (⟨Register.x2, BitVec.ofNat 64 w.sp⟩ :: (vpFrame w ins).pins)
        (ArmPay M o))
      (SegSt Arms.headPc (vpHead w) (ArmPay M o)) := by
  intro c h
  have acc := Steps.refl c
  vp_facts hr
  simp only [vpFrame, KFrame.pins, vpHead] at h ⊢
  kit_run h acc
  have e7 : bytesT8 M (BitVec.ofNat 64 w.ci).toNat = BitVec.ofNat 64 (w.func + 16) := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hfn
  have e8 : BitVec.ofNat 64 (w.func + 16) + sign_extend (m := 64) (16#12) =
      BitVec.ofNat 64 (w.func + 16 + 16) := by apply BitVec.eq_of_toNat_eq; kit_disch
  simp only [Vsa.Sim.sext_zero, BitVec.add_zero] at h
  simp only [e7, sext64_id] at h
  simp only [e8] at h
  refine ⟨_, acc, Vsa.Sim.SegSt.repin (h.at rfl) ?_⟩
  pins_of h

/-! ## The memory after the move -/

theorem bytesT1_wm8_out {m : Mem} {b a : Nat} {d : BitVec (8 * 8)} (h : a < b ∨ b + 8 ≤ a) :
    bytesT1 (writeMap8 m b d) a = bytesT1 m a := bytesT1_writeMap8_out m b d h

theorem bytesT1_wm8_in {m : Mem} {b a : Nat} {d : BitVec (8 * 8)} (h1 : b ≤ a) (h2 : a < b + 8) :
    bytesT1 (writeMap8 m b d) a = d.extractLsb' (8 * (a - b)) 8 := by
  have := getElem_writeMap8 m b d (a - b) (by omega)
  rw [show b + (a - b) = a by omega] at this
  simp only [bytesT1, this, Option.getD_some]

theorem extractLsb'_ofNat8 (v j : Nat) (hv : v < 2 ^ 64) :
    (BitVec.ofNat 64 v).extractLsb' (8 * j) 8 = BitVec.ofNat 8 (v / 256 ^ j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv,
    Nat.shiftRight_eq_div_pow, Nat.pow_mul]

theorem bytesT1_wm4_zero {m : Mem} {b a : Nat} (h1 : b ≤ a) (h2 : a < b + 4) :
    bytesT1 (writeMap4 m b (swData (0#64 : BitVec 64))) a = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j, a = b + j := ⟨a - b, by omega⟩
  have hj : j < 4 := by omega
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simp only [bytesT1, Nat.add_zero, getElem_writeMap4_0]; decide
  · simp only [bytesT1, getElem_writeMap4_1]; decide
  · simp only [bytesT1, getElem_writeMap4_2]; decide
  · simp only [bytesT1, getElem_writeMap4_3]; decide

theorem bytesT1_ins_self (m : Mem) (b : Nat) (x : BitVec 8) : bytesT1 (m.insert b x) b = x := by
  simp [bytesT1]

theorem bytesT1_ins_ne {m : Mem} {b a : Nat} {x : BitVec 8} (h : a ≠ b) :
    bytesT1 (m.insert b x) a = bytesT1 m a := by
  simp only [bytesT1, Std.ExtHashMap.getElem?_insert, beq_iff_eq, if_neg (Ne.symm h)]

theorem bytesT1_wle_in {m : Mem} {b n v a : Nat} (h1 : b ≤ a) (h2 : a < b + n) :
    bytesT1 (writeLE m b n v) a = BitVec.ofNat 8 (v / 256 ^ (a - b)) := by
  simp only [bytesT1, getElem?_writeLE, if_pos (And.intro h1 h2), Option.getD_some]

theorem bytesT1_wle_out {m : Mem} {b n v a : Nat} (h : a < b ∨ b + n ≤ a) :
    bytesT1 (writeLE m b n v) a = bytesT1 m a := by
  simp only [bytesT1, getElem?_writeLE, if_neg (fun hh : b ≤ a ∧ a < b + n => by omega)]

/-- **Outside the new window the memory is the moved complement**: the stored
bytes (`ci->func`, `ci->top`, `nextraargs`, the function's slot one up) are
`varargMem`'s; `savedpc`, `L->top` and `ra`'s save are scratch; every other byte
is the old complement's (`Core.frame`), the old slot 0's leaving the window
with the bytes the complement holds (`FreshAt.pad`). -/
theorem vmem_frame {p : Proto} {c : Config} {w : RelPtrs} {ι : Strs}
    (hc : Core p c State.init w) (hF : FreshAt p c w) (a : Nat) (ha : ¬ Win p (w.vmoved ι) a) :
    bytesT1 (avMem (vpM0 c.σ.mem w) w.L w.ci w.sp w.func w.rt.ciTop 0x8001cce8#64) a =
      bytesT1 (varargMem w.mo w.ci w.rt) a := by
  have hr := hc.ranges
  have hrg := hF.regions
  have hsle := hc.comp.runtime.lua.stack_le
  have hroom := hF.room
  have hctl := hc.comp.runtime.lua.ci_top_le
  have hst1 := hrg.stack_hi
  have hcis := hrg.ci_sep
  have hLs := hrg.L_sep_stack
  have hcr := cstack_room
  have hrf := hF.rt_func
  have hpad := hF.pad
  have hsp := hr.sp_eq
  have hLci := hr.L_sep_ci
  have hci := hr.ci_lo
  have hL := hr.L_lo
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hpay : bytesT8 (vpM0 c.σ.mem w) w.func = BitVec.ofNat 64 w.rt.cl := by
    have := hF.slot_val
    simp only [tvalueValOff, Nat.add_zero] at this
    rw [vpM0, bytesT8_wm8_out (by
      simp only [ciSize, stackValueSize, symHeapEnd] at hcis hroom hst1 hsle; rw [hrf] at hsle
      omega), this]
  have htag : bytesT1 (vpM0 c.σ.mem w) (w.func + 8) = BitVec.ofNat 8 vLcl := by
    have := hF.slot_tag
    simp only [tvalueTagOff] at this
    rw [vpM0, bytesT1_wm8_out (by
      simp only [ciSize, stackValueSize, symHeapEnd] at hcis hroom hst1 hsle; rw [hrf] at hsle
      omega), this]
  simp only [avMem, avM2, avM1, hpay, htag, stData_zext]
  simp only [varargMem, varargMemV, Win, Slots, Scratch, RelPtrs.vmoved, RelPtrs.base,
    stackValueSize, ciSavedpcOff, stateTopOff, execFrame, cStackBudget, RuntimeData.spEntry,
    symHeapEnd, ciSize, stateSize, ciFuncOff, ciTopOff, ciNextraargsOff, tvalueTagOff, not_or,
    not_and, Nat.not_lt, Nat.add_zero] at ha hroom hst1 hcis hLs hcr hpad hsp hLci ⊢
  try rw [hrf] at hsle
  try rw [hrf]
  by_cases hA : w.ci ≤ a ∧ a < w.ci + 8
  · rw [bytesT1_wm8_out (by omega), bytesT1_wm8_in (by omega) (by omega), sdData_id,
      extractLsb'_ofNat8 _ _ (by omega), bytesT1_wle_out (by omega),
      bytesT1_wle_in (by omega) (by omega)]
  by_cases hB : w.ci + 8 ≤ a ∧ a < w.ci + 16
  · rw [bytesT1_wm8_in (by omega) (by omega), sdData_id, extractLsb'_ofNat8 _ _ (by omega),
      bytesT1_wle_in (by omega) (by omega)]
  have hcl := hrg.cl_hi
  simp only [lclosureUpvalsOff, symHeapEnd] at hcl
  by_cases hC : w.ci + 44 ≤ a ∧ a < w.ci + 48
  · simp (disch := omega) only [bytesT1_wm8_out, bytesT1_ins_ne, bytesT1_wle_out]
    rw [bytesT1_wm4_zero (by omega) (by omega), bytesT1_wle_in (by omega) (by omega),
      Nat.zero_div]; rfl
  by_cases hD : w.func + 16 ≤ a ∧ a < w.func + 24
  · simp (disch := omega) only [bytesT1_wm8_out, bytesT1_ins_ne, bytesT1_wle_out]
    rw [bytesT1_wm8_in (by omega) (by omega), sdData_id, extractLsb'_ofNat8 _ _ (by omega),
      bytesT1_wle_in (by omega) (by omega)]
  by_cases hE : a = w.func + 24
  · subst hE
    simp (disch := omega) only [bytesT1_wm8_out, bytesT1_wle_out]
    rw [bytesT1_ins_self, bytesT1_wle_in (by omega) (by omega)]
    simp
  · simp only [vpM0]
    simp (disch := omega) only [bytesT1_wm8_out, bytesT1_ins_ne, bytesT1_wle_out, bytesT1_wm4_out]
    by_cases hw : Win p w a
    · simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, ciSavedpcOff, stateTopOff,
        execFrame, cStackBudget, RuntimeData.spEntry] at hw
      exact hpad a (by omega) (by omega)
    · exact hc.frame a hw

/-! ## The close and the arm -/

/-- **The close at the moved pointers**: the fetch head with the successor's
registers (`base` from the moved `ci->func`), the memory outside the new window
the moved complement (`vmem_frame`), and `0(sp) = k`. -/
theorem vclose {p : Proto} {c : Config} {w : RelPtrs} {ι : Strs} {c' : Config} {M : Mem}
    {L : List Pin} (hc : Core p c State.init w) (hP : RelParts p (w.vmoved ι))
    (hseg : SegSt Arms.headPc L (ArmPay M c.σ.sailOutput) c') (hpins : Pins c'.σ (w.vmoved ι) 1)
    (hM : ∀ a, ¬ Win p (w.vmoved ι) a → bytesT1 M a = bytesT1 (w.vmoved ι).mo a)
    (hk : bytesT8 M w.sp = BitVec.ofNat 64 w.k) :
    VmRelAt p c' ⟨1, State.init.regs, State.init.out⟩ (w.vmoved ι) := by
  have hm := hseg.armMem
  refine ⟨⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hseg.armText, fun a ha => ?_, ?_, fun j v _ h => ?_, hP.comp, hP.ranges⟩,
    hseg.pcAt⟩
  · rw [hm]; exact hM a ha
  · rw [hm]; exact hk
  · simp [State.init] at h

theorem vbytesT4_wm8_out {m : Mem} {b x : Nat} {d : BitVec (8 * 8)} (h : x + 4 ≤ b ∨ b + 8 ≤ x) :
    bytesT4 (writeMap8 m b d) x = bytesT4 m x :=
  bytesT4_congr fun _ _ => getElem?_writeMap8_out m b d _ (by omega)

theorem bytesT4_wm4_out {m : Mem} {b x : Nat} {d : BitVec (8 * 4)} (h : x + 4 ≤ b ∨ b + 4 ≤ x) :
    bytesT4 (writeMap4 m b d) x = bytesT4 m x :=
  bytesT4_congr fun _ _ => getElem?_writeMap4_out m b d _ (by omega)

theorem bytesT4_ins_out {m : Mem} {b x : Nat} {d : BitVec 8} (h : x + 4 ≤ b ∨ b < x) :
    bytesT4 (m.insert b d) x = bytesT4 m x :=
  bytesT4_congr fun i _ => by
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

theorem bytesT8_ins_out {m : Mem} {b x : Nat} {d : BitVec 8} (h : x + 8 ≤ b ∨ b < x) :
    bytesT8 (m.insert b d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => by
    rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; omega)]

/-- **`OP_VARARGPREP` at the entry** (`VarargSim`): dispatch, `vp1`, the call
node `adjvar_sum`, `vp2`, `vp3`, and the close at the moved pointers. -/
theorem varargSim : VarargSim := by
  intro p hS c w hR hF ins s' hf hop hstep
  have hc := hR.core
  -- the kernel: `A = 0`, a jump to pc 1
  have ha : ins.a = 0 ∧ kernelAt p State.init.pc = some (jump (0 + 1)) := by
    obtain ⟨hK0, -, -, -⟩ := hstep
    simp only [kernelAt, State.init, hf, kernel, hop, opKernel, Option.bind_some] at hK0 ⊢
    split at hK0
    · rename_i hcnd; exact ⟨hcnd.2, by rw [if_pos hcnd]⟩
    · cases hK0
  obtain rfl := step_jump hstep ha.2
  -- dispatch
  obtain ⟨c1, hs1, hlt1, hA, hmem⟩ := dispatchM hR hf (by rw [opNum_of_op? hop]; decide)
  have hF1 := hF.of_mem hmem
  have hc1 := hA.core
  have h0 := hA.seg (pc := 0x8001ccc8#64) (by rw [opNum_of_op? hop]; decide)
  have hr := hc1.ranges
  have hrg := hF1.regions
  have hsle := hc1.comp.runtime.lua.stack_le
  have hctl := hc1.comp.runtime.lua.ci_top_le
  have hrf := hF1.rt_func
  have hrp := hF1.rt_proto
  have hroom := hF1.room
  have hcr := cstack_room
  have hmszl := rd8_lt hc1.comp.proto.maxstack
  have hpas := hF1.pa_sep
  vp_facts hr
  have hst1 := hrg.stack_hi; have hst0 := hrg.stack_lo; have hcis := hrg.ci_sep
  have hLs := hrg.L_sep_stack; have hfal := hrg.func_al; have hcl1 := hrg.cl_lo
  have hcl2 := hrg.cl_hi; have hpr1 := hrg.proto_lo; have hpr2 := hrg.proto_hi
  rw [hrf] at hsle hfal
  rw [hrp] at hpr1 hpr2
  simp only [symEnd, symHeapEnd, lclosureUpvalsOff, protoCodeOff, protoMaxstacksizeOff, ciSize,
    stackValueSize, cStackBudget, stateSize] at hst1 hst0 hcis hLs hcl1 hcl2 hpr1 hpr2 hcr hroom hpas
  -- the arm up to the call
  obtain ⟨c2, hs2, h2⟩ := vp1 hr ha.1 hF1.clslot hF1.clp hrg.cl_lo hrg.cl_hi c1 h0
  -- the call node
  have hx : AvCx w.L w.ci w.pa w.sp w.func w.rt.stackLast p.maxstacksize w.rt.ciTop
      0x8001cce8#64 (vpM0 c1.σ.mem w) :=
    { ra := by decide
      sp_lo := by omega
      sp_hi := by omega
      sp_al := by omega
      L_lo := by omega
      L_hi := by simp only [stateSize]; omega
      L_al := by omega
      ci_lo := by omega
      ci_hi := by simp only [ciSize]; omega
      ci_al := by omega
      pa_lo := by omega
      pa_hi := by omega
      f_lo := by omega
      f_al := hfal
      sl_hi := by omega
      room := by omega
      msz_lt := hmszl
      ct_hi := by omega
      sLci := by simp only [stateSize, ciSize]; omega
      sLf := by simp only [stateSize]; omega
      scif := by simp only [ciSize]; omega
      spa := by omega
      top := by
        rw [vpM0, bytesT8_wm8_out (by omega)]
        have := hF1.top; simp only [stateTopOff, stackValueSize] at this; exact this
      fn := by
        rw [vpM0, bytesT8_wm8_out (by omega)]
        have := hF1.ci_func; simp only [ciFuncOff, Nat.add_zero] at this; exact this
      slast := by
        rw [vpM0, bytesT8_wm8_out (by omega)]
        have := hF1.stack_last; simp only [stateStackLastOff] at this; exact this
      maxst := by
        rw [vpM0, bytesT1_wm8_out (by omega)]
        have := hF1.msz; simp only [protoMaxstacksizeOff] at this; exact this
      citop := by
        rw [vpM0, bytesT8_wm8_out (by omega)]
        have := hF1.ci_top; simp only [ciTopOff] at this; exact this }
  obtain ⟨c3, hs3, h3⟩ := adjvar_sum hx (vpFrame w ins) _ c2 h2
  -- the trap reload and `updatebase`
  have htrap : bytesT4 (avMem (vpM0 c1.σ.mem w) w.L w.ci w.sp w.func w.rt.ciTop 0x8001cce8#64)
      (w.ci + ciTrapOff) = 0 := by
    simp only [avMem, avM2, avM1, vpM0, ciTrapOff]
    rw [vbytesT4_wm8_out (by omega)]
    rw [vbytesT4_wm8_out (by omega)]
    rw [bytesT4_ins_out (by omega)]
    rw [vbytesT4_wm8_out (by omega)]
    rw [vbytesT4_wm8_out (by omega)]
    rw [bytesT4_wm4_out (by omega)]
    rw [vbytesT4_wm8_out (by omega)]
    rw [vbytesT4_wm8_out (by omega)]
    exact hc1.trap
  obtain ⟨c4, hs4, h4⟩ := vp2 hr htrap c3 h3
  have hfn : bytesT8 (avMem (vpM0 c1.σ.mem w) w.L w.ci w.sp w.func w.rt.ciTop 0x8001cce8#64)
      w.ci = BitVec.ofNat 64 (w.func + stackValueSize) := by
    simp only [avMem]
    rw [bytesT8_wm8_out (by omega), bytesT8_writeMap8, sdData_id]; rfl
  obtain ⟨c5, hs5, h5⟩ := vp3 hr hfn c4 h4
  -- the close
  obtain ⟨ι, hP⟩ := hF1.post
  have hk : bytesT8 (avMem (vpM0 c1.σ.mem w) w.L w.ci w.sp w.func w.rt.ciTop 0x8001cce8#64)
      w.sp = BitVec.ofNat 64 w.k := by
    simp only [avMem, avM2, avM1, vpM0]
    rw [bytesT8_wm8_out (by omega), bytesT8_wm8_out (by omega), bytesT8_ins_out (by omega),
      bytesT8_wm8_out (by omega), bytesT8_wm8_out (by omega), bytesT8_wm4_out (by omega),
      bytesT8_wm8_out (by omega), bytesT8_wm8_out (by omega)]
    exact hc1.kptr
  have hP5 := h5.pins
  refine sim_of_run ⟨c5, hs1.trans (hs2.trans (hs3.trans (hs4.trans hs5))),
    Nat.lt_of_lt_of_le hlt1 (hs2.trans (hs3.trans (hs4.trans hs5))).steps_le,
    vclose hc1 hP h5 ⟨pinsHold_get hP5 2 (by simp), pinsHold_get hP5 3 (by simp),
      pinsHold_get hP5 4 (by simp), pinsHold_get hP5 5 (by simp), pinsHold_get hP5 6 (by simp),
      pinsHold_get hP5 7 (by simp), pinsHold_get hP5 8 (by simp), pinsHold_get hP5 9 (by simp),
      pinsHold_get hP5 0 (by simp), pinsHold_get hP5 1 (by simp)⟩
      (fun a ha' => vmem_frame hc1 hF1 a ha') hk⟩

end Lua.Vm.Sim.Kit

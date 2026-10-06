import Lua.Vm.Sim.Kit.Run
import Lua.Vm.Arms.Segs.HluaT_adjustvarargs
import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Sim.Kit.Multi
import Vsa.Sim.Mfr

/-!
# `luaT_adjustvarargs` at the entry, the call-node summary (lane F1-3)

`OP_VARARGPREP` calls `luaT_adjustvarargs(L, 0, ci, cl->p)`. At the entry
(`L->top = ci->func + 1`, no fixed parameters) the helper is loop-free:

* `ci->u.l.nextraargs = (L->top - ci->func) / 16 - 1 - 0 = 0` (`sw`);
* `luaD_checkstack(L, maxstacksize + 1)` does not fire (`bge` not taken):
  `L->stack_last - L->top > maxstacksize + 1` slots (`av_guard`, from the
  stack room);
* `setobjs2s(L, L->top++, ci->func)`: the payload and tag one slot up, and
  `L->top` advanced;
* the copy loop is skipped (`blez a4`, `A = 0`);
* `ci->func` and `ci->top` move one slot up.

It saves `ra` below `sp`. The summary `adjvar_sum` is three segment-local
lemmas (`av1`, `av2`, `av3`, one per generated segment, each in its own
declaration) composed.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## Bit-level facts -/

theorem toInt_ofNat_small (n : Nat) (h : n < 2 ^ 63) : (BitVec.ofNat 64 n).toInt = n := by
  rw [BitVec.toInt_eq_toNat_of_msb]
  · simp [BitVec.toNat_ofNat]; omega
  · rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]; omega

/-- `lbu a1,12(a3); addiw a1,a1,1`: `maxstacksize + 1`. -/
theorem av_a1 (msz : Nat) (hm : msz < 256) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((zero_extend (m := 64)
      (BitVec.ofNat 8 msz : BitVec (8 * 1))) + sign_extend (m := 64) (0x001#12)) 31 0) =
      BitVec.ofNat 64 (msz + 1) := by
  have h1 : (zero_extend (m := 64) (BitVec.ofNat 8 msz : BitVec (8 * 1))) +
      sign_extend (m := 64) (0x001#12) = BitVec.ofNat 64 (msz + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [zero_extend, Sail.BitVec.zeroExtend, sign_extend, Sail.BitVec.signExtend,
      BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [show (BitVec.signExtend 64 (0x001#12)).toNat = 1 by decide]
    omega
  rw [h1]
  have h2 : Sail.BitVec.extractLsb (BitVec.ofNat 64 (msz + 1)) 31 0 = BitVec.ofNat 32 (msz + 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, BitVec.toNat_ofNat,
      Nat.shiftRight_zero]
    omega
  rw [h2]
  apply BitVec.eq_of_toNat_eq
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, BitVec.toNat_ofNat,
    BitVec.toNat_setWidth]
  rw [BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat]
  rw [if_neg (by simp; omega)]
  omega

/-- `sub t4,t4,a5; srai t4,t4,4`: the free slots `(stack_last - top) / 16`. -/
theorem av_t4 (sl top : Nat) (hle : top ≤ sl) (hsl : sl < 2 ^ 63) :
    shift_bits_right_arith ((sign_extend (m := 64) (BitVec.ofNat 64 sl : BitVec (8 * 8))) -
      (sign_extend (m := 64) (BitVec.ofNat 64 top : BitVec (8 * 8))))
      (Sail.BitVec.extractLsb (0x04#6) 5 0) = BitVec.ofNat 64 ((sl - top) / 16) := by
  rw [sext64_id, sext64_id]
  have hsub : BitVec.ofNat 64 sl - BitVec.ofNat 64 top = BitVec.ofNat 64 (sl - top) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsub]
  unfold shift_bits_right_arith
  rw [show BitVec.toNatInt (Sail.BitVec.extractLsb (0x04#6) 5 0) = 4 by decide]
  rw [BitVec.sshiftRight_eq_of_msb_false (by rw [BitVec.msb_eq_decide]; simp; omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    show Int.toNat 4 = 4 from rfl]
  omega

/-- **`luaD_checkstack`'s test does not fire** (`bge a1, t4` not taken). -/
theorem av_guard (msz sl top : Nat) (hm : msz < 256) (hle : top ≤ sl) (hsl : sl < 2 ^ 63)
    (hroom : top + 16 * (msz + 2) ≤ sl) :
    zopz0zKzJ_s (sign_extend (m := 64) (Sail.BitVec.extractLsb ((zero_extend (m := 64)
      (BitVec.ofNat 8 msz : BitVec (8 * 1))) + sign_extend (m := 64) (0x001#12)) 31 0))
      (shift_bits_right_arith ((sign_extend (m := 64) (BitVec.ofNat 64 sl : BitVec (8 * 8))) -
        (sign_extend (m := 64) (BitVec.ofNat 64 top : BitVec (8 * 8))))
        (Sail.BitVec.extractLsb (0x04#6) 5 0)) = false := by
  rw [av_a1 msz hm, av_t4 sl top hle hsl]
  unfold zopz0zKzJ_s
  rw [toInt_ofNat_small _ (by omega), toInt_ofNat_small _ (by omega)]
  simp only [ge_iff_le, decide_eq_false_iff_not, Int.not_le]
  omega

/-- `(L->top - ci->func) >> 4 = 1`: one actual "argument" slot, the function. -/
theorem av_one (func : Nat) (_h : func + 16 < 2 ^ 63) :
    shift_bits_right_arith (BitVec.ofNat 64 (func + 16) - BitVec.ofNat 64 func)
      (Sail.BitVec.extractLsb (0x04#6) 5 0) = 1#64 := by
  have hsub : BitVec.ofNat 64 (func + 16) - BitVec.ofNat 64 func = 16#64 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [hsub]; decide

/-- `nextraargs = 1 - 1 - 0`. -/
theorem av_nx : sign_extend (m := 64) ((Sail.BitVec.extractLsb (sign_extend (m := 64)
    (Sail.BitVec.extractLsb ((1#64 : BitVec 64) + sign_extend (m := 64) (0xfff#12)) 31 0)) 31 0) -
    (Sail.BitVec.extractLsb ((0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 31 0)) =
    (0#64 : BitVec 64) := by decide

/-- `sext.w a7,a2` of `1`. -/
theorem av_a7 : sign_extend (m := 64) (Sail.BitVec.extractLsb ((1#64 : BitVec 64) +
    sign_extend (m := 64) (0x000#12)) 31 0) = (1#64 : BitVec 64) := by decide

theorem bytesT1_wm4_out {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x < a ∨ a + 4 ≤ x) :
    bytesT1 (writeMap4 m a d) x = bytesT1 m x := by
  simp only [bytesT1, getElem?_writeMap4_out m a d x h]

theorem bytesT8_wm4_out {m : Mem} {a x : Nat} {d : BitVec (8 * 4)} (h : x + 8 ≤ a ∨ a + 4 ≤ x) :
    bytesT8 (writeMap4 m a d) x = bytesT8 m x :=
  bytesT8_congr fun _ _ => getElem?_writeMap4_out m a d _ (by omega)

/-! ## The summary -/

/-- **The facts the helper's run uses**: the pointers in RAM above the HTIF
mailbox and below the frame (`sp - 48`), the objects apart, and the words it
reads. -/
structure AvCx (L ci pa sp func sl msz ct : Nat) (r : BitVec 64) (m : Mem) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 48 ≤ sp
  sp_hi : sp < 2 ^ 32
  sp_al : sp % 8 = 0
  L_lo : tohostAddr + 16 ≤ L
  L_hi : L + stateSize + 48 ≤ sp
  L_al : L % 8 = 0
  ci_lo : tohostAddr + 16 ≤ ci
  ci_hi : ci + ciSize + 48 ≤ sp
  ci_al : ci % 8 = 0
  pa_lo : tohostAddr + 16 ≤ pa
  pa_hi : pa + 16 + 48 ≤ sp
  f_lo : tohostAddr + 16 ≤ func
  f_al : func % 8 = 0
  sl_hi : sl + 48 ≤ sp
  room : func + 16 * (msz + 3) ≤ sl
  msz_lt : msz < 256
  ct_hi : ct + 16 + 48 ≤ sp
  sLci : L + stateSize ≤ ci ∨ ci + ciSize ≤ L
  sLf : L + stateSize ≤ func ∨ func + 32 ≤ L
  scif : ci + ciSize ≤ func ∨ func + 32 ≤ ci
  spa : pa + 12 < ci + 44 ∨ ci + 48 ≤ pa + 12
  top : bytesT8 m (L + 16) = BitVec.ofNat 64 (func + 16)
  fn : bytesT8 m ci = BitVec.ofNat 64 func
  slast : bytesT8 m (L + 40) = BitVec.ofNat 64 sl
  maxst : bytesT1 m (pa + 12) = BitVec.ofNat 8 msz
  citop : bytesT8 m (ci + 8) = BitVec.ofNat 64 ct

/-- The memory after the first segment: `ra` saved, `nextraargs = 0`. -/
abbrev avM1 (m : Mem) (ci sp : Nat) (r : BitVec 64) : Mem :=
  writeMap4 (writeMap8 m (sp - 8) (sdData_val r)) (ci + 44) (swData (0#64 : BitVec 64))

/-- The memory after the copy: `L->top` advanced, the function's payload and tag. -/
abbrev avM2 (m : Mem) (L ci sp func : Nat) (r : BitVec 64) : Mem :=
  (writeMap8 (writeMap8 (avM1 m ci sp r) (L + 16) (sdData_val (BitVec.ofNat 64 (func + 32))))
    (func + 16) (sdData_val (bytesT8 m func))).insert (func + 24)
    (stData 1 (zero_extend (m := 64) (bytesT1 m (func + 8) : BitVec (8 * 1))))

/-- The memory at the return: `ci->func` and `ci->top` one slot up. -/
abbrev avMem (m : Mem) (L ci sp func ct : Nat) (r : BitVec 64) : Mem :=
  writeMap8 (writeMap8 (avM2 m L ci sp func r) ci (sdData_val (BitVec.ofNat 64 (func + 16))))
    (ci + 8) (sdData_val (BitVec.ofNat 64 (ct + 16)))

/-- The registers the helper's second segment reads. -/
abbrev avRow1 (L ci sp func : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x6, BitVec.ofNat 64 func⟩ :: ⟨Register.x15, BitVec.ofNat 64 (func + 16)⟩ ::
    ⟨Register.x16, BitVec.ofNat 64 L⟩ :: ⟨Register.x14, 0#64⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ :: ⟨Register.x17, 1#64⟩ ::
    ⟨Register.x28, BitVec.ofNat 64 ci⟩ :: f.pins

set_option hygiene false in
/-- The context's facts, for `kit_disch`. -/
macro "av_facts " hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).L_lo; have := ($hx).L_hi; have := ($hx).L_al; have := ($hx).ci_lo
  have := ($hx).ci_hi; have := ($hx).ci_al; have := ($hx).pa_lo; have := ($hx).pa_hi
  have := ($hx).f_lo; have := ($hx).f_al; have := ($hx).sl_hi; have := ($hx).room
  have := ($hx).msz_lt; have := ($hx).ct_hi; have := ($hx).sLci; have := ($hx).sLf
  have := ($hx).scif; have := ($hx).spa
  have htop := ($hx).top; have hfn := ($hx).fn; have hsl' := ($hx).slast
  have hmsz := ($hx).maxst; have hct := ($hx).citop
  simp only [stateSize, ciSize] at *))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
    | decide
    | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
        bytesT1_writeMap8_out, bytesT1_wm4_out, bytesT8_wm8_out]
       rw [hmsz, hsl', htop]
       exact av_guard _ _ _ (by assumption) (by omega) (by omega) (by omega)))

local macro_rules
  | `(tactic| kit_val) => `(tactic| (apply BitVec.eq_of_toNat_eq; kit_disch))

/-- **The first segment**: the frame, `nextraargs = 0`, the stack test not
taken (`av_guard`). -/
theorem av1 {L ci pa sp func sl msz ct : Nat} {r : BitVec 64} {m : Mem}
    (hx : AvCx L ci pa sp func sl msz ct r m) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x800197f0#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 ci⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
        ⟨Register.x11, 0#64⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x13, BitVec.ofNat 64 pa⟩ :: f.pins)
        (ArmPay m o))
      (SegSt 0x8001983c#64 (avRow1 L ci sp func f) (ArmPay (avM1 m ci sp r) o)) := by
  intro c h
  have acc := Steps.refl c
  av_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s7, s8, s9, s11⟩ := f
  simp only [KFrame.pins, avRow1] at h ⊢
  have hA : bytesT8 m (BitVec.ofNat 64 L + sign_extend (m := 64) (16#12)).toNat =
      BitVec.ofNat 64 (func + 16) := by
    rw [add_imm _ 16 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact htop
  have hB : bytesT8 m (BitVec.ofNat 64 ci + sign_extend (m := 64) (0#12)).toNat =
      BitVec.ofNat 64 func := by
    rw [add_imm _ 0 (by decide), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.add_zero]
    exact hfn
  have hC := av_one func (by omega)
  kit_run h acc until [0x8001983c]
  have e0 : BitVec.ofNat 64 sp + sign_extend (m := 64) (4048#12) = BitVec.ofNat 64 (sp - 48) := by
    apply BitVec.eq_of_toNat_eq; kit_disch
  simp only [hA, hB, sext64_id] at h
  simp only [hC, av_a7, av_nx] at h
  simp only [e0, Vsa.Sim.sext_zero, BitVec.add_zero] at h
  have e1 : (BitVec.ofNat 64 (sp - 48) + sign_extend (m := 64) (40#12)).toNat = sp - 8 := by
    kit_disch
  have e2 : (BitVec.ofNat 64 ci + sign_extend (m := 64) (44#12)).toNat = ci + 44 := by kit_disch
  refine ⟨_, acc, Vsa.Sim.SegSt.mem_eq (Vsa.Sim.SegSt.repin h ?_) (by rw [e1, e2])⟩
  pins_of h

/-- The registers the helper's epilogue reads. -/
abbrev avRow2 (ci sp func : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x28, BitVec.ofNat 64 ci⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ ::
    ⟨Register.x17, 1#64⟩ :: ⟨Register.x6, BitVec.ofNat 64 func⟩ :: f.pins

/-- **The second segment**: `setobjs2s(L, L->top++, ci->func)`, the copy loop
skipped (`A = 0`). -/
theorem av2 {L ci pa sp func sl msz ct : Nat} {r : BitVec 64} {m : Mem}
    (hx : AvCx L ci pa sp func sl msz ct r m) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x8001983c#64 (avRow1 L ci sp func f) (ArmPay (avM1 m ci sp r) o))
      (SegSt 0x80019898#64 (avRow2 ci sp func f) (ArmPay (avM2 m L ci sp func r) o)) := by
  intro c h
  have acc := Steps.refl c
  av_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s7, s8, s9, s11⟩ := f
  simp only [KFrame.pins, avRow1, avRow2] at h ⊢
  kit_run h acc until [0x80019898]
  have b1 : (BitVec.ofNat 64 L + sign_extend (m := 64) (16#12)).toNat = L + 16 := by kit_disch
  have b2 : BitVec.ofNat 64 (func + 16) + sign_extend (m := 64) (16#12) =
      BitVec.ofNat 64 (func + 32) := by apply BitVec.eq_of_toNat_eq; kit_disch
  have b3 : (BitVec.ofNat 64 (func + 16) + sign_extend (m := 64) (0#12)).toNat = func + 16 := by
    kit_disch
  have b4 : (BitVec.ofNat 64 func + sign_extend (m := 64) (0#12)).toNat = func := by kit_disch
  have b5 : (BitVec.ofNat 64 (func + 16) + sign_extend (m := 64) (8#12)).toNat = func + 24 := by
    kit_disch
  have b6 : (BitVec.ofNat 64 func + sign_extend (m := 64) (8#12)).toNat = func + 8 := by kit_disch
  have b7 : bytesT8 (avM1 m ci sp r) func = bytesT8 m func := by
    rw [bytesT8_wm4_out (by omega), bytesT8_wm8_out (by omega)]
  simp only [b1, b2, b3, b4, b5, b6, b7, sext64_id] at h
  have b8 : bytesT1 (writeMap8 (writeMap8 (avM1 m ci sp r) (L + 16)
      (sdData_val (BitVec.ofNat 64 (func + 32)))) (func + 16) (sdData_val (bytesT8 m func)))
      (func + 8) = bytesT1 m (func + 8) := by
    rw [bytesT1_writeMap8_out _ _ _ (by omega), bytesT1_writeMap8_out _ _ _ (by omega),
      bytesT1_wm4_out (by omega), bytesT1_writeMap8_out _ _ _ (by omega)]
  simp only [b8] at h
  refine ⟨_, acc, Vsa.Sim.SegSt.repin h ?_⟩
  pins_of h

/-- `ld ra,40(sp)` in the epilogue reads the saved `ra` back. -/
theorem av_ra {L ci pa sp func sl msz ct : Nat} {r : BitVec 64} {m : Mem}
    (hx : AvCx L ci pa sp func sl msz ct r m) :
    sign_extend (m := 64) (bytesT8 (avM2 m L ci sp func r)
      (BitVec.ofNat 64 (sp - 48) + sign_extend (m := 64) (40#12)).toNat : BitVec (8 * 8)) = r := by
  av_facts hx
  have e : (BitVec.ofNat 64 (sp - 48) + sign_extend (m := 64) (40#12)).toNat = sp - 8 := by kit_disch
  rw [e, avM2, bytesT8_ins (by omega), bytesT8_wm8_out (by omega), bytesT8_wm8_out (by omega),
    avM1, bytesT8_wm4_out (by omega), bytesT8_writeMap8, sext64_id, sdData_id]

/-- `slli a2,a7,4` of `a7 = 1`. -/
theorem av_shl : shift_bits_left (1#64 : BitVec 64) (Sail.BitVec.extractLsb (0x04#6) 5 0) =
    (16#64 : BitVec 64) := by decide

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| (rw [hR, Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

/-- **The epilogue**: `ci->func` and `ci->top` one slot up, the return. -/
theorem av3 {L ci pa sp func sl msz ct : Nat} {r : BitVec 64} {m : Mem}
    (hx : AvCx L ci pa sp func sl msz ct r m) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x80019898#64 (avRow2 ci sp func f) (ArmPay (avM2 m L ci sp func r) o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (avMem m L ci sp func ct r) o)) := by
  intro c h
  have acc := Steps.refl c
  have hR := av_ra hx
  av_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s7, s8, s9, s11⟩ := f
  simp only [KFrame.pins, avRow2] at h ⊢
  kit_run h acc
  have c1 : (BitVec.ofNat 64 ci + sign_extend (m := 64) (8#12)).toNat = ci + 8 := by kit_disch
  have c2 : (BitVec.ofNat 64 ci + sign_extend (m := 64) (0#12)).toNat = ci := by kit_disch
  have c3 : bytesT8 (avM2 m L ci sp func r) (ci + 8) = BitVec.ofNat 64 ct := by
    rw [avM2, bytesT8_ins (by omega), bytesT8_wm8_out (by omega), bytesT8_wm8_out (by omega),
      avM1, bytesT8_wm4_out (by omega), bytesT8_wm8_out (by omega), hct]
  have c4 : ∀ x : Nat, x + 16 < 2 ^ 64 → BitVec.ofNat 64 x + (16#64 : BitVec 64) =
      BitVec.ofNat 64 (x + 16) := fun x hx => by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have c5 : BitVec.ofNat 64 (sp - 48) + sign_extend (m := 64) (48#12) = BitVec.ofNat 64 sp := by
    apply BitVec.eq_of_toNat_eq; kit_disch
  simp only [hR, c1, c2, c3, sext64_id, av_shl, c4 func (by omega), c4 ct (by omega), c5] at h
  refine ⟨_, acc, Vsa.Sim.SegSt.repin (h.at (Vsa.Sim.ret_tgt _ (by assumption))) ?_⟩
  pins_of h

/-- **`luaT_adjustvarargs(L, 0, ci, p)` at the entry, the call-node summary**
(`AvCx`: `L->top = func + 1`, room for `maxstacksize + 1` slots): it returns to
`ra` with the caller's frame, having stored `ra` below `sp`, `nextraargs = 0`,
`L->top`, the function's slot one up, and `ci->func`, `ci->top` one slot up
(`avMem`). -/
theorem adjvar_sum {L ci pa sp func sl msz ct : Nat} {r : BitVec 64} {m : Mem}
    (hx : AvCx L ci pa sp func sl msz ct r m) (f : KFrame) (o : Array String) :
    Triple (SegSt 0x800197f0#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x12, BitVec.ofNat 64 ci⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
        ⟨Register.x11, 0#64⟩ :: ⟨Register.x1, r⟩ :: ⟨Register.x13, BitVec.ofNat 64 pa⟩ :: f.pins)
        (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (avMem m L ci sp func ct r) o)) :=
  ((av1 hx f o).seq (av2 hx f o)).seq (av3 hx f o)

end Lua.Vm.Sim.Kit

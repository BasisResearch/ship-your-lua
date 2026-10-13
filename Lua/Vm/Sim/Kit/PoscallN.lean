import Lua.Vm.Sim.Kit.CallOpen
import Lua.Vm.Sim.Kit.Scan

/-!
# `luaD_poscall` with results wanted after a C function with none (lane F1-14)

`OP_CALL print` with `C ≥ 2` wants `w = C - 1 ≥ 1` results; `luaB_print`
returns `0`, so `luaD_poscall(L, ci, 0)` (no hooks: `beqz` to `0x8000a4d0`)
fills `w` nils from `res = ci->func`:

* `w = 1` (`moveresults`' case 1, `0x8000a548`): one `setnilvalue`
  (`pos_one`);
* `w ≥ 2` (the general case, `0x8000a5e0` → `0x8000a530`: no result to copy,
  `0x8000a484`): the nil-fill loop `0x8000a4a4` (`sb zero, 8(a5); addi a5,
  16; bne a4, a5`), the loop rule `seg_loop` with the comprehension log
  (`compMem`, as `OP_LOADNIL`'s `loadnil_loop`): `pn_loop`;

then `L->top = res + w`, `L->ci = ci->previous` and the return. The result
slots lie apart from the frame, the `CallInfo` and the `lua_State`
(`PcCxW.res_*`), so the post (`PoscallPost`) is one lemma over the final
memory (`pcw_post`). Each phase is its own declaration (the elaboration
budget is per declaration).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Ret

open Lua.Vm.Sim Lua.Vm.Sim.Kit Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

theorem sext16_ofNat {w : Nat} (h : w < 2 ^ 15) :
    sign_extend (m := 64) (BitVec.ofNat 16 w : BitVec (8 * 2)) = BitVec.ofNat 64 w := by
  have hm : (BitVec.ofNat 16 w).msb = false := by
    simp [BitVec.msb_eq_decide, BitVec.toNat_ofNat]; omega
  simp only [sign_extend, Sail.BitVec.signExtend]
  rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
  apply BitVec.eq_of_toNat_eq; simp; omega

theorem sge_nat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zopz0zKzJ_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (b ≤ a) := by
  have ea : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have eb : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  unfold zopz0zKzJ_s
  rw [ea, eb]; simp

theorem sge_neg {a k : Nat} (ha : a < 2 ^ 63) (hk1 : 2 ^ 63 ≤ k) (hk2 : k < 2 ^ 64) :
    zopz0zKzJ_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 k) = true := by
  have ea : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have eb : (BitVec.ofNat 64 k).toInt < 0 := by
    rw [BitVec.toInt_neg_iff]; simp; omega
  unfold zopz0zKzJ_s
  rw [ea]; simp; omega

/-- The loop's end `res + 16·w` (`subw`, the zero-extension, `slli 4`, `add`). -/
theorem pn_end {w res : Nat} (hw : w < 2 ^ 31) :
    shift_bits_left
        (shift_bits_right
          (shift_bits_left
            (sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 w) 31 0 - Sail.BitVec.extractLsb (0#64) 31 0))
            (Sail.BitVec.extractLsb (32#6) 5 0))
          (Sail.BitVec.extractLsb (32#6) 5 0))
        (Sail.BitVec.extractLsb (4#6) 5 0) + BitVec.ofNat 64 res = BitVec.ofNat 64 (res + 16 * w) := by
  have e1 : Sail.BitVec.extractLsb (BitVec.ofNat 64 w) 31 0 - Sail.BitVec.extractLsb (0#64) 31 0 =
      BitVec.ofNat 32 w := by
    apply BitVec.eq_of_toNat_eq
    simp [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
  rw [e1]
  have e2 : sign_extend (m := 64) (BitVec.ofNat 32 w) = BitVec.ofNat 64 w := by
    have hm : (BitVec.ofNat 32 w).msb = false := by
      simp [BitVec.msb_eq_decide, BitVec.toNat_ofNat]; omega
    simp only [sign_extend, Sail.BitVec.signExtend]
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hm]
    apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e2]
  apply BitVec.eq_of_toNat_eq
  simp [shift_bits_left, shift_bits_right, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  omega

/-- `L->top = res + (w << 4)`. -/
theorem pn_top {w res : Nat} (hw : w < 2 ^ 31) :
    BitVec.ofNat 64 res + shift_bits_left (BitVec.ofNat 64 w) (Sail.BitVec.extractLsb (4#6) 5 0) =
      BitVec.ofNat 64 (res + 16 * w) := by
  apply BitVec.eq_of_toNat_eq
  simp [shift_bits_left, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftLeft_eq]
  omega

/-- The loop's start `res + 0`. -/
theorem pn_start {res : Nat} : shift_bits_left (0#64) (Sail.BitVec.extractLsb (4#6) 5 0) + BitVec.ofNat 64 res =
    BitVec.ofNat 64 res := by
  simp [shift_bits_left]

set_option hygiene false in
macro "pcw_facts " hx:ident : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := ($hx).ra; have := ($hx).sp_lo; have := ($hx).sp_hi; have := ($hx).sp_al
  have := ($hx).L_lo; have := ($hx).L_hi; have := ($hx).ci_lo; have := ($hx).ci_hi
  have := ($hx).ci_al; have := ($hx).L_al
  have hhk := ($hx).hook; have hnr := ($hx).nres
  have := ($hx).res_lo; have := ($hx).res_hi; have := ($hx).res_ci; have := ($hx).res_L
  simp only [stateSize, ciSize, stateHookmaskOff, ciNresultsOff, stateTopOff, stateCiOff,
    ciFuncOff, ciPreviousOff, Nat.add_zero] at *
  have hresv0 : bytesT8 m ci = BitVec.ofNat 64 (bytesT8 m ci).toNat := by simp
  generalize hres : (bytesT8 m ci).toNat = res at *
  have hresv := hresv0
  clear hres hresv0))

/-- A word apart from a comprehension's stores. -/
theorem bytesT8_compMem_apart {M : Mem} {o s x k : Nat} {b : BitVec 8} (hs : 1 ≤ s)
    (h : x + 8 ≤ o ∨ o + s * k ≤ x) : bytesT8 (compMem M o s b k) x = bytesT8 M x :=
  AtF.bT8_congr fun j hj => compMem_out fun i hi e => by
    have : s * i < s * k := Nat.mul_lt_mul_of_pos_left hi (by omega)
    omega

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    bytesT2_wm8_out', bytesT8_wm8_out', hnr, sext16_ofNat, sext64_id, bytesT8_writeMap8,
    sdData_id, hresv, AtF.fw8_ins, pn_end, pn_start, bytesT8_compMem_apart] at $h:ident)

/-- A guard over `Nat`-valued words: their numbers compared, `omega`. -/
macro "pn_guard" : tactic => `(tactic| (
  (try simp (disch := kit_disch) only [add_imm, imm_neg_add, BitVec.ofNat_add_ofNat, Nat.zero_add,
    Vsa.Sim.sext_zero, BitVec.add_zero, sext64_id])
  simp (disch := omega) only [AtF.fbeq, AtF.fbne, sge_nat, sge_neg, slt_nat, decide_eq_true_eq,
    decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_eq_false'] <;> omega))

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | pn_guard
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, hhk]; decide)
      | (simp (disch := kit_disch) only [add_imm, sl_neg, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          sext64_id, bytesT8_writeMap8, sdData_id, Nat.reduceSub, Vsa.Sim.sext_zero, AtF.fw8_ins,
          BitVec.add_zero, bytesT8_compMem_apart]
         rw [rtgt _ hra]; exact hra)
      | decide)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| first | pn_guard | try simp (disch := kit_disch) only [add_imm, BitVec.ofNat_add_ofNat])

/-- `luaD_poscall`'s final memory: `ra` saved, the `w` nils from `res + 8`,
`L->top`, `L->ci`. -/
abbrev pnMem (m : Mem) (L sp res w : Nat) (r top pv : BitVec 64) : Mem :=
  writeMap8 (writeMap8 (compMem (writeMap8 m (sp - 64 + 56) r) (res + 8) 16 (stData 1 0#64) w) (L + 16) top)
    (L + 32) pv

/-- **`PoscallPost` of the final memory.** -/
theorem pcw_post {m : Mem} {L ci sp w res : Nat} {r top pv : BitVec 64} (hx : PcCxW L ci sp r m w)
    (hres : (bytesT8 m (ci + ciFuncOff)).toNat = res) (hpv : pv = bytesT8 m (ci + ciPreviousOff)) :
    PoscallPost m (pnMem m L sp res w r top pv) L ci sp w := by
  have h1 := hx.res_hi; have h2 := hx.res_L; have h3 := hx.L_hi; have h4 := hx.sp_hi; have h5 := hx.res_lo
  rw [hres] at h1 h2 h5
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  simp only [stateSize] at h2 h3
  refine ⟨?_, fun j hj => ?_, fun a ha => ?_⟩
  · simp only [pnMem, stateCiOff, bytesT8_writeMap8]; exact hpv
  · rw [hres]
    simp only [pnMem, tvalueTagOff]
    rw [AtF.bT1_congr (getElem?_writeMap8_out _ _ _ _ (by omega)),
      AtF.bT1_congr (getElem?_writeMap8_out _ _ _ _ (by omega))]
    have := compMem_in (M := writeMap8 m (sp - 64 + 56) r) (o := res + 8) (s := 16) (b := stData 1 0#64) hj
    rw [show res + 16 * j + 8 = res + 8 + 16 * j by omega]
    simp only [bytesT1, this, Option.getD_some]; decide
  · simp only [Rng, stateTopOff, stateCiOff, tvalueTagOff, hres, not_or, not_and, Nat.not_lt,
      not_exists] at ha
    obtain ⟨hf, hT, hC, hN⟩ := ha
    simp only [pnMem]
    rw [AtF.bT1_congr (getElem?_writeMap8_out _ _ _ _ (by omega)),
      AtF.bT1_congr (getElem?_writeMap8_out _ _ _ _ (by omega)),
      AtF.bT1_congr (compMem_out fun i hi e => hN i hi (by omega)),
      AtF.bT1_congr (getElem?_writeMap8_out _ _ _ _ (by omega))]

theorem ins_addr {M : Mem} {a a' : Nat} {b : BitVec 8} (h : a = a') : M.insert a b = M.insert a' b :=
  h ▸ rfl

/-- The nil-fill loop's row: the cursor `a5`, the end `a4`, the registers
the loop and the tail read. -/
abbrev pnRow (w res sp L ci a5 e : Nat) (f : RFrame) : List Pin :=
  [⟨Register.x15, BitVec.ofNat 64 a5⟩, ⟨Register.x14, BitVec.ofNat 64 e⟩, ⟨Register.x6, BitVec.ofNat 64 w⟩,
   ⟨Register.x17, BitVec.ofNat 64 res⟩, ⟨Register.x2, BitVec.ofNat 64 (sp - 64)⟩,
   ⟨Register.x3, f.gp⟩, ⟨Register.x8, f.s0⟩, ⟨Register.x9, f.s1⟩, ⟨Register.x16, BitVec.ofNat 64 L⟩,
   ⟨Register.x18, f.s2⟩, ⟨Register.x19, f.s3⟩, ⟨Register.x20, f.s4⟩, ⟨Register.x21, f.s5⟩,
   ⟨Register.x22, f.s6⟩, ⟨Register.x23, f.s7⟩, ⟨Register.x24, f.s8⟩, ⟨Register.x25, f.s9⟩,
   ⟨Register.x26, f.s10⟩, ⟨Register.x27, f.s11⟩, ⟨Register.x28, BitVec.ofNat 64 ci⟩]

/-- **The nil-fill loop** (`seg_loop`): `K` nils from `res + 8`, step 16. -/
theorem pn_loop (w res sp L ci : Nat) (f : RFrame) (o : Array String) (M : Mem) (K E : Nat) (hK : 0 < K)
    (hE : res + 16 * K = E) (hX : tohostAddr + 8 ≤ res) (hhi : E ≤ 2 ^ 32) :
    Triple (SegSt 0x8000a4a4#64 (pnRow w res sp L ci res E f)
        (ArmPay (compMem M (res + 8) 16 (stData 1 0#64) 0) o))
      (SegSt 0x8000a4b0#64 (pnRow w res sp L ci E E f) (ArmPay (compMem M (res + 8) 16 (stData 1 0#64) K) o)) :=
  fun c h => seg_loop (S := fun i c => i < K ∧ SegSt 0x8000a4a4#64 (pnRow w res sp L ci (res + 16 * i) E f)
      (ArmPay (compMem M (res + 8) 16 (stData 1 0#64) i) o) c) (fun i => K - i)
    (fun i c ⟨hi, h⟩ => by
      have acc := Steps.refl c
      have hTH : tohostAddr = 0x8005c6c0 := rfl
      have hra : (0#64 : BitVec 64).toNat % 4 = 0 := rfl
      have hhk : True := trivial
      have hnr : True := trivial
      have hresv : True := trivial
      by_cases hk : i + 1 = K
      · kit_run h acc until [0x8000a4b0, 0x8000a4a4]
        exact ⟨_, acc, .inr ((h.mem_eq (by rw [← hk]; exact ins_addr (by kit_disch))).repin
          (by pins_of h))⟩
      · kit_run h acc until [0x8000a4b0, 0x8000a4a4]
        exact ⟨_, acc, .inl ⟨i + 1, by omega, by omega,
          (h.mem_eq (ins_addr (by kit_disch))).repin (by pins_of h)⟩⟩) 0 c
    ⟨hK, by simpa only [Nat.mul_zero, Nat.add_zero] using h⟩

/-- `luaD_poscall`'s entry row at `luaB_print`'s `0` results. -/
abbrev pnEntry (L ci sp : Nat) (r : BitVec 64) (f : RFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 L⟩ :: ⟨Register.x11, BitVec.ofNat 64 ci⟩ :: ⟨Register.x12, 0x0#64⟩ ::
    ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins

/-- **`w = 1`**: the one nil, the return. -/
theorem pos_one {L ci sp w : Nat} {r : BitVec 64} {m : Mem} (hx : PcCxW L ci sp r m w) (hw1 : w = 1)
    (f : RFrame) (o : Array String) :
    Triple (SegSt 0x8000a39c#64 (pnEntry L ci sp r f) (ArmPay m o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (pnMem m L sp
        (bytesT8 m (ci + ciFuncOff)).toNat 1 r (BitVec.ofNat 64 ((bytesT8 m (ci + ciFuncOff)).toNat + 16))
        (bytesT8 m (ci + ciPreviousOff))) o)) := by
  intro c h
  have acc := Steps.refl c
  have hra := hx.ra
  have hw2 : w < 2 ^ 15 := by omega
  pcw_facts hx
  subst hw1
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [pnEntry, RFrame.pins] at h ⊢
  kit_run h acc
  have h := h.at (rtgt _ hra)
  rw [show sp - 64 + 64 = sp by omega] at h
  exact ⟨_, acc, (h.mem_eq rfl).repin (by pins_of h)⟩

/-- **`w ≥ 2`, up to the nil-fill loop.** -/
theorem posN_head {L ci sp w : Nat} {r : BitVec 64} {m : Mem} (hx : PcCxW L ci sp r m w) (h2 : 2 ≤ w)
    (hw2 : w < 2 ^ 15) (f : RFrame) (o : Array String) :
    Triple (SegSt 0x8000a39c#64 (pnEntry L ci sp r f) (ArmPay m o))
      (SegSt 0x8000a4a4#64 (pnRow w (bytesT8 m (ci + ciFuncOff)).toNat sp L ci (bytesT8 m (ci + ciFuncOff)).toNat
          ((bytesT8 m (ci + ciFuncOff)).toNat + 16 * w) f)
        (ArmPay (compMem (writeMap8 m (sp - 64 + 56) r) ((bytesT8 m (ci + ciFuncOff)).toNat + 8) 16
          (stData 1 0#64) 0) o)) := by
  intro c h
  have acc := Steps.refl c
  have hra := hx.ra
  have hw3 : w < 2 ^ 31 := by omega
  pcw_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [pnEntry, RFrame.pins] at h
  kit_run h acc until [0x8000a4a4]
  exact ⟨_, acc, (h.mem_eq rfl).repin (by pins_of h)⟩

/-- **`w ≥ 2`, after the loop**: `L->top`, `L->ci`, the return. -/
theorem posN_tail {L ci sp w : Nat} {r : BitVec 64} {m : Mem} (hx : PcCxW L ci sp r m w) (h2 : 2 ≤ w)
    (hw2 : w < 2 ^ 15) (f : RFrame) (o : Array String) :
    Triple (SegSt 0x8000a4b0#64 (pnRow w (bytesT8 m (ci + ciFuncOff)).toNat sp L ci
          ((bytesT8 m (ci + ciFuncOff)).toNat + 16 * w) ((bytesT8 m (ci + ciFuncOff)).toNat + 16 * w) f)
        (ArmPay (compMem (writeMap8 m (sp - 64 + 56) r) ((bytesT8 m (ci + ciFuncOff)).toNat + 8) 16
          (stData 1 0#64) w) o))
      (SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (pnMem m L sp
        (bytesT8 m (ci + ciFuncOff)).toNat w r (BitVec.ofNat 64 ((bytesT8 m (ci + ciFuncOff)).toNat + 16 * w))
        (bytesT8 m (ci + ciPreviousOff))) o)) := by
  intro c h
  have acc := Steps.refl c
  have hra := hx.ra
  have hw3 : w < 2 ^ 31 := by omega
  pcw_facts hx
  obtain ⟨gp, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [RFrame.pins] at h ⊢
  kit_run h acc
  have h := h.at (rtgt _ hra)
  rw [show sp - 64 + 64 = sp by omega, pn_top (by omega)] at h
  exact ⟨_, acc, (h.mem_eq rfl).repin (by pins_of h)⟩

/-- **`luaD_poscall(L, ci, 0)` with `wanted ≥ 1`** (lane F1-14). -/
theorem poscallN : PoscallN_Statement := by
  intro L ci sp w r m hx hw1 hw2 f o c h
  have hres := hx.res_hi; have hlo := hx.res_lo; have hhi := hx.sp_hi
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  rcases Nat.lt_or_ge w 2 with h1 | h2
  · obtain ⟨c', s', h'⟩ := pos_one hx (by omega) f o c h
    obtain rfl : w = 1 := by omega
    exact ⟨c', s', _, h', pcw_post hx rfl rfl⟩
  · obtain ⟨c1, s1, h1⟩ := posN_head hx h2 hw2 f o c h
    obtain ⟨c2, s2, h2'⟩ := pn_loop w _ sp L ci f o _ w _ (by omega) rfl (by omega) (by omega) c1 h1
    obtain ⟨c3, s3, h3⟩ := posN_tail hx h2 hw2 f o c2 h2'
    exact ⟨c3, s1.trans (s2.trans s3), _, h3, pcw_post hx rfl rfl⟩

/-- `CALL`'s `luaD_poscall` with results, discharged (lane F1-14). -/
theorem _root_.Lua.Vm.Sim.Kit.CallOpen.poscall (_O : Kit.CallOpen) : PoscallN_Statement := poscallN

end Lua.Vm.Sim.Ret

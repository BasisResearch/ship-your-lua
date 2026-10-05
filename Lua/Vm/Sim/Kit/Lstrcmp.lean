import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Sim.Kit.Lex
import Lua.Vm.Arms.Segs.Hl_strcmp
import Lua.Vm.Arms.Segs.Hstrcoll

/-!
# `l_strcmp` at the Lua ELF's address (round-4 bake-off, S-SCAN)

`l_strcmp(ls, rs)` (`0x8001a704`, lvm.c) compares two Lua strings chunk by
chunk: `strcoll` (`j strcmp`, `strcmp_sum`) up to the first event; on a
difference that answer is final (`lexLt_of_diff`); on a common `'\0'` the
chunk lengths (`strlen_sum`, twice) decide whether a string ended
(`lexLt_of_zero`) or both continue past the `'\0'`. The loop (`seg_loop`
over the chunk position) is entered at its call site `0x8001a790`, or, for
two long strings, at the first call site `0x8001a744`. The summary is
quotiented by the caller's observation, bit 31 of the answer (`srliw 31`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout Lua.Bytecode
open Vsa.Machine (MState Config Steps)

/-- A string `l_strcmp` reads: viewed, apart from its frame below `sp`. -/
structure LsStr (m : Mem) (ts : Nat) (s : List UInt8) (sp : Nat) : Prop where
  view : StrView m ts s
  apart : StrApart ts s (sp - 64) sp

/-- What `l_strcmp` needs. -/
structure LsCtx (m : Mem) (sp : Nat) (r : BitVec 64) (t1 t2 : Nat) (s1 s2 : List UInt8) : Prop where
  ro : RodataRead m
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 64 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  a1 : LsStr m t1 s1 sp
  a2 : LsStr m t2 s2 sp

/-- **What `l_strcmp`'s callers observe of its answer** `v`: bit 31
(`srliw 31`, `OP_LT`) is `lexLt`; zero iff the strings are equal; a
sign-extended 32-bit value, so `slti 1` (`OP_LE`) reads its sign
(`LsObs.le`). -/
structure LsObs (v : BitVec 64) (s1 s2 : List UInt8) : Prop where
  neg : v.getLsbD 31 = lexLt s1 s2
  zero : v = 0#64 ↔ s1 = s2
  small : v.toNat < 2 ^ 31 ∨ 2 ^ 64 - 2 ^ 31 ≤ v.toNat

theorem getLsbD31 (v : BitVec 64) : v.getLsbD 31 = decide (v.toNat / 2 ^ 31 % 2 = 1) := by
  rw [BitVec.getLsbD_eq_getElem (by omega), BitVec.getElem_eq_testBit_toNat, Nat.testBit_eq_decide_div_mod_eq]

/-- **`OP_LE`'s test** (`slti a0, a0, 1`): `l_strcmp(a, b) ≤ 0` is `a ≤ b`. -/
theorem LsObs.le {v : BitVec 64} {s1 s2 : List UInt8} (h : LsObs v s1 s2) :
    zopz0zI_s v (sign_extend (m := 64) (0x001#12)) = !lexLt s2 s1 := by
  have hn := h.neg; have hz := h.zero
  rw [not_lexLt_iff, ← hn, getLsbD31]
  unfold zopz0zI_s
  rw [show (sign_extend (m := 64) (0x001#12)).toInt = 1 by decide]
  rw [BitVec.toInt_eq_toNat_cond]
  rcases h.small with hs | hs
  · have e : v.toNat / 2 ^ 31 % 2 = 0 := by omega
    by_cases h0 : v = 0#64
    · have := hz.1 h0; subst h0; simp_all
    · have h0' : v.toNat ≠ 0 := fun e => h0 (BitVec.eq_of_toNat_eq e)
      have : ¬ s1 = s2 := fun e => h0 (hz.2 e)
      simp [this, e]; split <;> omega
  · have e : v.toNat / 2 ^ 31 % 2 = 1 := by omega
    have := v.isLt
    simp [e]; split <;> omega

theorem zext_bit_toNat (b : Bool) : (zero_extend (m := 64) (bool_to_bit b)).toNat < 2 := by
  cases b <;> decide

/-- The observation of a 0/1 answer (`snez`: the first string continues). -/
theorem lsObs_bit {s1 s2 : List UInt8} (b : Bool) (hz : b = false ↔ s1 = s2) (hn : lexLt s1 s2 = false) :
    LsObs (zero_extend (m := 64) (bool_to_bit b)) s1 s2 := by
  refine ⟨?_, ?_, ?_⟩
  · cases b <;> simp [hn] <;> decide
  · rw [← hz]; cases b <;> decide
  · have := zext_bit_toNat b; omega

/-- The observation of `-1` (the first string ended). -/
theorem lsObs_m1 {s1 s2 : List UInt8} (hn : lexLt s1 s2 = true) (hne : s1 ≠ s2) :
    LsObs ((0#64) + sign_extend (m := 64) (0xfff#12)) s1 s2 :=
  ⟨by rw [hn]; decide, ⟨fun e => absurd e (by decide), fun e => absurd e hne⟩, by decide⟩

/-- `snez` of a value. -/
theorem ult0_ofNat {a : Nat} (ha : a < 2 ^ 64) :
    zopz0zI_u (0#64) (BitVec.ofNat 64 a) = false ↔ a = 0 := by
  unfold zopz0zI_u
  simp [Sail.BitVec.toNatInt, Nat.mod_eq_of_lt ha]

/-- **`l_strcmp`'s answer**: some `a0` its callers observe as the strings'
order (`LsObs`), the memory changed only in `[lo, hi)`. -/
structure LsRet (r sp : BitVec 64) (f : KFrame) (m : Mem) (o : Array String) (lo hi : Nat)
    (s1 s2 : List UInt8) (c : Config) : Prop where
  intro ::
  ret : ∃ v m', AgreeOut m' m lo hi ∧ RetAt r sp f m' o v c ∧ LsObs v s1 s2

/-- `l_strcmp`'s frame `[sp - 48, sp)`: the saved registers. -/
structure LsFrame (mL m : Mem) (sp : Nat) (r : BitVec 64) (f : KFrame) : Prop where
  agree : AgreeOut mL m (sp - 48) sp
  ra : bytesT8 mL (sp - 48 + 40) = r
  s0 : bytesT8 mL (sp - 48 + 32) = f.s0
  s1 : bytesT8 mL (sp - 48 + 24) = f.s1
  s2 : bytesT8 mL (sp - 48 + 16) = f.s2
  s3 : bytesT8 mL (sp - 48 + 8) = f.s3
  s4 : bytesT8 mL (sp - 48) = f.s4

/-- The contents as their C view. -/
theorem _root_.Lua.Vm.Sim.StrView.cb_at {m : Mem} {ts : Nat} {s : List UInt8} (h : StrView m ts s) {j : Nat}
    (hj : j ≤ s.length) : bytesT1 m (ts + tstringContentsOff + j) = cb s j := by
  unfold cb
  rcases Nat.lt_or_ge j s.length with h' | h'
  · simp only [h', ↓reduceDIte]; exact h.bytes j h'
  · simp only [show ¬ j < s.length by omega, ↓reduceDIte]; rw [show j = s.length by omega]; exact h.term

theorem RodataRead.agree {m m' : Mem} (h : RodataRead m) {lo hi : Nat} (ha : AgreeOut m' m lo hi)
    (hlo : Image.rodataBase + Image.rodataSize ≤ lo) : RodataRead m' := fun o ho => by
  rw [show bytesT1 m' (Image.rodataBase + o) = bytesT1 m (Image.rodataBase + o) by
    simp only [bytesT1, ha (Image.rodataBase + o) (.inl (by omega))]]
  exact h o ho

/-- The loop's head (`0x8001a790`, the `strcoll` call site): the chunk at
`i`, `s4` some `z`. -/
abbrev lsH (P Q n1 n2 i : Nat) (z : BitVec 64) (sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x8, BitVec.ofNat 64 (P + i)⟩ :: ⟨Register.x9, BitVec.ofNat 64 (Q + i)⟩ ::
    ⟨Register.x18, BitVec.ofNat 64 (n1 - i)⟩ :: ⟨Register.x19, BitVec.ofNat 64 (n2 - i)⟩ ::
    ⟨Register.x20, z⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ :: ⟨Register.x3, f.gp⟩ ::
    ⟨Register.x21, f.s5⟩ :: ⟨Register.x23, f.s7⟩ :: ⟨Register.x24, f.s8⟩ :: ⟨Register.x25, f.s9⟩ ::
    ⟨Register.x27, f.s11⟩ :: []

/-- After a chunk's `strcoll` answered `0` (`0x8001a760`): `a0 = s0`. -/
abbrev lsM (P Q n1 n2 i : Nat) (z : BitVec 64) (sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + i)⟩ :: lsH P Q n1 n2 i z sp f

/-- The epilogue (`0x8001a7a8`): the answer in `a5`. -/
abbrev lsE (v : BitVec 64) (sp : Nat) (f : KFrame) (x8 x9 x18 x19 x20 : BitVec 64) : List Pin :=
  ⟨Register.x15, v⟩ :: ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ :: ⟨Register.x3, f.gp⟩ ::
    ⟨Register.x8, x8⟩ :: ⟨Register.x9, x9⟩ :: ⟨Register.x18, x18⟩ :: ⟨Register.x19, x19⟩ ::
    ⟨Register.x20, x20⟩ :: ⟨Register.x21, f.s5⟩ :: ⟨Register.x23, f.s7⟩ :: ⟨Register.x24, f.s8⟩ ::
    ⟨Register.x25, f.s9⟩ :: ⟨Register.x27, f.s11⟩ :: []

set_option hygiene false in
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| skip)

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, sl_neg, sl_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, Nat.add_zero,
    sext64_id, hF.ra, hF.s0, hF.s1, hF.s2, hF.s3, hF.s4, Vsa.Sim.sext_zero, BitVec.add_zero,
    BitVec.ofNat_add_ofNat] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | guard_assumption
      | (rw [Vsa.Sim.ret_tgt _ hra]; exact hra)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt, sext64_id, hF.ra]
         rw [Vsa.Sim.ret_tgt _ hra]; exact hra))

theorem ret_tgt' (r : BitVec 64) (h : r.toNat % 4 = 0) : BitVec.update r 0 0#1 = r := by
  have := Vsa.Sim.ret_tgt r h; rwa [Vsa.Sim.sext_zero, BitVec.add_zero] at this

/-- **The epilogue**: `l_strcmp` returns the answer in `a5`, its frame
restored. -/
theorem lstrcmp_exit (sp : Nat) (r : BitVec 64) (f : KFrame) (mL m : Mem) (o : Array String)
    (s1 s2 : List UInt8) (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 64 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : LsFrame mL m sp r f) (v x8 x9 x18 x19 x20 : BitVec 64) (hv : LsObs v s1 s2) :
    Triple (SegSt 0x8001a7a8#64 (lsE v sp f x8 x9 x18 x19 x20) (ArmPay mL o))
      (LsRet r (BitVec.ofNat 64 sp) f m o (sp - 48) sp s1 s2) := by
  intro c h
  have acc := Steps.refl c
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  kit_run h acc
  have h := h.at (ret_tgt' r hra)
  rw [show sp - 48 + 48 = sp by omega] at h
  exact ⟨_, acc, ⟨⟨v, mL, hF.agree, h.repin (by pins_of h), hv⟩⟩⟩

/-- The C views of both strings in `l_strcmp`'s memory, and the bounds. -/
structure LsMem (mL : Mem) (P Q : Nat) (s1 s2 : List UInt8) : Prop where
  c1 : ∀ j, j ≤ s1.length → bytesT1 mL (P + j) = cb s1 j
  c2 : ∀ j, j ≤ s2.length → bytesT1 mL (Q + j) = cb s2 j
  p_lo : tohostAddr + 16 ≤ P
  q_lo : tohostAddr + 16 ≤ Q
  p_hi : P + s1.length + 1 ≤ DlHeap.heapEnd + 8
  q_hi : Q + s2.length + 1 ≤ DlHeap.heapEnd + 8
  ro : RodataRead mL

theorem cb_len (s : List UInt8) : cb s s.length = 0#8 := by simp [cb]

/-- **`strcmp`'s answer at chunk `i`, in the strings' terms**: the first event
`k`, and either a difference (whose bit 31 is `lexLt`) or a common `'\0'`. -/
theorem ls_ans {mL : Mem} {P Q i : Nat} {s1 s2 : List UInt8} {v : BitVec 64} (hM : LsMem mL P Q s1 s2)
    (hA : Agree s1 s2 i) (hans : ScAns mL (P + i) (Q + i) v) :
    ∃ k, (∀ j, j < k → cb s1 (i + j) = cb s2 (i + j) ∧ cb s1 (i + j) ≠ 0#8) ∧
      ((v ≠ 0#64 ∧ LsObs v s1 s2) ∨ (v = 0#64 ∧ cb s1 (i + k) = 0#8 ∧ cb s2 (i + k) = 0#8)) := by
  obtain ⟨k, hok, hev, hobs⟩ := hans.ans
  have l1 := hA.le1; have l2 := hA.le2
  -- the scan stays within both strings
  have hk1 : i + k ≤ s1.length := Nat.not_lt.1 fun h => (hok (s1.length - i) (by omega)).2 (by
    rw [Nat.add_assoc, show i + (s1.length - i) = s1.length by omega, hM.c1 _ (Nat.le_refl _), cb_len])
  have hk2 : i + k ≤ s2.length := Nat.not_lt.1 fun h => by
    have := hok (s2.length - i) (by omega)
    simp only [ScOk] at this
    rw [Nat.add_assoc, Nat.add_assoc, show i + (s2.length - i) = s2.length by omega,
      hM.c2 _ (Nat.le_refl _), cb_len] at this
    exact this.2 this.1
  have conv : ∀ j, j ≤ k → bytesT1 mL (P + i + j) = cb s1 (i + j) ∧ bytesT1 mL (Q + i + j) = cb s2 (i + j) :=
    fun j hj => ⟨by rw [Nat.add_assoc]; exact hM.c1 _ (by omega), by rw [Nat.add_assoc]; exact hM.c2 _ (by omega)⟩
  have hok' : ∀ j, j < k → cb s1 (i + j) = cb s2 (i + j) ∧ cb s1 (i + j) ≠ 0#8 := fun j hj => by
    have := hok j hj; simp only [ScOk] at this
    rw [(conv j (by omega)).1, (conv j (by omega)).2] at this; exact this
  obtain ⟨e1, e2⟩ := conv k (Nat.le_refl _)
  rw [e1, e2] at hobs
  simp only [ScOk, e1, e2] at hev
  refine ⟨k, hok', ?_⟩
  by_cases hd : cb s1 (i + k) = cb s2 (i + k)
  · refine .inr ⟨hobs.zero.2 (by rw [hd]), ?_, ?_⟩
    · exact Classical.byContradiction fun hz => hev ⟨hd, hz⟩
    · rw [← hd]; exact Classical.byContradiction fun hz => hev ⟨hd, hz⟩
  · have hv0 : v ≠ 0#64 := fun e => hd (BitVec.eq_of_toNat_eq (hobs.zero.1 e))
    refine .inl ⟨hv0, ⟨?_, ⟨fun e => absurd e hv0, fun e => absurd (by rw [e]) hd⟩, hobs.small⟩⟩
    rw [hobs.neg, lexLt_of_diff (hA.scan hok') hd]

/-- **A chunk's outcome**: `l_strcmp`'s answer, or the next chunk's head. -/
structure LsNext (r : BitVec 64) (sp : Nat) (f : KFrame) (m mL : Mem) (o : Array String) (P Q : Nat)
    (s1 s2 : List UInt8) (i : Nat) (c : Config) : Prop where
  intro ::
  next : LsRet r (BitVec.ofNat 64 sp) f m o (sp - 48) sp s1 s2 c ∨
    ∃ i' z', i < i' ∧ Agree s1 s2 i' ∧
      SegSt 0x8001a790#64 (lsH P Q s1.length s2.length i' z' sp f) (ArmPay mL o) c

theorem zext_bit31 (b : Bool) : (zero_extend (m := 64) (bool_to_bit b)).getLsbD 31 = false := by
  cases b <;> decide

theorem ofNat_beq_t {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a = b) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = true := by rw [ofNat_beq ha hb]; simp [h]

theorem ofNat_beq_f {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = false := by rw [ofNat_beq ha hb]; simp [h]

set_option hygiene false in
local macro "ls_ctx" : tactic => `(tactic| (
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have := hM.p_lo; have := hM.q_lo; have := hM.p_hi; have := hM.q_hi
  simp only [DlHeap.heapEnd, symHeapEnd] at *))

/-- **After a chunk's `'\0'`** (`0x8001a760`): the two chunk lengths (`strlen`
twice), then an answer if a string ended, else the next chunk. -/
theorem lstrcmp_mid (P Q sp : Nat) (r : BitVec 64) (f : KFrame) (mL m : Mem) (o : Array String)
    (s1 s2 : List UInt8) (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 64 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : LsFrame mL m sp r f) (hM : LsMem mL P Q s1 s2) (i k : Nat) (z : BitVec 64) (hA : Agree s1 s2 i)
    (hok : ∀ j, j < k → cb s1 (i + j) = cb s2 (i + j) ∧ cb s1 (i + j) ≠ 0#8)
    (hz1 : cb s1 (i + k) = 0#8) (hz2 : cb s2 (i + k) = 0#8) :
    Triple (SegSt 0x8001a760#64 (lsM P Q s1.length s2.length i z sp f) (ArmPay mL o))
      (LsNext r sp f m mL o P Q s1 s2 i) := by
  intro c h
  have acc := Steps.refl c
  ls_ctx
  have hAk := hA.scan hok
  have := hAk.le1; have := hAk.le2
  have sl1 : SlCtx mL (P + i) k 0x8001a764#64 := ⟨by decide, by omega, by omega,
    by rw [Nat.add_assoc, hM.c1 _ (by omega), hz1],
    fun j hj => by rw [Nat.add_assoc, hM.c1 _ (by omega)]; exact (hok j hj).2⟩
  have sl2 : SlCtx mL (Q + i) k 0x8001a770#64 := ⟨by decide, by omega, by omega,
    by rw [Nat.add_assoc, hM.c2 _ (by omega), hz2],
    fun j hj => by rw [Nat.add_assoc, hM.c2 _ (by omega), ← (hok j hj).1]; exact (hok j hj).2⟩
  kit_run h acc until [0x8003b770]
  obtain ⟨_, acc, h⟩ := h.call acc (by pins_of h)
    (strlen_sum (P + i) k 0x8001a764#64 (BitVec.ofNat 64 (sp - 48)) (KFrame.mk _ _ _ _ _ _ _ _ _ _ _) mL o sl1)
  dsimp only [RetAt] at h
  kit_run h acc until [0x8003b770]
  obtain ⟨_, acc, h⟩ := h.call acc (by pins_of h)
    (strlen_sum (Q + i) k 0x8001a770#64 (BitVec.ofNat 64 (sp - 48)) (KFrame.mk _ _ _ _ _ _ _ _ _ _ _) mL o sl2)
  dsimp only [RetAt] at h
  have hL := lexLt_of_zero hAk hz1 hz2
  by_cases e2 : s2.length - i = k
  · have g := ofNat_beq_t (a := s2.length - i) (b := k) (by omega) (by omega) e2
    kit_run h acc until [0x8001a7a8]
    have h2 := h.repin (L' := lsE _ sp f _ _ _ _ _) (by pins_of h)
    obtain ⟨c', hs, h'⟩ := lstrcmp_exit sp r f mL m o s1 s2 hra hsp hsp2 hF _ _ _ _ _ _
      (lsObs_bit _ ((ult0_ofNat (by omega)).trans ((hAk.eq_iff (by omega)).trans (by omega)).symm) (hL.1 (by omega))) _ h2
    exact ⟨c', acc.trans hs, ⟨.inl h'⟩⟩
  · have g := ofNat_beq_f (a := s2.length - i) (b := k) (by omega) (by omega) e2
    by_cases e1 : s1.length - i = k
    · have g' := ofNat_beq_t (a := s1.length - i) (b := k) (by omega) (by omega) e1
      kit_run h acc until [0x8001a7a8]
      have h2 := h.repin (L' := lsE _ sp f _ _ _ _ _) (by pins_of h)
      obtain ⟨c', hs, h'⟩ := lstrcmp_exit sp r f mL m o s1 s2 hra hsp hsp2 hF _ _ _ _ _ _
        (lsObs_m1 (hL.2.1 (by omega) (by omega)) fun e => by subst e; omega) _ h2
      exact ⟨c', acc.trans hs, ⟨.inl h'⟩⟩
    · have g' := ofNat_beq_f (a := s1.length - i) (b := k) (by omega) (by omega) e1
      kit_run h acc until [0x8001a790]
      exact ⟨_, acc, ⟨.inr ⟨i + k + 1, _, by omega, hL.2.2 (by omega) (by omega), h.repin (by pins_of h)⟩⟩⟩

set_option hygiene false in
/-- `strcmp`'s context at chunk `i`, then the call (`strcoll` is `j strcmp`). -/
local macro "ls_call" ret:term : tactic => `(tactic| (
  have sc : ScCtx mL (P + i) (Q + i) (s1.length - i) $ret := ⟨hM.ro, by decide, by omega, by omega,
    by omega, by omega, by rw [Nat.add_assoc, show i + (s1.length - i) = s1.length by omega,
      hM.c1 _ (Nat.le_refl _), cb_len]⟩
  kit_run h acc until [0x8003b920]
  obtain ⟨_, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h)
    (strcmp_sum (P + i) (Q + i) (s1.length - i) $ret (BitVec.ofNat 64 (sp - 48))
      (KFrame.mk _ _ _ _ _ _ _ _ _ _ _) mL o sc)
  dsimp only [RetAt] at h
  obtain ⟨k, hok, hd | ⟨hv0, hz1, hz2⟩⟩ := ls_ans hM hA hv))

/-- **A chunk from the loop's call site** (`0x8001a790`). -/
theorem lstrcmp_B (P Q sp : Nat) (r : BitVec 64) (f : KFrame) (mL m : Mem) (o : Array String)
    (s1 s2 : List UInt8) (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 64 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : LsFrame mL m sp r f) (hM : LsMem mL P Q s1 s2) (i : Nat) (z : BitVec 64) (hA : Agree s1 s2 i) :
    Triple (SegSt 0x8001a790#64 (lsH P Q s1.length s2.length i z sp f) (ArmPay mL o))
      (LsNext r sp f m mL o P Q s1 s2 i) := by
  intro c h
  have acc := Steps.refl c
  ls_ctx
  have := hA.le1; have := hA.le2
  ls_call 0x8001a79c#64
  · have g : ((v + sign_extend (m := 64) (0x000#12)) == 0#64) = false := by simp [Vsa.Sim.sext_zero, hd.1]
    kit_run h acc until [0x8001a7a8]
    have h2 := h.repin (L' := lsE _ sp f _ _ _ _ _) (by pins_of h)
    obtain ⟨c', hs, h'⟩ := lstrcmp_exit sp r f mL m o s1 s2 hra hsp hsp2 hF _ _ _ _ _ _ hd.2 _ h2
    exact ⟨c', acc.trans hs, ⟨.inl h'⟩⟩
  · have g : ((v + sign_extend (m := 64) (0x000#12)) == 0#64) = true := by simp [Vsa.Sim.sext_zero, hv0]
    kit_run h acc until [0x8001a760]
    obtain ⟨c', hs, h'⟩ := lstrcmp_mid P Q sp r f mL m o s1 s2 hra hsp hsp2 hF hM i k z hA hok hz1 hz2 _
      (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩

/-- **The loop** (`seg_loop` over the chunk position). -/
theorem lstrcmp_loop (P Q sp : Nat) (r : BitVec 64) (f : KFrame) (mL m : Mem) (o : Array String)
    (s1 s2 : List UInt8) (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 64 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : LsFrame mL m sp r f) (hM : LsMem mL P Q s1 s2) (i : Nat) (z : BitVec 64) (hA : Agree s1 s2 i) :
    Triple (SegSt 0x8001a790#64 (lsH P Q s1.length s2.length i z sp f) (ArmPay mL o))
      (LsRet r (BitVec.ofNat 64 sp) f m o (sp - 48) sp s1 s2) := fun c h =>
  seg_loop (S := fun (a : Nat × BitVec 64) c => Agree s1 s2 a.1 ∧
      SegSt 0x8001a790#64 (lsH P Q s1.length s2.length a.1 a.2 sp f) (ArmPay mL o) c)
    (fun a => s1.length + 1 - a.1) (fun ⟨i, z⟩ c ⟨hA, h⟩ => by
      obtain ⟨c', hs, ⟨hn⟩⟩ := lstrcmp_B P Q sp r f mL m o s1 s2 hra hsp hsp2 hF hM i z hA c h
      rcases hn with hr | ⟨i', z', hi, hA', h'⟩
      · exact ⟨c', hs, .inr hr⟩
      · exact ⟨c', hs, .inl ⟨(i', z'), by have := hA'.le1; simp only; omega, hA', h'⟩⟩) (i, z) c ⟨hA, h⟩

/-- The first call site (`0x8001a744`, a long second string): `s3 = lnglen`. -/
abbrev lsA (P Q t2 n1 : Nat) (y z : BitVec 64) (sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x11, BitVec.ofNat 64 t2⟩ :: ⟨Register.x8, BitVec.ofNat 64 P⟩ :: ⟨Register.x9, BitVec.ofNat 64 Q⟩ ::
    ⟨Register.x18, BitVec.ofNat 64 n1⟩ :: ⟨Register.x19, y⟩ :: ⟨Register.x20, z⟩ ::
    ⟨Register.x2, BitVec.ofNat 64 (sp - 48)⟩ :: ⟨Register.x3, f.gp⟩ ::
    ⟨Register.x21, f.s5⟩ :: ⟨Register.x23, f.s7⟩ :: ⟨Register.x24, f.s8⟩ :: ⟨Register.x25, f.s9⟩ ::
    ⟨Register.x27, f.s11⟩ :: []

/-- **The first chunk from the first call site** (`0x8001a744`). -/
theorem lstrcmp_A (P Q t2 sp : Nat) (r : BitVec 64) (f : KFrame) (mL m : Mem) (o : Array String)
    (s1 s2 : List UInt8) (hra : r.toNat % 4 = 0) (hsp : tohostAddr + 16 + 64 ≤ sp) (hsp2 : sp ≤ 2 ^ 32)
    (hF : LsFrame mL m sp r f) (hM : LsMem mL P Q s1 s2) (y z : BitVec 64)
    (ht2 : tohostAddr + 16 ≤ t2) (ht2' : t2 + 24 ≤ 2 ^ 32)
    (hln : bytesT8 mL (t2 + 16) = BitVec.ofNat 64 s2.length) :
    Triple (SegSt 0x8001a744#64 (lsA P Q t2 s1.length y z sp f) (ArmPay mL o))
      (LsNext r sp f m mL o P Q s1 s2 0) := by
  intro c h
  have acc := Steps.refl c
  ls_ctx
  have i := 0
  have hA : Agree s1 s2 0 := ⟨Nat.zero_le _, Nat.zero_le _, fun j _ _ hj => absurd hj (Nat.not_lt_zero j)⟩
  have sc : ScCtx mL (P + 0) (Q + 0) (s1.length - 0) 0x8001a754#64 := ⟨hM.ro, by decide, by omega, by omega,
    by omega, by omega, by rw [Nat.add_assoc, show 0 + (s1.length - 0) = s1.length by omega,
      hM.c1 _ (Nat.le_refl _), cb_len]⟩
  kit_run h acc until [0x8003b920]
  have hln' := hln; unfold bytesT8 at hln'; rw [hln'] at h
  obtain ⟨_, acc, ⟨v, h, hv⟩⟩ := h.call acc (by pins_of h)
    (strcmp_sum (P + 0) (Q + 0) (s1.length - 0) 0x8001a754#64 (BitVec.ofNat 64 (sp - 48))
      (KFrame.mk _ _ _ _ _ _ _ _ _ _ _) mL o sc)
  dsimp only [RetAt] at h
  obtain ⟨k, hok, hd | ⟨hv0, hz1, hz2⟩⟩ := ls_ans hM hA hv
  · have g : ((v + sign_extend (m := 64) (0x000#12)) != 0#64) = true := by simp [Vsa.Sim.sext_zero, hd.1]
    kit_run h acc until [0x8001a7a8]
    have h2 := h.repin (L' := lsE _ sp f _ _ _ _ _) (by pins_of h)
    obtain ⟨c', hs, h'⟩ := lstrcmp_exit sp r f mL m o s1 s2 hra hsp hsp2 hF _ _ _ _ _ _ hd.2 _ h2
    exact ⟨c', acc.trans hs, ⟨.inl h'⟩⟩
  · have g : ((v + sign_extend (m := 64) (0x000#12)) != 0#64) = false := by simp [Vsa.Sim.sext_zero, hv0]
    kit_run h acc until [0x8001a760]
    obtain ⟨c', hs, h'⟩ := lstrcmp_mid P Q sp r f mL m o s1 s2 hra hsp hsp2 hF hM 0 k z hA hok hz1 hz2 _
      (h.repin (by pins_of h))
    exact ⟨c', acc.trans hs, h'⟩

end Lua.Vm.Sim.Kit

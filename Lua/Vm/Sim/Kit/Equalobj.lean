import Lua.Vm.Sim.Kit.Close
import Lua.Vm.Arms.Segs.HluaV_equalobj
import Vsa.Sim.Muldi3Spec

/-!
# `luaV_equalobj` at the Lua ELF's address: the call-node summary (M5)

On two represented F1 values that are not both long strings, the helper is
loop-free (`ttypetag` compare, then the jump table on the variant: nil and
booleans equal, integers, short strings and `print` by payload), so it is
classified after value pruning (ROUND-3 §3, M5) and run under its generated
segments. The long-string case (`luaS_eqlngstr` → `memcmp`) is outside the
summary: see `abstractions/bakeoff3/KIT.md`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-! ## Reads -/

/-- A tag read at a raw address that is slot `n`'s tag byte. -/
theorem bytesT1_tag {m : Mem} {a : Nat} (n : Nat) (h : a = n + 8) : bytesT1 m a = slotTag m n := by
  subst h; rfl

theorem bytesT8_wm8_out {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bytesT8_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

theorem bytesT4_wm8_out {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 4 ≤ a ∨ a + 8 ≤ x) :
    bytesT4 (writeMap8 m a d) x = bytesT4 m x :=
  bytesT4_congr fun i _ => getElem?_writeMap8_out m a d _ (by omega)

/-- `ld ra, 40(sp)` reads back the prologue's `sd ra, 40(sp)`. -/
theorem ld_ra {m : Mem} {a : Nat} {r : BitVec 64} :
    sign_extend (m := 64) (bytesT8 (writeMap8 m a (sdData_val r)) a : BitVec (8 * 8)) = r := by
  rw [bytesT8_writeMap8, sext64_id, sdData_id]

/-- `addi sp, sp, -48` then `addi sp, sp, 48`. -/
theorem sp_back (x : BitVec 64) :
    x + sign_extend (m := 64) (0xfd0#12) + sign_extend (m := 64) (0x030#12) = x := by
  rw [BitVec.add_assoc, show sign_extend (m := 64) (0xfd0#12) + sign_extend (m := 64) (0x030#12)
    = 0#64 by decide, BitVec.add_zero]

/-! ## The jump table on the variant -/

/-- Byte `i` of the jump table's entry `v` (`.rodata` at `0x80053310`). -/
def eqByte (v i : Nat) : BitVec 8 := Image.rodataByte (0x80053310 - Image.rodataBase + 4 * v + i)

/-- The jump table's entry `v`, as `lw` reads it. -/
def eqWord (v : Nat) : BitVec 32 :=
  (((eqByte v 3).append (eqByte v 2)).append (eqByte v 1)).append (eqByte v 0)

theorem eqWord_eq {m : Mem} (h : RodataRead m) {v : Nat} (hv : v < 23) :
    bytesT4 m (0x80053310 + 4 * v) = eqWord v := by
  have hb : ∀ i, i < 4 → bytesT1 m (0x80053310 + 4 * v + i) = eqByte v i := by
    intro i hi
    have := h (0x80053310 - Image.rodataBase + 4 * v + i)
      (by simp only [Image.rodataBase, Image.rodataSize]; omega)
    rw [show Image.rodataBase + (0x80053310 - Image.rodataBase + 4 * v + i)
      = 0x80053310 + 4 * v + i by simp only [Image.rodataBase]; omega] at this
    exact this
  have h0 := hb 0 (by omega)
  simp only [bytesT1, Nat.add_zero] at h0 hb
  simp only [bytesT4, eqWord, h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega)]

/-- The table's base `0x80053310`. -/
abbrev eqTB : BitVec 64 :=
  ((0x8001b7d4#64) + sign_extend (m := 64) ((0x00038#20) +++ 0x000#12)) + sign_extend (m := 64) (0xb3c#12)

/-- The arm of variant `t` (`tt & 63`): nil and booleans return 1
(`0x8001b84c`), integers, short strings and light C functions compare
payloads (`0x8001b7f4`). -/
theorem eq_target : ∀ t ∈ [0, 1, 17, 3, 4, 22],
    BitVec.update ((sign_extend (m := 64) (eqWord t) + eqTB) +
      sign_extend (m := 64) (0x000#12)) 0 0#1
      = if t = 3 ∨ t = 4 ∨ t = 22 then 0x8001b7f4#64 else 0x8001b84c#64 := by
  decide +kernel

theorem RodataRead.wm8 {m : Mem} (h : RodataRead m) {a : Nat} {d : BitVec (8 * 8)}
    (ha : Image.rodataBase + Image.rodataSize ≤ a) : RodataRead (writeMap8 m a d) := fun o ho => by
  rw [bytesT1_writeMap8_out m a d (by omega)]; exact h o ho

/-- **The jump on the variant** (`jr a5` at `0x8001b7f0`): with the variant
`V = tt & 63` one of F1's, the target is the arm of `eq_target`. -/
theorem eq_jump {m : Mem} (hro : RodataRead m) {V : BitVec 64} (t : Nat) (ht : t ∈ [0, 1, 17, 3, 4, 22])
    (hV : V = BitVec.ofNat 64 t) :
    BitVec.update (((sign_extend (m := 64) (bytesT4 m (((shift_bits_left V
      (Sail.BitVec.extractLsb (0x02#6) 5 0)) + eqTB) + sign_extend (m := 64) (0x000#12)).toNat :
        BitVec (8 * 4))) + eqTB) + sign_extend (m := 64) (0x000#12)) 0 0#1
      = if t = 3 ∨ t = 4 ∨ t = 22 then 0x8001b7f4#64 else 0x8001b84c#64 := by
  subst hV
  have ha : ∀ t ∈ [0, 1, 17, 3, 4, 22], ((shift_bits_left (BitVec.ofNat 64 t)
      (Sail.BitVec.extractLsb (0x02#6) 5 0)) + eqTB + sign_extend (m := 64) (0x000#12)).toNat
      = 0x80053310 + 4 * t := by decide +kernel
  have hlt : t < 23 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht; rcases ht with h | h | h | h | h | h <;> omega
  rw [ha t ht, eqWord_eq hro hlt]
  exact eq_target t ht

/-- `luaV_equalobj`'s entry: `L`, the two `TValue` addresses, the return
address, `sp` and the caller's frame. -/
abbrev eqPre (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) : List Pin :=
  ⟨Register.x10, L⟩ :: ⟨Register.x11, BitVec.ofNat 64 n1⟩ :: ⟨Register.x12, BitVec.ofNat 64 n2⟩ ::
    ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins

/-- The memory at the return: `ra` saved below `sp`. -/
syntax "eqMem(" term ", " term ", " term ")" : term
macro_rules
  | `(eqMem($m, $sp, $r)) => `(writeMap8 $m ((BitVec.ofNat 64 $sp + sign_extend (m := 64) (0xfd0#12)) +
      sign_extend (m := 64) (0x028#12)).toNat (sdData_val $r))

/-- The facts every path of the summary uses. -/
structure EqCtx (m : Mem) (n1 n2 sp : Nat) (r : BitVec 64) : Prop where
  ro : RodataRead m
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 48 ≤ sp
  sp_hi : sp < 2^32
  sp_al : sp % 8 = 0
  n1_lo : tohostAddr + 16 ≤ n1
  n1_hi : n1 + 16 + 48 ≤ sp
  n2_lo : tohostAddr + 16 ≤ n2
  n2_hi : n2 + 16 + 48 ≤ sp

set_option hygiene false in
local macro_rules
  | `(tactic| kit_bv_norm) => `(tactic| try simp (disch := kit_disch) only [bytesT1_writeMap8_out,
      bytesT1_tag n1, bytesT1_tag n2, slotTag_wm8, ht1, ht2])

set_option hygiene false in
/-- The variant jump's target, from the tag (`eq_jump`). -/
local macro "eq_jr" : tactic => `(tactic| first
  | rw [eq_jump hro' 0 (by decide) (by kit_bv_norm; decide)]
  | rw [eq_jump hro' 1 (by decide) (by kit_bv_norm; decide)]
  | rw [eq_jump hro' 17 (by decide) (by kit_bv_norm; decide)]
  | rw [eq_jump hro' 3 (by decide) (by kit_bv_norm; decide)]
  | rw [eq_jump hro' 4 (by decide) (by kit_bv_norm; decide)]
  | rw [eq_jump hro' 22 (by decide) (by kit_bv_norm; decide)])

local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
    | (kit_bv_norm; decide)
    | (eq_jr; decide)
    | (rw [ld_ra, Vsa.Sim.ret_tgt _ (by assumption)]; assumption))

theorem eqo_const (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) (t : Nat) (ht : t = 0 ∨ t = 1 ∨ t = 17)
    (ht1 : slotTag m n1 = BitVec.ofNat 8 t) (ht2 : slotTag m n2 = BitVec.ofNat 8 t) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, 1#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (eqMem(m, sp, r)) o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hro' : RodataRead (eqMem(m, sp, r)) :=
    RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch)
  rcases ht with rfl | rfl | rfl
  all_goals
    kit_run h acc
    have h := h.at (pc' := 0x8001b84c#64) (by eq_jr; decide)
    kit_run h acc
    have h := h.at (pc' := r) (by rw [ld_ra]; exact Vsa.Sim.ret_tgt r hra)
    simp only [sp_back, Vsa.Sim.sext_one, BitVec.zero_add] at h
    exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- Integers, short strings, `print`: the payloads compared (`0x8001b7f4`). -/
theorem eqo_pay (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) (t : Nat) (ht : t = 3 ∨ t = 68 ∨ t = 22)
    (ht1 : slotTag m n1 = BitVec.ofNat 8 t) (ht2 : slotTag m n2 = BitVec.ofNat 8 t) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if slotVal m n1 = slotVal m n2 then 1#64 else 0#64⟩ ::
        ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay (eqMem(m, sp, r)) o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hro' : RodataRead (eqMem(m, sp, r)) :=
    RodataRead.wm8 hro (by simp only [Image.rodataBase, Image.rodataSize]; kit_disch)
  rcases ht with rfl | rfl | rfl
  all_goals
    kit_run h acc
    have h := h.at (pc' := 0x8001b7f4#64) (by eq_jr; decide)
    kit_run h acc
    have h := h.at (pc' := r) (by rw [ld_ra]; exact Vsa.Sim.ret_tgt r hra)
    simp (disch := kit_disch) only [sp_back, ld_slot_gen n1, ld_slot_gen n2, slotVal_wm8,
      ult_one_sub, bitb, decide_eq_true_eq] at h
    exact ⟨_, acc, h.repin (by pins_of h)⟩

/-- F1's register tags (`ValRepr`): nil, false, true, integer, short and long
string, `print`. -/
abbrev f1Tags : List (BitVec 8) := [0#8, 1#8, 17#8, 3#8, 68#8, 84#8, 22#8]

theorem diff_var : ∀ t1 ∈ f1Tags, ∀ t2 ∈ f1Tags, t1 ≠ t2 →
    ((zero_extend (m := 64) (t1 : BitVec (8 * 1)) ^^^ zero_extend (m := 64) (t2 : BitVec (8 * 1))) &&&
      sign_extend (m := 64) (0x03f#12) == 0#64) = false := by decide +kernel

theorem diff_num : ∀ t1 ∈ f1Tags, ∀ t2 ∈ f1Tags, t1 ≠ t2 →
    ((zero_extend (m := 64) (t1 : BitVec (8 * 1)) ^^^ zero_extend (m := 64) (t2 : BitVec (8 * 1))) &&&
      sign_extend (m := 64) (0x00f#12) != 0#64) = false →
    ((zero_extend (m := 64) (t1 : BitVec (8 * 1)) &&& sign_extend (m := 64) (0x00f#12)) ==
      (0#64 + sign_extend (m := 64) (0x003#12))) = false := by decide +kernel

/-- Different variants: not equal (`0x8001b7b8`). -/
theorem eqo_diff (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) (ht1 : slotTag m n1 ∈ f1Tags) (ht2 : slotTag m n2 ∈ f1Tags)
    (hne : slotTag m n1 ≠ slotTag m n2) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins)
        (ArmPay (eqMem(m, sp, r)) o)) := by
  intro c h
  have acc := Steps.refl c
  obtain ⟨hro, hra, h1, h2, h3, h4, h5, h6, h7⟩ := hx
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have g1 := diff_var _ ht1 _ ht2 hne
  by_cases g2 : ((zero_extend (m := 64) (slotTag m n1 : BitVec (8 * 1)) ^^^
      zero_extend (m := 64) (slotTag m n2 : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x00f#12)
        != 0#64) = false
  · have g3 := diff_num _ ht1 _ ht2 hne g2
    kit_run h acc
    have h := h.at (pc' := r) (by rw [ld_ra]; exact Vsa.Sim.ret_tgt r hra)
    simp only [sp_back, Vsa.Sim.sext_zero, BitVec.zero_add] at h
    exact ⟨_, acc, h.repin (by pins_of h)⟩
  · simp only [Bool.not_eq_false] at g2
    kit_run h acc
    have h := h.at (pc' := r) (by rw [ld_ra]; exact Vsa.Sim.ret_tgt r hra)
    simp only [sp_back, Vsa.Sim.sext_zero, BitVec.zero_add] at h
    exact ⟨_, acc, h.repin (by pins_of h)⟩

/-! ## M2: what the tag says about the value -/

section
variable {mo : Mem} {ι : Strs}

theorem strTag_lit (s : List UInt8) :
    BitVec.ofNat 8 (strTag s) = 68#8 ∨ BitVec.ofNat 8 (strTag s) = 84#8 := by
  rcases strTag_cases s with e | e <;> rw [e] <;> decide

theorem _root_.Lua.Vm.Sim.ValRepr.tag_mem {t : BitVec 8} {x : BitVec 64} {v : Value} (h : ValRepr mo ι t x v)
    (hv : v.NotFlt) : t ∈ f1Tags := by
  cases h with
  | str => rcases strTag_lit _ with e | e <;> rw [e] <;> decide
  | flt => exact absurd rfl (hv _ _)
  | _ => decide

/-- The tag of a value (`ValRepr`). -/
def tagOf : Value → BitVec 8
  | .nil => 0#8
  | .bool false => 1#8
  | .bool true => 17#8
  | .int _ => 3#8
  | .flt _ _ => 19#8
  | .str s => BitVec.ofNat 8 (strTag s)
  | .builtin _ => 22#8

theorem str_tag (s : List UInt8) : tagOf (.str s) = 68#8 ∨ tagOf (.str s) = 84#8 := strTag_lit s

theorem _root_.Lua.Vm.Sim.ValRepr.tag_eq {t : BitVec 8} {x : BitVec 64} {v : Value} (h : ValRepr mo ι t x v) :
    t = tagOf v := by
  cases h <;> rfl

/-- A value has one tag. -/
theorem _root_.Lua.Vm.Sim.ValRepr.tag_det {t1 t2 : BitVec 8} {x1 x2 : BitVec 64} {v : Value}
    (h1 : ValRepr mo ι t1 x1 v) (h2 : ValRepr mo ι t2 x2 v) : t1 = t2 :=
  h1.tag_eq.trans h2.tag_eq.symm

/-- Nil and the booleans: the tag is the value. -/
theorem _root_.Lua.Vm.Sim.ValRepr.eq_of_tag {t : BitVec 8} {x1 x2 : BitVec 64} {v1 v2 : Value}
    (h1 : ValRepr mo ι t x1 v1) (h2 : ValRepr mo ι t x2 v2) (ht : t = 0#8 ∨ t = 1#8 ∨ t = 17#8) :
    v1 = v2 := by
  have e1 := h1.tag_eq; have e2 := h2.tag_eq
  have hns : ∀ s, t ≠ tagOf (.str s) := fun s e => by
    rcases str_tag s with e' | e' <;> rw [e'] at e <;> subst e <;> revert ht <;> decide
  rcases v1 with _ | b1 | i1 | ⟨x1, n1⟩ | s1 | f1 <;> rcases v2 with _ | b2 | i2 | ⟨x2, n2⟩ | s2 | f2
  all_goals (try cases b1) <;> (try cases b2) <;> (try cases f1) <;> (try cases f2)
  all_goals first
    | rfl
    | exact absurd e1 (hns _)
    | exact absurd e2 (hns _)
    | (exfalso; subst e1; revert e2 ht; simp only [tagOf]; decide)
end

section
variable {mo : Mem} {ι : Strs}

theorem strTag_short {s : List UInt8} (h : BitVec.ofNat 8 (strTag s) = 68#8) : s.length ≤ maxShortLen := by
  unfold strTag at h; split at h
  · assumption
  · exact absurd h (by decide)

/-- Integers, short strings, `print`: equal values are equal payloads
(`eqshrstr` is pointer equality: the intern map `ι`, `TStringRepr.inj`). -/
theorem _root_.Lua.Vm.Sim.ValRepr.eq_iff_payload {t1 t2 : BitVec 8} {x1 x2 : BitVec 64} {v1 v2 : Value}
    (h1 : ValRepr mo ι t1 x1 v1) (h2 : ValRepr mo ι t2 x2 v2) (he : t1 = t2)
    (ht : t1 = 3#8 ∨ t1 = 68#8 ∨ t1 = 22#8) : v1 = v2 ↔ x1 = x2 := by
  cases h1 <;> cases h2
  all_goals first
    | (exfalso; revert he ht; decide)
    | (exfalso; rcases strTag_lit ‹List UInt8› with e | e <;> simp only [e] at he ht <;>
        first | done | (revert he ht; decide))
    | (simp; done)
    | (rename_i e1 e2; subst e1 e2; simp)
    | skip
  rename_i s1 r1 i1 _ s2 r2 i2 _
  have h68 : BitVec.ofNat 8 (strTag s1) = 68#8 := by
    rcases strTag_lit s1 with e | e <;> rw [e] at ht ⊢ <;> revert ht <;> decide
  have hs1 := i1 (strTag_short h68)
  have hs2 := i2 (strTag_short (he ▸ h68))
  constructor
  · intro e; cases e; exact BitVec.eq_of_toNat_eq (hs1.trans hs2.symm)
  · intro e; subst e; rw [TStringRepr.inj r1 r2]
end

/-- **`luaV_equalobj`, the call-node summary**: on two represented values,
neither a float (`FloatArms`) and not both long strings, `a0` is `δ .eq`'s
answer as 0/1; `ra` is saved below `sp`. -/
theorem equalobj_sum (L r : BitVec 64) (n1 n2 sp : Nat) (f : KFrame) (m : Mem) (o : Array String)
    (hx : EqCtx m n1 n2 sp r) {mo : Mem} {ι : Strs} {v1 v2 : Value}
    (hv1 : ValRepr mo ι (slotTag m n1) (slotVal m n1) v1)
    (hv2 : ValRepr mo ι (slotTag m n2) (slotVal m n2) v2) (hf1 : v1.NotFlt) (hf2 : v2.NotFlt)
    (hl : ¬ (slotTag m n1 = 84#8 ∧ slotTag m n2 = 84#8)) :
    Triple (SegSt 0x8001b780#64 (eqPre L r n1 n2 sp f) (ArmPay m o))
      (SegSt r (⟨Register.x10, if v1 = v2 then 1#64 else 0#64⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
        f.pins) (ArmPay (eqMem(m, sp, r)) o)) := by
  by_cases he : slotTag m n1 = slotTag m n2
  · have ht := hv1.tag_mem hf1
    simp only [f1Tags, List.mem_cons, List.not_mem_nil, or_false] at ht
    have hv2' := he ▸ hv2
    rcases ht with e | e | e | e | e | e | e
    · rw [if_pos (hv1.eq_of_tag hv2' (.inl e))]; exact eqo_const L r n1 n2 sp f m o hx 0 (.inl rfl) e (he ▸ e)
    · rw [if_pos (hv1.eq_of_tag hv2' (.inr (.inl e)))]
      exact eqo_const L r n1 n2 sp f m o hx 1 (.inr (.inl rfl)) e (he ▸ e)
    · rw [if_pos (hv1.eq_of_tag hv2' (.inr (.inr e)))]
      exact eqo_const L r n1 n2 sp f m o hx 17 (.inr (.inr rfl)) e (he ▸ e)
    · simp only [hv1.eq_iff_payload hv2 he (.inl e)]
      exact eqo_pay L r n1 n2 sp f m o hx 3 (.inl rfl) e (he ▸ e)
    · simp only [hv1.eq_iff_payload hv2 he (.inr (.inl e))]
      exact eqo_pay L r n1 n2 sp f m o hx 68 (.inr (.inl rfl)) e (he ▸ e)
    · exact absurd ⟨e, he ▸ e⟩ hl
    · simp only [hv1.eq_iff_payload hv2 he (.inr (.inr e))]
      exact eqo_pay L r n1 n2 sp f m o hx 22 (.inr (.inr rfl)) e (he ▸ e)
  · rw [if_neg (fun e => he (by subst e; exact hv1.tag_det hv2))]
    exact eqo_diff L r n1 n2 sp f m o hx (hv1.tag_mem hf1) (hv2.tag_mem hf2) he

end Lua.Vm.Sim.Kit

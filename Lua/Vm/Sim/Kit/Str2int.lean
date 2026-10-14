import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Sim.Kit.Memcmp
import Lua.Vm.Sim.Kit.AtArm
import Lua.Vm.Sim.Kit.Equalobj
import Lua.Vm.Arms.Segs.HluaO_str2num
import Lua.Num.DecimalIdx

/-!
# `luaO_str2num` on an integer numeral (lane F1-F8)

`luaO_str2num(s, o)` (`lobject.c:308`, `0x80011998`) first runs `l_str2int`
(inlined): the leading spaces (`lisspace`, `luai_ctype_`'s bit 3), a sign,
`0x`/`0X` and hex digits (wrapping) or decimal digits (`MAXBY10`/`MAXLASTD`
overflow test), the trailing spaces, the terminating `\0`; on success `o` is
the integer and the result the string's size plus one. This file proves that
path on a string `str2int` accepts (`Lua.Num.str2int`), by `kit_run` over the
generated segments (`Segs/HluaO_str2num.lean`) and `seg_loop` per loop.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Layout Lua.Num
open Vsa.Machine (MState Config Steps)

/-! ## `luai_ctype_` (`lctype.c`, `.rodata` at `0x80052030`) -/

/-- The table entry of byte `c` (`luai_ctype_[c + 1]`). -/
def ctypeOf (c : BitVec 8) : BitVec 8 := Image.rodataByte (0x80052031 - Image.rodataBase + c.toNat)

theorem ctype_rd {m : Mem} (h : RodataRead m) (c : BitVec 8) :
    bytesT1 m (0x80052031 + c.toNat) = ctypeOf c := by
  have hc := c.isLt
  have := h (0x80052031 - Image.rodataBase + c.toNat) (by simp only [Image.rodataBase, Image.rodataSize]; omega)
  rwa [show Image.rodataBase + (0x80052031 - Image.rodataBase + c.toNat) = 0x80052031 + c.toNat by
    simp only [Image.rodataBase]; omega] at this

/-- `lisspace` is `isSpace`. -/
theorem ctype_space : ∀ c : BitVec 8, ((ctypeOf c) &&& 8#8 != 0#8) = isSpace (UInt8.ofBitVec c) := by
  decide

/-- `lisdigit` is a decimal digit. -/
theorem ctype_digit : ∀ c : BitVec 8,
    ((ctypeOf c) &&& 2#8 != 0#8) = (digitVal false (UInt8.ofBitVec c)).isSome := by
  decide

/-- `lisxdigit` is a hex digit. -/
theorem ctype_xdigit : ∀ c : BitVec 8,
    ((ctypeOf c) &&& 16#8 != 0#8) = (digitVal true (UInt8.ofBitVec c)).isSome := by
  decide

-- the table is read through the lemmas above, never evaluated in a run
attribute [irreducible] ctypeOf

/-! ## The string in memory -/

/-- Byte `k` of `s` (`0` past its end: the terminator). -/
def sb (s : List UInt8) (k : Nat) : BitVec 8 := (s.getD k 0).toBitVec

/-- **The string `s` at `P`, `\0`-terminated**, in RAM off the HTIF mailbox. -/
structure StrAt (m : Mem) (P : Nat) (s : List UInt8) : Prop where
  byte : ∀ k, k ≤ s.length → bytesT1 m (P + k) = sb s k
  lo : 0x80000000 ≤ P
  hi : P + s.length + 16 ≤ tohostAddr ∨ tohostAddr + 16 ≤ P
  top : P + s.length + 16 ≤ 2 ^ 32

/-- The `luai_ctype_` base built by `auipc; addi`. -/
theorem ctype_base :
    (((0x8001199c#64) + sign_extend (m := 64) ((0x00040#20) +++ 0x000#12)) + sign_extend (m := 64) (0x694#12)) =
      0x80052030#64 := by decide

/-- A table read's address. -/
theorem ctype_addr (c : BitVec 8) :
    ((0x80052030#64 + (zero_extend (m := 64) (c : BitVec (8 * 1)))) + sign_extend (m := 64) (0x001#12)).toNat =
      0x80052031 + c.toNat := by
  have := c.isLt
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_add, BitVec.toNat_setWidth,
    show (sign_extend (m := 64) (0x001#12)).toNat = 1 by decide]
  simp only [BitVec.toNat_ofNat]
  omega

/-- The masks of the table entry as the machine tests them. -/
theorem zext_and8 (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x008#12) != 0#64) = (x &&& 8#8 != 0#8) := by
  revert x; decide
theorem zext_and8_eq (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x008#12) == 0#64) = !(x &&& 8#8 != 0#8) := by
  revert x; decide

theorem ofBitVec_sb (s : List UInt8) (k : Nat) : UInt8.ofBitVec (sb s k) = bAt s k := rfl

/-- The table test of a string byte: `lisspace`. -/
theorem sp_test {m : Mem} (hro : RodataRead m) (c : BitVec 8) :
    ((zero_extend (m := 64) (bytesT1 m ((0x80052030#64 + (zero_extend (m := 64) (c : BitVec (8 * 1)))) +
      sign_extend (m := 64) (0x001#12)).toNat : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x008#12) == 0#64) =
      !isSpace (UInt8.ofBitVec c) := by
  rw [ctype_addr, ctype_rd hro, zext_and8_eq, ctype_space]

theorem sp_test_ne {m : Mem} (hro : RodataRead m) (c : BitVec 8) :
    ((zero_extend (m := 64) (bytesT1 m ((0x80052030#64 + (zero_extend (m := 64) (c : BitVec (8 * 1)))) +
      sign_extend (m := 64) (0x001#12)).toNat : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x008#12) != 0#64) =
      isSpace (UInt8.ofBitVec c) := by
  rw [ctype_addr, ctype_rd hro, zext_and8, ctype_space]

/-- The frame of `luaO_str2num`'s integer path (a leaf: every callee-saved
register kept). -/
abbrev s2Pre (P o : Nat) (r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 P⟩ :: ⟨Register.x11, BitVec.ofNat 64 o⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- `o` with the integer `v` stored (`setivalue`). -/
abbrev s2Mem (m : Mem) (o : Nat) (v : BitVec 64) : Mem :=
  (writeMap8 m o (sdData_val v)).insert (o + 8) (stData 1 (3#64))

/-- **The return**: the size `len + 1`, `o` the integer. -/
abbrev s2Post (len : Nat) (r : BitVec 64) (f : HFrame) (m : Mem) (o : Nat) (v : BitVec 64)
    (out : Array String) : Config → Prop :=
  SegSt r (⟨Register.x10, BitVec.ofNat 64 (len + 1)⟩ :: f.pins) (ArmPay (s2Mem m o v) out)

/-- The facts every phase uses. -/
structure S2Ctx (m : Mem) (P o : Nat) (s : List UInt8) (r : BitVec 64) : Prop where
  ro : RodataRead m
  str : StrAt m P s
  ra : r.toNat % 4 = 0
  o_al : o % 8 = 0
  o_lo : tohostAddr + 16 ≤ o
  o_hi : o + 16 ≤ 2 ^ 32

set_option hygiene false in
/-- The phases' context facts in scope (`kit_disch`'s). -/
local macro "s2_facts" : tactic => `(tactic| (
  have hro := hx.ro; have hbyte := hx.str.byte
  have hbyte0 : bytesT1 m P = sb s 0 := hbyte 0 (Nat.zero_le _)
  have hP := hx.str.lo; have hP2 := hx.str.top; have hPh := hx.str.hi
  have hra := hx.ra; have ho1 := hx.o_al; have ho2 := hx.o_lo; have ho3 := hx.o_hi
  have hTH : tohostAddr = 0x8005c6c0 := rfl))

/-- A byte against a character (`li; beq`/`bne`, the constant as `add_imm` leaves it). -/
theorem s2_c48 : ∀ x : BitVec 8, ((zero_extend (m := 64) (x : BitVec (8 * 1))) ==
    BitVec.ofNat 64 (0 + 48)) = (UInt8.ofBitVec x == 48) := by decide
theorem s2_c45 : ∀ x : BitVec 8, ((zero_extend (m := 64) (x : BitVec (8 * 1))) ==
    BitVec.ofNat 64 (0 + 45)) = (UInt8.ofBitVec x == 45) := by decide
theorem s2_c43 : ∀ x : BitVec 8, ((zero_extend (m := 64) (x : BitVec (8 * 1))) !=
    BitVec.ofNat 64 (0 + 43)) = !(UInt8.ofBitVec x == 43) := by decide
theorem s2_cX : ∀ x : BitVec 8, (((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x0df#12)) !=
    BitVec.ofNat 64 (0 + 88)) = !(UInt8.ofBitVec x == 120 || UInt8.ofBitVec x == 88) := by decide

set_option hygiene false in
/-- The run's normal form: addresses over `Nat`, the string's bytes, the
table's answers. -/
local macro "s2_norm" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic|
  simp (disch := first | assumption | (simp only [ofBitVec_sb]; assumption) | kit_disch) only [Nat.add_zero, bgeu_ofNat, bne_ofNat, blt_ofNat, s2_dig, Nat.ble_eq,
    Nat.blt_eq, Nat.beq_eq, Bool.not_eq_true', Bool.not_eq_false', decide_eq_true_eq, decide_eq_false_iff_not, ctype_base, addr0, add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_assoc, hbyte, hbyte0, ctype_addr, ctype_rd hro, zext_and8, zext_and8_eq, ctype_space, ofBitVec_sb,
    Vsa.Sim.ret_tgt _ hra, sextw_zext, sextw_zext', sb_len, zext_zero8, s2_add0, zext_and2,
    zext_and2_eq, zext_and16, zext_and16_eq, ctype_digit, ctype_xdigit, s2_t3, s2_t5, s2_t6, s2_mul10,
    s2_mul16, s2_zero, s2_hexl, s2_c48, s2_c45, s2_c43, s2_cX] $[$loc]?)

theorem sb_len (s : List UInt8) : sb s s.length = 0#8 := by
  simp only [sb]; rw [show s.getD s.length 0 = bAt s s.length from rfl, bAt_ge (Nat.le_refl _)]; rfl

theorem sb_ge {s : List UInt8} {j : Nat} (h : s.length ≤ j) : sb s j = 0#8 := by
  simp only [sb]; rw [show s.getD j 0 = bAt s j from rfl, bAt_ge h]; rfl

/-- `sext.w` of a byte (`lbu` then `sext.w`). -/
theorem sextw_zext (c : BitVec 8) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((zero_extend (m := 64) (c : BitVec (8 * 1))) +
      sign_extend (m := 64) (0x000#12)) 31 0) = zero_extend (m := 64) (c : BitVec (8 * 1)) := by
  revert c; decide

theorem sextw_zext' (c : BitVec 8) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (zero_extend (m := 64) (c : BitVec (8 * 1))) 31 0) =
      zero_extend (m := 64) (c : BitVec (8 * 1)) := by
  revert c; decide

theorem zext_zero8 : zero_extend (m := 64) ((0#8 : BitVec 8) : BitVec (8 * 1)) = 0#64 := by decide

theorem s2_add0 (c : BitVec 8) :
    (zero_extend (m := 64) (c : BitVec (8 * 1))) + sign_extend (m := 64) (0x000#12) = zero_extend (m := 64) (c : BitVec (8 * 1)) := by
  rw [Vsa.Sim.sext_zero, BitVec.add_zero]

theorem zext_and2 (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x002#12) != 0#64) = (x &&& 2#8 != 0#8) := by
  revert x; decide
theorem zext_and2_eq (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x002#12) == 0#64) = !(x &&& 2#8 != 0#8) := by
  revert x; decide
theorem zext_and16 (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x010#12) != 0#64) = (x &&& 16#8 != 0#8) := by
  revert x; decide
theorem zext_and16_eq (x : BitVec 8) :
    ((zero_extend (m := 64) (x : BitVec (8 * 1))) &&& sign_extend (m := 64) (0x010#12) == 0#64) = !(x &&& 16#8 != 0#8) := by
  revert x; decide

/-- `MAXBY10 - 1` and `MAXBY10` as `l_str2int`'s prologue builds them. -/
theorem s2_t3 : ((shift_bits_left ((sign_extend (m := 64) ((0x03333#20) +++ 0x000#12)) + sign_extend (m := 64) (0x333#12))
    (Sail.BitVec.extractLsb (0x22#6) 5 0)) + ((shift_bits_left ((sign_extend (m := 64) ((0x000cd#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0xccd#12)) (Sail.BitVec.extractLsb (0x0c#6) 5 0)) + sign_extend (m := 64) (0xccb#12))) =
    BitVec.ofNat 64 922337203685477579 := by decide
theorem s2_t5 : ((shift_bits_left ((sign_extend (m := 64) ((0x03333#20) +++ 0x000#12)) + sign_extend (m := 64) (0x333#12))
    (Sail.BitVec.extractLsb (0x22#6) 5 0)) + (shift_bits_left ((sign_extend (m := 64) ((0x33333#20) +++ 0x000#12)) +
    sign_extend (m := 64) (0x333#12)) (Sail.BitVec.extractLsb (0x02#6) 5 0))) =
    BitVec.ofNat 64 922337203685477580 := by decide
/-- `MAXLASTD + neg` (`addiw t6, t4, 7`). -/
theorem s2_t6 (neg : Bool) : sign_extend (m := 64) (Sail.BitVec.extractLsb ((if neg then 1#64 else 0#64) +
    sign_extend (m := 64) (0x007#12)) 31 0) = BitVec.ofNat 64 (7 + if neg then 1 else 0) := by
  cases neg <;> decide

/-- A decimal digit's value (`addiw a3, a2, -48`). -/
theorem s2_dig : ∀ c : BitVec 8, (digitVal false (UInt8.ofBitVec c)).isSome = true →
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((zero_extend (m := 64) (c : BitVec (8 * 1))) +
      sign_extend (m := 64) (0xfd0#12)) 31 0) =
      BitVec.ofNat 64 ((digitVal false (UInt8.ofBitVec c)).getD 0) := by decide

/-- `10 · a + d` (`slli 2; add; slli 1; add`). -/
theorem s2_mul10 (A d : Nat) :
    BitVec.ofNat 64 d + shift_bits_left ((shift_bits_left (BitVec.ofNat 64 A) (Sail.BitVec.extractLsb (0x02#6) 5 0)) +
      BitVec.ofNat 64 A) (Sail.BitVec.extractLsb (0x01#6) 5 0) = BitVec.ofNat 64 (A * 10 + d) := by
  rw [shl_ofNat _ 2 (by decide), BitVec.ofNat_add_ofNat, shl_ofNat _ 1 (by decide), BitVec.ofNat_add_ofNat]
  congr 1; omega

theorem bgeu_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    zopz0zKzJ_u (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (y ≤ x) := by
  unfold zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  exact decide_eq_decide.mpr Int.ofNat_le

theorem blt_ofNat {x y : Nat} (hx : x < 2 ^ 63) (hy : y < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 x) (BitVec.ofNat 64 y) = decide (x < y) := by
  rw [Lua.Vm.Sim.At.slt_toInt]
  have e1 : (BitVec.ofNat 64 x).toInt = x := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_ofNat]; omega)]; simp; omega
  have e2 : (BitVec.ofNat 64 y).toInt = y := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp [BitVec.toNat_ofNat]; omega)]; simp; omega
  rw [e1, e2]; exact decide_eq_decide.mpr Int.ofNat_lt

theorem bne_ofNat {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    (BitVec.ofNat 64 x != BitVec.ofNat 64 y) = !decide (x = y) := by
  by_cases h : x = y
  · subst h; simp
  · have : BitVec.ofNat 64 x ≠ BitVec.ofNat 64 y := fun e => h (by
      have := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at this; omega)
    simp [h, this]

/-- A hex digit's value: a decimal one (`addiw a2, t3, -48`)… -/
theorem s2_hexd : ∀ c : BitVec 8, (digitVal false (UInt8.ofBitVec c)).isSome = true →
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((zero_extend (m := 64) (c : BitVec (8 * 1))) +
      sign_extend (m := 64) (0xfd0#12)) 31 0) =
      BitVec.ofNat 64 ((digitVal true (UInt8.ofBitVec c)).getD 0) := by decide

/-- … or a letter (`ori a2, a2, 32; addiw a2, a2, -87`). -/
theorem s2_hexl : ∀ c : BitVec 8, (digitVal true (UInt8.ofBitVec c)).isSome = true →
    (digitVal false (UInt8.ofBitVec c)).isSome = false →
    sign_extend (m := 64) (Sail.BitVec.extractLsb (((zero_extend (m := 64) (c : BitVec (8 * 1))) |||
      sign_extend (m := 64) (0x020#12)) + sign_extend (m := 64) (0xfa9#12)) 31 0) =
      BitVec.ofNat 64 ((digitVal true (UInt8.ofBitVec c)).getD 0) := by decide

/-- `16 · a + d` (`slli 4; add`). -/
theorem s2_mul16 (A d : Nat) :
    BitVec.ofNat 64 d + shift_bits_left (BitVec.ofNat 64 A) (Sail.BitVec.extractLsb (0x04#6) 5 0) =
      BitVec.ofNat 64 (A * 16 + d) := by
  rw [shl_ofNat _ 4 (by decide), BitVec.ofNat_add_ofNat]; congr 1; omega

theorem s2_zero : (0#64 : BitVec 64) + sign_extend (m := 64) (0x000#12) = BitVec.ofNat 64 0 := by decide

local macro_rules | `(tactic| kit_side_pre) => `(tactic| (try s2_norm))
local macro_rules | `(tactic| kit_bv_norm) => `(tactic| (try s2_norm))
local macro_rules | `(tactic| kit_norm $h) => `(tactic| (try s2_norm at $h:ident))

theorem s2_size (P len : Nat) (h : P + len + 1 < 2 ^ 64) :
    (BitVec.ofNat 64 (P + len) - BitVec.ofNat 64 P) + sign_extend (m := 64) (0x001#12) =
      BitVec.ofNat 64 (len + 1) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, show (sign_extend (m := 64) (0x001#12)).toNat = 1 by decide]
  omega

/-- **The end** (`0x80011aa8`): the terminator, a digit seen, the sign. -/
theorem s2_end (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (acc : BitVec 64) (neg : Bool) :
    Triple (SegSt 0x80011aa8#64 (⟨Register.x15, 0#64⟩ :: ⟨Register.x11, 0#64⟩ :: ⟨Register.x14, acc⟩ ::
        ⟨Register.x10, BitVec.ofNat 64 (P + s.length)⟩ :: ⟨Register.x6, BitVec.ofNat 64 P⟩ ::
        ⟨Register.x17, BitVec.ofNat 64 o⟩ :: ⟨Register.x29, if neg then 1#64 else 0#64⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m out))
      (s2Post s.length r f m o (if neg then 0 - acc else acc) out) := by
  intro c h
  s2_facts
  have acc0 := Steps.refl c
  obtain ⟨sp', gp', s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11⟩ := f
  simp only [HFrame.pins] at h ⊢
  cases neg
  all_goals
    kit_run h acc0
    rw [s2_size P s.length (by omega)] at h
    simp only [Nat.add_zero, Nat.zero_add] at h
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨_, acc0, h.repin (by pins_of h)⟩

/-- The trailing spaces' loop row (`0x80011a8c`): at the space at `k`. -/
abbrev s2T (P o k : Nat) (acc t4 r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + k)⟩ :: ⟨Register.x16, 0x80052030#64⟩ :: ⟨Register.x11, 0#64⟩ ::
    ⟨Register.x14, acc⟩ :: ⟨Register.x6, BitVec.ofNat 64 P⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ ::
    ⟨Register.x29, t4⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- **The trailing spaces** (`0x80011a8c`): spaces up to the terminator. -/
theorem s2_trail (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (acc : BitVec 64) (neg : Bool) :
    ∀ k, k < s.length → (∀ j, k ≤ j → j < s.length → isSpace (bAt s j) = true) →
      Triple (SegSt 0x80011a8c#64 (s2T P o k acc (if neg then 1#64 else 0#64) r f) (ArmPay m out))
        (s2Post s.length r f m o (if neg then 0 - acc else acc) out) := by
  intro k₀ hk₀ hs₀ c₀ h₀
  refine seg_loop (S := fun k c => k < s.length ∧ (∀ j, k ≤ j → j < s.length → isSpace (bAt s j) = true) ∧
      SegSt 0x80011a8c#64 (s2T P o k acc (if neg then 1#64 else 0#64) r f) (ArmPay m out) c)
    (fun k => s.length - k) (fun k c ⟨hk, hs, h⟩ => ?_) k₀ c₀ ⟨hk₀, hs₀, h₀⟩
  s2_facts
  have acc0 := Steps.refl c
  have hc1 := (sb s (k + 1)).isLt
  by_cases he : k + 1 = s.length
  · have hsp : isSpace (bAt s (k + 1)) = false := by rw [he, bAt_ge (Nat.le_refl _)]; rfl
    kit_run h acc0 until [0x80011aa8]
    rw [he] at h
    s2_norm at h
    obtain ⟨c2, s2', h2⟩ := s2_end P o s r f m out hx acc neg _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', .inr h2⟩
  · have hsp : isSpace (bAt s (k + 1)) = true := hs (k + 1) (by omega) (by omega)
    kit_run h acc0 until [0x80011a8c]
    refine ⟨_, acc0, .inl ⟨k + 1, by omega, by omega, fun j hj hj' => hs j (by omega) hj', ?_⟩⟩
    exact h.repin (by pins_of h)

/-- The decimal digits' loop row (`0x80011a44`): at the digit at `j`, the
value `A` of the digits before it. -/
abbrev s2D (P o j A : Nat) (neg : Bool) (r : BitVec 64) (f : HFrame) (s : List UInt8) : List Pin :=
  ⟨Register.x14, BitVec.ofNat 64 A⟩ :: ⟨Register.x10, BitVec.ofNat 64 (P + j)⟩ ::
    ⟨Register.x12, zero_extend (m := 64) (sb s j : BitVec (8 * 1))⟩ ::
    ⟨Register.x28, BitVec.ofNat 64 922337203685477579⟩ :: ⟨Register.x6, BitVec.ofNat 64 P⟩ ::
    ⟨Register.x16, 0x80052030#64⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ ::
    ⟨Register.x29, if neg then 1#64 else 0#64⟩ :: ⟨Register.x30, BitVec.ofNat 64 922337203685477580⟩ ::
    ⟨Register.x31, BitVec.ofNat 64 (7 + if neg then 1 else 0)⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- After the digits (`0x80011a80`'s test, then the trailing spaces or the
terminator). -/
theorem s2_after (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (acc : BitVec 64) (neg : Bool) (e : Nat) (he : e ≤ s.length)
    (hsp : ∀ j, e ≤ j → j < s.length → isSpace (bAt s j) = true) {c : Config}
    (h : SegSt 0x80011aa8#64 (⟨Register.x15, zero_extend (m := 64) (sb s e : BitVec (8 * 1))⟩ :: ⟨Register.x11, 0#64⟩ ::
        ⟨Register.x14, acc⟩ :: ⟨Register.x10, BitVec.ofNat 64 (P + e)⟩ :: ⟨Register.x6, BitVec.ofNat 64 P⟩ ::
        ⟨Register.x17, BitVec.ofNat 64 o⟩ :: ⟨Register.x29, if neg then 1#64 else 0#64⟩ :: ⟨Register.x1, r⟩ :: f.pins)
        (ArmPay m out) c) (hend : e = s.length) :
    ∃ c', Steps c c' ∧ s2Post s.length r f m o (if neg then 0 - acc else acc) out c' := by
  subst hend
  rw [sb_len, zext_zero8] at h
  exact s2_end P o s r f m out hx acc neg c h

theorem dig_le9' : ∀ c : BitVec 8, (digitVal false (UInt8.ofBitVec c)).isSome = true →
    (digitVal false (UInt8.ofBitVec c)).getD 0 ≤ 9 := by decide
theorem dig_le9 (c : UInt8) (h : (digitVal false c).isSome = true) : (digitVal false c).getD 0 ≤ 9 :=
  dig_le9' c.toBitVec h

/-- The decimal loop's facts (`s2_dec`'s hypotheses). -/
structure S2Dec (s : List UInt8) (neg : Bool) (i2 n : Nat) : Prop where
  dig : ∀ k, k < n → (digitVal false (bAt s (i2 + k))).isSome = true
  ndig : (digitVal false (bAt s (i2 + n))).isSome = false
  len : i2 + n ≤ s.length
  tsp : ∀ k, i2 + n ≤ k → k < s.length → isSpace (bAt s k) = true
  ovf : dacc false s i2 0 n ≤ 2 ^ 63 - 1 + (if neg then 1 else 0)

/-- The decimal post (`s2Post` at the value of the digits). -/
abbrev s2DPost (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (neg : Bool) (i2 n : Nat) : Config → Prop :=
  s2Post s.length r f m o (if neg then 0 - BitVec.ofNat 64 (dacc false s i2 0 n)
    else BitVec.ofNat 64 (dacc false s i2 0 n)) out

set_option hygiene false in
/-- One decimal step's facts: the digit, the value one digit further, the
overflow test's case (`hcase`). -/
local macro "s2_dfacts" : tactic => `(tactic| (
  s2_facts
  have hdk := hd.dig k hk
  have hd9 := dig_le9 _ hdk
  have hA' := dacc_succ false s k i2 0
  simp only [Bool.false_eq_true, ↓reduceIte] at hA'
  have hF : dacc false s i2 0 (k + 1) ≤ dacc false s i2 0 n := by
    rw [dacc_split false s (k + 1) i2 0 n (by omega)]; exact dacc_ge _ _ _ _ _
  have hovf := hd.ovf
  have hlen := hd.len
  have hc1 := (sb s (i2 + (k + 1))).isLt
  have hneg1 : (if neg = true then 1 else 0) ≤ 1 := by split <;> omega
  have hcase : dacc false s i2 0 k ≤ 922337203685477579 ∨ (dacc false s i2 0 k = 922337203685477580 ∧
      (digitVal false (bAt s (i2 + k))).getD 0 ≤ 7 + (if neg = true then 1 else 0)) := by
    have := hF; rw [hA'] at this; omega))

/-- A decimal step to the next digit. -/
theorem s2_dec_next (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Dec s neg i2 n) (k : Nat) (hk : k < n)
    (hk1 : k + 1 < n) :
    Triple (SegSt 0x80011a44#64 (s2D P o (i2 + k) (dacc false s i2 0 k) neg r f s) (ArmPay m out))
      (SegSt 0x80011a44#64 (s2D P o (i2 + (k + 1)) (dacc false s i2 0 (k + 1)) neg r f s) (ArmPay m out)) := by
  intro c h
  s2_dfacts
  have acc0 := Steps.refl c
  have hdk1 := hd.dig (k + 1) hk1
  rcases hcase with hA | ⟨hA, hd'⟩
  all_goals
    kit_run h acc0 until [0x80011a44]
    rw [← hA'] at h
    exact ⟨_, acc0, h.repin (by pins_of h)⟩

/-- The last decimal digit, then the trailing spaces. -/
theorem s2_dec_trail (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Dec s neg i2 n) (k : Nat) (hk : k < n)
    (hkn : k + 1 = n) (he : i2 + n < s.length) :
    Triple (SegSt 0x80011a44#64 (s2D P o (i2 + k) (dacc false s i2 0 k) neg r f s) (ArmPay m out))
      (s2DPost P o s r f m out neg i2 n) := by
  intro c h
  s2_dfacts
  have acc0 := Steps.refl c
  have hnd : (digitVal false (bAt s (i2 + (k + 1)))).isSome = false := by rw [hkn]; exact hd.ndig
  have hsp : isSpace (bAt s (i2 + (k + 1))) = true := hd.tsp _ (by omega) (by omega)
  rcases hcase with hA | ⟨hA, hd'⟩
  all_goals
    kit_run h acc0 until [0x80011a8c]
    rw [← hA', hkn] at h
    obtain ⟨c2, s2', h2⟩ := s2_trail P o s r f m out hx (BitVec.ofNat 64 (dacc false s i2 0 n)) neg (i2 + n) he
      hd.tsp _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', h2⟩

/-- The last decimal digit, then the terminator. -/
theorem s2_dec_end (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Dec s neg i2 n) (k : Nat) (hk : k < n)
    (hkn : k + 1 = n) (he : ¬ i2 + n < s.length) :
    Triple (SegSt 0x80011a44#64 (s2D P o (i2 + k) (dacc false s i2 0 k) neg r f s) (ArmPay m out))
      (s2DPost P o s r f m out neg i2 n) := by
  intro c h
  s2_dfacts
  have acc0 := Steps.refl c
  have hnd : (digitVal false (bAt s (i2 + (k + 1)))).isSome = false := by rw [hkn]; exact hd.ndig
  have hsp : isSpace (bAt s (i2 + (k + 1))) = false := by
    rw [show i2 + (k + 1) = s.length by have := hd.len; omega, bAt_ge (Nat.le_refl _)]; rfl
  rcases hcase with hA | ⟨hA, hd'⟩
  all_goals
    kit_run h acc0 until [0x80011aa8]
    rw [← hA', hkn] at h
    obtain ⟨c2, s2', h2⟩ := s2_after P o s r f m out hx (BitVec.ofNat 64 (dacc false s i2 0 n)) neg (i2 + n)
      hd.len hd.tsp (h.repin (by pins_of h)) (by omega)
    exact ⟨c2, acc0.trans s2', h2⟩

/-- **The decimal digits** (`0x80011a44`): the `n` digits at `i2`, then the
trailing spaces and the terminator; the overflow test passes on a value
`str2int` accepts. -/
theorem s2_dec (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Dec s neg i2 n) :
    ∀ k, k < n → Triple (SegSt 0x80011a44#64 (s2D P o (i2 + k) (dacc false s i2 0 k) neg r f s) (ArmPay m out))
      (s2DPost P o s r f m out neg i2 n) := by
  intro k₀ hk₀ c₀ h₀
  refine seg_loop (S := fun k c => k < n ∧
      SegSt 0x80011a44#64 (s2D P o (i2 + k) (dacc false s i2 0 k) neg r f s) (ArmPay m out) c)
    (fun k => n - k) (fun k c ⟨hk, h⟩ => ?_) k₀ c₀ ⟨hk₀, h₀⟩
  by_cases hk1 : k + 1 < n
  · obtain ⟨c2, s2, h2⟩ := s2_dec_next P o s r f m out hx neg i2 n hd k hk hk1 c h
    exact ⟨c2, s2, .inl ⟨k + 1, by omega, hk1, h2⟩⟩
  · by_cases he : i2 + n < s.length
    · obtain ⟨c2, s2, h2⟩ := s2_dec_trail P o s r f m out hx neg i2 n hd k hk (by omega) he c h
      exact ⟨c2, s2, .inr h2⟩
    · obtain ⟨c2, s2, h2⟩ := s2_dec_end P o s r f m out hx neg i2 n hd k hk (by omega) he c h
      exact ⟨c2, s2, .inr h2⟩

/-! ## The hex digits (`0x80011b2c`) -/

theorem dv_tf : ∀ c : BitVec 8, (digitVal false (UInt8.ofBitVec c)).isSome = true →
    digitVal true (UInt8.ofBitVec c) = digitVal false (UInt8.ofBitVec c) := by decide

/-- The hex loop's row: at the hex digit at `j`, the value `A` before it. -/
abbrev s2H (P o j A : Nat) (neg : Bool) (r : BitVec 64) (f : HFrame) (s : List UInt8) : List Pin :=
  ⟨Register.x13, zero_extend (m := 64) (ctypeOf (sb s j) : BitVec (8 * 1))⟩ ::
    ⟨Register.x12, zero_extend (m := 64) (sb s j : BitVec (8 * 1))⟩ ::
    ⟨Register.x28, zero_extend (m := 64) (sb s j : BitVec (8 * 1))⟩ ::
    ⟨Register.x14, BitVec.ofNat 64 A⟩ :: ⟨Register.x10, BitVec.ofNat 64 (P + j)⟩ ::
    ⟨Register.x6, BitVec.ofNat 64 P⟩ :: ⟨Register.x16, 0x80052030#64⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ ::
    ⟨Register.x29, if neg then 1#64 else 0#64⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- The hex loop's facts. -/
structure S2Hex (s : List UInt8) (i2 n : Nat) : Prop where
  dig : ∀ k, k < n → (digitVal true (bAt s (i2 + k))).isSome = true
  ndig : (digitVal true (bAt s (i2 + n))).isSome = false
  len : i2 + n ≤ s.length
  tsp : ∀ k, i2 + n ≤ k → k < s.length → isSpace (bAt s k) = true

abbrev s2HPost (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (neg : Bool) (i2 n : Nat) : Config → Prop :=
  s2Post s.length r f m o (if neg then 0 - BitVec.ofNat 64 (dacc true s i2 0 n)
    else BitVec.ofNat 64 (dacc true s i2 0 n)) out

set_option hygiene false in
local macro "s2_hfacts" : tactic => `(tactic| (
  s2_facts
  have hdk := hd.dig k hk
  have hlen := hd.len
  have hA' := dacc_succ true s k i2 0
  simp only [↓reduceIte] at hA'
  have hc1 := (sb s (i2 + (k + 1))).isLt
  have hc0 := (sb s (i2 + k)).isLt))

set_option hygiene false in
/-- The digit's class (decimal or letter) and the value one digit further. -/
local macro "s2_hcase" : tactic => `(tactic| (
  cases hdd : (digitVal false (bAt s (i2 + k))).isSome
  all_goals try rw [show digitVal true (bAt s (i2 + k)) = digitVal false (bAt s (i2 + k)) from dv_tf _ hdd] at hA'))

theorem s2_hex_next (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Hex s i2 n) (k : Nat) (hk : k < n)
    (hk1 : k + 1 < n) :
    Triple (SegSt 0x80011b2c#64 (s2H P o (i2 + k) (dacc true s i2 0 k) neg r f s) (ArmPay m out))
      (SegSt 0x80011b2c#64 (s2H P o (i2 + (k + 1)) (dacc true s i2 0 (k + 1)) neg r f s) (ArmPay m out)) := by
  intro c h
  s2_hfacts
  have acc0 := Steps.refl c
  have hdk1 := hd.dig (k + 1) hk1
  s2_hcase
  all_goals
    kit_run h acc0 until [0x80011b2c]
    rw [← hA'] at h
    exact ⟨_, acc0, h.repin (by pins_of h)⟩

theorem s2_hex_trail (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Hex s i2 n) (k : Nat) (hk : k < n)
    (hkn : k + 1 = n) (he : i2 + n < s.length) :
    Triple (SegSt 0x80011b2c#64 (s2H P o (i2 + k) (dacc true s i2 0 k) neg r f s) (ArmPay m out))
      (s2HPost P o s r f m out neg i2 n) := by
  intro c h
  s2_hfacts
  have acc0 := Steps.refl c
  have hnd : (digitVal true (bAt s (i2 + (k + 1)))).isSome = false := by rw [hkn]; exact hd.ndig
  have hsp : isSpace (bAt s (i2 + (k + 1))) = true := hd.tsp _ (by omega) (by omega)
  s2_hcase
  all_goals
    kit_run h acc0 until [0x80011a8c]
    rw [← hA', hkn] at h
    obtain ⟨c2, s2', h2⟩ := s2_trail P o s r f m out hx (BitVec.ofNat 64 (dacc true s i2 0 n)) neg (i2 + n) he
      hd.tsp _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', h2⟩

theorem s2_hex_end (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Hex s i2 n) (k : Nat) (hk : k < n)
    (hkn : k + 1 = n) (he : ¬ i2 + n < s.length) :
    Triple (SegSt 0x80011b2c#64 (s2H P o (i2 + k) (dacc true s i2 0 k) neg r f s) (ArmPay m out))
      (s2HPost P o s r f m out neg i2 n) := by
  intro c h
  s2_hfacts
  have acc0 := Steps.refl c
  have hnd : (digitVal true (bAt s (i2 + (k + 1)))).isSome = false := by rw [hkn]; exact hd.ndig
  have hsp : isSpace (bAt s (i2 + (k + 1))) = false := by
    rw [show i2 + (k + 1) = s.length by omega, bAt_ge (Nat.le_refl _)]; rfl
  s2_hcase
  all_goals
    kit_run h acc0 until [0x80011aa8]
    rw [← hA', hkn] at h
    obtain ⟨c2, s2', h2⟩ := s2_after P o s r f m out hx (BitVec.ofNat 64 (dacc true s i2 0 n)) neg (i2 + n)
      hd.len hd.tsp (h.repin (by pins_of h)) (by omega)
    exact ⟨c2, acc0.trans s2', h2⟩

/-- **The hex digits** (`0x80011b2c`, wrapping), then the trailing spaces and
the terminator. -/
theorem s2_hex (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i2 n : Nat) (hd : S2Hex s i2 n) :
    ∀ k, k < n → Triple (SegSt 0x80011b2c#64 (s2H P o (i2 + k) (dacc true s i2 0 k) neg r f s) (ArmPay m out))
      (s2HPost P o s r f m out neg i2 n) := by
  intro k₀ hk₀ c₀ h₀
  refine seg_loop (S := fun k c => k < n ∧
      SegSt 0x80011b2c#64 (s2H P o (i2 + k) (dacc true s i2 0 k) neg r f s) (ArmPay m out) c)
    (fun k => n - k) (fun k c ⟨hk, h⟩ => ?_) k₀ c₀ ⟨hk₀, h₀⟩
  by_cases hk1 : k + 1 < n
  · obtain ⟨c2, s2, h2⟩ := s2_hex_next P o s r f m out hx neg i2 n hd k hk hk1 c h
    exact ⟨c2, s2, .inl ⟨k + 1, by omega, hk1, h2⟩⟩
  · by_cases he : i2 + n < s.length
    · obtain ⟨c2, s2, h2⟩ := s2_hex_trail P o s r f m out hx neg i2 n hd k hk (by omega) he c h
      exact ⟨c2, s2, .inr h2⟩
    · obtain ⟨c2, s2, h2⟩ := s2_hex_end P o s r f m out hx neg i2 n hd k hk (by omega) he c h
      exact ⟨c2, s2, .inr h2⟩

/-! ## The sign, `0x`, and the start of the digits (`0x800119ec`) -/

/-- The row after the sign (`0x800119ec`): `x10` at `i1`. -/
abbrev s2S (P o i1 : Nat) (neg : Bool) (r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + i1)⟩ :: ⟨Register.x16, 0x80052030#64⟩ ::
    ⟨Register.x6, BitVec.ofNat 64 P⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ ::
    ⟨Register.x29, if neg then 1#64 else 0#64⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- **The decimal start** (`0x800119ec` → `0x80011a44`): no `0x`. -/
theorem s2_dstart (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i1 n : Nat) (hd : S2Dec s neg i1 n) (hn : 0 < n)
    (hh : (bAt s i1 == 48 && (bAt s (i1 + 1) == 120 || bAt s (i1 + 1) == 88)) = false) :
    Triple (SegSt 0x800119ec#64 (s2S P o i1 neg r f) (ArmPay m out))
      (s2DPost P o s r f m out neg i1 n) := by
  intro c h
  s2_facts
  have acc0 := Steps.refl c
  have hdk := hd.dig 0 hn
  have hlen := hd.len
  simp only [Nat.add_zero] at hdk
  have hc1 := (sb s (i1 + 1)).isLt
  have hc0 := (sb s i1).isLt
  have hgo := s2_dec P o s r f m out hx neg i1 n hd 0 hn
  simp only [Nat.add_zero, dacc] at hgo
  cases h48 : (bAt s i1 == 48)
  · kit_run h acc0 until [0x80011a44]
    obtain ⟨c2, s2', h2⟩ := hgo _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', h2⟩
  · simp only [h48, Bool.true_and] at hh
    kit_run h acc0 until [0x80011a44]
    obtain ⟨c2, s2', h2⟩ := hgo _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', h2⟩

/-- **The hex start** (`0x800119ec` → `0x80011ad0` → `0x80011b2c`): `0x`. -/
theorem s2_hstart (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (neg : Bool) (i1 n : Nat) (hd : S2Hex s (i1 + 2) n) (hn : 0 < n)
    (h48 : (bAt s i1 == 48) = true) (hX : (bAt s (i1 + 1) == 120 || bAt s (i1 + 1) == 88) = true) :
    Triple (SegSt 0x800119ec#64 (s2S P o i1 neg r f) (ArmPay m out))
      (s2HPost P o s r f m out neg (i1 + 2) n) := by
  intro c h
  s2_facts
  have acc0 := Steps.refl c
  have hdk := hd.dig 0 hn
  have hlen := hd.len
  simp only [Nat.add_zero] at hdk
  have hc2 := (sb s (i1 + 2)).isLt
  have hc1 := (sb s (i1 + 1)).isLt
  have hc0 := (sb s i1).isLt
  have hgo := s2_hex P o s r f m out hx neg (i1 + 2) n hd 0 hn
  simp only [Nat.add_zero, dacc] at hgo
  kit_run h acc0 until [0x80011b2c]
  obtain ⟨c2, s2', h2⟩ := hgo _ (h.repin (by pins_of h))
  exact ⟨c2, acc0.trans s2', h2⟩

/-- The row after the leading spaces (`0x800119d4`): the byte at `i0` in `x14`. -/
abbrev s2L (P o i0 : Nat) (r : BitVec 64) (f : HFrame) (s : List UInt8) : List Pin :=
  ⟨Register.x14, zero_extend (m := 64) (sb s i0 : BitVec (8 * 1))⟩ ::
    ⟨Register.x10, BitVec.ofNat 64 (P + i0)⟩ :: ⟨Register.x16, 0x80052030#64⟩ ::
    ⟨Register.x6, BitVec.ofNat 64 P⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- The sign `str2int` takes (`takeSign`): its length and whether it is `-`. -/
abbrev s2I1 (s : List UInt8) (i0 : Nat) : Nat := i0 + (if bAt s i0 = 45 ∨ bAt s i0 = 43 then 1 else 0)

/-- **The sign** (`0x800119d4` → `0x800119ec`). -/
theorem s2_sign (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (i0 : Nat) (hi0 : i0 < s.length) :
    Triple (SegSt 0x800119d4#64 (s2L P o i0 r f s) (ArmPay m out))
      (SegSt 0x800119ec#64 (s2S P o (s2I1 s i0) (bAt s i0 == 45) r f) (ArmPay m out)) := by
  intro c h
  s2_facts
  have acc0 := Steps.refl c
  have hc0 := (sb s i0).isLt
  cases h45 : (bAt s i0 == 45)
  · cases h43 : (bAt s i0 == 43)
    · have e : s2I1 s i0 = i0 := by simp only [s2I1]; simp_all
      rw [e]
      kit_run h acc0 until [0x800119ec]
      exact ⟨_, acc0, h.repin (by pins_of h)⟩
    · have e : s2I1 s i0 = i0 + 1 := by simp only [s2I1]; simp_all
      rw [e]
      kit_run h acc0 until [0x800119ec]
      exact ⟨_, acc0, h.repin (by pins_of h)⟩
  · have e : s2I1 s i0 = i0 + 1 := by simp only [s2I1]; simp_all
    rw [e]
    kit_run h acc0 until [0x800119ec]
    exact ⟨_, acc0, h.repin (by pins_of h)⟩

/-! ## The leading spaces (`0x80011998`, `0x800119bc`) -/

/-- The leading spaces' loop row (`0x800119bc`): at the space at `j`. -/
abbrev s2Sp (P o j : Nat) (r : BitVec 64) (f : HFrame) : List Pin :=
  ⟨Register.x10, BitVec.ofNat 64 (P + j)⟩ :: ⟨Register.x16, 0x80052030#64⟩ ::
    ⟨Register.x6, BitVec.ofNat 64 P⟩ :: ⟨Register.x17, BitVec.ofNat 64 o⟩ :: ⟨Register.x1, r⟩ :: f.pins

/-- **The leading spaces' loop** (`0x800119bc`): the spaces before `i0`. -/
theorem s2_lead (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (i0 : Nat) (hi0 : i0 < s.length)
    (hsp : ∀ k, k < i0 → isSpace (bAt s k) = true) (hns : isSpace (bAt s i0) = false) :
    ∀ j, j < i0 → Triple (SegSt 0x800119bc#64 (s2Sp P o j r f) (ArmPay m out))
      (SegSt 0x800119d4#64 (s2L P o i0 r f s) (ArmPay m out)) := by
  intro j₀ hj₀ c₀ h₀
  refine seg_loop (S := fun j c => j < i0 ∧ SegSt 0x800119bc#64 (s2Sp P o j r f) (ArmPay m out) c)
    (fun j => i0 - j) (fun j c ⟨hj, h⟩ => ?_) j₀ c₀ ⟨hj₀, h₀⟩
  s2_facts
  have acc0 := Steps.refl c
  have hc1 := (sb s (j + 1)).isLt
  by_cases he : j + 1 = i0
  · have hs1 : isSpace (bAt s (j + 1)) = false := he ▸ hns
    kit_run h acc0 until [0x800119d4]
    rw [he] at h
    exact ⟨_, acc0, .inr (h.repin (by pins_of h))⟩
  · have hs1 : isSpace (bAt s (j + 1)) = true := hsp (j + 1) (by omega)
    kit_run h acc0 until [0x800119bc]
    exact ⟨_, acc0, .inl ⟨j + 1, by omega, by omega, h.repin (by pins_of h)⟩⟩

/-- **The entry** (`0x80011998`): the leading spaces, to the byte at `i0`. -/
theorem s2_entry (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) (i0 : Nat) (hi0 : i0 < s.length)
    (hsp : ∀ k, k < i0 → isSpace (bAt s k) = true) (hns : isSpace (bAt s i0) = false) :
    Triple (SegSt 0x80011998#64 (s2Pre P o r f) (ArmPay m out))
      (SegSt 0x800119d4#64 (s2L P o i0 r f s) (ArmPay m out)) := by
  intro c h
  s2_facts
  have acc0 := Steps.refl c
  have hc0 := (sb s 0).isLt
  rcases Nat.eq_zero_or_pos i0 with e | hpos
  · subst e
    kit_run h acc0 until [0x800119d4]
    exact ⟨_, acc0, h.repin (by pins_of h)⟩
  · have hs0 : isSpace (bAt s 0) = true := hsp 0 hpos
    kit_run h acc0 until [0x800119bc]
    obtain ⟨c2, s2', h2⟩ := s2_lead P o s r f m out hx i0 hi0 hsp hns 0 hpos _ (h.repin (by pins_of h))
    exact ⟨c2, acc0.trans s2', h2⟩

/-! ## `luaO_str2num`'s integer path -/

/-- **`luaO_str2num` on a string `str2int` accepts** (`0x80011998`, lane
F1-F8): `o` holds the integer `str2int` reads (`setivalue`) and the result is
the string's size plus one; the run is `l_str2int`'s, never `l_str2d`'s. -/
theorem str2num_int (P o : Nat) (s : List UInt8) (r : BitVec 64) (f : HFrame) (m : Mem) (out : Array String)
    (hx : S2Ctx m P o s r) {v : BitVec 64} (hv : str2int s = some v) :
    Triple (SegSt 0x80011998#64 (s2Pre P o r f) (ArmPay m out)) (s2Post s.length r f m o v out) := by
  obtain ⟨S⟩ := str2int_S2I hv
  have hle : S.i0 ≤ S.i2 := by rw [S.i2_eq, S.i1_eq]; split <;> split <;> omega
  have hi0 : S.i0 < s.length := by have := S.len; have := S.n_pos; omega
  refine (s2_entry P o s r f m out hx S.i0 hi0 S.sp0 S.nsp0).seq
    ((s2_sign P o s r f m out hx S.i0 hi0).seq ?_)
  rw [show s2I1 s S.i0 = S.i1 from S.i1_eq.symm, ← S.neg_eq]
  have hdig := S.dig; have hndig := S.ndig; have hlen := S.len; have htsp := S.tsp
  have hval := S.val; have hovf := S.ovf; have hhex := S.hex_eq; have hi2 := S.i2_eq
  cases hh : S.hex
  · rw [hh] at hdig hndig hval hhex hi2
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hi2
    rw [hi2] at hdig hndig hlen htsp hval
    have hovf' := hovf hh; rw [hh, hi2] at hovf'
    exact (s2_dstart P o s r f m out hx S.neg S.i1 S.n ⟨hdig, hndig, hlen, htsp, hovf'⟩ S.n_pos
      hhex.symm).conseq (fun _ h => h) (fun _ h => hval ▸ h)
  · rw [hh] at hdig hndig hval hhex hi2
    simp only [↓reduceIte] at hi2
    rw [hi2] at hdig hndig hlen htsp hval
    have h2 := hhex.symm
    simp only [Bool.and_eq_true] at h2
    exact (s2_hstart P o s r f m out hx S.neg S.i1 S.n ⟨hdig, hndig, hlen, htsp⟩ S.n_pos
      h2.1 h2.2).conseq (fun _ h => h) (fun _ h => hval ▸ h)

end Lua.Vm.Sim.Kit

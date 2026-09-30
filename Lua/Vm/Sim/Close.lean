import Lua.Vm.Sim.Rel
import Lua.Vm.Sim.Bits
import Lua.Vm.Sim.StepK

/-!
# Branch guards and closes of the two-exit arms (A1)

What the generated simulations of the branching arms (`scripts/gen_lua_arm.py`
kinds `arith`, `condjump`, `forloop`) consume beyond `Core.write`/`Core.jump`:

* **tags decide the path** (`ValRepr.int_of_tag`, `ValRepr.tag_of_int`,
  `ValRepr.ne_float`): a register's tag byte is `LUA_VNUMINT` exactly when it
  holds an integer, and never `LUA_VNUMFLT` (F1 has no floats), so the
  float paths of an arm are discharged at their first branch;
* **guards** (`guard_*`): the branch conditions of the generated segments,
  over a raw address `a` with `a = n + off` (discharged by `slot_arith`);
* **field terms** the two-exit arms decode (`sext_shr`, `field1`,
  `addiw_bias`, `ult_one_sub`);
* **closes**: `Core.update` (any register writes inside the window) and the
  read-backs of `OP_FORLOOP`'s four stores (`forloop_store`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config)

/-! ## Tags -/

section
variable {mo : Mem} {t : BitVec 8} {x : BitVec 64} {v : Value}

theorem ValRepr.ne_float (h : ValRepr mo t x v) : t ≠ BitVec.ofNat 8 19 := by
  cases h with
  | nil h => intro he; subst he; simp at h
  | str h _ => intro he; subst he; simp [vShrStr, vLngStr] at h
  | _ => decide

theorem ValRepr.int_of_tag (h : ValRepr mo t x v) (ht : t = BitVec.ofNat 8 vNumInt) :
    v = .int x := by
  cases h with
  | nil h => subst ht; simp [vNumInt] at h
  | str h _ => subst ht; simp [vShrStr, vLngStr, vNumInt] at h
  | int => rfl
  | _ => exact absurd ht (by decide)

theorem ValRepr.tag_of_int {i : BitVec 64} (h : ValRepr mo t x (.int i)) :
    t = BitVec.ofNat 8 vNumInt ∧ x = i := by
  cases h; exact ⟨rfl, rfl⟩

theorem ValRepr.not_int (h : ValRepr mo t x v) (ht : t ≠ BitVec.ofNat 8 vNumInt) :
    ∀ i, v ≠ .int i := by
  rintro i rfl; exact ht h.tag_of_int.1

end

/-! ## Guards -/

theorem zext_tag_beq (b : BitVec 8) (t : Nat) (ht : t < 256) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) == BitVec.ofNat 64 t) = decide (b = BitVec.ofNat 8 t) := by
  simp only [zero_extend, Sail.BitVec.zeroExtend]
  by_cases h : b = BitVec.ofNat 8 t
  · subst h; simp only [decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; simp; omega
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro he; apply h; apply BitVec.eq_of_toNat_eq
    have := congrArg BitVec.toNat he
    simp [Nat.mod_eq_of_lt ht] at this ⊢; omega

theorem const_19 : (0#64) + sign_extend (m := 64) (0x013#12) = BitVec.ofNat 64 19 := by decide

section
variable {m : Mem} {a n : Nat} {t : Nat}

theorem guard_tag_eq (ha : a = n + 8) (h : slotTag m n = BitVec.ofNat 8 t) (ht : t < 256) :
    (zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) == BitVec.ofNat 64 t) = true := by
  subst ha; rw [zext_tag_beq _ _ ht]; simpa [slotTag, tvalueTagOff] using h

theorem guard_tag_ne (ha : a = n + 8) (h : slotTag m n ≠ BitVec.ofNat 8 t) (ht : t < 256) :
    (zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) == BitVec.ofNat 64 t) = false := by
  subst ha; rw [zext_tag_beq _ _ ht]; simpa [slotTag, tvalueTagOff] using h

theorem guard_tag_bne_t (ha : a = n + 8) (h : slotTag m n ≠ BitVec.ofNat 8 t) (ht : t < 256) :
    (zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) != BitVec.ofNat 64 t) = true := by
  simp only [bne, guard_tag_ne ha h ht, Bool.not_false]

theorem guard_tag_bne_f (ha : a = n + 8) (h : slotTag m n = BitVec.ofNat 8 t) (ht : t < 256) :
    (zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) != BitVec.ofNat 64 t) = false := by
  simp only [bne, guard_tag_eq ha h ht, Bool.not_true]

/-- The float test (`li 19; bne`), never taken on an F1 value. -/
theorem guard_not_float {mo : Mem} {x : BitVec 64} {v : Value} (ha : a = n + 8)
    (h : ValRepr mo (slotTag m n) x v) :
    (zero_extend (m := 64) (bytesT1 m a : BitVec (8 * 1)) != ((0#64) + sign_extend (m := 64) (0x013#12))) = true := by
  rw [const_19]; exact guard_tag_bne_t ha h.ne_float (by decide)

end

/-! ## Field terms -/

/-- `srliw k` (k ≥ 1), sign-extended: non-negative. -/
theorem sext_shr (x : BitVec 32) (k : Nat) (hk : 1 ≤ k) (hk2 : k < 32) :
    sign_extend (m := 64) (shift_bits_right x (BitVec.ofNat 5 k)) = BitVec.ofNat 64 (x.toNat >>> k) := by
  simp only [sign_extend, Sail.BitVec.signExtend, shift_bits_right]
  apply BitVec.eq_of_toNat_eq
  have hs : (x >>> (BitVec.ofNat 5 k)).toNat = x.toNat >>> k := by
    simp [Nat.mod_eq_of_lt (show k < 32 by omega)]
  have hlt := shr_lt_two_pow_31 x.toNat k x.isLt hk
  rw [sext_toNat_small _ (hs ▸ hlt), hs, BitVec.toNat_ofNat]
  omega

/-- `zext.b` of a value already read as `BitVec.ofNat` (after `sext_shr`). -/
theorem and255 (n : Nat) :
    BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x0ff#12) = BitVec.ofNat 64 (n % 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  have h255 : (sign_extend (m := 64) (0x0ff#12)).toNat = 2 ^ 8 - 1 := by decide
  rw [BitVec.toNat_and, h255, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `srliw k` then `andi 1`: one bit (`GETARG_k`). -/
theorem field1 (x : BitVec 32) (k : Nat) (hk : 1 ≤ k) (hk2 : k < 32) :
    sign_extend (m := 64) (shift_bits_right x (BitVec.ofNat 5 k)) &&& sign_extend (m := 64) (0x001#12)
      = BitVec.ofNat 64 ((x.toNat >>> k) % 2) := by
  rw [sext_shr x k hk hk2]
  apply BitVec.eq_of_toNat_eq
  have h1 : (sign_extend (m := 64) (0x001#12)).toNat = 2 ^ 1 - 1 := by decide
  rw [BitVec.toNat_and, h1, Nat.and_two_pow_sub_one_eq_mod, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `addiw rd, rs, -127` of an 8-bit field: `sB`/`sC` (`n - OFFSET_sC`). -/
theorem addiw_bias : ∀ n : Fin 256,
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 n.val + sign_extend (m := 64) (0xf81#12)) 31 0)
      = BitVec.ofInt 64 ((n.val : Int) - 127) := by
  decide +kernel

/-- `sub` then `sltiu 1` (`seqz`): equality. -/
theorem ult_one_sub (x y : BitVec 64) :
    zopz0zI_u (x - y) (sign_extend (m := 64) (0x001#12)) = decide (x = y) := by
  have h1 : (sign_extend (m := 64) (0x001#12)).toNat = 1 := by decide
  simp only [zopz0zI_u, BitVec.toNatInt, h1]
  by_cases h : x = y
  · subst h; simp
  · have hne : x.toNat ≠ y.toNat := fun e => h (BitVec.eq_of_toNat_eq e)
    have := BitVec.toNat_sub x y
    have := x.isLt
    have := y.isLt
    simp [h]; omega

theorem sext64_id (x : BitVec (8 * 8)) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- A read at a raw address that is the slot's. -/
theorem bytesT8_at {m : Mem} {a n : Nat} (h : a = n) : bytesT8 m a = slotVal m n := by
  subst h; simp [slotVal, tvalueValOff]

theorem bytesT4_at {m : Mem} {a n : Nat} (h : a = n) : bytesT4 m a = bytesT4 m n := by
  rw [h]

/-- A pin whose value is shown equal to a normal form. -/
theorem pin_eq {α : Type} {x : Option α} {a b : α} (h : x = some a) (e : a = b) : x = some b :=
  e ▸ h

/-- `sw`-free window reads: `ci->u.l.trap` from any memory that agrees with
the complement outside the window. -/
theorem trap_of_frame {p : Proto} {w : RelPtrs} {m : Mem} (hr : Ranges p w) (hc : Complement p w)
    (hf : ∀ a, ¬ Win p w a → bytesT1 m a = bytesT1 w.mo a) : bytesT4 m (w.ci + ciTrapOff) = 0 := by
  refine (bytesT4_congrT fun i hi => ?_).trans hc.trap_word
  exact hf _ (hr.ci_out _ (by omega) (by simp only [ciTrapOff, ciSize]; omega))

/-- `sext.w` of the loaded `trap` (`lw t6,40(s7)`; `sext.w s5,t6`). -/
theorem trap_zero :
    sign_extend (m := 64) (Sail.BitVec.extractLsb ((sign_extend (m := 64) (0 : BitVec (8 * 4)))
      + sign_extend (m := 64) (0x000#12)) 31 0) = 0#64 := by decide

/-- **Slot arithmetic**: `arm_arith` with the slot and field definitions
unfolded (the raw address terms of the generated segments against
`RelPtrs.slot`). -/
macro "slot_arith" : tactic => `(tactic| (
  try simp (config := { decide := true }) only [extract_sext, field8, sext_shr, add_imm, shl_ofNat,
    BitVec.ofNat_add_ofNat, BitVec.toNat_ofNat, Nat.add_zero, RelPtrs.slot,
    stackValueSize, Word.a, Word.b, Word.c, Word.bx, Word.field, ciTrapOff, and255,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_sub]
  all_goals try simp (disch := omega) only [Nat.mod_eq_of_lt]
  all_goals omega))

/-- A pin's position is inside its bundle (the list's spine only). -/
macro "len_arith" : tactic => `(tactic| (
  simp only [List.length_cons, List.length_nil]
  all_goals omega))

/-! ## Closes -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- **Any register writes inside the window**: the memory outside the window
is unchanged and every defined register of the new file is represented. -/
theorem Core.update (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {P : MState → Prop} (hseg : SegSt pcv L P c') {pc' : Nat} {regs' : Nat → Option Value}
    (hpins : Pins c'.σ w pc') (hout : c'.σ.sailOutput = c.σ.sailOutput)
    (hframe : ∀ x, ¬ Win p w x → c'.σ.mem[x]? = c.σ.mem[x]?)
    (hstack : ∀ j v, j < p.maxstacksize → regs' j = some v →
      ValRepr w.mo (slotTag c'.σ.mem (w.slot j)) (slotVal c'.σ.mem (w.slot j)) v) :
    Core p c' ⟨pc', regs', s.out⟩ w :=
  ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hout).trans hc.out,
    hc.text_of hframe, hc.frame_of hframe, hstack, hc.comp, hc.ranges⟩

end

/-- `sb` then `sd` at raw addresses equal to the slot's tag and payload. -/
theorem slotStore_sb_sd {m m' : Mem} {A a1 a2 : Nat} {d : BitVec (8 * 8)} {b : BitVec 8}
    (h : m' = writeMap8 (m.insert a1 b) a2 d) (h1 : a1 = A + 8) (h2 : a2 = A) :
    SlotStore m m' A b d := by
  subst h; rw [h1, h2]; exact store_sb_sd m A d b

theorem getElem?_insert_out {m : Mem} {a x : Nat} {b : BitVec 8} (h : x ≠ a) :
    (m.insert a b)[x]? = m[x]? := by
  rw [Std.ExtHashMap.getElem?_insert, ite_eq_right_iff.2 (fun h => by simp only [beq_iff_eq] at h; omega)]

/-- **`OP_FORLOOP`'s stores** from the slot `n` of `R[A]`: `sd` count−1 to
`R[A+1]`'s payload, `sb` the integer tag to `R[A+3]`, `sd` the index to
`R[A]`'s and `R[A+3]`'s payloads. -/
structure ForStore (m m' : Mem) (n : Nat) (d1 d2 : BitVec 64) (b : BitVec 8) : Prop where
  val1 : slotVal m' (n + 16) = d1
  tag1 : slotTag m' (n + 16) = slotTag m (n + 16)
  val0 : slotVal m' n = d2
  tag0 : slotTag m' n = slotTag m n
  val3 : slotVal m' (n + 48) = d2
  tag3 : slotTag m' (n + 48) = b
  frame : ∀ x, (x < n ∨ n + 9 ≤ x) → (x < n + 16 ∨ n + 25 ≤ x) → (x < n + 48 ∨ n + 57 ≤ x) →
    m'[x]? = m[x]?

theorem forloop_store {m m' : Mem} {n a16 a56 a0 a48 : Nat} {d1 d2 d3 : BitVec (8 * 8)}
    {b : BitVec 8}
    (h : m' = writeMap8 (writeMap8 ((writeMap8 m a16 d1).insert a56 b) a0 d2) a48 d3)
    (h16 : a16 = n + 16) (h56 : a56 = n + 56) (h0 : a0 = n) (h48 : a48 = n + 48) (h3 : d3 = d2) :
    ForStore m m' n d1 d2 b := by
  subst h
  rw [h16, h56, h0, h48, h3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun x h1 h2 h3 => ?_⟩
  · simp only [slotVal, tvalueValOff, Nat.add_zero]
    refine (bytesT8_congr fun i hi => ?_).trans (bytesT8_writeMap8 m _ d1)
    rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_insert_out (by omega)]
  · simp only [slotTag, bytesT1, tvalueTagOff]
    rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_insert_out (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]
  · simp only [slotVal, tvalueValOff, Nat.add_zero]
    refine (bytesT8_congr fun i hi => ?_).trans
      (bytesT8_writeMap8 ((writeMap8 m (n + 16) d1).insert (n + 56) b) n d2)
    rw [getElem?_writeMap8_out _ _ _ _ (by omega)]
  · simp only [slotTag, bytesT1, tvalueTagOff]
    rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_insert_out (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]
  · simp only [slotVal, tvalueValOff, Nat.add_zero]
    exact bytesT8_writeMap8 _ _ d2
  · simp only [slotTag, bytesT1, tvalueTagOff]
    rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      Std.ExtHashMap.getElem?_insert_self]
    rfl
  · rw [getElem?_writeMap8_out _ _ _ _ (by omega), getElem?_writeMap8_out _ _ _ _ (by omega),
      getElem?_insert_out (by omega), getElem?_writeMap8_out _ _ _ _ (by omega)]


/-! ## The instruction's `k` bit and `sB`, and the `EQI` guards -/

theorem kraw_eq (x : Word) :
    (sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x0f#5))
      &&& sign_extend (m := 64) (0x001#12)) = if x.k then 1#64 else 0#64 := by
  rw [extract_sext, field1 x 15 (by decide) (by decide)]
  simp only [Word.k, Word.field, Nat.pow_one]
  rcases Nat.mod_two_eq_zero_or_one (x.toNat >>> 15) with h | h <;> simp [h]

theorem sbraw_eq (x : Word) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x10#5))) &&& sign_extend (m := 64) (0x0ff#12))
      + sign_extend (m := 64) (0xf81#12)) 31 0) = BitVec.ofInt 64 x.sb := by
  rw [extract_sext, field8 x 16 (by decide) (by decide)]
  have hb : (x.toNat >>> 16) % 2 ^ 8 < 256 := Nat.mod_lt _ (by decide)
  have := addiw_bias ⟨_, hb⟩
  simp only at this
  rw [this]
  simp only [Word.sb, Word.b, Word.field, Word.offsetSC]
  rfl

theorem bitb (b : Bool) : zero_extend (m := 64) (bool_to_bit b) = if b then 1#64 else 0#64 := by
  cases b <;> decide

/-- `EQI`'s integer test against `k` (`seqz`; `beq k, cond`). -/
theorem guard_eqk {m : Mem} {a n : Nat} (x : Word) (ha : a = n) :
    ((sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x0f#5))
      &&& sign_extend (m := 64) (0x001#12)) ==
      zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)))
        - sign_extend (m := 64) (Sail.BitVec.extractLsb (((sign_extend (m := 64) (shift_bits_right
          (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x10#5))) &&& sign_extend (m := 64) (0x0ff#12))
          + sign_extend (m := 64) (0xf81#12)) 31 0)) (sign_extend (m := 64) (0x001#12)))))
      = (x.k == decide (slotVal m n = BitVec.ofInt 64 x.sb)) := by
  rw [kraw_eq, sbraw_eq, bytesT8_at ha, sext64_id, ult_one_sub, bitb]
  cases x.k <;> by_cases h : slotVal m n = BitVec.ofInt 64 x.sb <;> simp [h]

theorem guard_eqk_t {m : Mem} {a n : Nat} {x : Word} (ha : a = n)
    (hJ : x.k = decide (slotVal m n = BitVec.ofInt 64 x.sb)) :
    ((sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x0f#5))
      &&& sign_extend (m := 64) (0x001#12)) ==
      zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)))
        - sign_extend (m := 64) (Sail.BitVec.extractLsb (((sign_extend (m := 64) (shift_bits_right
          (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x10#5))) &&& sign_extend (m := 64) (0x0ff#12))
          + sign_extend (m := 64) (0xf81#12)) 31 0)) (sign_extend (m := 64) (0x001#12))))) = true := by
  rw [guard_eqk x ha, hJ, beq_self_eq_true]

theorem guard_eqk_f {m : Mem} {a n : Nat} {x : Word} (ha : a = n)
    (hJ : ¬ x.k = decide (slotVal m n = BitVec.ofInt 64 x.sb)) :
    ((sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x0f#5))
      &&& sign_extend (m := 64) (0x001#12)) ==
      zero_extend (m := 64) (bool_to_bit (zopz0zI_u ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8)))
        - sign_extend (m := 64) (Sail.BitVec.extractLsb (((sign_extend (m := 64) (shift_bits_right
          (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x10#5))) &&& sign_extend (m := 64) (0x0ff#12))
          + sign_extend (m := 64) (0xf81#12)) 31 0)) (sign_extend (m := 64) (0x001#12))))) = false := by
  rw [guard_eqk x ha]; simpa using hJ

/-- The non-integer path's `bne k, 0`. -/
theorem guard_k (x : Word) :
    ((sign_extend (m := 64) (shift_bits_right (Sail.BitVec.extractLsb (sign_extend (m := 64) x) 31 0) (0x0f#5))
      &&& sign_extend (m := 64) (0x001#12)) != ((0#64) + sign_extend (m := 64) (0x000#12))) = x.k := by
  rw [kraw_eq]; cases x.k <;> decide

/-- `donextjump`'s target (`lw` the next word, `srliw 7`, `+ (2 - 2^24)`,
`slli 2`, `add` to pc + 1). -/
theorem nextjump_pc {m : Mem} {code pc t a : Nat} {ni : Word} (ha : a = code + 4 * (pc + 1))
    (hni : bytesT4 m (code + 4 * (pc + 1)) = ni) (ht : jumpTo (pc + 2) ni.sj = some t)
    (_hb : code + 4 * (pc + 2) < 2 ^ 64) (hbt : code + 4 * t < 2 ^ 64) :
    BitVec.ofNat 64 (code + 4 * (pc + 1)) + shift_bits_left ((sign_extend (m := 64) (shift_bits_right
      (Sail.BitVec.extractLsb (sign_extend (m := 64) (bytesT4 m a : BitVec (8 * 4))) 31 0) (0x07#5)))
      + ((sign_extend (m := 64) ((0xff000#20) +++ 0x000#12)) + sign_extend (m := 64) (0x002#12)))
      (Sail.BitVec.extractLsb (0x02#6) 5 0) = BitVec.ofNat 64 (code + 4 * t) := by
  subst ha
  have hK : (sign_extend (m := 64) ((0xff000#20) +++ 0x000#12)) + sign_extend (m := 64) (0x002#12)
      = BitVec.ofNat 64 (2 ^ 64 - 2 ^ 24 + 2) := by decide
  rw [hni, extract_sext, sext_shr ni 7 (by decide) (by decide), hK, BitVec.ofNat_add_ofNat,
    shl_ofNat _ 2 (by decide), BitVec.ofNat_add_ofNat]
  obtain ⟨h0, htv⟩ := jumpTo_eq ht
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Word.sj, Word.ax, Word.field, Word.offsetSJ] at htv h0 ⊢
  have : ni.toNat >>> 7 < 2 ^ 25 := by rw [Nat.shiftRight_eq_div_pow]; have := ni.isLt; omega
  omega

/-! ## `OP_FORLOOP`'s count test and values -/

theorem guard_zero_t {m : Mem} {a n : Nat} (ha : a = n) (h : slotVal m n = 0) :
    ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8))) == (0#64)) = true := by
  rw [bytesT8_at ha, sext64_id, h]; rfl

theorem guard_zero_f {m : Mem} {a n : Nat} {v : BitVec 64} (ha : a = n) (h : slotVal m n = v)
    (hv : ¬ v = 0) : ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8))) == (0#64)) = false := by
  rw [bytesT8_at ha, sext64_id, h]; simpa using hv

theorem stData_int : stData 1 (BitVec.ofNat 64 vNumInt) = BitVec.ofNat 8 vNumInt := by decide

/-- `ADD`'s payload (`ld`, `ld`, `add`, `sd`). -/
theorem add_val {m : Mem} {a1 a2 n1 n2 : Nat} (h1 : a1 = n1) (h2 : a2 = n2) :
    sdData_val ((sign_extend (m := 64) (bytesT8 m a1 : BitVec (8 * 8)))
      + (sign_extend (m := 64) (bytesT8 m a2 : BitVec (8 * 8)))) = slotVal m n1 + slotVal m n2 := by
  rw [bytesT8_at h1, bytesT8_at h2, sext64_id, sext64_id, sdData_id]

/-- `FORLOOP`'s count − 1 (`ld`, `addi -1`, `sd`). -/
theorem dec_val {m : Mem} {a n : Nat} {v : BitVec 64} (ha : a = n) (h : slotVal m n = v) :
    sdData_val ((sign_extend (m := 64) (bytesT8 m a : BitVec (8 * 8))) + sign_extend (m := 64) (0xfff#12))
      = v - 1 := by
  rw [bytesT8_at ha, sext64_id, h, sdData_id]
  have : sign_extend (m := 64) (0xfff#12) = (-1 : BitVec 64) := by decide
  rw [this, BitVec.sub_eq_add_neg]

/-- `FORLOOP`'s index + step, read after the count's store. -/
theorem step_val {m : Mem} {a16 a0 a32 n : Nat} {d : BitVec (8 * 8)} {x st : BitVec 64}
    (h16 : a16 = n + 16) (h0 : a0 = n) (h32 : a32 = n + 32) (hx : slotVal m n = x)
    (hs : slotVal m (n + 32) = st) :
    sdData_val ((sign_extend (m := 64) (bytesT8 (writeMap8 m a16 d) a0 : BitVec (8 * 8)))
      + (sign_extend (m := 64) (bytesT8 (writeMap8 m a16 d) a32 : BitVec (8 * 8)))) = x + st := by
  subst h16 h0 h32
  rw [sext64_id, sext64_id, sdData_id, ← hx, ← hs]
  simp only [slotVal, tvalueValOff, Nat.add_zero]
  congr 1
  · exact bytesT8_congr fun i hi => getElem?_writeMap8_out _ _ _ _ (by omega)
  · exact bytesT8_congr fun i hi => getElem?_writeMap8_out _ _ _ _ (by omega)

theorem ForStore.congr {m m' : Mem} {n : Nat} {d1 d2 d1' d2' : BitVec 64} {b b' : BitVec 8}
    (h : ForStore m m' n d1 d2 b) (h1 : d1 = d1') (h2 : d2 = d2') (hb : b = b') :
    ForStore m m' n d1' d2' b' := by
  subst h1 h2 hb; exact h

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

theorem ForStore.frame_mo (hc : Core p c s w) {m' : Mem} {a : Nat} {d1 d2 : BitVec 64}
    {b : BitVec 8} (ha : a + 3 < p.maxstacksize)
    (hfs : ForStore c.σ.mem m' (w.slot a) d1 d2 b) : ∀ x, ¬ Win p w x → m'[x]? = c.σ.mem[x]? := by
  intro x hx
  refine hfs.frame x ?_ ?_ ?_
  all_goals
    refine Classical.byContradiction fun h => hx ?_
    simp only [Win, RelPtrs.slot, stackValueSize] at h ⊢
    left; omega

/-- **`OP_FORLOOP`'s jump back**: count−1 to `R[A+1]`, the index to `R[A]`
and `R[A+3]` (payload stores keep the integer tags of `R[A]`, `R[A+1]`). -/
theorem Core.forloop (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {P : MState → Prop} (hseg : SegSt pcv L P c') {pc' a : Nat} {n st x : BitVec 64}
    (hpins : Pins c'.σ w pc') (hout : c'.σ.sailOutput = c.σ.sailOutput)
    (ha : a + 3 < p.maxstacksize)
    (hfs : ForStore c.σ.mem c'.σ.mem (w.slot a) (n - 1) (x + st) (BitVec.ofNat 8 vNumInt))
    (hn : s.regs (a + 1) = some (.int n)) (hi : s.regs a = some (.int x)) :
    Core p c' ⟨pc', upd (upd (upd s.regs (a + 3) (.int (x + st))) a (.int (x + st)))
      (a + 1) (.int (n - 1)), s.out⟩ w := by
  have hsl : ∀ j, w.slot (a + j) = w.slot a + 16 * j := fun j => by
    simp only [RelPtrs.slot, stackValueSize]; omega
  have ht1 := (hc.stack (a + 1) _ (by omega) hn).tag_of_int.1
  have ht0 := (hc.stack a _ (by omega) hi).tag_of_int.1
  refine hc.update hseg hpins hout (fun y hy => ?_) (fun j v hj hv => ?_)
  · exact hfs.frame_mo hc ha y hy
  · simp only [upd] at hv
    by_cases h1 : j = a + 1
    · subst h1
      simp only [ite_true, Option.some.injEq] at hv
      subst hv
      rw [hsl 1, Nat.mul_one, hfs.val1, hfs.tag1, ← Nat.mul_one 16, ← hsl 1, ht1]
      exact .int
    by_cases h0 : j = a
    · subst h0
      simp only [h1, ite_true, ite_false, Option.some.injEq] at hv
      subst hv
      rw [hfs.val0, hfs.tag0, ht0]
      exact .int
    by_cases h3 : j = a + 3
    · subst h3
      simp only [h1, h0, ite_true, ite_false, Option.some.injEq] at hv
      subst hv
      rw [hsl 3, show 16 * 3 = 48 from rfl, hfs.val3, hfs.tag3]
      exact .int
    · simp only [h1, h0, h3, ite_false] at hv
      obtain ⟨ht, hv2⟩ := slot_congr (m := c'.σ.mem) (m' := c.σ.mem) (a := w.slot j) fun i hi => by
        refine hfs.frame _ ?_ ?_ ?_ <;> simp only [RelPtrs.slot, stackValueSize] <;>
          rcases Nat.lt_or_gt_of_ne h0 with h | h <;> omega
      rw [ht, hv2]
      exact hc.stack j v hj hv

end

end Lua.Vm.Sim

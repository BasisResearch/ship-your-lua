import Lua.Vm.Sim.Kit.Stdio
import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.AtF.Memmove

/-!
# `memmove(dst, src, n)` on disjoint ranges (lane F1-8)

`__sfvwrite_r` copies the bytes `print` writes into `stdout`'s buffer with
`memmove` (`0x8003b444`). Its at-lemmas are generated
(`Lua/Vm/AtF/Memmove.lean`, `scripts/gen_lua_at.py --fn memmove`): the entry's
paths, and each of its three copy loops as a root (bytes; 32-byte blocks;
words). This file runs each loop by `seg_loop` with the copy so far as the
invariant (`MoveOut`), and joins them at their arrivals.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-! ## The copy so far -/

/-- **`t` bytes copied** from `S` to `D` over `m`: the moved bytes, and
everything outside `[D, D + t)` as in `m`. -/
structure MoveOut (m M : Mem) (D S t : Nat) : Prop where
  moved : ∀ i, i < t → bytesT1 M (D + i) = bytesT1 m (S + i)
  keep : ∀ a, (a < D ∨ D + t ≤ a) → M[a]? = m[a]?

theorem MoveOut.zero (m : Mem) (D S : Nat) : MoveOut m m D S 0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- A read outside the copied range. -/
theorem MoveOut.rd1 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a < D ∨ D + t ≤ a) :
    bytesT1 M a = bytesT1 m a := bT1_congr (h.keep a ha)

theorem MoveOut.rd8 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a + 8 ≤ D ∨ D + t ≤ a) :
    bytesT8 M a = bytesT8 m a := bT8_congr fun _ _ => h.keep _ (by omega)

/-- The byte lanes of two equal words (in two memories). -/
theorem lanes8 {m1 m2 : Mem} {a b : Nat} (h : bytesT8 m1 a = bytesT8 m2 b) :
    ∀ k, k < 8 → bytesT1 m1 (a + k) = bytesT1 m2 (b + k) := by
  intro k hk
  simp only [bytesT8] at h
  obtain ⟨h, h0⟩ := append_inj' h
  obtain ⟨h, h1⟩ := append_inj' h
  obtain ⟨h, h2⟩ := append_inj' h
  obtain ⟨h, h3⟩ := append_inj' h
  obtain ⟨h, h4⟩ := append_inj' h
  obtain ⟨h, h5⟩ := append_inj' h
  obtain ⟨h7, h6⟩ := append_inj' h
  simp only [bytesT1]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa

/-- `sb` of a loaded byte (`lbu`'s zero extension, then the low byte). -/
theorem stData_zext (b : BitVec 8) : stData 1 (zero_extend (m := 64) (b : BitVec (8 * 1))) = b := by
  revert b; decide

/-- One byte more. -/
theorem MoveOut.ins {m M : Mem} {D S t a : Nat} {b : BitVec 8} (h : MoveOut m M D S t) (ha : a = D + t)
    (hb : b = bytesT1 m (S + t)) : MoveOut m (M.insert a b) D S (t + 1) := by
  subst ha hb
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · by_cases e : i = t
    · subst e; exact fw1_same rfl
    · rw [fw1_ins (by omega)]; exact h.moved i (by omega)
  · rw [ins_out _ _ _ _ (by omega)]; exact h.keep x (by omega)

/-- One word more. -/
theorem MoveOut.wm8 {m M : Mem} {D S t a : Nat} {v : BitVec 64} (h : MoveOut m M D S t) (ha : a = D + t)
    (hv : v = bytesT8 m (S + t)) : MoveOut m (writeMap8 M a (sdData_val v)) D S (t + 8) := by
  subst ha hv
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · by_cases e : i < t
    · rw [fw1_wm8 (by omega)]; exact h.moved i e
    · have := lanes8 (fw8_same (m := M) (a := D + t) (x := D + t) (v := bytesT8 m (S + t)) rfl) (i - t) (by omega)
      rwa [show D + t + (i - t) = D + i by omega, show S + t + (i - t) = S + i by omega] at this
  · rw [getElem?_writeMap8_out _ _ _ _ (by omega)]; exact h.keep x (by omega)

/-- The copy's end: `n` bytes copied, the memory equal off `[D, D + n)`. -/
theorem MoveOut.mono {m M : Mem} {D S t t' : Nat} (h : MoveOut m M D S t) (e : t = t') : MoveOut m M D S t' :=
  e ▸ h

/-! ## The return -/

/-- `memmove`'s return: `a0 = dst`, `sp`, `gp` and the caller's frame. -/
abbrev mmRet (r : BitVec 64) (sp : Nat) (a0 : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) :
    Config → Prop :=
  SegSt r (⟨Register.x10, a0⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins) (ArmPay M o)

/-- A context of `memmove`'s rows: `sp`, the Nat atoms, `ra`, the frame, `a0`. -/
@[at_row] abbrev mmCx (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (a0 : BitVec 64) (M : Mem) (o : Array String) :
    FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, a0] M o

/-- The ranges of a copy phase: `[d, d + k)` and `[s, s + k)` apart, in RAM,
off `tohost`. -/
structure MmSpan (d s k : Nat) : Prop where
  d_lo : 0x8005c6d0 ≤ d
  s_lo : 0x80000000 ≤ s
  disj : d + k ≤ s ∨ s + k ≤ d
  d_hi : d + k ≤ 2 ^ 32
  s_hi : s + k ≤ 2 ^ 32
  s_th : s + k ≤ 0x8005c6c0 ∨ 0x8005c6c8 ≤ s

/-! ## The byte loop (`0x8003b48c`) -/

/-- **The byte loop** from `i` of `k` bytes copied (the phase's bases `d = D + T`,
`s = S + T`): the rest copied, then the return. -/
theorem mm_bytes (sp d s k D S T : Nat) (r a0 : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hd : d = D + T) (hs : s = S + T) (hk : MmSpan d s k) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0)
    (hsd : S + (T + k) ≤ D ∨ D + (T + k) ≤ S) :
    ∀ i M, i < k → MoveOut m M D S (T + i) →
      Triple (SegSt 0x8003b48c#64 (Lua.Vm.AtF.Memmove.r10 (mmCx [sp, d, s, k, i] r f a0 M o))
          (ArmPay (mmCx [sp, d, s, k, i] r f a0 M o).m (mmCx [sp, d, s, k, i] r f a0 M o).o))
        (fun c => ∃ M', mmRet r sp a0 f M' o c ∧ MoveOut m M' D S (T + k)) := by
  intro i₀ M₀ hi₀ hM₀ c₀ h₀
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < k ∧ MoveOut m p.2 D S (T + p.1) ∧
      SegSt 0x8003b48c#64 (Lua.Vm.AtF.Memmove.r10 (mmCx [sp, d, s, k, p.1] r f a0 p.2 o))
        (ArmPay (mmCx [sp, d, s, k, p.1] r f a0 p.2 o).m (mmCx [sp, d, s, k, p.1] r f a0 p.2 o).o) c)
    (fun p => k - p.1) (fun ⟨i, M⟩ c ⟨hi, hM, h⟩ => ?_) (i₀, M₀) c₀ ⟨hi₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memmove.Ok_B (mmCx [sp, d, s, k, i] r f a0 M o) :=
    ⟨hk.d_lo, hk.s_lo, hsp, hra, hk.disj, hk.d_hi, hk.s_hi, hk.s_th, hi⟩
  have acc := Steps.refl c
  -- the byte read is the source's
  have hb : bytesT1 M (s + i) = bytesT1 m (S + (T + i)) := by
    rw [hM.rd1 (by omega), hs, Nat.add_assoc]
  have hM' := hM.ins (a := d + i) (b := bytesT1 m (S + (T + i))) (by omega) rfl
  by_cases he : i + 1 = k
  · fat_run Lua.Vm.AtF.Memmove h acc
    fcx_unfold at h
    rw [hb, stData_zext] at h
    exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b48c]
    fcx_unfold at h
    rw [hb, stData_zext] at h
    refine ⟨_, acc, .inl ⟨(i + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

/-! ## The size arithmetic of the aligned path -/

/-- `andi rd, rs, k` (a small positive mask) on a Nat-valued register. -/
theorem and_imm (n k : Nat) (hn : n < 2 ^ 64) (hk : k < 2048) :
    BitVec.ofNat 64 n &&& sign_extend (m := 64) (BitVec.ofNat 12 k) = BitVec.ofNat 64 (n &&& k) := by
  rw [Lua.Vm.Sim.imm12 k hk]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_left hn)]

theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and31 (n : Nat) : n &&& 31 = n % 32 := Nat.and_two_pow_sub_one_eq_mod n 5
theorem and24 (n : Nat) : n &&& 24 = 8 * (n % 32 / 8) := by
  have : n &&& 24 = (n &&& 31) &&& 24 := by
    rw [Nat.and_assoc, show (31 &&& 24 : Nat) = 24 from rfl]
  rw [this, and31]
  have h := Nat.mod_lt n (show 0 < 32 by decide)
  generalize n % 32 = r at h ⊢
  revert r; decide

/-- `srli rd, rs, 5`. -/
theorem srl5 (n : Nat) (hn : n < 2 ^ 64) :
    shift_bits_right (BitVec.ofNat 64 n) (Sail.BitVec.extractLsb (0x05#6) 5 0) = BitVec.ofNat 64 (n / 32) := by
  simp only [shift_bits_right, Sail.BitVec.extractLsb]
  apply BitVec.eq_of_toNat_eq
  simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hn]
  omega

/-- `slli rd, rs, 5`. -/
theorem sll5 (x : Nat) :
    shift_bits_left (BitVec.ofNat 64 x) (Sail.BitVec.extractLsb (0x05#6) 5 0) = BitVec.ofNat 64 (32 * x) := by
  rw [show (0x05#6 : BitVec 6) = BitVec.ofNat 6 5 from rfl, Lua.Vm.Sim.shl_ofNat x 5 (by decide)]
  congr 1; omega

/-- `addi -1; addi 1` cancel. -/
theorem m1p1 (x : BitVec 64) : x + sign_extend (m := 64) (0xfff#12) + sign_extend (m := 64) (0x001#12) = x := by
  rw [BitVec.add_assoc, show sign_extend (m := 64) (0xfff#12) + sign_extend (m := 64) (0x001#12) = 0#64 by decide,
    BitVec.add_zero]

/-- The byte tail's end after the words (`a3 = a5 + ((n & 7) - 1 + 1)`). -/
theorem tail7 (A n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 A + (((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x007#12)) +
      sign_extend (m := 64) (0xfff#12)) + sign_extend (m := 64) (0x001#12)) = BitVec.ofNat 64 (A + n % 8) := by
  rw [m1p1, show (0x007#12 : BitVec 12) = BitVec.ofNat 12 7 from rfl, and_imm n 7 hn (by decide), and7,
    BitVec.ofNat_add_ofNat]

/-- … after the blocks (`a3 = a5 + ((n & 31) - 1 + 1)`). -/
theorem tail31 (A n : Nat) (hn : n < 2 ^ 64) :
    BitVec.ofNat 64 A + (((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x01f#12)) +
      sign_extend (m := 64) (0xfff#12)) + sign_extend (m := 64) (0x001#12)) = BitVec.ofNat 64 (A + n % 32) := by
  rw [m1p1, show (0x01f#12 : BitVec 12) = BitVec.ofNat 12 31 from rfl, and_imm n 31 hn (by decide), and31,
    BitVec.ofNat_add_ofNat]

/-- The words' guard (`andi a2, a2, 7; beqz`). -/
theorem guard7 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x007#12)) == 0x0#64) = decide (n % 8 = 0) := by
  rw [show (0x007#12 : BitVec 12) = BitVec.ofNat 12 7 from rfl, and_imm n 7 hn (by decide), and7,
    show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]

/-! ## The word loop (`0x8003b52c`) -/

/-- **The word loop** from `i` of `w` words (the phase's bases `d = D + T`,
`s = S + T`), then the `n % 8` byte tail, then the return. -/
theorem mm_words (sp d s w n D S T : Nat) (r a0 : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hd : d = D + T) (hs : s = S + T) (hk : MmSpan d s (8 * w + n % 8)) (hsp : sp ≤ 2 ^ 32)
    (hra : r.toNat % 4 = 0) (hal : d % 8 = 0) (hal' : s % 8 = 0) (hn : n < 2 ^ 64)
    (hsd : S + (T + (8 * w + n % 8)) ≤ D ∨ D + (T + (8 * w + n % 8)) ≤ S) :
    ∀ i M, i < w → MoveOut m M D S (T + 8 * i) →
      Triple (SegSt 0x8003b52c#64 (Lua.Vm.AtF.Memmove.r26 (mmCx [sp, d, s, w, i, n] r f a0 M o))
          (ArmPay (mmCx [sp, d, s, w, i, n] r f a0 M o).m (mmCx [sp, d, s, w, i, n] r f a0 M o).o))
        (fun c => ∃ M', mmRet r sp a0 f M' o c ∧ MoveOut m M' D S (T + (8 * w + n % 8))) := by
  intro i₀ M₀ hi₀ hM₀ c₀ h₀
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < w ∧ MoveOut m p.2 D S (T + 8 * p.1) ∧
      SegSt 0x8003b52c#64 (Lua.Vm.AtF.Memmove.r26 (mmCx [sp, d, s, w, p.1, n] r f a0 p.2 o))
        (ArmPay (mmCx [sp, d, s, w, p.1, n] r f a0 p.2 o).m (mmCx [sp, d, s, w, p.1, n] r f a0 p.2 o).o) c)
    (fun p => w - p.1) (fun ⟨i, M⟩ c ⟨hi, hM, h⟩ => ?_) (i₀, M₀) c₀ ⟨hi₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memmove.Ok_W8 (mmCx [sp, d, s, w, i, n] r f a0 M o) := by fcx_ok
  have acc := Steps.refl c
  have hv : bytesT8 M (s + 8 * i) = bytesT8 m (S + (T + 8 * i)) := by
    rw [hM.rd8 (by omega), hs, Nat.add_assoc]
  have hM' := hM.wm8 (a := d + 8 * i) (v := bytesT8 m (S + (T + 8 * i))) (by omega) rfl
  by_cases he : i + 1 = w
  · have hg7 := guard7 n hn
    by_cases h8 : n % 8 = 0
    · simp only [h8, decide_true] at hg7
      fat_run Lua.Vm.AtF.Memmove h acc
      fcx_unfold at h
      rw [hv] at h
      exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
    · simp only [h8, decide_false] at hg7
      fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b48c]
      fcx_unfold at h
      rw [hv, tail7 _ _ hn] at h
      obtain ⟨c2, s2, M2, hr, hMo⟩ := mm_bytes sp (d + 8 * w) (s + 8 * w) (n % 8) D S (T + 8 * w) r a0 f m o
        (by omega) (by omega) ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ hsp hra (by omega)
        0 (writeMap8 M (d + 8 * i) (sdData_val (bytesT8 m (S + (T + 8 * i))))) (by omega)
        (hM'.mono (by omega)) _ (by fcx_unfold; exact h.repin (by at_pins h))
      exact ⟨c2, acc.trans s2, .inr ⟨M2, hr, hMo.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b52c]
    fcx_unfold at h
    rw [hv] at h
    refine ⟨_, acc, .inl ⟨(i + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

/-- The blocks' exit guards (`andi a6, a2, 24`; `andi a3, a2, 31`). -/
theorem guard24 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x018#12)) == (0#64)) = decide (n % 32 < 8) := by
  rw [show (0x018#12 : BitVec 12) = BitVec.ofNat 12 24 from rfl, and_imm n 24 hn (by decide), and24,
    show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide), decide_eq_decide]
  omega

theorem guard31 (n : Nat) (hn : n < 2 ^ 64) :
    ((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x01f#12)) == 0x0#64) = decide (n % 32 = 0) := by
  rw [show (0x01f#12 : BitVec 12) = BitVec.ofNat 12 31 from rfl, and_imm n 31 hn (by decide), and31,
    show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]

/-- The words' end offset on the 24 lanes `r = n % 32 ≥ 8` (ground). -/
theorem w8end_lane : ∀ r, r < 32 → 8 ≤ r →
    (BitVec.ofNat 64 r + sign_extend (m := 64) (0xff8#12)) &&& sign_extend (m := 64) (0xff8#12) =
      BitVec.ofNat 64 (8 * (r / 8) - 8) := by
  decide

/-- The words' end offset (`addi a3, a3, -8; andi a3, a3, -8`, `a3 = (n & 31)`). -/
theorem w8end (n : Nat) (hn : n < 2 ^ 64) (h8 : 8 ≤ n % 32) :
    ((BitVec.ofNat 64 n &&& sign_extend (m := 64) (0x01f#12)) + sign_extend (m := 64) (0xff8#12)) &&&
      sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (8 * (n % 32 / 8) - 8) := by
  rw [show (0x01f#12 : BitVec 12) = BitVec.ofNat 12 31 from rfl, and_imm n 31 hn (by decide), and31]
  exact w8end_lane _ (Nat.mod_lt n (by decide)) h8

/-! ## The 32-byte blocks (`0x8003b4c8`) -/

/-- **The block loop** from `j` of `q = n / 32` blocks, then the words and
the bytes of `n % 32`, then the return (`a0 = d`). -/
theorem mm_blocks (sp d s n q : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hq : q = n / 32) (hq1 : 1 ≤ q) (hk : MmSpan d s n) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0)
    (hal : d % 8 = 0) (hal' : s % 8 = 0) :
    ∀ j M, j < q → MoveOut m M d s (32 * j) →
      Triple (SegSt 0x8003b4c8#64 (Lua.Vm.AtF.Memmove.r24 (mmCx [sp, d, s, n, j, q] r f 0#64 M o))
          (ArmPay (mmCx [sp, d, s, n, j, q] r f 0#64 M o).m (mmCx [sp, d, s, n, j, q] r f 0#64 M o).o))
        (fun c => ∃ M', mmRet r sp (BitVec.ofNat 64 d) f M' o c ∧ MoveOut m M' d s n) := by
  intro j₀ M₀ hj₀ hM₀ c₀ h₀
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  have hn : n < 2 ^ 64 := by omega
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < q ∧ MoveOut m p.2 d s (32 * p.1) ∧
      SegSt 0x8003b4c8#64 (Lua.Vm.AtF.Memmove.r24 (mmCx [sp, d, s, n, p.1, q] r f 0#64 p.2 o))
        (ArmPay (mmCx [sp, d, s, n, p.1, q] r f 0#64 p.2 o).m (mmCx [sp, d, s, n, p.1, q] r f 0#64 p.2 o).o) c)
    (fun p => q - p.1) (fun ⟨j, M⟩ c ⟨hj, hM, h⟩ => ?_) (j₀, M₀) c₀ ⟨hj₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memmove.Ok_W32 (mmCx [sp, d, s, n, j, q] r f 0#64 M o) := by fcx_ok
  have acc := Steps.refl c
  have hv0 : bytesT8 M (s + 32 * j) = bytesT8 m (s + (32 * j)) := hM.rd8 (by omega)
  have hv1 : bytesT8 M (s + 32 * j + 8) = bytesT8 m (s + (32 * j + 8)) := by
    rw [hM.rd8 (by omega), Nat.add_assoc]
  have hv2 : bytesT8 M (s + 32 * j + 16) = bytesT8 m (s + (32 * j + 8 + 8)) := by
    rw [hM.rd8 (by omega)]; congr 1 <;> omega
  have hv3 : bytesT8 M (s + 32 * j + 24) = bytesT8 m (s + (32 * j + 8 + 8 + 8)) := by
    rw [hM.rd8 (by omega)]; congr 1 <;> omega
  have hM' := ((((hM.wm8 (a := d + 32 * j) (v := bytesT8 m (s + 32 * j)) rfl rfl).wm8
    (a := d + 32 * j + 8) (v := bytesT8 m (s + (32 * j + 8))) (by omega) rfl).wm8
    (a := d + 32 * j + 16) (v := bytesT8 m (s + (32 * j + 8 + 8))) (by omega) rfl).wm8
    (a := d + 32 * j + 24) (v := bytesT8 m (s + (32 * j + 8 + 8 + 8))) (by omega) rfl)
  by_cases he : j + 1 = q
  · have hg24 := guard24 n hn
    have hg31 := guard31 n hn
    by_cases h8 : n % 32 < 8
    · simp only [h8, decide_true] at hg24
      by_cases h0 : n % 32 = 0
      · simp only [h0, decide_true] at hg31
        fat_run Lua.Vm.AtF.Memmove h acc
        fcx_unfold at h
        rw [hv0, hv1, hv2, hv3] at h
        exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
      · simp only [h0, decide_false] at hg31
        fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b48c]
        fcx_unfold at h
        rw [hv0, hv1, hv2, hv3, tail31 _ _ hn] at h
        obtain ⟨c2, s2, M2, hr, hMo⟩ := mm_bytes sp (d + 32 * q) (s + 32 * q) (n % 32) d s (32 * q) r
          (BitVec.ofNat 64 d) f m o (by omega) (by omega)
          ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ hsp hra (by omega) 0 _ (by omega)
          (hM'.mono (by omega)) _ (by fcx_unfold; exact h.repin (by at_pins h))
        exact ⟨c2, acc.trans s2, .inr ⟨M2, hr, hMo.mono (by omega)⟩⟩
    · simp only [h8, decide_false] at hg24
      fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b52c]
      fcx_unfold at h
      rw [hv0, hv1, hv2, hv3, w8end n hn (by omega)] at h
      obtain ⟨c2, s2, M2, hr, hMo⟩ := mm_words sp (d + 32 * q) (s + 32 * q) (n % 32 / 8) n d s (32 * q) r
        (BitVec.ofNat 64 d) f m o (by omega) (by omega)
        ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩ hsp hra (by omega) (by omega) hn
        (by omega) 0 _ (by omega) (hM'.mono (by omega)) _ (by fcx_unfold; exact h.repin (by at_pins h))
      exact ⟨c2, acc.trans s2, .inr ⟨M2, hr, hMo.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b4c8]
    fcx_unfold at h
    rw [hv0, hv1, hv2, hv3] at h
    refine ⟨_, acc, .inl ⟨(j + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

end Lua.Vm.Sim.Kit

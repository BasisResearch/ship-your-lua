import Lua.Vm.Sim.Kit.Memmove
import Lua.Vm.AtF.Memchr

/-!
# `memchr(s, '\n', n)` (lane F1-8)

`__sfvwrite_r` finds the next newline of the bytes `print` writes with
`memchr` (`0x800360d8`). Its at-lemmas are generated
(`Lua/Vm/AtF/Memchr.lean`, `scripts/gen_lua_at.py --fn memchr`): the entry's
paths and its three loops as roots (the alignment bytes; the words, tested
with the zero-lane trick on `word ^ 0x0a…0a`; the bytes). This file runs the
loops by `seg_loop` with "no newline before the position" (`NlClear`) as the
invariant. The word test is proved in one direction only (`mc_hz`: a zero
test means a clear word); when it fires, the byte scan decides.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)


/-- The first index with `P`, below a known one. -/
theorem first_of {P : Nat → Prop} : ∀ j, (∃ i, i ≤ j ∧ P i) → ∃ j0, j0 ≤ j ∧ P j0 ∧ ∀ i, i < j0 → ¬ P i := by
  intro j
  induction j with
  | zero =>
    rintro ⟨i, hi, hp⟩
    exact ⟨0, Nat.le_refl _, by rwa [show i = 0 by omega] at hp, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | succ j ih =>
    rintro ⟨i, hi, hp⟩
    by_cases e : ∃ i, i ≤ j ∧ P i
    · obtain ⟨j0, h1, h2, h3⟩ := ih e
      exact ⟨j0, by omega, h2, h3⟩
    · have hij : i = j + 1 := by
        rcases Nat.lt_or_ge i (j + 1) with h | h
        · exact absurd ⟨i, by omega, hp⟩ e
        · omega
      subst hij
      exact ⟨j + 1, Nat.le_refl _, hp, fun i hi hp' => e ⟨i, by omega, hp'⟩⟩

/-- The newline word: `0x0a` in every byte lane. -/
abbrev nlW : BitVec 64 := 0xa0a0a0a0a0a0a0a#64


/-- The lanes of the newline word. -/
theorem nlW_dig : ∀ i, i < 8 → (0xa0a0a0a0a0a0a0a : Nat) / 2 ^ (8 * i) % 2 ^ 8 = 10 := by decide

/-- A lane `10 ^ b` is zero only at a newline. -/
theorem xor10_pos {b : BitVec 8} (h : b ≠ 0x0a#8) : 1 ≤ 10 ^^^ b.toNat := by
  rcases Nat.eq_zero_or_pos (10 ^^^ b.toNat) with e | e
  · exfalso; apply h
    apply BitVec.eq_of_toNat_eq
    apply Nat.eq_of_testBit_eq; intro k
    have := congrArg (Nat.testBit · k) e
    simp only [Nat.testBit_xor, Nat.zero_testBit] at this
    show b.toNat.testBit k = (10 : Nat).testBit k
    revert this
    cases Nat.testBit 10 k <;> cases Nat.testBit b.toNat k <;> simp
  · exact e

/-- **The borrow lane**: subtracting `0x01…01` from a word whose lanes below
`J` are nonzero and whose lane `J` is zero sets the top bit of lane `J`. -/
theorem borrow_bit (t J : Nat) (hJ : J < 8) (ht : t < 2 ^ 64)
    (hlo : ∀ i, i < J → 1 ≤ t / 2 ^ (8 * i) % 2 ^ 8) (hz : t / 2 ^ (8 * J) % 2 ^ 8 = 0) :
    ((t + 18374403900871474943) % 2 ^ 64).testBit (8 * J + 7) = true ∧ t.testBit (8 * J + 7) = false := by
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq, decide_eq_true_eq, decide_eq_false_iff_not]
  rcases (by omega : J = 0 ∨ J = 1 ∨ J = 2 ∨ J = 3 ∨ J = 4 ∨ J = 5 ∨ J = 6 ∨ J = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    (try have n0 := hlo 0 (by decide)); (try have n1 := hlo 1 (by decide))
    (try have n2 := hlo 2 (by decide)); (try have n3 := hlo 3 (by decide))
    (try have n4 := hlo 4 (by decide)); (try have n5 := hlo 5 (by decide))
    (try have n6 := hlo 6 (by decide))
    simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] at *
    constructor <;> omega

/-- **`memchr`'s word test** (`((x - 0x01…01) & ~x & 0x80…80)` on
`x = word ^ 0x0a…0a`): zero only when no byte of the word is a newline (the
lowest newline lane borrows: its top bit is set in all three). -/
theorem mc_hz (M : Mem) (p : Nat)
    (h : (((((nlW ^^^ bytesT8 M p) + 0xfefefefefefefeff#64) &&&
      ((nlW ^^^ bytesT8 M p) ^^^ sign_extend (m := 64) (0xfff#12))) &&& 0x8080808080808080#64) != 0#64) = false) :
    ∀ j, j < 8 → bytesT1 M (p + j) ≠ 0x0a#8 := by
  intro j hj hb
  obtain ⟨j0, hj0, hb0, hlow⟩ := first_of (P := fun i => bytesT1 M (p + i) = 0x0a#8) j ⟨j, Nat.le_refl _, hb⟩
  have hw := bytesT8_toNat (m := M) (p := p)
  have b0 := (bytesT1 M p).isLt; have b1 := (bytesT1 M (p + 1)).isLt; have b2 := (bytesT1 M (p + 2)).isLt
  have b3 := (bytesT1 M (p + 3)).isLt; have b4 := (bytesT1 M (p + 4)).isLt; have b5 := (bytesT1 M (p + 5)).isLt
  have b6 := (bytesT1 M (p + 6)).isLt; have b7 := (bytesT1 M (p + 7)).isLt
  have dig : ∀ i, i < 8 → (nlW ^^^ bytesT8 M p).toNat / 2 ^ (8 * i) % 2 ^ 8 =
      10 ^^^ (bytesT1 M (p + i)).toNat := by
    intro i hi
    rw [BitVec.toNat_xor, Nat.xor_div_two_pow, Nat.xor_mod_two_pow, show nlW.toNat = 0xa0a0a0a0a0a0a0a from rfl,
      nlW_dig i hi]
    congr 1
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (try simp only [Nat.add_zero] at hw ⊢) <;> omega
  have hx := (nlW ^^^ bytesT8 M p).isLt
  generalize nlW ^^^ bytesT8 M p = x at h dig hx
  have hR : ((x + 0xfefefefefefefeff#64) &&& (x ^^^ sign_extend (m := 64) (0xfff#12))) &&&
      0x8080808080808080#64 = 0#64 := by
    simpa only [bne_eq_false_iff_eq] using h
  have hk := congrArg (fun v : BitVec 64 => v.getLsbD (8 * j0 + 7)) hR
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_zero] at hk
  have hz := dig j0 (by omega)
  rw [show bytesT1 M (p + j0) = 0x0a#8 from hb0, show (10 : Nat) ^^^ (0x0a#8 : BitVec 8).toNat = 0 from rfl] at hz
  obtain ⟨f1, f2⟩ := borrow_bit x.toNat j0 (by omega) hx
    (fun i hi => by rw [dig i (by omega)]; exact xor10_pos (hlow i hi)) hz
  rw [← BitVec.testBit_toNat, ← BitVec.testBit_toNat, BitVec.toNat_add,
    show (0xfefefefefefefeff#64 : BitVec 64).toNat = 18374403900871474943 from rfl, f1, f2] at hk
  have e1 : (sign_extend (m := 64) (0xfff#12) : BitVec 64).getLsbD (8 * j0 + 7) = true := by
    rcases (by omega : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 ∨ j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 ∨ j0 = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have e2 : (0x8080808080808080#64 : BitVec 64).getLsbD (8 * j0 + 7) = true := by
    rcases (by omega : j0 = 0 ∨ j0 = 1 ∨ j0 = 2 ∨ j0 = 3 ∨ j0 = 4 ∨ j0 = 5 ∨ j0 = 6 ∨ j0 = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  rw [e1, e2] at hk
  simp at hk


/-! ## The answer -/

/-- No newline in `[s, s + q)`. -/
def NlClear (M : Mem) (s q : Nat) : Prop := ∀ j, j < q → bytesT1 M (s + j) ≠ 0x0a#8

theorem NlClear.snoc {M : Mem} {s q : Nat} (h : NlClear M s q) (hb : bytesT1 M (s + q) ≠ 0x0a#8) :
    NlClear M s (q + 1) := fun j hj => by
  rcases Nat.lt_or_ge j q with e | e
  · exact h j e
  · rwa [show j = q by omega]

theorem NlClear.word {M : Mem} {s q : Nat} (h : NlClear M s q) (hw : ∀ j, j < 8 → bytesT1 M (s + q + j) ≠ 0x0a#8) :
    NlClear M s (q + 8) := fun j hj => by
  rcases Nat.lt_or_ge j q with e | e
  · exact h j e
  · have := hw (j - q) (by omega); rwa [show s + q + (j - q) = s + j by omega] at this

/-- **`memchr`'s answer** over `[s, s + n)`: the first newline's address, or `0`. -/
inductive NlAns (M : Mem) (s n : Nat) : BitVec 64 → Prop
  | found (k : Nat) : k < n → bytesT1 M (s + k) = 0x0a#8 → NlClear M s k → NlAns M s n (BitVec.ofNat 64 (s + k))
  | none : NlClear M s n → NlAns M s n 0#64

/-- `memchr`'s return: the answer in `a0`, the memory unchanged. -/
abbrev mcPost (r : BitVec 64) (sp : Nat) (f : AbiFrame) (M : Mem) (o : Array String) (s n : Nat) :
    Config → Prop :=
  fun c => ∃ a0, mmRet r sp a0 f M o c ∧ NlAns M s n a0

/-- A context of `memchr`'s rows. -/
@[at_row] abbrev mcCx (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) : FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11] M o

/-- The range searched: in RAM, off `tohost`. -/
structure McSpan (s n : Nat) : Prop where
  s_lo : 0x80000000 ≤ s
  s_hi : s + n ≤ 2 ^ 32
  s_th : s + n ≤ 0x8005c6c0 ∨ 0x8005c6c8 ≤ s

/-! ## The guards -/

theorem zb_ne (b : BitVec 8) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) != 0xa#64) = !decide (b = 0x0a#8) := by
  rw [bne, show (0xa#64 : BitVec 64) = zero_extend (m := 64) (0x0a#8 : BitVec (8 * 1)) by decide, zext8_beq]

theorem zb_eq (b : BitVec 8) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) == 0xa#64) = decide (b = 0x0a#8) := by
  rw [show (0xa#64 : BitVec 64) = zero_extend (m := 64) (0x0a#8 : BitVec (8 * 1)) by decide, zext8_beq]

theorem al_next (p : Nat) (hp : p + 1 < 2 ^ 64) :
    (((BitVec.ofNat 64 p + sign_extend (m := 64) (0x001#12)) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) =
      !decide ((p + 1) % 8 = 0) := by
  rw [show (0x001#12 : BitVec 12) = BitVec.ofNat 12 1 from rfl, add_imm p 1 (by decide),
    show (0x007#12 : BitVec 12) = BitVec.ofNat 12 7 from rfl, and_imm _ 7 hp (by decide), and7,
    show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbne (by omega) (by decide)]

theorem al_at (p : Nat) (hp : p < 2 ^ 64) :
    (((BitVec.ofNat 64 p) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = decide (p % 8 = 0) := by
  rw [show (0x007#12 : BitVec 12) = BitVec.ofNat 12 7 from rfl, and_imm _ 7 hp (by decide), and7,
    show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbeq (by omega) (by decide)]

/-- The count after `addi a2, a2, -1`, as the row prints it (modular). -/
theorem dec_mod (r : Nat) (h : 1 ≤ r) (hr : r < 2 ^ 64) :
    BitVec.ofNat 64 (r + 18446744073709551615) = BitVec.ofNat 64 (r - 1) := by
  apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega

/-- The word test of `memchr`, as its rows state it. -/
abbrev mcG (M : Mem) (p : Nat) : Bool :=
  ((((((0xa0a0a0a0a0a0a0a#64) ^^^ (sign_extend (m := 64) (bytesT8 (M) ((BitVec.ofNat 64 (p)) +
    sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)))) + (0xfefefefefefefeff#64)) &&&
    (((0xa0a0a0a0a0a0a0a#64) ^^^ (sign_extend (m := 64) (bytesT8 (M) ((BitVec.ofNat 64 (p)) +
    sign_extend (m := 64) (0x000#12)).toNat : BitVec (8 * 8)))) ^^^ sign_extend (m := 64) (0xfff#12))) &&&
    (0x8080808080808080#64)) != (0#64))

theorem mcG_clear {M : Mem} {p : Nat} (hp : p < 2 ^ 64) (h : mcG M p = false) :
    ∀ j, j < 8 → bytesT1 M (p + j) ≠ 0x0a#8 := by
  apply mc_hz M p
  simp only [mcG, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp, sext64_id] at h
  exact h

/-! ## The byte scan (`0x80036184`) -/

theorem mc_bytes (sp s n : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) (hk : McSpan s n)
    (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) :
    ∀ p, s ≤ p → p < s + n → NlClear M s (p - s) →
      Triple (SegSt 0x80036184#64 (Lua.Vm.AtF.Memchr.r4 (mcCx [sp, p, s + n] r f M o))
          (ArmPay (mcCx [sp, p, s + n] r f M o).m (mcCx [sp, p, s + n] r f M o).o))
        (mcPost r sp f M o s n) := by
  intro p₀ h1₀ h2₀ hc₀ c₀ h₀
  have := hk.s_lo; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun p c => s ≤ p ∧ p < s + n ∧ NlClear M s (p - s) ∧
      SegSt 0x80036184#64 (Lua.Vm.AtF.Memchr.r4 (mcCx [sp, p, s + n] r f M o))
        (ArmPay (mcCx [sp, p, s + n] r f M o).m (mcCx [sp, p, s + n] r f M o).o) c)
    (fun p => s + n - p) (fun p c ⟨h1, h2, hc, h⟩ => ?_) p₀ c₀ ⟨h1₀, h2₀, hc₀, h₀⟩
  have hX : Lua.Vm.AtF.Memchr.Ok_B (mcCx [sp, p, s + n] r f M o) := by fcx_ok
  have acc := Steps.refl c
  have hg := zb_ne (bytesT1 M p)
  by_cases hb : bytesT1 M p = 0x0a#8
  · simp only [hb, decide_true, Bool.not_true] at hg
    rw [← hb] at hg
    fat_run Lua.Vm.AtF.Memchr h acc
    fcx_unfold at h
    refine ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), ?_⟩⟩
    have e : p = s + (p - s) := by omega
    rw [e]; exact .found _ (by omega) (by rw [← e]; exact hb) hc
  · simp only [hb, decide_false, Bool.not_false] at hg
    have hc' : NlClear M s (p - s + 1) := hc.snoc (by rwa [show s + (p - s) = p by omega])
    by_cases he : p + 1 = s + n
    · fat_run Lua.Vm.AtF.Memchr h acc
      fcx_unfold at h
      exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), .none (fun j hj => hc' j (by omega))⟩⟩
    · fat_run Lua.Vm.AtF.Memchr h acc until [0x80036184]
      fcx_unfold at h
      refine ⟨_, acc, .inl ⟨p + 1, by omega, by omega, by omega, fun j hj => hc' j (by omega), ?_⟩⟩
      fcx_unfold
      exact h.repin (by pins_of h)

/-! ## The words (`0x80036148`) -/

theorem mc_words (sp s n : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) (hk : McSpan s n)
    (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) :
    ∀ p rem, s ≤ p → p + rem = s + n → 7 < rem → p % 8 = 0 → NlClear M s (p - s) →
      Triple (SegSt 0x80036148#64 (Lua.Vm.AtF.Memchr.r20 (mcCx [sp, p, rem] r f M o))
          (ArmPay (mcCx [sp, p, rem] r f M o).m (mcCx [sp, p, rem] r f M o).o))
        (mcPost r sp f M o s n) := by
  intro p₀ q₀ h1₀ h2₀ h3₀ h4₀ hc₀ c₀ h₀
  have := hk.s_lo; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (pq : Nat × Nat) c => s ≤ pq.1 ∧ pq.1 + pq.2 = s + n ∧ 7 < pq.2 ∧ pq.1 % 8 = 0 ∧
      NlClear M s (pq.1 - s) ∧
      SegSt 0x80036148#64 (Lua.Vm.AtF.Memchr.r20 (mcCx [sp, pq.1, pq.2] r f M o))
        (ArmPay (mcCx [sp, pq.1, pq.2] r f M o).m (mcCx [sp, pq.1, pq.2] r f M o).o) c)
    (fun pq => pq.2) (fun ⟨p, rem⟩ c ⟨h1, h2, h3, h4, hc, h⟩ => ?_) (p₀, q₀) c₀ ⟨h1₀, h2₀, h3₀, h4₀, hc₀, h₀⟩
  simp only at h1 h2 h3 h4 hc ⊢
  have hX : Lua.Vm.AtF.Memchr.Ok_W (mcCx [sp, p, rem] r f M o) := by fcx_ok
  have acc := Steps.refl c
  by_cases hg7 : mcG M p = true
  · fat_run Lua.Vm.AtF.Memchr h acc until [0x80036184]
    fcx_unfold at h
    obtain ⟨c2, s2, hp⟩ := mc_bytes sp s n r f M o hk hsp hra p h1 (by omega) hc _
      (by fcx_unfold; exact h.repin (by pins_of h))
    exact ⟨c2, acc.trans s2, .inr hp⟩
  · simp only [Bool.not_eq_true] at hg7
    have hw := mcG_clear (by omega) hg7
    have hc' : NlClear M s (p - s + 8) := hc.word (by rwa [show s + (p - s) = p by omega])
    by_cases hr : 7 < rem - 8
    · fat_run Lua.Vm.AtF.Memchr h acc until [0x80036148]
      fcx_unfold at h
      refine ⟨_, acc, .inl ⟨(p + 8, rem - 8), by simp only; omega, by simp only; omega, by simp only; omega,
        by simp only; omega, by simp only; omega, fun j hj => hc' j (by simp only at hj; omega), ?_⟩⟩
      fcx_unfold
      exact h.repin (by pins_of h)
    · by_cases h0 : rem - 8 = 0
      · fat_run Lua.Vm.AtF.Memchr h acc
        fcx_unfold at h
        exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), .none (fun j hj => hc' j (by omega))⟩⟩
      · fat_run Lua.Vm.AtF.Memchr h acc until [0x80036184]
        fcx_unfold at h
        obtain ⟨c2, s2, hp⟩ := mc_bytes sp s n r f M o hk hsp hra (p + 8) (by omega) (by omega)
          (fun j hj => hc' j (by omega)) _ (by fcx_unfold; exact h.repin (by pins_of h))
        exact ⟨c2, acc.trans s2, .inr hp⟩

end Lua.Vm.Sim.Kit

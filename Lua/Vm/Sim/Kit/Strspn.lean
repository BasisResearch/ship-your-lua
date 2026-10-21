import Lua.Vm.Sim.Kit.Memchr
import Lua.Vm.Sim.Kit.AtAlign
import Lua.Vm.AtF.Strspn

/-!
# `strspn(s, "-0123456789")` (lane F1-25)

`tostringbuff` asks whether a float's `%.14g` "looks like an int" by
`buff[strspn(buff, "-0123456789")] == '\0'`. `strspn` (`0x800368dc`) scans
`s` with an inner scan over the set; the set is a `.rodata` literal, so its
at-lemmas (`Lua/Vm/AtF/Strspn.lean`, `gen_lua_at.py --fn strspn`) unroll the
inner scan into one fork per character and keep the outer loop a root (`O`).
This file runs the outer loop by `seg_loop` with "every byte before the cursor
is in the set" as the invariant: the answer is `spanLen`, the length of the
longest prefix in the set.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- A byte of a list read by `bytesAt`. (Moved from `Kit/PushfI.lean`.) -/
theorem bytesAt_get {M : Mem} {a n : Nat} {l : List (BitVec 8)} (h : bytesAt M a n = l) {j : Nat} (hj : j < n) :
    bytesT1 M (a + j) = l.getD j 0 := by
  subst h
  simp [bytesAt, List.getD_eq_getElem?_getD, hj]

/-! ## The model -/

/-- A byte of `"-0123456789"`. -/
def spnIn (c : BitVec 8) : Bool := c.toNat == 45 || (48 ≤ c.toNat && c.toNat ≤ 57)

/-- **`strspn`'s answer**: the length of the longest prefix in the set. -/
def spanLen : List (BitVec 8) → Nat
  | [] => 0
  | c :: cs => if spnIn c then spanLen cs + 1 else 0

/-- The answer from where the scan stops: every byte before `k` in the set,
and `k` the end or a byte outside it. -/
theorem spanLen_of : ∀ (bs : List (BitVec 8)) (k : Nat), (∀ j, j < k → spnIn (bs.getD j 0) = true) →
    (k < bs.length → spnIn (bs.getD k 0) = false) → k ≤ bs.length → spanLen bs = k
  | [], k, _, _, hk => by simp only [List.length_nil, Nat.le_zero] at hk; subst hk; rfl
  | c :: cs, 0, _, hn, _ => by
    have := hn (by simp); simp only [List.getD_cons_zero] at this; simp [spanLen, this]
  | c :: cs, k + 1, hin, hn, hk => by
    have h0 := hin 0 (by omega)
    simp only [List.getD_cons_zero] at h0
    simp only [spanLen, h0, if_true, Nat.add_right_cancel_iff]
    refine spanLen_of cs k (fun j hj => ?_) (fun h => ?_) (by simp at hk; omega)
    · have := hin (j + 1) (by omega); simpa using this
    · have := hn (by simp; omega); simpa using this

/-- `strspn`'s answer lies within the string. -/
theorem spanLen_le : ∀ bs : List (BitVec 8), spanLen bs ≤ bs.length
  | [] => Nat.le_refl _
  | c :: cs => by
    have := spanLen_le cs
    simp only [spanLen, List.length_cons]; split <;> omega

/-! ## The guards -/

/-- A loaded byte against a literal byte. -/
theorem zb_bne (b : BitVec 8) (k : Nat) (hk : k < 256) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) != BitVec.ofNat 64 k) = !decide (b = BitVec.ofNat 8 k) := by
  rw [bne, show (BitVec.ofNat 64 k : BitVec 64) = zero_extend (m := 64) (BitVec.ofNat 8 k : BitVec (8 * 1)) by
    apply BitVec.eq_of_toNat_eq; simp [zero_extend, Sail.BitVec.zeroExtend]; omega, zext8_beq]

/-- A loaded byte against zero. -/
theorem zb_bne0 (b : BitVec 8) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) != 0x0#64) = !decide (b = 0#8) := zb_bne b 0 (by decide)

theorem zb_beq0 (b : BitVec 8) :
    (zero_extend (m := 64) (b : BitVec (8 * 1)) == 0x0#64) = decide (b = 0#8) := by
  have := zb_bne0 b; simp only [bne] at this; simpa using this

/-- The set's bytes, as `.rodata` holds them. -/
def spnSetBytes : List (BitVec 8) :=
  [0x2d#8, 0x30#8, 0x31#8, 0x32#8, 0x33#8, 0x34#8, 0x35#8, 0x36#8, 0x37#8, 0x38#8, 0x39#8, 0#8]

/-- A context of `strspn`'s rows: `sp`, `s`, the cursor; the caller's frame, the cursor's byte. -/
@[at_row] abbrev spCx (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (b : BitVec 64) (M : Mem) (o : Array String) :
    FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, b] M o

/-- **`strspn`'s inputs**: the string `bs` and its terminator at `s` (no zero
byte in `bs`), in RAM above `tohost`, the set at `0x8004f3e0`. -/
structure SpnIn (M : Mem) (s : Nat) (bs : List (BitVec 8)) : Prop where
  bytes : bytesAt M s (bs.length + 1) = bs ++ [0#8]
  nz : ∀ j, j < bs.length → bs.getD j 0 ≠ 0#8
  s_lo : 0x8005c6c8 ≤ s
  s_hi : s + bs.length + 2 ≤ 2 ^ 32
  set : bytesAt M 0x8004f3e0 12 = spnSetBytes

theorem SpnIn.byte {M : Mem} {s : Nat} {bs : List (BitVec 8)} (h : SpnIn M s bs) {j : Nat} (hj : j < bs.length) :
    bytesT1 M (s + j) = bs.getD j 0 := by
  rw [bytesAt_get h.bytes (j := j) (by omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem SpnIn.term {M : Mem} {s : Nat} {bs : List (BitVec 8)} (h : SpnIn M s bs) :
    bytesT1 M (s + bs.length) = 0#8 := by
  have := bytesAt_get h.bytes (j := bs.length) (by omega)
  rw [this]; simp

theorem SpnIn.setb {M : Mem} {s : Nat} {bs : List (BitVec 8)} (h : SpnIn M s bs) (j : Nat) (hj : j < 12) :
    bytesT1 M (0x8004f3e0 + j) = spnSetBytes.getD j 0 := bytesAt_get h.set hj

/-- A byte in the set is one of its eleven characters. -/
theorem spnIn_cases (c : BitVec 8) (h : spnIn c = true) :
    c = 0x2d#8 ∨ c = 0x30#8 ∨ c = 0x31#8 ∨ c = 0x32#8 ∨ c = 0x33#8 ∨ c = 0x34#8 ∨ c = 0x35#8 ∨ c = 0x36#8 ∨
      c = 0x37#8 ∨ c = 0x38#8 ∨ c = 0x39#8 := by
  have hc := c.isLt
  simp only [spnIn, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq] at h
  have e : c = BitVec.ofNat 8 c.toNat := by simp
  rcases h with h | ⟨h1, h2⟩
  · rw [e, h]; simp
  · have : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51 ∨ c.toNat = 52 ∨ c.toNat = 53 ∨
        c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨ c.toNat = 57 := by omega
    rw [e]; rcases this with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> simp

/-- A byte off the set is none of its characters. -/
theorem spnIn_ne (c : BitVec 8) (h : spnIn c = false) (k : Nat) (hk : k = 45 ∨ (48 ≤ k ∧ k ≤ 57)) :
    c ≠ BitVec.ofNat 8 k := by
  rintro rfl
  simp only [spnIn, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
    decide_eq_false_iff_not, Nat.not_le, BitVec.toNat_ofNat] at h
  omega

set_option hygiene false in
/-- The cursor's byte against the set's eleven characters, decided by its value. -/
macro "spn_guards" b:term : tactic => `(tactic| (
  have hg0 := zb_bne $b 0x2d (by decide); have hg1 := zb_bne $b 0x30 (by decide)
  have hg2 := zb_bne $b 0x31 (by decide); have hg3 := zb_bne $b 0x32 (by decide)
  have hg4 := zb_bne $b 0x33 (by decide); have hg5 := zb_bne $b 0x34 (by decide)
  have hg6 := zb_bne $b 0x35 (by decide); have hg7 := zb_bne $b 0x36 (by decide)
  have hg8 := zb_bne $b 0x37 (by decide); have hg9 := zb_bne $b 0x38 (by decide)
  have hg10 := zb_bne $b 0x39 (by decide)))

set_option hygiene false in
/-- The guards' decisions at a cursor byte `e : b = c` of the set. -/
macro "spn_dec" e:ident : tactic => `(tactic| (
  (conv at hg0 => rhs; rw [$e:ident]); (conv at hg1 => rhs; rw [$e:ident]); (conv at hg2 => rhs; rw [$e:ident])
  (conv at hg3 => rhs; rw [$e:ident]); (conv at hg4 => rhs; rw [$e:ident]); (conv at hg5 => rhs; rw [$e:ident])
  (conv at hg6 => rhs; rw [$e:ident]); (conv at hg7 => rhs; rw [$e:ident]); (conv at hg8 => rhs; rw [$e:ident])
  (conv at hg9 => rhs; rw [$e:ident]); (conv at hg10 => rhs; rw [$e:ident])
  simp (config := { decide := true }) only [decide_true, decide_false, Bool.not_true, Bool.not_false]
    at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10))

/-! ## The scan -/

set_option hygiene false in
/-- The outer loop's facts at the cursor `p`: the context, the set's bytes, the
cursor's byte, the guards against the set. -/
macro "spn_setup" : tactic => `(tactic| (
  have hX : Lua.Vm.AtF.Strspn.Ok_O
      (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o) := by fcx_ok
  have hc0 : bytesT1 M 0x8004f3e0 = 0x2d#8 := hI.setb 0 (by decide)
  have hc1 : bytesT1 M 0x8004f3e1 = 0x30#8 := hI.setb 1 (by decide)
  have hc2 : bytesT1 M 0x8004f3e2 = 0x31#8 := hI.setb 2 (by decide)
  have hc3 : bytesT1 M 0x8004f3e3 = 0x32#8 := hI.setb 3 (by decide)
  have hc4 : bytesT1 M 0x8004f3e4 = 0x33#8 := hI.setb 4 (by decide)
  have hc5 : bytesT1 M 0x8004f3e5 = 0x34#8 := hI.setb 5 (by decide)
  have hc6 : bytesT1 M 0x8004f3e6 = 0x35#8 := hI.setb 6 (by decide)
  have hc7 : bytesT1 M 0x8004f3e7 = 0x36#8 := hI.setb 7 (by decide)
  have hc8 : bytesT1 M 0x8004f3e8 = 0x37#8 := hI.setb 8 (by decide)
  have hc9 : bytesT1 M 0x8004f3e9 = 0x38#8 := hI.setb 9 (by decide)
  have hc10 : bytesT1 M 0x8004f3ea = 0x39#8 := hI.setb 10 (by decide)
  have hc11 : bytesT1 M 0x8004f3eb = 0x0#8 := hI.setb 11 (by decide)
  have h : SegSt 0x800368f0#64
      (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
      (ArmPay (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o).m
        (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o).o) c := h
  have acc := Steps.refl c
  spn_guards (bytesT1 M p)
  have hn := zb_bne0 (bytesT1 M (p + 1))))

/-- **A cursor byte in the set, the next byte the string's**: around the loop. -/
theorem spn_in_loop (sp s : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (bs : List (BitVec 8)) (hI : SpnIn M s bs) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) (p : Nat)
    (h1 : s ≤ p) (hl : p + 1 < s + bs.length) (hin : spnIn (bytesT1 M p) = true)
    (hz : bytesT1 M (p + 1) ≠ 0#8) (c : Config)
    (h : SegSt 0x800368f0#64
      (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
      (ArmPay M o) c) :
    ∃ c', Steps c c' ∧ SegSt 0x800368f0#64 (Lua.Vm.AtF.Strspn.r5
      (spCx [sp, s, p + 1] r f (zero_extend (m := 64) (bytesT1 M (p + 1) : BitVec (8 * 1))) M o)) (ArmPay M o) c' := by
  have hs1 := hI.s_lo; have hs2 := hI.s_hi
  spn_setup
  simp only [hz, decide_false, Bool.not_false] at hn
  rcases spnIn_cases _ hin with e | e | e | e | e | e | e | e | e | e | e <;>
    spn_dec e <;>
    (fat_run Lua.Vm.AtF.Strspn h acc until [0x800368f0]
     fcx_unfold at h
     refine ⟨_, acc, ?_⟩
     fcx_unfold
     exact h.repin (by pins_of h))

/-- **A cursor byte in the set, the next the terminator**: the end. -/
theorem spn_in_end (sp s : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (bs : List (BitVec 8)) (hI : SpnIn M s bs) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) (p : Nat)
    (h1 : s ≤ p) (hl : p + 1 = s + bs.length) (hin : spnIn (bytesT1 M p) = true) (c : Config)
    (h : SegSt 0x800368f0#64
      (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
      (ArmPay M o) c) :
    ∃ c', Steps c c' ∧ wrRet r sp (p + 1 - s) f M o c' := by
  have hs1 := hI.s_lo; have hs2 := hI.s_hi
  spn_setup
  have hz : bytesT1 M (p + 1) = 0#8 := by rw [hl]; exact hI.term
  rw [decide_eq_true hz, Bool.not_true] at hn
  rcases spnIn_cases _ hin with e | e | e | e | e | e | e | e | e | e | e <;>
    spn_dec e <;>
    (fat_run Lua.Vm.AtF.Strspn h acc
     fcx_unfold at h
     refine ⟨_, acc, ?_⟩
     rw [ofNat_sub_ofNat (by omega) (by omega)] at h
     exact h.repin (by pins_of h))

/-- **A cursor byte off the set**: the end. -/
theorem spn_out (sp s : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String)
    (bs : List (BitVec 8)) (hI : SpnIn M s bs) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) (p : Nat)
    (h1 : s ≤ p) (h2 : p < s + bs.length) (hin : spnIn (bytesT1 M p) = false) (c : Config)
    (h : SegSt 0x800368f0#64
      (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
      (ArmPay M o) c) :
    ∃ c', Steps c c' ∧ wrRet r sp (p - s) f M o c' := by
  have hs1 := hI.s_lo; have hs2 := hI.s_hi
  spn_setup
  have hne := spnIn_ne _ hin
  simp only [hne 45 (.inl rfl), hne 48 (.inr ⟨by decide, by decide⟩), hne 49 (.inr ⟨by decide, by decide⟩),
    hne 50 (.inr ⟨by decide, by decide⟩), hne 51 (.inr ⟨by decide, by decide⟩),
    hne 52 (.inr ⟨by decide, by decide⟩), hne 53 (.inr ⟨by decide, by decide⟩),
    hne 54 (.inr ⟨by decide, by decide⟩), hne 55 (.inr ⟨by decide, by decide⟩),
    hne 56 (.inr ⟨by decide, by decide⟩), hne 57 (.inr ⟨by decide, by decide⟩), decide_false,
    Bool.not_false] at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7 hg8 hg9 hg10
  fat_run Lua.Vm.AtF.Strspn h acc
  fcx_unfold at h
  refine ⟨_, acc, ?_⟩
  rw [ofNat_sub_ofNat (by omega) (by omega)] at h
  exact h.repin (by pins_of h)

/-- **The outer loop** (`O`, `0x800368f0`): every byte before the cursor `p` in
the set, the cursor's byte in `a3`. -/
theorem spn_loop (sp s : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) (bs : List (BitVec 8))
    (hI : SpnIn M s bs) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) :
    ∀ p, s ≤ p → p < s + bs.length → (∀ j, j < p - s → spnIn (bs.getD j 0) = true) →
      Triple (SegSt 0x800368f0#64
          (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
          (ArmPay M o))
        (wrRet r sp (spanLen bs) f M o) := by
  intro p₀ h1₀ h2₀ hc₀ c₀ h₀
  have hs1 := hI.s_lo; have hs2 := hI.s_hi
  refine seg_loop (S := fun p c => s ≤ p ∧ p < s + bs.length ∧
      (∀ j, j < p - s → spnIn (bs.getD j 0) = true) ∧
      SegSt 0x800368f0#64
        (Lua.Vm.AtF.Strspn.r5 (spCx [sp, s, p] r f (zero_extend (m := 64) (bytesT1 M p : BitVec (8 * 1))) M o))
        (ArmPay M o) c)
    (fun p => s + bs.length - p) (fun p c ⟨h1, h2, hc, h⟩ => ?_) p₀ c₀ ⟨h1₀, h2₀, hc₀, h₀⟩
  have hb := hI.byte (j := p - s) (by omega)
  rw [show s + (p - s) = p by omega] at hb
  cases hin : spnIn (bytesT1 M p) with
  | false =>
    obtain ⟨c', s', h'⟩ := spn_out sp s r f M o bs hI hsp hra p h1 h2 hin c h
    refine ⟨c', s', .inr ?_⟩
    rw [spanLen_of bs (p - s) hc (fun _ => by rw [← hb]; exact hin) (by omega)]
    exact h'
  | true =>
    have hc' : ∀ j, j < p + 1 - s → spnIn (bs.getD j 0) = true := fun j hj => by
      rcases Nat.lt_or_ge j (p - s) with e | e
      · exact hc j e
      · rw [show j = p - s by omega, ← hb]; exact hin
    by_cases hl : p + 1 < s + bs.length
    · have hz : bytesT1 M (p + 1) ≠ 0#8 := by
        have := hI.byte (j := p + 1 - s) (by omega)
        rw [show s + (p + 1 - s) = p + 1 by omega] at this
        rw [this]; exact hI.nz _ (by omega)
      obtain ⟨c', s', h'⟩ := spn_in_loop sp s r f M o bs hI hsp hra p h1 hl hin hz c h
      exact ⟨c', s', .inl ⟨p + 1, by omega, by omega, by omega, hc', h'⟩⟩
    · obtain ⟨c', s', h'⟩ := spn_in_end sp s r f M o bs hI hsp hra p h1 (by omega) hin c h
      refine ⟨c', s', .inr ?_⟩
      rw [spanLen_of bs bs.length (fun j hj => hc' j (by omega)) (fun h => absurd h (Nat.lt_irrefl _))
        (Nat.le_refl _), show bs.length = p + 1 - s by omega]
      exact h'

/-- **`strspn(s, "-0123456789")`** on a string without zero bytes: the length
of its longest prefix in the set (`spanLen`), the memory unchanged. -/
theorem strspn_sum (sp s : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String) (bs : List (BitVec 8))
    (hI : SpnIn m s bs) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0) :
    Triple (SegSt 0x800368dc#64 (callPre [⟨Register.x10, BitVec.ofNat 64 s⟩, ⟨Register.x11, 0x8004f3e0#64⟩] sp r f)
        (ArmPay m o))
      (wrRet r sp (spanLen bs) f m o) := by
  intro c h
  have hs1 := hI.s_lo; have hs2 := hI.s_hi
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hX : Lua.Vm.AtF.Strspn.Ok (spCx [sp, s] r f 0#64 m o) := by fcx_ok
  have h : SegSt 0x800368dc#64 (Lua.Vm.AtF.Strspn.r0 (spCx [sp, s] r f 0#64 m o))
      (ArmPay (spCx [sp, s] r f 0#64 m o).m (spCx [sp, s] r f 0#64 m o).o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  have hc0 : bytesT1 m 0x8004f3e0 = 0x2d#8 := hI.setb 0 (by decide)
  have hg := zb_beq0 (bytesT1 m s)
  rcases Nat.eq_zero_or_pos bs.length with hl | hl
  · -- the empty string
    have hz : bytesT1 m s = 0#8 := by have := hI.term; rwa [hl, Nat.add_zero] at this
    rw [decide_eq_true hz] at hg
    fat_run Lua.Vm.AtF.Strspn h acc
    fcx_unfold at h
    refine ⟨_, acc, ?_⟩
    rw [show spanLen bs = 0 by have := spanLen_le bs; omega]
    exact h.repin (by pins_of h)
  · have hb := hI.byte (j := 0) hl
    rw [Nat.add_zero] at hb
    have hz : bytesT1 m s ≠ 0#8 := by rw [hb]; exact hI.nz 0 hl
    simp only [hz, decide_false] at hg
    fat_run Lua.Vm.AtF.Strspn h acc until [0x800368f0]
    fcx_unfold at h
    obtain ⟨c2, s2, hp⟩ := spn_loop sp s r f m o bs hI hsp hra s (Nat.le_refl _) (by omega)
      (fun j hj => absurd hj (by omega)) _ (by fcx_unfold; exact h.repin (by pins_of h))
    exact ⟨c2, acc.trans s2, hp⟩

end Lua.Vm.Sim.Kit

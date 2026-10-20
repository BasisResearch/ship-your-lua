import Lua.Num.Decimal

/-!
# The bytes of `%.14g` (lane F1-25)

Every byte `fmt14g` writes is a digit, a sign, the decimal point, `e`, or a
letter of `inf`/`nan` (`fmt14g_byte`): in particular none is zero, so
`tostringbuff`'s `strspn` scan stops at the terminator `snprintf` writes.
-/

namespace Lua.Num

/-- A byte `%.14g` writes. -/
def G14Byte (c : UInt8) : Prop :=
  c.toNat = 43 ∨ c.toNat = 45 ∨ c.toNat = 46 ∨ (48 ≤ c.toNat ∧ c.toNat ≤ 57) ∨ c.toNat = 97 ∨ c.toNat = 101 ∨
    c.toNat = 102 ∨ c.toNat = 105 ∨ c.toNat = 110

instance : DecidablePred G14Byte := fun c => by unfold G14Byte; infer_instance

theorem G14Byte.ne_zero {c : UInt8} (h : G14Byte c) : c.toNat ≠ 0 := by
  unfold G14Byte at h; omega

/-- A decimal digit's byte. -/
theorem natDigits_digit (n : Nat) : ∀ c ∈ natDigits n, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  intro c hc
  simp only [natDigits, List.mem_map] at hc
  obtain ⟨ch, hch, rfl⟩ := hc
  have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hch
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
  have h1 : 48 ≤ ch.toNat := by
    have := (show '0'.val ≤ ch.val from hd.1); rw [UInt32.le_iff_toNat_le] at this; exact this
  have h2 : ch.toNat ≤ 57 := by
    have := hd.2; rw [UInt32.le_iff_toNat_le] at this; exact this
  have e : (ch.toNat.toUInt8).toNat = ch.toNat := by
    rw [Nat.toUInt8, UInt8.toNat_ofNat']; omega
  rw [e]; exact ⟨h1, h2⟩

theorem natDigits_g14 (n : Nat) : ∀ c ∈ natDigits n, G14Byte c := fun c hc =>
  .inr (.inr (.inr (.inl (natDigits_digit n c hc))))

/-- The exponent's bytes. -/
theorem expBytes_g14 (x : Int) : ∀ c ∈ expBytes x, G14Byte c := by
  intro c hc
  simp only [expBytes, List.mem_cons] at hc
  rcases hc with rfl | rfl | hc
  · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
  · split <;> simp [G14Byte]
  · split at hc
    · simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · simp [G14Byte]
      · exact natDigits_g14 _ c hc
    · exact natDigits_g14 _ c hc

/-- The significant digits without trailing zeros. -/
theorem trim_g14 (d : List UInt8) (h : ∀ c ∈ d, G14Byte c) :
    ∀ c ∈ (d.reverse.dropWhile (· == 48)).reverse, G14Byte c := by
  intro c hc
  rw [List.mem_reverse] at hc
  exact h c (List.mem_reverse.mp ((List.dropWhile_sublist _).subset hc))

/-- `fmtFinite`'s layout of the significant digits `sig` with decimal exponent
`k` (vfprintf.c:1455-1510), as a function of its own. -/
def fmtBody (sig : List UInt8) (k : Int) : List UInt8 :=
  let ndig := sig.length
  let expt := k + 1
  if expt ≤ -4 || expt > 14 then
    match sig with
    | c :: rest => c :: ((if rest.isEmpty then [] else 46 :: rest) ++ expBytes k)
    | [] => []
  else if expt ≤ 0 then
    [48, 46] ++ List.replicate (-expt).toNat 48 ++ sig
  else if ndig ≤ expt.toNat then
    sig ++ List.replicate (expt.toNat - ndig) 48
  else sig.take expt.toNat ++ 46 :: sig.drop expt.toNat

/-- `fmtFinite` is its sign and `fmtBody`. -/
theorem fmtFinite_eq (neg : Bool) (m : Nat) (e : Int) :
    fmtFinite neg m e = (if neg then [45] else []) ++ fmtBody (if keepsZeros m e then natDigits (dec14 m e).1
      else ((natDigits (dec14 m e).1).reverse.dropWhile (· == 48)).reverse) (dec14 m e).2 := rfl

/-- The bytes of `%.14g`'s layout of digits. -/
theorem fmtBody_byte (sig : List UInt8) (hsig : ∀ c ∈ sig, G14Byte c) (k : Int) :
    ∀ c ∈ fmtBody sig k, G14Byte c := by
  intro c hc
  unfold fmtBody at hc
  simp only at hc
  by_cases h1 : (decide (k + 1 ≤ -4) || decide (k + 1 > 14)) = true
  · rw [if_pos h1] at hc
    cases sig with
    | nil => simp at hc
    | cons hd tl =>
      simp only [List.mem_cons, List.mem_append] at hc
      rcases hc with h | h | h
      · rw [h]; exact hsig _ (by simp)
      · by_cases he : tl.isEmpty = true
        · rw [if_pos he] at h; simp at h
        · rw [if_neg he] at h
          rcases List.mem_cons.mp h with h | h
          · rw [h]; decide
          · exact hsig _ (List.mem_cons_of_mem _ h)
      · exact expBytes_g14 _ c h
  · rw [if_neg h1] at hc
    by_cases h2 : k + 1 ≤ 0
    · rw [if_pos h2] at hc
      simp only [List.mem_append, List.cons_append, List.mem_cons, List.mem_replicate, List.nil_append] at hc
      rcases hc with h | h | h | h
      · rw [h]; decide
      · rw [h]; decide
      · rw [h.2]; decide
      · exact hsig _ h
    · rw [if_neg h2] at hc
      by_cases h3 : sig.length ≤ (k + 1).toNat
      · rw [if_pos h3] at hc
        rcases List.mem_append.mp hc with h | h
        · exact hsig _ h
        · rw [(List.mem_replicate.mp h).2]; decide
      · rw [if_neg h3] at hc
        rcases List.mem_append.mp hc with h | h
        · exact hsig _ (List.mem_of_mem_take h)
        · rcases List.mem_cons.mp h with h | h
          · rw [h]; decide
          · exact hsig _ (List.mem_of_mem_drop h)

/-- The bytes of `%.14g` of a finite non-zero value. -/
theorem fmtFinite_byte (neg : Bool) (m : Nat) (e : Int) : ∀ c ∈ fmtFinite neg m e, G14Byte c := by
  rw [fmtFinite_eq, List.forall_mem_append]
  refine ⟨by split <;> simp <;> decide, ?_⟩
  apply fmtBody_byte
  split
  · exact natDigits_g14 _
  · exact trim_g14 _ (natDigits_g14 _)

/-- **Every byte of `%.14g` is a digit, a sign, the point, `e`, or a letter
of `inf`/`nan`.** -/
theorem fmt14g_byte (nn : Bool) (x : Float.Model) : ∀ c ∈ fmt14g nn x, G14Byte c := by
  unfold fmt14g
  split
  · split <;> decide
  · rw [List.forall_mem_append]
    exact ⟨by split <;> decide, by decide⟩
  · rw [List.forall_mem_append]
    exact ⟨by split <;> decide, by decide⟩
  · exact fmtFinite_byte _ _ _

/-- No byte of `%.14g` is zero. -/
theorem fmt14g_ne_zero (nn : Bool) (x : Float.Model) : ∀ c ∈ fmt14g nn x, c.toNat ≠ 0 :=
  fun c hc => (fmt14g_byte nn x c hc).ne_zero

end Lua.Num

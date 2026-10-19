import Lua.Num.Decimal

/-!
# `str2int` by positions (lane F1-F8)

`Lua.Num.str2int` restated over positions of the string (`S2IOk`): the
leading spaces, the sign, `0x`, the digits and the trailing spaces, as
`l_str2int`'s pointer walks them (`Lua/Vm/Sim/Kit/Str2int.lean`).
-/

namespace Lua.Num

/-- `s`'s byte at `k`, `0` past its end (the C string's terminator). -/
def bAt (s : List UInt8) (k : Nat) : UInt8 := s.getD k 0

theorem getD_drop (s : List UInt8) (i k : Nat) : (s.drop i).getD k 0 = bAt s (i + k) := by
  unfold bAt
  simp [List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- The digit value of the `n` digits at `i`, accumulated from `a`
(`luaO_hexavalue` folded; the order `l_str2int` reads them). -/
def dacc (hex : Bool) (s : List UInt8) : Nat → Nat → Nat → Nat
  | _, a, 0 => a
  | i, a, n + 1 => dacc hex s (i + 1) (a * (if hex then 16 else 10) + (digitVal hex (bAt s i)).getD 0) n

/-- `dropWhile` is a `drop` of a prefix that satisfies `p`. -/
theorem dropWhile_idx (p : UInt8 → Bool) : ∀ (s : List UInt8), ∃ i, i ≤ s.length ∧
    s.dropWhile p = s.drop i ∧ (∀ k, k < i → p (bAt s k) = true) ∧ (i < s.length → p (bAt s i) = false)
  | [] => ⟨0, by simp, by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun h => absurd h (by simp)⟩
  | c :: cs => by
    by_cases hc : p c = true
    · obtain ⟨i, h1, h2, h3, h4⟩ := dropWhile_idx p cs
      refine ⟨i + 1, by simp; omega, by simp [hc, h2], fun k hk => ?_, fun hi => ?_⟩
      · cases k with
        | zero => simpa [bAt] using hc
        | succ k => simpa [bAt] using h3 k (by omega)
      · simpa [bAt] using h4 (by simp at hi; omega)
    · refine ⟨0, by simp, by simp [hc], fun _ h => absurd h (Nat.not_lt_zero _), fun _ => ?_⟩
      simpa [bAt] using hc

theorem bAt_of_lt {s : List UInt8} {i : Nat} (h : i < s.length) : bAt s i = s[i] := by
  rw [bAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- `digits` on a suffix: the run of digits at `i`, its value and length,
the rest after it. -/
theorem digits_idx (hex : Bool) (s : List UInt8) : ∀ (i a c : Nat), i ≤ s.length → ∃ n,
    digits hex (s.drop i) a c = (dacc hex s i a n, c + n, s.drop (i + n)) ∧
    i + n ≤ s.length ∧ (∀ k, k < n → (digitVal hex (bAt s (i + k))).isSome = true) ∧
    (i + n < s.length → (digitVal hex (bAt s (i + n))).isSome = false) := by
  intro i a c hi
  induction h : s.length - i generalizing i a c with
  | zero =>
    have e : s.drop i = [] := List.drop_eq_nil_of_le (by omega)
    exact ⟨0, by simp [e, digits, dacc], by omega, fun _ h => absurd h (Nat.not_lt_zero _),
      fun h' => absurd h' (by omega)⟩
  | succ r ih =>
    have hlt : i < s.length := by omega
    have e : s.drop i = s[i] :: s.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons hlt]
    have hb := bAt_of_lt hlt
    cases hd : digitVal hex s[i] with
    | none =>
      refine ⟨0, by rw [e]; simp only [digits, hd, dacc, Nat.add_zero, ← e], by omega, fun _ h => absurd h (Nat.not_lt_zero _), fun _ => ?_⟩
      rw [Nat.add_zero, hb, hd]; rfl
    | some d =>
      obtain ⟨n, h1, h2, h3, h4⟩ := ih (i + 1) (a * (if hex then 16 else 10) + d) (c + 1) (by omega) (by omega)
      refine ⟨n + 1, ?_, by omega, fun k hk => ?_, fun hn => ?_⟩
      · rw [e]; simp only [digits, hd]; rw [h1]
        simp only [dacc, hb, hd, Option.getD_some, Prod.mk.injEq, true_and]
        exact ⟨by omega, by rw [show i + 1 + n = i + (n + 1) by omega]⟩
      · cases k with
        | zero => rw [Nat.add_zero, hb, hd]; rfl
        | succ k => rw [show i + (k + 1) = i + 1 + k by omega]; exact h3 k (by omega)
      · rw [show i + (n + 1) = i + 1 + n by omega]; exact h4 (by omega)

theorem bAt_drop (s : List UInt8) (i k : Nat) : bAt (s.drop i) k = bAt s (i + k) := getD_drop s i k

theorem bAt_ge {s : List UInt8} {k : Nat} (h : s.length ≤ k) : bAt s k = 0 := by
  simp [bAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem takeSign_other {c : UInt8} (t : List UInt8) (h1 : c ≠ 45) (h2 : c ≠ 43) :
    takeSign (c :: t) = (false, c :: t) := by
  unfold takeSign; split
  · rename_i h; cases h; exact absurd rfl h1
  · rename_i h; cases h; exact absurd rfl h2
  · rfl

/-- `takeSign` on a suffix. -/
theorem takeSign_idx (s : List UInt8) (i : Nat) :
    takeSign (s.drop i) = ((bAt s i == 45),
      s.drop (i + (if bAt s i = 45 ∨ bAt s i = 43 then 1 else 0))) := by
  rcases Nat.lt_or_ge i s.length with h | h
  · rw [List.drop_eq_getElem_cons h, bAt_of_lt h]
    by_cases e1 : s[i] = 45
    · simp [takeSign, e1]
    · by_cases e2 : s[i] = 43
      · simp [takeSign, e2]
      · rw [takeSign_other _ e1 e2]; simp [e1, e2]
  · rw [List.drop_eq_nil_of_le (by omega), bAt_ge (by omega)]; simp [takeSign]; omega

/-- **`str2int` by positions**: the spaces, the sign, `0x`, the digits, the
trailing spaces (`l_str2int`'s walk). -/
structure S2I (s : List UInt8) (v : BitVec 64) where
  i0 : Nat
  i1 : Nat
  i2 : Nat
  n : Nat
  neg : Bool
  hex : Bool
  sp0 : ∀ k, k < i0 → isSpace (bAt s k) = true
  nsp0 : isSpace (bAt s i0) = false
  i1_eq : i1 = i0 + (if bAt s i0 = 45 ∨ bAt s i0 = 43 then 1 else 0)
  neg_eq : neg = (bAt s i0 == 45)
  hex_eq : hex = (bAt s i1 == 48 && (bAt s (i1 + 1) == 120 || bAt s (i1 + 1) == 88))
  i2_eq : i2 = i1 + (if hex then 2 else 0)
  n_pos : 0 < n
  dig : ∀ k, k < n → (digitVal hex (bAt s (i2 + k))).isSome = true
  ndig : (digitVal hex (bAt s (i2 + n))).isSome = false
  len : i2 + n ≤ s.length
  tsp : ∀ k, i2 + n ≤ k → k < s.length → isSpace (bAt s k) = true
  ovf : hex = false → dacc hex s i2 0 n ≤ 2 ^ 63 - 1 + (if neg then 1 else 0)
  val : v = if neg then 0 - BitVec.ofNat 64 (dacc hex s i2 0 n) else BitVec.ofNat 64 (dacc hex s i2 0 n)

/-- The `0x` test on a list. -/
theorem hex_list (l : List UInt8) :
    hexStrip l = ((l.getD 0 0 == 48 && (l.getD 1 0 == 120 || l.getD 1 0 == 88)),
      l.drop (if (l.getD 0 0 == 48 && (l.getD 1 0 == 120 || l.getD 1 0 == 88)) then 2 else 0)) := by
  match l with
  | [] => rfl
  | [a] => simp [hexStrip]
  | a :: b :: t =>
    by_cases e : a = 48
    · subst e
      by_cases ex : (b == 120 || b == 88) = true
      · simp [hexStrip, ex]
      · simp only [Bool.not_eq_true] at ex
        simp [hexStrip, ex]
    · have : (a == 48) = false := by simpa using e
      have h2 : hexStrip (a :: b :: t) = (false, a :: b :: t) := by
        unfold hexStrip; split
        · rename_i x t' heq; exact absurd (List.cons.inj heq).1 e
        · rfl
      simp [h2, this]

/-- The `0x` test on a suffix. -/
theorem hex_idx (s : List UInt8) (i : Nat) :
    hexStrip (s.drop i) =
    ((bAt s i == 48 && (bAt s (i + 1) == 120 || bAt s (i + 1) == 88)),
      s.drop (i + if (bAt s i == 48 && (bAt s (i + 1) == 120 || bAt s (i + 1) == 88)) then 2 else 0)) := by
  rw [hex_list]
  have e0 : (s.drop i).getD 0 0 = bAt s i := by rw [getD_drop, Nat.add_zero]
  have e1 : (s.drop i).getD 1 0 = bAt s (i + 1) := by rw [getD_drop]
  rw [e0, e1, List.drop_drop]

/-- Nothing but `p` after `j`. -/
theorem dropWhile_nil (p : UInt8 → Bool) (s : List UInt8) (j : Nat) (h : (s.drop j).dropWhile p = []) :
    ∀ k, j ≤ k → k < s.length → p (bAt s k) = true := by
  obtain ⟨i, hi, e, hp, _⟩ := dropWhile_idx p (s.drop j)
  rw [e] at h
  intro k hk hk'
  have hl : (s.drop j).length ≤ i := List.drop_eq_nil_iff.mp h
  simp only [List.length_drop] at hl
  have := hp (k - j) (by omega)
  rwa [bAt_drop, show j + (k - j) = k by omega] at this

/-- **`str2int` by positions.** -/
theorem str2int_S2I {s : List UInt8} {v : BitVec 64} (h : str2int s = some v) : Nonempty (S2I s v) := by
  obtain ⟨i0, hi0, e0, hs0, hn0⟩ := dropWhile_idx isSpace s
  unfold str2int at h
  simp only [e0, takeSign_idx] at h
  generalize hi1 : i0 + (if bAt s i0 = 45 ∨ bAt s i0 = 43 then 1 else 0) = i1 at h
  rw [hex_idx] at h
  generalize hhx : (bAt s i1 == 48 && (bAt s (i1 + 1) == 120 || bAt s (i1 + 1) == 88)) = hex at h
  generalize hi2 : i1 + (if hex = true then 2 else 0) = i2 at h
  rcases Nat.lt_or_ge s.length i2 with hlt | hge
  · -- past the end: no digit
    rw [List.drop_eq_nil_of_le (by omega)] at h
    simp [digits] at h
  obtain ⟨n, hd, hlen, hdig, hndig⟩ := digits_idx hex s i2 0 0 hge
  rw [hd] at h
  simp only [Nat.zero_add] at h
  by_cases hc : n = 0 ∨ List.dropWhile isSpace (List.drop (i2 + n) s) ≠ [] ∨
      (!hex) = true ∧ (2 ^ 63 - 1 + if (bAt s i0 == 45) = true then 1 else 0) < dacc hex s i2 0 n
  · rw [if_pos hc] at h; cases h
  rw [if_neg hc, Option.some.injEq] at h
  subst h
  simp only [not_or, ne_eq, Decidable.not_not, not_and, Nat.not_lt] at hc
  obtain ⟨hn, hrest, hov⟩ := hc
  exact ⟨{
    i0 := i0, i1 := i1, i2 := i2, n := n, neg := (bAt s i0 == 45), hex := hex
    sp0 := hs0
    nsp0 := by
      rcases Nat.lt_or_ge i0 s.length with h | h
      · exact hn0 h
      · rw [bAt_ge h]; rfl
    i1_eq := hi1.symm
    neg_eq := rfl
    hex_eq := hhx.symm
    i2_eq := hi2.symm
    n_pos := by omega
    dig := hdig
    ndig := by
      rcases Nat.lt_or_ge (i2 + n) s.length with h | h
      · exact hndig h
      · rw [bAt_ge h]; cases hex <;> rfl
    len := hlen
    tsp := dropWhile_nil isSpace s (i2 + n) hrest
    ovf := fun hh => hov (by simp [hh])
    val := rfl }⟩

/-- The accumulator one digit further. -/
theorem dacc_succ (hex : Bool) (s : List UInt8) : ∀ (k i a : Nat),
    dacc hex s i a (k + 1) = dacc hex s i a k * (if hex then 16 else 10) +
      (digitVal hex (bAt s (i + k))).getD 0
  | 0, i, a => by simp [dacc]
  | k + 1, i, a => by
    rw [dacc, dacc_succ hex s k (i + 1), dacc, show i + 1 + k = i + (k + 1) by omega]

/-- The rest of the digits from a prefix's value. -/
theorem dacc_split (hex : Bool) (s : List UInt8) : ∀ (k i a n : Nat), k ≤ n →
    dacc hex s i a n = dacc hex s (i + k) (dacc hex s i a k) (n - k)
  | 0, i, a, n, _ => by simp [dacc]
  | k + 1, i, a, n, h => by
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [dacc, dacc_split hex s k (i + 1) _ n' (by omega), dacc, show i + 1 + k = i + (k + 1) by omega,
      show n' + 1 - (k + 1) = n' - k by omega]

/-- The accumulator only grows. -/
theorem dacc_ge (hex : Bool) (s : List UInt8) : ∀ (n i a : Nat), a ≤ dacc hex s i a n
  | 0, _, _ => Nat.le_refl _
  | n + 1, i, a => by
    rw [dacc]
    refine Nat.le_trans ?_ (dacc_ge hex s n (i + 1) _)
    cases hex <;> simp <;> omega

end Lua.Num

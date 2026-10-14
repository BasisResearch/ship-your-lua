import Lua.Vm.Sim.Kit.CallSpec

/-!
# Decimal digits as `_svfprintf_r` writes them (lane F1-FMT)

`%lld`'s digit loop (`do { *--cp = n % 10 + '0'; if (n <= 9) break; n /= 10; }`)
emits the digits of `n` last to first; `decBytes n` is the bytes of
`Nat.toDigits 10 n`, and `decBytes_ge`/`decBytes_lt` are the loop's step
and exit. `intBytes_eq` reads `IntegerToStr_Statement`'s bytes (`toString`
of the signed value) as the sign and the digits of the magnitude the
machine negates into (`0 - i`, `__udivdi3` unsigned: `LUA_MININTEGER`'s
magnitude is `2 ^ 63`).
-/

namespace Lua.Vm.Sim.Kit

/-- The ASCII byte of the digit `d`. -/
def digB (d : Nat) : BitVec 8 := BitVec.ofNat 8 (d + 48)

/-- The decimal digits of `n`, as bytes. -/
def decBytes (n : Nat) : List (BitVec 8) :=
  (Nat.toDigits 10 n).map fun ch => BitVec.ofNat 8 ch.toNat

theorem decBytes_lt {n : Nat} (h : n < 10) : decBytes n = [digB n] := by
  simp only [decBytes, Nat.toDigits_of_lt_base h, List.map_cons, List.map_nil, digB,
    Nat.toNat_digitChar_of_lt_ten h, Nat.add_comm]

theorem decBytes_ge {n : Nat} (h : 10 ≤ n) : decBytes n = decBytes (n / 10) ++ [digB (n % 10)] := by
  simp only [decBytes, Nat.toDigits_of_base_le (by decide) h, List.map_append, List.map_cons, List.map_nil,
    digB, Nat.toNat_digitChar_of_lt_ten (Nat.mod_lt n (by decide)), Nat.add_comm]

theorem decBytes_ne_nil (n : Nat) : decBytes n ≠ [] := by
  simp only [decBytes, ne_eq, List.map_eq_nil_iff]
  exact List.ne_nil_of_length_pos Nat.length_toDigits_pos

/-- At most `k` digits below `10 ^ k`. -/
theorem decBytes_length_le : ∀ (k n : Nat), n < 10 ^ (k + 1) → (decBytes n).length ≤ k + 1
  | 0, n, h => by rw [decBytes_lt (by simpa using h)]; simp
  | k + 1, n, h => by
    by_cases h10 : n < 10
    · rw [decBytes_lt h10]; simp
    · rw [decBytes_ge (by omega)]
      have := decBytes_length_le k (n / 10) (by
        rw [Nat.div_lt_iff_lt_mul (by decide)]; rw [Nat.pow_succ] at h; exact h)
      simp; omega

theorem decBytes_length_64 {n : Nat} (h : n < 2 ^ 64) : (decBytes n).length ≤ 20 :=
  decBytes_length_le 19 n (Nat.lt_of_lt_of_le h (by decide))

/-- The magnitude `%lld` prints: `i`, or `0 - i` for a negative `i`. -/
def magOf (i : BitVec 64) : Nat := if i.toInt < 0 then (0#64 - i).toNat else i.toNat

theorem intBytes_eq (i : BitVec 64) :
    intBytes i = (if i.toInt < 0 then [45#8] else []) ++ decBytes (magOf i) := by
  have hi := i.isLt
  have hc := BitVec.toInt_eq_toNat_cond i
  simp only [intBytes, magOf, toString, Int.repr_eq_ite]
  by_cases hn : i.toInt < 0
  · have e : (- i.toInt).toNat = (0#64 - i).toNat := by
      rw [BitVec.toNat_sub]
      simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero]
      split at hc <;> rw [hc] at hn ⊢ <;> omega
    simp only [show ¬ (0 ≤ i.toInt) by omega, hn, ↓reduceIte, Nat.repr, e]
    simp [decBytes]
  · simp only [show 0 ≤ i.toInt by omega, hn, ↓reduceIte, Nat.repr, List.nil_append]
    have e : i.toInt.toNat = i.toNat := by
      split at hc <;> rw [hc] at hn ⊢ <;> omega
    simp [decBytes, e]

end Lua.Vm.Sim.Kit

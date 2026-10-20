import Lua.Vm.Sim.Kit.AtNarrow

/-!
# An address rounded to its word (lane F1-24)

With `xres` (`gen_lua_at.py`), the callee-context generator rounds an address
over the atoms with a known residue down to its word (`andi …, -8`:
`memcpy`'s end of the word copies) as the address less its residue, and
decides the test on the words left to copy. The at-lemmas' obligations: the
value equation, one `at_eq_ext` rule (`and_sxm8_bv`, guarded by the mask's
presence, `at_has_and8`; the `toNat`s expanded by `rw`, never `simp`: `simp`'s
proof of `toNat_ofNat` on `sp - k + (2 ^ 64 - 1)` sends the kernel past its
recursion limit), and the decided signed test, one `fat_gnd` rule
(`and_sxm8`, `ofNat_sub_ofNat`, `slt_ofNat`); an address plus a 32-bit literal
count (`fmt_sext32_ofNat`). No `FmtLib` hooks: a callee
outside the format routines imports this alone (its `at_eq` hooks unify
`zero_extend (bytesT1 …)` against an `ofNat` of a stack offset at default
transparency, which unfolds `Nat.sub` of a large literal past the recursion
limit).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

theorem nat_and_m8 (n : Nat) (h : n < 2 ^ 64) : n &&& (2 ^ 64 - 8) = n - n % 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, show n - n % 8 = 2 ^ 3 * (n / 2 ^ 3) by omega, Nat.testBit_two_pow_mul,
    Nat.testBit_div_two_pow]
  by_cases hi : 3 ≤ i
  · by_cases h64 : i < 64
    · have : (2 ^ 64 - 8).testBit i = true := by
        rw [show 2 ^ 64 - 8 = 2 ^ 3 * (2 ^ 61 - 1) by decide, Nat.testBit_two_pow_mul,
          Nat.testBit_two_pow_sub_one]
        simp; omega
      rw [this, show i - 3 + 3 = i by omega]; simp [hi]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega)))
      rw [this, show i - 3 + 3 = i by omega, this]; simp
  · have : (2 ^ 64 - 8).testBit i = false := by
      rw [show 2 ^ 64 - 8 = 2 ^ 3 * (2 ^ 61 - 1) by decide, Nat.testBit_two_pow_mul]
      simp; omega
    rw [this]; simp; omega

/-- **An address rounded down to its word**: the address less its residue. -/
theorem and_sxm8 (n : Nat) (h : n < 2 ^ 64) :
    BitVec.ofNat 64 n &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (n - n % 8) := by
  rw [show sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (2 ^ 64 - 8) by decide]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h,
    Nat.mod_eq_of_lt (show 2 ^ 64 - 8 < 2 ^ 64 by decide), Nat.mod_eq_of_lt (show n - n % 8 < 2 ^ 64 by omega)]
  exact nat_and_m8 n h

/-- Any word rounded down: the `ofNat` of its `Nat` less the residue. -/
theorem and_sxm8_bv (x : BitVec 64) :
    x &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (x.toNat - x.toNat % 8) := by
  have h := and_sxm8 x.toNat x.isLt
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
  exact h

/-- The difference of two `ofNat`s, in order. -/
theorem ofNat_sub_ofNat {a b : Nat} (h : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

/-- A signed test of two small `ofNat`s: their order. -/
theorem slt_ofNat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  have ea : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have eb : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  simp only [zopz0zI_s, ea, eb]
  by_cases h : a < b <;> simp [h] <;> omega

open Lean Elab Tactic Meta in
/-- Fails unless the goal holds a word mask `x &&& sign_extend 0xff8#12`. -/
elab "at_has_and8" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some _ := t.find? fun e => e.isAppOfArity ``HAnd.hAnd 6 &&
      (e.appArg!.find? fun x => x.isAppOfArity ``BitVec.ofNat 2 && x.appArg!.nat? == some 0xff8).isSome
    | throwError "at_has_and8: none"

/-- A word-rounded address in a machine value (an `at_eq` goal): its `Nat`. -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (
      at_has_and8
      simp only [and_sxm8_bv]
      apply BitVec.eq_of_toNat_eq
      repeat (first | rw [BitVec.toNat_sub] | rw [BitVec.toNat_add] | rw [BitVec.toNat_ofNat])
      omega))

/-- A decided signed test of a word-rounded address less another (`memcpy`'s
`blt` on the words to copy). -/
macro_rules
  | `(tactic| fat_gnd) => `(tactic| (
      at_has_and8
      rw [and_sxm8 _ (by omega), ofNat_sub_ofNat (by omega) (by omega)]
      simp (disch := omega) only [add_imm]
      rw [slt_ofNat (by omega) (by omega)]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq]
      omega))

/-- An address over the atoms plus a 32-bit literal count (`blen` reloaded by
`lw`, a literal on a path whose format pieces are literals): its `Nat`. -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (
      at_has_ofNat32
      simp (disch := omega) only [fmt_sext32_ofNat, BitVec.ofNat_add_ofNat]
      apply BitVec.eq_of_toNat_eq
      simp (disch := omega) only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
      omega))

/-- Two `ofNat`s of equal `Nat`s. -/
theorem ofNat64_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := by subst h; rfl

open Lean Elab Tactic Meta in
/-- Fails unless the goal is an equation of two `BitVec.ofNat 64`s. -/
elab "at_ofNat_eq" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, r) := t.eq? | throwError "at_ofNat_eq: not an equation"
  unless l.isAppOfArity ``BitVec.ofNat 2 && r.isAppOfArity ``BitVec.ofNat 2 do
    throwError "at_ofNat_eq: not two ofNat"

/-- **Two stack offsets** (`ofNat (sp - k + 1) = ofNat (sp - (k - 1))`: a byte
cursor stepped): their `Nat`s by `omega`, never by unification (`rfl`, even
reducible, unfolds `Nat.sub` of the large literal `k` past the recursion
limit). -/
macro_rules
  | `(tactic| at_eq_ext) => `(tactic| (at_ofNat_eq; apply ofNat64_congr; omega))

end Lua.Vm.Sim.Kit

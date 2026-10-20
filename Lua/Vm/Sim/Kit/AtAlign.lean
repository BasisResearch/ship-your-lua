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
(`andm8`, `ofNat_sub_ofNat`, `slt_ofNat`); an address plus a 32-bit literal
count (`fmt_sext32_ofNat`). No `FmtLib` hooks: a callee
outside the format routines imports this alone (its `at_eq` hooks unify
`zero_extend (bytesT1 …)` against an `ofNat` of a stack offset at default
transparency, which unfolds `Nat.sub` of a large literal past the recursion
limit).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

/-- `andi rd, rs, -8` on a Nat-valued register: the value rounded down to 8. -/
theorem andm8 (x : Nat) (hx : x < 2 ^ 64) :
    BitVec.ofNat 64 x &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (8 * (x / 8)) := by
  rw [show sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 18446744073709551608 by decide]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and]
  rw [show 8 * (x / 8) = 2 ^ 3 * (x / 2 ^ 3) by rfl, Nat.testBit_two_pow_mul, Nat.testBit_div_two_pow]
  by_cases h3 : 3 ≤ i
  · have e : (18446744073709551608 : Nat) = 2 ^ 3 * (2 ^ 61 - 1) := by decide
    rw [e, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_sub_one]
    simp only [h3, decide_true, Bool.true_and, show i - 3 + 3 = i by omega]
    have : i - 3 < 61 := by omega
    simp [this]
  · have e : (18446744073709551608 : Nat) = 2 ^ 3 * (2 ^ 61 - 1) := by decide
    rw [e, Nat.testBit_two_pow_mul]
    simp [h3]

/-- Two 8-aligned addresses: their `xor`'s low three bits are zero. -/
theorem xor_al (s d : Nat) (hs : s % 8 = 0) (hd : d % 8 = 0) :
    (((BitVec.ofNat 64 s) ^^^ (BitVec.ofNat 64 d)) &&& sign_extend (m := 64) (0x007#12) != (0#64)) = false := by
  rw [show sign_extend (m := 64) (0x007#12) = BitVec.ofNat 64 7 by decide]
  simp only [bne_eq_false_iff_eq]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ofNat, hi, decide_true, Bool.true_and,
    BitVec.getLsbD_zero]
  by_cases h3 : i < 3
  · have e1 : s = 2 ^ 3 * (s / 8) := by omega
    have e2 : d = 2 ^ 3 * (d / 8) := by omega
    rw [e1, e2, Nat.testBit_two_pow_mul, Nat.testBit_two_pow_mul]
    simp [show ¬ (3 ≤ i) by omega]
  · have : (7 : Nat).testBit i = false := Nat.testBit_lt_two_pow (by
      calc 7 < 2 ^ 3 := by decide
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) (by omega))
    simp [this]

/-- Two addresses of different residues mod 8: their `xor`'s low three bits
are not all zero (`memcpy`'s byte path). -/
theorem xor_mis (s d : Nat) (hs : s < 2 ^ 64) (hd : d < 2 ^ 64) (h : s % 8 ≠ d % 8) :
    (((BitVec.ofNat 64 s) ^^^ (BitVec.ofNat 64 d)) &&& sign_extend (m := 64) (0x007#12) != (0#64)) = true := by
  rw [show sign_extend (m := 64) (0x007#12) = BitVec.ofNat 64 7 by decide]
  simp only [bne_iff_ne, ne_eq]
  intro he
  have e := congrArg BitVec.toNat he
  simp only [BitVec.toNat_and, BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd,
    Nat.zero_mod] at e
  rw [Nat.mod_eq_of_lt (show (7 : Nat) < 2 ^ 64 by decide),
    show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.xor_mod_two_pow] at e
  have h1 : s % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
  have h2 : d % 2 ^ 3 < 8 := Nat.mod_lt _ (by decide)
  have key : ∀ a, a < 8 → ∀ b, b < 8 → a ≠ b → (a ^^^ b) ≠ 0 := by decide
  exact key _ h1 _ h2 h e

/-- Any word rounded down: the `ofNat` of its `Nat` less the residue. -/
theorem and_sxm8_bv (x : BitVec 64) :
    x &&& sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 (8 * (x.toNat / 8)) := by
  have h := andm8 x.toNat x.isLt
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
      rw [andm8 _ (by omega), ofNat_sub_ofNat (by omega) (by omega)]
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

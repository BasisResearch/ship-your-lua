import Lua.Vm.Fn.SqrtLoop1

/-!
# `__ieee754_sqrt`'s subnormal normalisation (lane float-sf6, (b1))

`e_sqrt.c:112-121`: whole 21-bit words while `ix0 == 0` (the cycle at
`0x8002d590`, at most twice), then the bit shifts of `ix0` to bit 20 (the
cycle at `0x8002d5b8`, `SfRef.sqClz`), and the two-word shift by `i`
(`0x8002d5cc`, `sllw`/`srlw` by a register); each on to the set-up
(`core_478`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Sqrt

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim Lua.Num.SfRef

set_option linter.unusedVariables false

section norm
variable {m : Mem} (s : Nat) (r : BitVec 64) (g : SFrame)

/-- The low word shifted by a register: its residue. -/
theorem shl_mod (L : Int) (l P : Nat) (hl : L % 4294967296 = (l : Int)) :
    (L * (P : Int)).bmod 4294967296 % 4294967296 = ((l * P % 2 ^ 32 : Nat) : Int) ∧
    -2147483648 ≤ (L * (P : Int)).bmod 4294967296 ∧ (L * (P : Int)).bmod 4294967296 < 2147483648 := by
  have ⟨b1, b2, b3⟩ := bm_facts (L * (P : Int))
  refine ⟨?_, b2, b3⟩
  have e : ((l * P % 2 ^ 32 : Nat) : Int) = ((l : Int) * (P : Int)) % 4294967296 := by
    rw [Int.natCast_emod, Int.natCast_mul]; rfl
  rw [b1, e, Int.mul_emod, hl, Int.mul_emod (l : Int), Int.emod_emod_of_dvd _ (Int.dvd_refl _), ← Int.mul_emod]

/-- The high word's new bits by a register shift: `l >> (32 - i)`. -/
theorem srl_val (L : Int) (l i : Nat) (hl : L % 4294967296 = (l : Int)) (hl2 : l < 2 ^ 32) (hi : i ≤ 20) :
    L % 4294967296 / 2 ^ (32 - i) = ((l / 2 ^ (32 - i) : Nat) : Int) ∧ l / 2 ^ (32 - i) < 2 ^ i := by
  refine ⟨by rw [hl]; push_cast; rfl, ?_⟩
  refine Nat.div_lt_of_lt_mul ?_
  rw [← Nat.pow_add, show 32 - i + i = 32 by omega]; exact hl2

/-- The two-word shift (`0x8002d5cc`, `e_sqrt.c:118-120`): `ix0 |= ix1 >> (32-i)`,
`ix1 <<= i`, `m -= i - 1`. -/
theorem st_5cc (i h l : Nat) (L M : Int) (hi1 : 1 ≤ i) (hi2 : i ≤ 20) (hl : L % 4294967296 = (l : Int))
    (hl2 : l < 2 ^ 32) (hh : h * 2 ^ i < 2 ^ 21) (hM1 : -2 ^ 30 ≤ M) (hM2 : M < 2 ^ 30) :
    N_8002d5cc m s r g (BitVec.ofInt 64 ((i : Int) - 1)) (BitVec.ofInt 64 (i : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 ((h * 2 ^ i : Nat) : Int)) (BitVec.ofInt 64 M) =
      N_8002d478 m s r g (BitVec.ofInt 64 ((L * ((2 ^ i : Nat) : Int)).bmod 4294967296))
        (BitVec.ofInt 64 ((h * 2 ^ i + l / 2 ^ (32 - i) : Nat) : Int)) (BitVec.ofInt 64 (M - (i - 1 : Int))) ∧
    T_8002d5cc m s r g (BitVec.ofInt 64 ((i : Int) - 1)) (BitVec.ofInt 64 (i : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 ((h * 2 ^ i : Nat) : Int)) (BitVec.ofInt 64 M) =
      T_8002d478 m s r g (BitVec.ofInt 64 ((L * ((2 ^ i : Nat) : Int)).bmod 4294967296))
        (BitVec.ofInt 64 ((h * 2 ^ i + l / 2 ^ (32 - i) : Nat) : Int)) (BitVec.ofInt 64 (M - (i - 1 : Int))) := by
  have e1 : ((i : Int) % 32).toNat = i := by omega
  have e2 : ((32 - (i : Int)) % 32).toNat = 32 - i := by omega
  have ⟨sv, sb⟩ := srl_val L l i hl hl2 hi2
  have sb' : l / 2 ^ (32 - i) < 2147483648 :=
    Nat.lt_of_lt_of_le sb (Nat.le_trans (Nat.pow_le_pow_right (by decide) hi2) (by decide))
  have hsm : ((l / 2 ^ (32 - i) : Nat) : Int).bmod 4294967296 = ((l / 2 ^ (32 - i) : Nat) : Int) :=
    bmod_small' _ (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr sb')
  have hdv : ((h * 2 ^ i : Nat) : Int) % 2 ^ i = 0 := by
    rw [Int.natCast_mul, Int.natCast_pow]
    exact Int.mul_emod_left _ _
  have hor : BitVec.ofInt 64 ((h * 2 ^ i : Nat) : Int) ||| BitVec.ofInt 64 ((l / 2 ^ (32 - i) : Nat) : Int) =
      BitVec.ofInt 64 ((h * 2 ^ i + l / 2 ^ (32 - i) : Nat) : Int) := by
    rw [or_low _ _ i (by omega) hdv (Int.natCast_nonneg _)
      (by have := Int.ofNat_lt.mpr sb; rwa [Int.natCast_pow] at this), ← Int.natCast_add]
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d5cc] | rw [T_8002d5cc]) <;> fm_nf <;>
    rw [e1, e2, sv, hsm, hor] <;> sq_close

/-- `and` with bit 20 (`0x00100000`). -/
theorem and_b20 (a : Int) (ha : 0 ≤ a) (ha2 : a < 2 ^ 63) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 1048576 = BitVec.ofInt 64 (a / 1048576 % 2 * 1048576) :=
  and_field a 1048576 20 1 ha ha2 (by decide) (by decide)

/-- A bit shift of `ix0` (`0x8002d5b8`, `e_sqrt.c:117`): on while bit 20 is clear. -/
theorem st_5b8 (k : Nat) (j L hd M : Int) (hd0 : 0 ≤ hd) (hd1 : hd < 2 ^ 20) (hj0 : 0 ≤ j) (hj1 : j ≤ 20) :
    N_8002d5b8 (k + 1) m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 j) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 hd) (BitVec.ofInt 64 M) =
      (if 2 * hd < 2 ^ 20 then
        N_8002d5b8 k m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 (j + 1)) (BitVec.ofInt 64 L)
          (BitVec.ofInt 64 (2 * hd)) (BitVec.ofInt 64 M)
      else
        N_8002d5cc m s r g (BitVec.ofInt 64 j) (BitVec.ofInt 64 (j + 1)) (BitVec.ofInt 64 L)
          (BitVec.ofInt 64 (2 * hd)) (BitVec.ofInt 64 M)) ∧
    T_8002d5b8 (k + 1) m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 j) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 hd) (BitVec.ofInt 64 M) =
      (if 2 * hd < 2 ^ 20 then
        T_8002d5b8 k m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 (j + 1)) (BitVec.ofInt 64 L)
          (BitVec.ofInt 64 (2 * hd)) (BitVec.ofInt 64 M)
      else
        T_8002d5cc m s r g (BitVec.ofInt 64 j) (BitVec.ofInt 64 (j + 1)) (BitVec.ofInt 64 L)
          (BitVec.ofInt 64 (2 * hd)) (BitVec.ofInt 64 M)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d5b8] | rw [T_8002d5b8]) <;> fm_nf <;>
    simp (disch := fm_disch) only [and_b20] <;> fm_nf <;>
    (by_cases hc : 2 * hd < 2 ^ 20) <;> fm_nf <;> sq_close

/-- **The bit shifts** (the cycle at `0x8002d5b8`): `SfRef.sqClz n hd` of them,
then the two-word shift. -/
theorem l5b8 : ∀ (n hd j fuel : Nat) (L M : Int), 0 < hd → hd < 2 ^ 20 → 2 ^ 20 ≤ hd * 2 ^ n →
    n + 1 ≤ fuel → j + n ≤ 20 →
    N_8002d5b8 fuel m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 (j : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 (hd : Int)) (BitVec.ofInt 64 M) =
      N_8002d5cc m s r g (BitVec.ofInt 64 (((j + sqClz n hd : Nat) : Int) - 1))
        (BitVec.ofInt 64 ((j + sqClz n hd : Nat) : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 ((hd * 2 ^ sqClz n hd : Nat) : Int)) (BitVec.ofInt 64 M) ∧
    T_8002d5b8 fuel m s r g (BitVec.ofInt 64 1048576) (BitVec.ofInt 64 (j : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 (hd : Int)) (BitVec.ofInt 64 M) =
      T_8002d5cc m s r g (BitVec.ofInt 64 (((j + sqClz n hd : Nat) : Int) - 1))
        (BitVec.ofInt 64 ((j + sqClz n hd : Nat) : Int)) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 ((hd * 2 ^ sqClz n hd : Nat) : Int)) (BitVec.ofInt 64 M) := by
  intro n
  induction n with
  | zero => intro hd j fuel L M h0 h1 h2; simp at h2; omega
  | succ n ih =>
    intro hd j fuel L M h0 h1 h2 hf hj
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
    have e := st_5b8 (m := m) s r g k (j : Int) L (hd : Int) M (by omega) (by omega) (by omega) (by omega)
    rw [e.1, e.2]
    unfold sqClz
    by_cases hc : 2 * hd < 2 ^ 20
    · rw [if_pos (by omega : 2 * (hd : Int) < 2 ^ 20), if_pos (by omega : 2 * (hd : Int) < 2 ^ 20), if_pos hc]
      have h2' : 2 ^ 20 ≤ 2 * hd * 2 ^ n := by
        rw [Nat.pow_succ] at h2; rw [Nat.mul_comm 2 hd, Nat.mul_assoc, Nat.mul_comm 2]; exact h2
      have e' := ih (2 * hd) (j + 1) k L M (by omega) hc h2' (by omega) (by omega)
      rw [show (j : Int) + 1 = ((j + 1 : Nat) : Int) by omega, show 2 * (hd : Int) = ((2 * hd : Nat) : Int) by omega,
        e'.1, e'.2]
      have ea : j + 1 + sqClz n (2 * hd) = j + (sqClz n (2 * hd) + 1) := by omega
      have eb : 2 * hd * 2 ^ sqClz n (2 * hd) = hd * 2 ^ (sqClz n (2 * hd) + 1) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [ea, eb]; exact ⟨rfl, rfl⟩
    · rw [if_neg (by omega : ¬ 2 * (hd : Int) < 2 ^ 20), if_neg (by omega : ¬ 2 * (hd : Int) < 2 ^ 20), if_neg hc]
      refine ⟨?_, ?_⟩ <;> congr 2 <;> (try simp only [Nat.pow_one]) <;> omega

variable (hro : RodataRead m) (hs : FnSp s 160)

include hro hs in
/-- **A subnormal `ix0 != 0` without bit 20** (`0x8002d5b0`): the bit shifts, the
two-word shift, the set-up (`SfRef.sqNorm`'s second case). -/
theorem sub_5b0 (h l : Nat) (L M : Int) (h0 : 0 < h) (h1 : h < 2 ^ 20) (hl : L % 4294967296 = (l : Int))
    (hl2 : l < 2 ^ 32) (hM1 : -2 ^ 29 ≤ M) (hM2 : M < 2 ^ 29) (hres : -51 ≤ (sqNorm h l M).2.2)
    (hres2 : (sqNorm h l M).2.2 ≤ 2046) :
    N_8002d5b0 m s r g (BitVec.ofInt 64 L) (BitVec.ofInt 64 (h : Int)) (BitVec.ofInt 64 M) =
      sqCore (sqNorm h l M).1 (sqNorm h l M).2.1 (sqNorm h l M).2.2 ∧
    T_8002d5b0 m s r g (BitVec.ofInt 64 L) (BitVec.ofInt 64 (h : Int)) (BitVec.ofInt 64 M) = true := by
  have hn : ¬ 2 ^ 20 ≤ h := by omega
  have ⟨i1, i2, i3, i4⟩ := sqClz_spec 20 h h0 h1 (by
    calc 2 ^ 20 = 1 * 2 ^ 20 := by rw [Nat.one_mul]
      _ ≤ h * 2 ^ 20 := Nat.mul_le_mul_right _ h0)
  have lp := l5b8 (m := m) s r g 20 h 0 fnFuel L M h0 h1 (by
    calc 2 ^ 20 = 1 * 2 ^ 20 := by rw [Nat.one_mul]
      _ ≤ h * 2 ^ 20 := Nat.mul_le_mul_right _ h0) (by decide) (by omega)
  simp only [Nat.zero_add] at lp
  generalize hi : sqClz 20 h = i at i1 i2 i3 i4 lp
  have c5 := st_5cc (m := m) s r g i h l L M i1 i2 hl hl2 i4 (by omega) (by omega)
  have ⟨sm1, sm2, sm3⟩ := shl_mod L l (2 ^ i) hl
  have ⟨_, sb⟩ := srl_val L l i hl hl2 i2
  have hh := add_below h (l / 2 ^ (32 - i)) i (by omega) i4 sb
  have hsn : sqNorm h l M = (h * 2 ^ i + l / 2 ^ (32 - i), l * 2 ^ i % 2 ^ 32, M - ((i - 1 : Nat) : Int)) := by
    unfold sqNorm; rw [if_neg hn, hi]
  rw [hsn] at hres hres2 ⊢
  have hM : M - ((i : Int) - 1) = M - ((i - 1 : Nat) : Int) := by omega
  have core := core_478 s r g hro hs (h * 2 ^ i + l / 2 ^ (32 - i)) (l * 2 ^ i % 2 ^ 32)
    ((L * ((2 ^ i : Nat) : Int)).bmod 4294967296) (M - ((i - 1 : Nat) : Int)) (by omega) sm1
    (Nat.mod_lt _ (by decide)) hres hres2
  rw [← hM] at core
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d5b0] | rw [T_8002d5b0]) <;> fm_nf
  · rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, lp.1, c5.1, core.1, hM]
  · rw [show (0 : Int) = ((0 : Nat) : Int) from rfl, lp.2, c5.2, core.2]

end norm

end Lua.Vm.Fn.Ieee754Sqrt

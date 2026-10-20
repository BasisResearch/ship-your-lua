import Lua.Vm.Fn.SqrtLoop2

/-!
# `__ieee754_sqrt`'s first root loop and its set-up (lane float-sf6, (b1))

`L1Claim c`: from count `c`, the 22-bit loop at `0x8002d4c8` computes
`SfRef.sqRun c 32` (the bits `2^(c+31) … 2^32` of the root, `q`), then the
second loop (`l2_claim`) and the pack. The set-up `0x8002d478`
(`e_sqrt.c:122-132`) feeds it the radicand `Y`; `core_478` is the routine
from there: `SfRef.sqCore`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Sqrt

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim Lua.Num.SfRef

set_option linter.unusedVariables false

/-- The registers of the first loop (`0x8002d4c8`) at count `c`: `s0 = 2Q/2^32`
(`s1 = 0`), `ix0:ix1 = W`, `q = Q/2^32`, `r = 2^(c-1)`. -/
structure L1Inv (N c W Q : Nat) (s0 L H q K : Int) : Prop where
  inv : SqInv N (32 + c) W Q
  nlo : 2 ^ 106 ≤ N
  nhi : N < 2 ^ 108
  s0e : s0 = 2 * (Q : Int) / 4294967296
  Lm : L % 4294967296 = (W : Int) % 4294967296
  Ll : -2147483648 ≤ L
  Lh : L < 2147483648
  He : H = (W : Int) / 4294967296
  qe : q = (Q : Int) / 4294967296
  Kl : -600 ≤ K
  Kh : K ≤ 600

section claim1
variable {m : Mem} (s : Nat) (r : BitVec 64) (g : SFrame) (hro : RodataRead m) (hs : FnSp s 160)

/-- The first loop from count `c` computes `sqRun c 32`, then the second loop. -/
def L1Claim (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (c : Nat) : Prop :=
  ∀ (fuel N W Q : Nat) (s0 L H q K : Int), 3 * c ≤ fuel → L1Inv N c W Q s0 L H q K →
    N_8002d4c8 fuel m s r g (BitVec.ofInt 64 (c : Int)) (BitVec.ofInt 64 ((2 ^ (c - 1) : Nat) : Int))
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      sqOut K (sqRun 32 0 (sqRun c 32 (W, Q))).1 (sqRun 32 0 (sqRun c 32 (W, Q))).2 ∧
    T_8002d4c8 fuel m s r g (BitVec.ofInt 64 (c : Int)) (BitVec.ofInt 64 ((2 ^ (c - 1) : Nat) : Int))
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) = true

/-- The hand-over to the second loop (`0x8002d4f8`): `s1 = 0`, `r = 0x80000000`,
count `32`, `q1 = 0`. -/
theorem st_4f8 (m : Mem) (s0 L H K q : Int) :
    N_8002d4f8 m s r g (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 q) =
      N_8002d544 fnFuel m s r g (BitVec.ofInt 64 0) (BitVec.ofInt 64 (-2147483648)) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 ((31 + 1 : Nat) : Int)) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) ∧
    T_8002d4f8 m s r g (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 q) =
      T_8002d544 fnFuel m s r g (BitVec.ofInt 64 0) (BitVec.ofInt 64 (-2147483648)) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 ((31 + 1 : Nat) : Int)) (BitVec.ofInt 64 0)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d4f8] | rw [T_8002d4f8]) <;> fm_nf

/-- `Q`, a multiple of `2^32`, has empty low words. -/
theorem lo_zero (Q c : Nat) (h : 2 ^ (32 + c) ∣ Q) : (Q : Int) % 4294967296 = 0 ∧ 2 * (Q : Int) % 4294967296 = 0 := by
  have h32 : 4294967296 ∣ Q := Nat.dvd_trans ⟨2 ^ c, by rw [Nat.pow_add]⟩ h
  omega

include hro hs in
/-- **The exit of the first loop**: the second loop from `W`, `Q`. -/
theorem l1_exit (N W Q : Nat) (s0 L H q K : Int) (inv : SqInv N 32 W Q) (nlo : 2 ^ 106 ≤ N)
    (nhi : N < 2 ^ 108) (s0e : s0 = 2 * (Q : Int) / 4294967296) (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (Ll : -2147483648 ≤ L) (Lh : L < 2147483648) (He : H = (W : Int) / 4294967296)
    (qe : q = (Q : Int) / 4294967296) (Kl : -600 ≤ K) (Kh : K ≤ 600) :
    N_8002d4f8 m s r g (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 q) = sqOut K (sqRun 32 0 (W, Q)).1 (sqRun 32 0 (W, Q)).2 ∧
    T_8002d4f8 m s r g (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 q) = true := by
  have ⟨z1, z2⟩ := lo_zero Q 0 inv.dvd
  rw [(st_4f8 s r g m s0 L H K q).1, (st_4f8 s r g m s0 L H K q).2]
  exact l2_claim s r g hro hs 31 (by decide) fnFuel N W Q 0 (-2147483648) s0 L H 0 q K (by decide)
    ⟨inv, nlo, nhi, by omega, by decide, by decide, by decide, by decide, by decide, s0e, Lm, Ll, Lh, He,
      by omega, by decide, by decide, qe, Kl, Kh⟩

/-! ### One iteration's word facts (small contexts) -/

section facts1
variable (W Q P : Nat) (s0 L H q : Int)

theorem l1_take (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (z2 : 2 * (Q : Int) % 4294967296 = 0) :
    (2 * Q + P * 4294967296 ≤ W) ↔ ¬ H < s0 + (P : Int) := by
  omega

theorem l1_bnds (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (qe : q = (Q : Int) / 4294967296) (hQ : Q < 2 ^ 54) (hW : W < 2 ^ 57) (hP : P ≤ 2 ^ 21) :
    0 ≤ s0 ∧ s0 + (P : Int) < 2 ^ 31 ∧ 0 ≤ H ∧ H < 2 ^ 31 ∧ 2 * H + 1 < 2 ^ 31 ∧ 0 ≤ q ∧
      q + (P : Int) < 2 ^ 31 := by
  omega

theorem l1_L (Lm : L % 4294967296 = (W : Int) % 4294967296) (W' : Nat)
    (hW' : (W' : Int) % 4294967296 = 2 * (W : Int) % 4294967296) :
    (L * 2).bmod 4294967296 % 4294967296 = (W' : Int) % 4294967296 ∧
    -2147483648 ≤ (L * 2).bmod 4294967296 ∧ (L * 2).bmod 4294967296 < 2147483648 := by
  have := bm_facts (L * 2)
  omega

theorem l1_b (Lm : L % 4294967296 = (W : Int) % 4294967296) :
    0 ≤ L % 4294967296 / 2147483648 ∧ L % 4294967296 / 2147483648 ≤ 1 := by
  omega

theorem l1_nt (He : H = (W : Int) / 4294967296) (Lm : L % 4294967296 = (W : Int) % 4294967296) :
    L % 4294967296 / 2147483648 + H * 2 = ((2 * W : Nat) : Int) / 4294967296 ∧
    ((2 * W : Nat) : Int) % 4294967296 = 2 * (W : Int) % 4294967296 := by
  omega

theorem l1_tk (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296) (z2 : 2 * (Q : Int) % 4294967296 = 0)
    (ht : 2 * Q + P * 4294967296 ≤ W) (qe : q = (Q : Int) / 4294967296) (z1 : (Q : Int) % 4294967296 = 0) :
    L % 4294967296 / 2147483648 + (H - (s0 + P)) * 2 =
        ((2 * (W - (2 * Q + P * 4294967296)) : Nat) : Int) / 4294967296 ∧
    ((2 * (W - (2 * Q + P * 4294967296)) : Nat) : Int) % 4294967296 = 2 * (W : Int) % 4294967296 ∧
    s0 + P + P = 2 * ((Q + P * 4294967296 : Nat) : Int) / 4294967296 ∧
    q + P = ((Q + P * 4294967296 : Nat) : Int) / 4294967296 := by
  omega

theorem l1_rr (n : Nat) (hn : 1 ≤ n) : ((2 ^ n : Nat) : Int) / 2 = ((2 ^ (n - 1) : Nat) : Int) := by
  have : 2 ^ n = 2 * 2 ^ (n - 1) := pow_pred n hn
  omega

end facts1

include hro hs in
/-- **One iteration of the first loop** (`e_sqrt.c:135-144`). -/
theorem l1_step (n : Nat) (hn : n ≤ 21) (ih : 1 ≤ n → L1Claim m s r g n) : L1Claim m s r g (n + 1) := by
  intro fuel N W Q s0 L H q K hf hI
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 + 1 + 1 := ⟨fuel - 3, by omega⟩
  have hk : 3 * n ≤ k := by omega
  clear hf
  obtain ⟨inv, nlo, nhi, s0e, Lm, Ll, Lh, He, qe, Kl, Kh⟩ := hI
  have ⟨hQ, hW⟩ := sqInv_bounds inv nhi (by omega)
  have ⟨z1, z2⟩ := lo_zero Q (n + 1) inv.dvd
  have hP : 2 ^ n ≤ 2 ^ 21 := Nat.pow_le_pow_right (by decide) hn
  have hρ : 2 ^ (32 + n) = 2 ^ n * 4294967296 := by rw [Nat.pow_add, Nat.mul_comm]
  have ⟨b0, b1, b2, b3, b4, b5, b6⟩ := l1_bnds W Q (2 ^ n) s0 H q s0e He qe hQ hW hP
  have ⟨bb0, bb1⟩ := l1_b W L Lm
  have hrun : sqRun (n + 1) 32 (W, Q) = sqRun n 32 (sqBit (2 ^ (32 + n)) (W, Q)) := rfl
  rw [hrun]
  have inv' := sqBit_inv (p := 32 + n) inv
  rw [hρ] at inv' ⊢
  have htk := l1_take W Q (2 ^ n) s0 H s0e He z2
  simp only [Nat.add_sub_cancel]
  have e4c8 := st_4c8 m s r g (k + 1 + 1) ((n + 1 : Nat) : Int) ((2 ^ n : Nat) : Int) s0 L H K q
    (by omega) (by omega) (by omega) b0 b1 b2 b3 Ll Lh
  rw [e4c8.1, e4c8.2]
  clear e4c8
  have hc1 := c_pred n
  by_cases h1 : H < s0 + ((2 ^ n : Nat) : Int)
  · -- no bit
    rw [if_pos h1, if_pos h1]
    have hnt : ¬ (2 * Q + 2 ^ n * 4294967296 ≤ W) := fun h => htk.1 h h1
    have hb : sqBit (2 ^ n * 4294967296) (W, Q) = (2 * W, Q) := by unfold sqBit; simp only [hnt, if_false]
    rw [hb] at inv' ⊢
    rw [hc1]
    have e4e4 := st_4e4 m s r g (k + 1) (n : Int) ((2 ^ n : Nat) : Int) s0 L H (L % 4294967296 / 2147483648) K q
      (by omega) (by omega) (by omega) (by omega) b2 (by omega) bb0 bb1 Ll Lh
    rw [e4e4.1, e4e4.2]
    clear e4e4
    have ⟨nt1, nt2⟩ := l1_nt W L H He Lm
    have ⟨L1, L2, L3⟩ := l1_L W L Lm (2 * W) nt2
    by_cases hn0 : n = 0
    · subst hn0
      rw [if_pos (show ((0 : Nat) : Int) = 0 from rfl), if_pos (show ((0 : Nat) : Int) = 0 from rfl)]
      exact l1_exit s r g hro hs N (2 * W) Q s0 _ _ q K inv' nlo nhi s0e L1 L2 L3 nt1 qe Kl Kh
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [l1_rr n (Nat.pos_of_ne_zero hn0)]
      have h := ih (Nat.pos_of_ne_zero hn0) (k + 1) N (2 * W) Q s0 _ _ q K (Nat.le_succ_of_le hk)
        ⟨inv', nlo, nhi, s0e, L1, L2, L3, nt1, qe, Kl, Kh⟩
      exact h
  · -- a bit
    rw [if_neg h1, if_neg h1]
    have ht : 2 * Q + 2 ^ n * 4294967296 ≤ W := htk.2 h1
    have hb : sqBit (2 ^ n * 4294967296) (W, Q) = (2 * (W - (2 * Q + 2 ^ n * 4294967296)), Q + 2 ^ n * 4294967296) := by
      unfold sqBit; simp only [ht, if_true]
    rw [hb] at inv' ⊢
    have ⟨tk1, tk2, tk3, tk4⟩ := l1_tk W Q (2 ^ n) s0 L H q s0e He Lm z2 ht qe z1
    have e4d8 := st_4d8 m s r g (k + 1) (((n + 1 : Nat) : Int) - 1) ((2 ^ n : Nat) : Int) (s0 + ((2 ^ n : Nat) : Int)) L H
      (L % 4294967296 / 2147483648) K q (by omega) (by omega) (by omega) (by omega) b3 b5 (by omega)
    rw [e4d8.1, e4d8.2]
    clear e4d8
    rw [hc1]
    have e4e4 := st_4e4 m s r g k (n : Int) ((2 ^ n : Nat) : Int) (s0 + ((2 ^ n : Nat) : Int) + ((2 ^ n : Nat) : Int)) L
      (H - (s0 + ((2 ^ n : Nat) : Int))) (L % 4294967296 / 2147483648) K (q + ((2 ^ n : Nat) : Int))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) bb0 bb1 Ll Lh
    rw [e4e4.1, e4e4.2]
    clear e4e4
    have ⟨L1, L2, L3⟩ := l1_L W L Lm _ tk2
    by_cases hn0 : n = 0
    · subst hn0
      rw [if_pos (show ((0 : Nat) : Int) = 0 from rfl), if_pos (show ((0 : Nat) : Int) = 0 from rfl)]
      exact l1_exit s r g hro hs N _ _ _ _ _ _ K inv' nlo nhi tk3 L1 L2 L3 tk1 tk4 Kl Kh
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [l1_rr n (Nat.pos_of_ne_zero hn0)]
      exact ih (Nat.pos_of_ne_zero hn0) k N _ _ _ _ _ _ K hk
        ⟨inv', nlo, nhi, tk3, L1, L2, L3, tk1, tk4, Kl, Kh⟩

include hro hs in
/-- **The first loop** at every count `n + 1 ≤ 22`. -/
theorem l1_claim : ∀ n, n ≤ 21 → L1Claim m s r g (n + 1) := by
  intro n
  induction n with
  | zero => intro hn; exact l1_step s r g hro hs 0 hn (fun h => absurd h (by decide))
  | succ n ih => intro hn; exact l1_step s r g hro hs (n + 1) hn (fun _ => ih (by omega))

/-- `and` with `1`: the low bit, of any sign. -/
theorem and_one (a : Int) : BitVec.ofInt 64 a &&& BitVec.ofInt 64 1 = BitVec.ofInt 64 (a % 2) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (BitVec.ofInt 64 1).toNat = 1 by decide, Nat.and_one_is_mod]
  have h1 := ofInt_toNat a
  have h2 := ofInt_toNat (a % 2)
  omega

/-- The set-up's words, odd `m - 1023` (`ix0:ix1` doubled twice): `Y = 4W`. -/
theorem pre_odd (h l W : Nat) (L0 : Int) (hW : W = (h % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 + l)
    (hl : L0 % 4294967296 = (l : Int)) (hl2 : l < 2 ^ 32) :
    2 ^ 53 ≤ 4 * W ∧ 4 * W < 2 ^ 55 ∧
    ((L0 * 2).bmod 4294967296 * 2).bmod 4294967296 % 4294967296 = ((4 * W : Nat) : Int) % 4294967296 ∧
    -2147483648 ≤ ((L0 * 2).bmod 4294967296 * 2).bmod 4294967296 ∧
    ((L0 * 2).bmod 4294967296 * 2).bmod 4294967296 < 2147483648 ∧
    ((1048576 + (h : Int) % 1048576) * 2 + L0 % 4294967296 / 2147483648) * 2 +
        (L0 * 2).bmod 4294967296 % 4294967296 / 2147483648 = ((4 * W : Nat) : Int) / 4294967296 := by
  have := bm_facts (L0 * 2)
  have := bm_facts ((L0 * 2).bmod 4294967296 * 2)
  subst hW
  omega

/-- The set-up's words, even `m - 1023`: `Y = 2W`. -/
theorem pre_even (h l W : Nat) (L0 : Int) (hW : W = (h % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 + l)
    (hl : L0 % 4294967296 = (l : Int)) (hl2 : l < 2 ^ 32) :
    2 ^ 53 ≤ 2 * W ∧ 2 * W < 2 ^ 55 ∧
    (L0 * 2).bmod 4294967296 % 4294967296 = ((2 * W : Nat) : Int) % 4294967296 ∧
    -2147483648 ≤ (L0 * 2).bmod 4294967296 ∧ (L0 * 2).bmod 4294967296 < 2147483648 ∧
    (1048576 + (h : Int) % 1048576) * 2 + L0 % 4294967296 / 2147483648 = ((2 * W : Nat) : Int) / 4294967296 := by
  have := bm_facts (L0 * 2)
  subst hW
  omega

theorem kbnd (M : Int) (hM1 : -51 ≤ M) (hM2 : M ≤ 2046) : -600 ≤ (M + -1023) / 2 ∧ (M + -1023) / 2 ≤ 600 := by
  omega

include hro hs in
/-- **The routine from the set-up** (`0x8002d478`, `e_sqrt.c:122-191`): `SfRef.sqCore`. -/
theorem core_478 (h l : Nat) (L0 M : Int) (hh : h < 2 ^ 31) (hl : L0 % 4294967296 = (l : Int))
    (hl2 : l < 2 ^ 32) (hM1 : -51 ≤ M) (hM2 : M ≤ 2046) :
    N_8002d478 m s r g (BitVec.ofInt 64 L0) (BitVec.ofInt 64 (h : Int)) (BitVec.ofInt 64 M) = sqCore h l M ∧
    T_8002d478 m s r g (BitVec.ofInt 64 L0) (BitVec.ofInt 64 (h : Int)) (BitVec.ofInt 64 M) = true := by
  have hiff : ((M + -1023) % 2 % 18446744073709551616 = 0) ↔ ((M + -1023) % 2 = 0) := by omega
  have ⟨k1, k2⟩ := kbnd M hM1 hM2
  have hc : ((21 + 1 : Nat) : Int) = 22 := rfl
  have hr : ((2 ^ (21 + 1 - 1) : Nat) : Int) = 2097152 := by decide
  have l1 := l1_claim s r g hro hs 21 (by decide) fnFuel
  rw [hc, hr] at l1
  have nlo : ∀ Y : Nat, 2 ^ 53 ≤ Y → 2 ^ 106 ≤ Y * 2 ^ 53 := fun Y hY => by
    calc 2 ^ 106 = 2 ^ 53 * 2 ^ 53 := by rw [← Nat.pow_add]
      _ ≤ Y * 2 ^ 53 := Nat.mul_le_mul_right _ hY
  have nhi : ∀ Y : Nat, Y < 2 ^ 55 → Y * 2 ^ 53 < 2 ^ 108 := fun Y hY => by
    calc Y * 2 ^ 53 < 2 ^ 55 * 2 ^ 53 := Nat.mul_lt_mul_of_pos_right hY (Nat.two_pow_pos _)
      _ = 2 ^ 108 := by rw [← Nat.pow_add]
  have z : (0 : Int) = 2 * ((0 : Nat) : Int) / 4294967296 ∧ (0 : Int) = ((0 : Nat) : Int) / 4294967296 := by decide
  unfold sqCore
  dsimp only
  generalize hW : (h % 2 ^ 20 + 2 ^ 20) * 2 ^ 32 + l = W
  by_cases ho : (M + -1023) % 2 = 0
  · have ⟨p1, p2, p3, p4, p5, p6⟩ := pre_even h l W L0 hW.symm hl hl2
    have e := l1 _ _ _ _ _ _ _ _ (by decide)
      ⟨sqInv_init (2 * W) p2, nlo _ p1, nhi _ p2, z.1, p3, p4, p5, p6, z.2, k1, k2⟩
    rw [if_neg (by omega : ¬ (M - 1023) % 2 = 1), show M - 1023 = M + -1023 by omega]
    refine ⟨?_, ?_⟩
    · rw [N_8002d478]; fm_nf; simp only [and_one]; fm_nf; try simp only [hiff]
      rw [N_8002d4a4]; fm_nf
      exact e.1
    · rw [T_8002d478]; fm_nf; simp only [and_one]; fm_nf; try simp only [hiff]
      rw [T_8002d4a4]; fm_nf
      exact e.2
  · have ⟨p1, p2, p3, p4, p5, p6⟩ := pre_odd h l W L0 hW.symm hl hl2
    have e := l1 _ _ _ _ _ _ _ _ (by decide)
      ⟨sqInv_init (4 * W) p2, nlo _ p1, nhi _ p2, z.1, p3, p4, p5, p6, z.2, k1, k2⟩
    rw [if_pos (by omega : (M - 1023) % 2 = 1), show M - 1023 = M + -1023 by omega]
    refine ⟨?_, ?_⟩
    · rw [N_8002d478]; fm_nf; simp only [and_one]; fm_nf; try simp only [hiff]
      rw [N_8002d494, N_8002d4a4]; fm_nf
      exact e.1
    · rw [T_8002d478]; fm_nf; simp only [and_one]; fm_nf; try simp only [hiff]
      rw [T_8002d494, T_8002d4a4]; fm_nf
      exact e.2

end claim1

end Lua.Vm.Fn.Ieee754Sqrt

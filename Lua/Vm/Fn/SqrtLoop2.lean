import Lua.Vm.Fn.SqrtLoop

/-!
# `__ieee754_sqrt`'s second root loop as an induction (lane float-sf6, (b1))

`L2Claim c`: from count `c`, the 32-bit loop at `0x8002d544` computes
`SfRef.sqRun c 0` on the remainder and root its registers hold (`L2Inv`), then
the pack (`tail_608`). One iteration ends at `0x8002d5e8` (no bit: `via_5e8`)
or `0x8002d520` (a bit: `via_520`), each on to the claim at `c - 1`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Sqrt

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-! ## Loop 2: 32 bits of `q1` -/

open Lua.Num.SfRef

/-- The registers of the second loop (`0x8002d544`) at count `c` against the
remainder `W` and root `Q` (`N = Y · 2^53` the radicand): `s0:s1 = 2Q`,
`ix0:ix1 = W`, `q:q1 = Q`, `r = 2^(c-1)`, the words sign-extended. -/
structure L2Inv (N c W Q : Nat) (s1 rr s0 L H q1 q K : Int) : Prop where
  inv : SqInv N c W Q
  nlo : 2 ^ 106 ≤ N
  nhi : N < 2 ^ 108
  s1m : s1 % 4294967296 = 2 * (Q : Int) % 4294967296
  s1l : -2147483648 ≤ s1
  s1h : s1 < 2147483648
  rrm : rr % 4294967296 = ((2 ^ (c - 1) : Nat) : Int)
  rrl : -2147483648 ≤ rr
  rrh : rr < 2147483648
  s0e : s0 = 2 * (Q : Int) / 4294967296
  Lm : L % 4294967296 = (W : Int) % 4294967296
  Ll : -2147483648 ≤ L
  Lh : L < 2147483648
  He : H = (W : Int) / 4294967296
  q1m : q1 % 4294967296 = (Q : Int) % 4294967296
  q1l : -2147483648 ≤ q1
  q1h : q1 < 2147483648
  qe : q = (Q : Int) / 4294967296
  Kl : -600 ≤ K
  Kh : K ≤ 600

section claim2
variable {m : Mem} (s : Nat) (r : BitVec 64) (g : SFrame) (hro : RodataRead m) (hs : FnSp s 160)

/-- The second loop from count `c` computes `sqRun c 0` and then the pack. -/
def L2Claim (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame) (c : Nat) : Prop :=
  ∀ (fuel N W Q : Nat) (s1 rr s0 L H q1 q K : Int), 8 * c ≤ fuel → L2Inv N c W Q s1 rr s0 L H q1 q K →
    N_8002d544 fuel m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (c : Int)) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      sqOut K (sqRun c 0 (W, Q)).1 (sqRun c 0 (W, Q)).2 ∧
    T_8002d544 fuel m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (c : Int)) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) = true

/-! ## One iteration's word facts, each in a small context -/

section facts
variable (W Q P : Nat) (s1 rr s0 L H t1 q : Int)

theorem l2_t1 (s1m : s1 % 4294967296 = 2 * (Q : Int) % 4294967296) (rrm : rr % 4294967296 = (P : Int))
    (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32) :
    (rr + s1).bmod 4294967296 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int) ∧
    -2 ^ 31 ≤ (rr + s1).bmod 4294967296 ∧ (rr + s1).bmod 4294967296 < 2 ^ 31 := by
  have := bm_facts (rr + s1)
  omega

theorem l2_t1m (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int))
    (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32) :
    t1 % 4294967296 = (2 * (Q : Int) + (P : Int)) % 4294967296 := by
  omega

theorem l2_take (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32) :
    (2 * Q + P ≤ W) ↔ (s0 < H ∨ (H = s0 ∧ t1 % 4294967296 ≤ L % 4294967296)) := by
  omega

theorem l2_s1 (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int))
    (rrm : rr % 4294967296 = (P : Int)) :
    (t1 + rr).bmod 4294967296 % 4294967296 = 2 * ((Q + P : Nat) : Int) % 4294967296 ∧
    -2 ^ 31 ≤ (t1 + rr).bmod 4294967296 ∧ (t1 + rr).bmod 4294967296 < 2 ^ 31 := by
  have := bm_facts (t1 + rr)
  omega

theorem l2_carry54 (s0e : s0 = 2 * (Q : Int) / 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (rrm : rr % 4294967296 = (P : Int))
    (hP1 : 1 ≤ P) (hP2 : P ≤ 2 ^ 31)
    (al2 : 2 * Q % 2 ^ 32 + 4 * P ≤ 2 ^ 32 ∨ (2 * Q % 2 ^ 32 = 0 ∧ P = 2 ^ 31)) :
    (s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0) =
      2 * ((Q + P : Nat) : Int) / 4294967296 := by
  split <;> omega

theorem l2_carry514 (s0e : s0 = 2 * (Q : Int) / 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (rrm : rr % 4294967296 = (P : Int))
    (ht1 : -2 ^ 31 ≤ t1) (ht2 : t1 < 2 ^ 31) (hP1 : 1 ≤ P) (hP2 : P ≤ 2 ^ 31)
    (al2 : 2 * Q % 2 ^ 32 + 4 * P ≤ 2 ^ 32 ∨ (2 * Q % 2 ^ 32 = 0 ∧ P = 2 ^ 31)) :
    (t1 < 0 → (t1 + rr).bmod 4294967296 < 0 → s0 = 2 * ((Q + P : Nat) : Int) / 4294967296) ∧
    (t1 < 0 → ¬ (t1 + rr).bmod 4294967296 < 0 → s0 + 1 = 2 * ((Q + P : Nat) : Int) / 4294967296) ∧
    (¬ t1 < 0 → s0 = 2 * ((Q + P : Nat) : Int) / 4294967296) := by
  have := bm_facts (t1 + rr)
  refine ⟨fun _ _ => ?_, fun _ _ => ?_, fun _ => ?_⟩ <;> omega

theorem l2_x54a (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32)
    (hb : t1 % 4294967296 ≤ L % 4294967296) :
    2 * (H - s0) = 2 * (((W : Int) - (2 * Q + (P : Int))) / 4294967296) := by
  omega

theorem l2_x54b (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32)
    (hb : ¬ t1 % 4294967296 ≤ L % 4294967296) :
    2 * (H - s0) - 2 = 2 * (((W : Int) - (2 * Q + (P : Int))) / 4294967296) := by
  omega

theorem l2_x514 (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = 2 * (Q : Int) % 4294967296 + (P : Int)) (hD : 2 * Q % 2 ^ 32 + P < 2 ^ 32)
    (he : H = s0) (hb : ¬ L % 4294967296 < t1 % 4294967296) :
    (0 : Int) = 2 * (((W : Int) - (2 * Q + (P : Int))) / 4294967296) := by
  omega

theorem l2_qe (qe : q = (Q : Int) / 4294967296) (al1 : Q % 2 ^ 32 + 2 * P ≤ 2 ^ 32) :
    q = ((Q + P : Nat) : Int) / 4294967296 := by
  omega

theorem l2_bnds (s0e : s0 = 2 * (Q : Int) / 4294967296) (He : H = (W : Int) / 4294967296) (hQ : Q < 2 ^ 54)
    (hW : W < 2 ^ 57) : 0 ≤ s0 ∧ s0 < 2 ^ 23 ∧ 0 ≤ H ∧ H < 2 ^ 25 := by
  omega

theorem l2_hD (hP1 : 1 ≤ P) (hP2 : P ≤ 2 ^ 31)
    (al2 : 2 * Q % 2 ^ 32 + 4 * P ≤ 2 ^ 32 ∨ (2 * Q % 2 ^ 32 = 0 ∧ P = 2 ^ 31)) :
    2 * Q % 2 ^ 32 + P < 2 ^ 32 := by
  omega

end facts

include hro hs in
/-- **No bit** (`0x8002d5e8`): on to `2W`, `Q` at count `n`. -/
theorem via_5e8 (n : Nat) (hn : n ≤ 31) (ih : 1 ≤ n → L2Claim m s r g n) (k N W Q : Nat)
    (s1 rr s0 L H q1 q K : Int) (hk : 8 * n ≤ k) (inv : SqInv N n (2 * W) Q) (nlo : 2 ^ 106 ≤ N)
    (nhi : N < 2 ^ 108) (hW : W < 2 ^ 57)
    (s1m : s1 % 4294967296 = 2 * (Q : Int) % 4294967296) (s1l : -2147483648 ≤ s1) (s1h : s1 < 2147483648)
    (rrm : rr % 4294967296 = ((2 ^ n : Nat) : Int)) (rrl : -2147483648 ≤ rr) (rrh : rr < 2147483648)
    (s0e : s0 = 2 * (Q : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296) (Ll : -2147483648 ≤ L) (Lh : L < 2147483648)
    (He : H = (W : Int) / 4294967296)
    (q1m : q1 % 4294967296 = (Q : Int) % 4294967296) (q1l : -2147483648 ≤ q1) (q1h : q1 < 2147483648)
    (qe : q = (Q : Int) / 4294967296) (Kl : -600 ≤ K) (Kh : K ≤ 600) :
    N_8002d5e8 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 ((n + 1 : Nat) : Int)) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      sqOut K (sqRun n 0 (2 * W, Q)).1 (sqRun n 0 (2 * W, Q)).2 ∧
    T_8002d5e8 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0)
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 ((n + 1 : Nat) : Int)) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) = true := by
  have ⟨hQ, hW'⟩ := sqInv_bounds inv nhi (by omega)
  have hst := st_5e8 m s r g k s1 rr s0 L H ((n + 1 : Nat) : Int) q1 K q (by omega) (by omega) (by omega)
    (by omega) Ll Lh
  rw [hst.1, hst.2]
  clear hst
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos (by omega), if_pos (by omega)]
    refine ⟨?_, rfl⟩
    have hQ1 : 2 ^ 53 ≤ Q := by
      have := inv.lt
      simp only [Nat.pow_zero] at this
      refine Nat.le_of_not_lt fun hc => ?_
      have : (Q + 1) * (Q + 1) ≤ 2 ^ 53 * 2 ^ 53 := Nat.mul_le_mul (by omega) (by omega)
      rw [← Nat.pow_add] at this; omega
    exact tail_608 s r g hro hs (2 * W) Q _ _ q1 q K (by bm_omega) (by bm_omega) (by bm_omega)
      (by bm_omega) hW' q1m q1l q1h qe hQ1 hQ Kl Kh
  · rw [if_neg (by omega), if_neg (by omega)]
    have hPh : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← Nat.pow_succ']; congr 1; omega
    have h := ih (by omega) k N (2 * W) Q s1 (rr % 4294967296 / 2) s0 ((L * 2).bmod 4294967296)
      (L % 4294967296 / 2147483648 + H * 2) q1 q K hk
      ⟨inv, nlo, nhi, s1m, s1l, s1h, by omega, by omega, by omega, s0e, by bm_omega, by bm_omega, by bm_omega,
        by omega, q1m, q1l, q1h, qe, Kl, Kh⟩
    rw [show (((n + 1 : Nat) : Int) - 1) = ((n : Nat) : Int) by omega]
    exact h

/-! The word arithmetic of a bit, each in a small context (`omega` takes every
arithmetic hypothesis in scope). -/

theorem bit_ix1 (L t1 : Int) (W Q P : Nat) (ht : 2 * Q + P ≤ W) (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = (2 * (Q : Int) + (P : Int)) % 4294967296) :
    ((L - t1) * 2).bmod 4294967296 % 4294967296 = ((2 * (W - (2 * Q + P)) : Nat) : Int) % 4294967296 := by
  have := bm_facts ((L - t1) * 2)
  omega

theorem bit_ix0 (L t1 X : Int) (W Q P : Nat) (ht : 2 * Q + P ≤ W) (Lm : L % 4294967296 = (W : Int) % 4294967296)
    (t1m : t1 % 4294967296 = (2 * (Q : Int) + (P : Int)) % 4294967296)
    (hX : X = 2 * (((W : Int) - (2 * Q + (P : Int))) / 4294967296)) :
    (L - t1) % 4294967296 / 2147483648 + X = ((2 * (W - (2 * Q + P)) : Nat) : Int) / 4294967296 := by
  omega

theorem bit_q1 (rr q1 : Int) (Q P : Nat) (rrm : rr % 4294967296 = (P : Int))
    (q1m : q1 % 4294967296 = (Q : Int) % 4294967296) :
    (rr + q1).bmod 4294967296 % 4294967296 = ((Q + P : Nat) : Int) % 4294967296 := by
  have := bm_facts (rr + q1)
  omega

theorem x_bnd (W Q P : Nat) (X : Int) (ht : 2 * Q + P ≤ W) (hW : W < 2 ^ 57)
    (hX : X = 2 * (((W : Int) - (2 * Q + (P : Int))) / 4294967296)) : 0 ≤ X ∧ X < 2 ^ 30 := by
  omega

theorem c_bnd (n : Nat) (hn : n ≤ 31) : 1 ≤ ((n + 1 : Nat) : Int) ∧ ((n + 1 : Nat) : Int) ≤ 32 := by omega

theorem c_ne1 (n : Nat) (hn : n ≠ 0) : ¬ ((n + 1 : Nat) : Int) = 1 := by omega

theorem pow_pred (n : Nat) (h : 1 ≤ n) : 2 ^ n = 2 * 2 ^ (n - 1) := by
  rw [← Nat.pow_succ']; congr 1; omega

theorem c_pred (n : Nat) : ((n + 1 : Nat) : Int) - 1 = ((n : Nat) : Int) := by omega

/-- The last bit's root is at least `2^53` (`N ≥ 2^106`). -/
theorem q_lo (N Q : Nat) (h : N < (Q + 1) * (Q + 1)) (nlo : 2 ^ 106 ≤ N) : 2 ^ 53 ≤ Q := by
  refine Nat.le_of_not_lt fun hc => ?_
  have : (Q + 1) * (Q + 1) ≤ 2 ^ 53 * 2 ^ 53 := Nat.mul_le_mul (by omega) (by omega)
  rw [← Nat.pow_add] at this; omega

/-- The bit halved (`srliw a2, a2, 1`). -/
theorem rr_next (rr : Int) (n : Nat) (hn1 : 1 ≤ n) (rrm : rr % 4294967296 = ((2 ^ n : Nat) : Int))
    (hP2 : 2 ^ n ≤ 2 ^ 31) (hPh : 2 ^ n = 2 * 2 ^ (n - 1)) :
    (rr % 4294967296 / 2) % 4294967296 = ((2 ^ (n - 1) : Nat) : Int) ∧
      -2147483648 ≤ rr % 4294967296 / 2 ∧ rr % 4294967296 / 2 < 2147483648 := by
  omega

include hro hs in
/-- **A bit** (`0x8002d520`): `ix0:ix1 -= s0:t1` (with the borrow in `X`, the
doubled high difference), doubled; on to `2 (W - (2Q + P))`, `Q + P`. -/
theorem via_520 (n : Nat) (hn : n ≤ 31) (ih : 1 ≤ n → L2Claim m s r g n) (k N W Q : Nat)
    (s1 t1 rr s0 L X q1 q K : Int) (hk : 8 * n ≤ k) (ht : 2 * Q + 2 ^ n ≤ W)
    (inv : SqInv N n (2 * (W - (2 * Q + 2 ^ n))) (Q + 2 ^ n)) (nlo : 2 ^ 106 ≤ N)
    (nhi : N < 2 ^ 108) (hW : W < 2 ^ 57)
    (s1m : s1 % 4294967296 = 2 * ((Q + 2 ^ n : Nat) : Int) % 4294967296) (s1l : -2147483648 ≤ s1)
    (s1h : s1 < 2147483648)
    (t1m : t1 % 4294967296 = (2 * (Q : Int) + ((2 ^ n : Nat) : Int)) % 4294967296)
    (rrm : rr % 4294967296 = ((2 ^ n : Nat) : Int)) (rrl : -2147483648 ≤ rr) (rrh : rr < 2147483648)
    (s0e : s0 = 2 * ((Q + 2 ^ n : Nat) : Int) / 4294967296)
    (Lm : L % 4294967296 = (W : Int) % 4294967296) (Ll : -2147483648 ≤ L) (Lh : L < 2147483648)
    (hX : X = 2 * (((W : Int) - (2 * Q + ((2 ^ n : Nat) : Int))) / 4294967296))
    (q1m : q1 % 4294967296 = (Q : Int) % 4294967296) (q1l : -2147483648 ≤ q1) (q1h : q1 < 2147483648)
    (qe : q = ((Q + 2 ^ n : Nat) : Int) / 4294967296) (Kl : -600 ≤ K) (Kh : K ≤ 600) :
    N_8002d520 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 ((n + 1 : Nat) : Int))
        (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      sqOut K (sqRun n 0 (2 * (W - (2 * Q + 2 ^ n)), Q + 2 ^ n)).1
        (sqRun n 0 (2 * (W - (2 * Q + 2 ^ n)), Q + 2 ^ n)).2 ∧
    T_8002d520 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 ((n + 1 : Nat) : Int))
        (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) = true := by
  have ⟨hQ, hW'⟩ := sqInv_bounds inv nhi (Nat.le_trans hn (by decide))
  have hP2 : 2 ^ n ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hn
  have ⟨hX0, hX1⟩ := x_bnd W Q _ X ht hW hX
  have ⟨hc0, hc1⟩ := c_bnd n hn
  have hst := st_520 m s r g k s1 t1 rr s0 L X ((n + 1 : Nat) : Int) q1 K q hc0 hc1 hX0 hX1
  rw [hst.1, hst.2]
  clear hst
  have b1 := bm_facts ((L - t1) * 2)
  have b2 := bm_facts (rr + q1)
  by_cases hn0 : n = 0
  · subst hn0
    rw [if_pos (show ((0 + 1 : Nat) : Int) = 1 from rfl), if_pos (show ((0 + 1 : Nat) : Int) = 1 from rfl)]
    refine ⟨?_, rfl⟩
    have hQ1 := q_lo N (Q + 2 ^ 0) (by simpa using inv.lt) nlo
    exact tail_608 s r g hro hs (2 * (W - (2 * Q + 2 ^ 0))) (Q + 2 ^ 0) _ _ _ q K (bit_ix0 L t1 X W Q _ ht Lm t1m hX)
      (bit_ix1 L t1 W Q _ ht Lm t1m) b1.2.1 b1.2.2 hW' (bit_q1 rr q1 Q _ rrm q1m) b2.2.1 b2.2.2 qe hQ1 hQ Kl Kh
  · rw [if_neg (c_ne1 n hn0), if_neg (c_ne1 n hn0)]
    have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
    have hPh := pow_pred n hn1
    have ⟨r1, r2, r3⟩ := rr_next rr n hn1 rrm hP2 hPh
    have h := ih hn1 k N _ _ s1 (rr % 4294967296 / 2) s0 (((L - t1) * 2).bmod 4294967296)
      ((L - t1) % 4294967296 / 2147483648 + X) ((rr + q1).bmod 4294967296) q K hk
      ⟨inv, nlo, nhi, s1m, s1l, s1h, r1, r2, r3, s0e, bit_ix1 L t1 W Q _ ht Lm t1m,
        b1.2.1, b1.2.2, (bit_ix0 L t1 X W Q _ ht Lm t1m hX),
        bit_q1 rr q1 Q _ rrm q1m, b2.2.1, b2.2.2, qe, Kl, Kh⟩
    rw [c_pred n]
    exact h

theorem le3 {a k : Nat} (h : a ≤ k) : a ≤ k + 1 + 1 + 1 := Nat.le_succ_of_le (Nat.le_succ_of_le (Nat.le_succ_of_le h))

include hro hs in
/-- **One iteration of the second loop** (`e_sqrt.c:149-163`): count `n + 1`
from count `n`. -/
theorem l2_step (n : Nat) (hn : n ≤ 31) (ih : 1 ≤ n → L2Claim m s r g n) : L2Claim m s r g (n + 1) := by
  intro fuel N W Q s1 rr s0 L H q1 q K hf hI
  obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨fuel - 8, by omega⟩
  have hk : 8 * n ≤ k := by omega
  clear hf
  obtain ⟨inv, nlo, nhi, s1m, s1l, s1h, rrm, rrl, rrh, s0e, Lm, Ll, Lh, He, q1m, q1l, q1h, qe, Kl, Kh⟩ := hI
  have ⟨hQ, hW⟩ := sqInv_bounds inv nhi (Nat.le_trans (Nat.succ_le_succ hn) (by decide))
  have ⟨al1, al2⟩ := sq_align (c := n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.succ_le_succ hn) inv.dvd
  simp only [Nat.add_sub_cancel] at rrm al1 al2
  have hP1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hP2 : 2 ^ n ≤ 2 ^ 31 := Nat.pow_le_pow_right (by decide) hn
  have hD := l2_hD Q (2 ^ n) hP1 hP2 al2
  have ⟨hs00, hs0b, hH0, hHb⟩ := l2_bnds W Q s0 H s0e He hQ hW
  have ⟨t1m, t1l, t1h⟩ := l2_t1 Q (2 ^ n) s1 rr s1m rrm hD
  have hrun : sqRun (n + 1) 0 (W, Q) = sqRun n 0 (sqBit (2 ^ n) (W, Q)) := by
    show sqRun n 0 (sqBit (2 ^ (0 + n)) (W, Q)) = _; rw [Nat.zero_add]
  rw [hrun]
  have inv' := sqBit_inv (p := n) inv
  have htk := l2_take W Q (2 ^ n) s0 L H _ s0e He Lm t1m hD
  have hs0' : s0 < 2 ^ 31 := Int.lt_trans hs0b (by decide)
  have hH' : H < 2 ^ 31 := Int.lt_trans hHb (by decide)
  have hH29 : H < 2 ^ 29 := Int.lt_trans hHb (by decide)
  have hs29 : s0 < 2 ^ 29 := Int.lt_trans hs0b (by decide)
  have e544 := st_544 m s r g (k + 1 + 1 + 1 + 1 + 1 + 1 + 1) s1 rr s0 L H ((n + 1 : Nat) : Int) q1 K q
    hs00 hs0' hH0 hH'
  rw [e544.1, e544.2]
  clear e544
  by_cases h1 : H ≤ s0
  · rw [if_pos h1, if_pos h1]
    -- no bit unless `t == ix0` and `t1 <= ix1`
    have hnt0 : (2 * Q + 2 ^ n ≤ W) → H = s0 ∧ (rr + s1).bmod 4294967296 % 4294967296 ≤ L % 4294967296 := by
      intro h
      rcases htk.1 h with h' | h'
      · exact absurd h' (Int.not_lt.mpr h1)
      · exact h'
    have e50c := st_50c m s r g (k + 1 + 1 + 1 + 1 + 1 + 1) s1 ((rr + s1).bmod 4294967296) rr s0 L H
      ((n + 1 : Nat) : Int) q1 K q hs00 hs0' hH0 hH'
    rw [e50c.1, e50c.2]
    clear e50c
    by_cases h2 : H = s0
    · rw [if_pos h2, if_pos h2]
      have e510 := st_510 m s r g (k + 1 + 1 + 1 + 1 + 1) s1 ((rr + s1).bmod 4294967296) rr s0 L H
        ((n + 1 : Nat) : Int) q1 K q t1l t1h Ll Lh
      rw [e510.1, e510.2]
      clear e510
      by_cases h3 : L % 4294967296 < (rr + s1).bmod 4294967296 % 4294967296
      · rw [if_pos h3, if_pos h3]
        have hnt : ¬ (2 * Q + 2 ^ n ≤ W) := fun h => Int.not_le.mpr h3 (hnt0 h).2
        have hb : sqBit (2 ^ n) (W, Q) = (2 * W, Q) := by unfold sqBit; simp only [hnt, if_false]
        rw [hb] at inv' ⊢
        exact via_5e8 s r g hro hs n hn ih (k + 1 + 1 + 1 + 1) N W Q s1 rr s0 L H q1 q K
          (Nat.le_succ_of_le (le3 hk)) inv' nlo nhi hW s1m s1l s1h rrm rrl rrh s0e Lm Ll Lh He q1m q1l q1h qe
          Kl Kh
      · rw [if_neg h3, if_neg h3]
        -- a bit, `t == ix0`: through `0x8002d514`
        have ht : 2 * Q + 2 ^ n ≤ W := htk.2 (Or.inr ⟨h2, Int.not_lt.mp h3⟩)
        have hb : sqBit (2 ^ n) (W, Q) = (2 * (W - (2 * Q + 2 ^ n)), Q + 2 ^ n) := by
          unfold sqBit; simp only [ht, if_true]
        rw [hb] at inv' ⊢
        have ⟨s1m', s1l', s1h'⟩ := l2_s1 Q (2 ^ n) rr _ t1m rrm
        have ⟨c1, c2, c3⟩ := l2_carry514 Q (2 ^ n) rr s0 _ s0e t1m rrm t1l t1h hP1 hP2 al2
        have hX := l2_x514 W Q (2 ^ n) s0 L H _ s0e He Lm t1m hD h2 h3
        have t1m2 := l2_t1m Q (2 ^ n) _ t1m hD
        have qe' := l2_qe Q (2 ^ n) q qe al1
        have e514 := st_514 m s r g (k + 1 + 1 + 1 + 1) ((rr + s1).bmod 4294967296) rr s0 L
          ((n + 1 : Nat) : Int) q1 K q t1l t1h
        rw [e514.1, e514.2]
        clear e514
        by_cases h4 : (rr + s1).bmod 4294967296 < 0
        · rw [if_pos h4, if_pos h4]
          have e658 := st_658 m s r g (k + 1 + 1 + 1) (((rr + s1).bmod 4294967296 + rr).bmod 4294967296)
            ((rr + s1).bmod 4294967296) rr s0 L 0 ((n + 1 : Nat) : Int) q1 K q s1l' s1h'
          rw [e658.1, e658.2]
          clear e658
          by_cases h5 : ((rr + s1).bmod 4294967296 + rr).bmod 4294967296 < 0
          · rw [if_pos h5, if_pos h5]
            exact via_520 s r g hro hs n hn ih (k + 1 + 1) N W Q _ _ rr s0 L 0 q1 q K
              (Nat.le_succ_of_le (Nat.le_succ_of_le hk)) ht inv' nlo nhi hW s1m' s1l' s1h' t1m2 rrm rrl rrh
              (c1 h4 h5) Lm Ll Lh hX q1m q1l q1h qe' Kl Kh
          · rw [if_neg h5, if_neg h5]
            have e65c := st_65c m s r g (k + 1 + 1) (((rr + s1).bmod 4294967296 + rr).bmod 4294967296)
              ((rr + s1).bmod 4294967296) rr s0 L 0 ((n + 1 : Nat) : Int) q1 K q hs00
              (Int.lt_trans hs0b (by decide))
            rw [e65c.1, e65c.2]
            clear e65c
            exact via_520 s r g hro hs n hn ih (k + 1) N W Q _ _ rr (s0 + 1) L 0 q1 q K
              (Nat.le_succ_of_le hk) ht inv' nlo nhi hW s1m' s1l' s1h' t1m2 rrm rrl rrh
              (c2 h4 h5) Lm Ll Lh hX q1m q1l q1h qe' Kl Kh
        · rw [if_neg h4, if_neg h4]
          exact via_520 s r g hro hs n hn ih (k + 1 + 1 + 1) N W Q _ _ rr s0 L 0 q1 q K
            (le3 hk) ht inv' nlo nhi hW s1m' s1l' s1h' t1m2 rrm rrl rrh
            (c3 h4) Lm Ll Lh hX q1m q1l q1h qe' Kl Kh
    · rw [if_neg h2, if_neg h2]
      have hnt : ¬ (2 * Q + 2 ^ n ≤ W) := fun h => h2 (hnt0 h).1
      have hb : sqBit (2 ^ n) (W, Q) = (2 * W, Q) := by unfold sqBit; simp only [hnt, if_false]
      rw [hb] at inv' ⊢
      exact via_5e8 s r g hro hs n hn ih (k + 1 + 1 + 1 + 1 + 1) N W Q s1 rr s0 L H q1 q K
        (Nat.le_succ_of_le (Nat.le_succ_of_le (le3 hk))) inv' nlo nhi hW s1m s1l s1h rrm rrl rrh s0e Lm Ll Lh He
        q1m q1l q1h qe Kl Kh
  · rw [if_neg h1, if_neg h1]
    -- a bit, `t < ix0`: through `0x8002d54c`
    have hlt : s0 < H := Int.not_le.mp h1
    have ht : 2 * Q + 2 ^ n ≤ W := htk.2 (Or.inl hlt)
    have hb : sqBit (2 ^ n) (W, Q) = (2 * (W - (2 * Q + 2 ^ n)), Q + 2 ^ n) := by
      unfold sqBit; simp only [ht, if_true]
    rw [hb] at inv' ⊢
    have ⟨s1m', s1l', s1h'⟩ := l2_s1 Q (2 ^ n) rr _ t1m rrm
    have cy := l2_carry54 Q (2 ^ n) rr s0 _ s0e t1m rrm hP1 hP2 al2
    have t1m2 := l2_t1m Q (2 ^ n) _ t1m hD
    have qe' := l2_qe Q (2 ^ n) q qe al1
    have e54c := st_54c m s r g (k + 1 + 1 + 1 + 1 + 1 + 1) ((rr + s1).bmod 4294967296) rr s0 L H
      ((n + 1 : Nat) : Int) q1 K q t1l t1h Ll Lh hs00 hs29 hlt hH29
    rw [e54c.1, e54c.2]
    clear e54c
    by_cases h3 : (rr + s1).bmod 4294967296 % 4294967296 ≤ L % 4294967296
    · rw [if_pos h3, if_pos h3]
      have hX := l2_x54a W Q (2 ^ n) s0 L H _ s0e He Lm t1m hD h3
      have e650 := st_650 m s r g (k + 1 + 1 + 1 + 1 + 1) (((rr + s1).bmod 4294967296 + rr).bmod 4294967296)
        ((rr + s1).bmod 4294967296) rr
        (s0 + if 2147483648 ≤ (rr + s1).bmod 4294967296 % 4294967296 ∧
          ((rr + s1).bmod 4294967296 + rr) % 4294967296 < 2147483648 then 1 else 0)
        L (H - s0) ((n + 1 : Nat) : Int) q1 K q
        (Int.sub_nonneg.mpr (Int.le_of_lt hlt)) (Int.lt_of_le_of_lt (Int.sub_le_self _ hs00) hH29)
      rw [e650.1, e650.2]
      clear e650
      exact via_520 s r g hro hs n hn ih (k + 1 + 1 + 1 + 1) N W Q _ _ rr _ L _ q1 q K
        (Nat.le_succ_of_le (le3 hk)) ht inv' nlo nhi hW s1m' s1l' s1h' t1m2 rrm rrl rrh
        cy Lm Ll Lh hX q1m q1l q1h qe' Kl Kh
    · rw [if_neg h3, if_neg h3]
      have hX := l2_x54b W Q (2 ^ n) s0 L H _ s0e He Lm t1m hD h3
      have e56c := st_56c m s r g (k + 1 + 1 + 1 + 1 + 1) (((rr + s1).bmod 4294967296 + rr).bmod 4294967296)
        ((rr + s1).bmod 4294967296) rr
        (s0 + if 2147483648 ≤ (rr + s1).bmod 4294967296 % 4294967296 ∧
          ((rr + s1).bmod 4294967296 + rr) % 4294967296 < 2147483648 then 1 else 0)
        L (H - s0) ((n + 1 : Nat) : Int) q1 K q
        (Int.sub_pos.mpr hlt) (Int.lt_of_le_of_lt (Int.sub_le_self _ hs00) hH29)
      rw [e56c.1, e56c.2]
      clear e56c
      exact via_520 s r g hro hs n hn ih (k + 1 + 1 + 1 + 1) N W Q _ _ rr _ L _ q1 q K
        (Nat.le_succ_of_le (le3 hk)) ht inv' nlo nhi hW s1m' s1l' s1h' t1m2 rrm rrl rrh
        cy Lm Ll Lh hX q1m q1l q1h qe' Kl Kh

include hro hs in
/-- **The second loop** at every count `n + 1 ≤ 32`. -/
theorem l2_claim : ∀ n, n ≤ 31 → L2Claim m s r g (n + 1) := by
  intro n
  induction n with
  | zero => intro hn; exact l2_step s r g hro hs 0 hn (fun h => absurd h (by decide))
  | succ n ih => intro hn; exact l2_step s r g hro hs (n + 1) hn (fun _ => ih (by omega))

end claim2

end Lua.Vm.Fn.Ieee754Sqrt


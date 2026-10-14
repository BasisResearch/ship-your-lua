import Lua.Vm.Fn.Ieee754Sqrt
import Lua.Vm.Fn.FmodLens
import Lua.Num.SfRefSqrt

/-!
# `__ieee754_sqrt`'s root loops (lane float-sf6, (b1))

`e_sqrt.c:133-171`, the cycles at `0x8002d4c8` (22 bits of `q`; three
nodes) and `0x8002d544` (32 bits of `q1`; thirteen nodes): each iteration is
one `SfRef.sqBit` on the remainder `W = ix0:ix1` and the root `Q = q:q1`
(`s0:s1 = 2Q`). The node steps are in the signed-integer lens of
`Lua/Vm/Fn/FmodLens.lean` (`fm_nf`); an iteration is the composition of its
nodes' steps, and the loop is an induction on the remaining count.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Lua.Vm.Fn.Ieee754Sqrt

open Lua.Vm.Fn.FmodLens Lua.Vm.Sim Vsa.Sim

set_option linter.unusedVariables false

/-- The facts of a sign-extended word (`Int.bmod 2^32`), for `omega`. -/
theorem bm_facts (z : Int) :
    z.bmod 4294967296 % 4294967296 = z % 4294967296 ∧
    -2147483648 ≤ z.bmod 4294967296 ∧ z.bmod 4294967296 < 2147483648 := by
  have hb1 := Int.bmod_emod (x := z) (m := 2 ^ 32)
  have hb2 := Int.le_bmod (x := z) (m := 2 ^ 32) (by decide)
  have hb3 := Int.bmod_lt (x := z) (m := 2 ^ 32) (by decide)
  simp only [show ((2 ^ 32 : Nat) : Int) = 4294967296 by decide, Nat.reducePow] at hb1 hb2 hb3
  exact ⟨hb1, by omega, by omega⟩

open Lean in
/-- The arguments `z` of the `Int.bmod z _` subterms of `e`. -/
partial def bmodArgs (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``Int.bmod 2 && !acc.contains e.appFn!.appArg! then
    acc.push e.appFn!.appArg! else acc
  match e with
  | .app f a => bmodArgs a (bmodArgs f acc)
  | .lam _ d b _ => bmodArgs b (bmodArgs d acc)
  | .forallE _ d b _ => bmodArgs b (bmodArgs d acc)
  | .mdata _ b => bmodArgs b acc
  | _ => acc

open Lean Elab Tactic Meta in
/-- **Every sign-extended word's facts** (`bm_facts`) for the `Int.bmod _ 2^32`
terms of the goal, then `omega`. -/
elab "bm_omega" : tactic => withMainContext do
  let acc := bmodArgs (← instantiateMVars (← getMainTarget)) #[]
  for z in acc do
    unless z.hasLooseBVars do
      let zs ← Term.exprToSyntax z
      evalTactic (← `(tactic| have := Lua.Vm.Fn.Ieee754Sqrt.bm_facts $zs))
  evalTactic (← `(tactic| omega))

/-! ## The invariant's bounds -/

open Lua.Num.SfRef in
/-- The root and the remainder are small: `Q < 2^54`, `W < 2^57`. -/
theorem sqInv_bounds {N p W Q : Nat} (h : SqInv N p W Q) (hN : N < 2 ^ 108) (hp : p ≤ 54) :
    Q < 2 ^ 54 ∧ W < 2 ^ 57 := by
  obtain ⟨hle, hrem, hlt, _⟩ := h
  have hQ : Q < 2 ^ 54 := by
    refine Nat.lt_of_not_le fun hc => ?_
    have : 2 ^ 54 * 2 ^ 54 ≤ Q * Q := Nat.mul_le_mul hc hc
    rw [← Nat.pow_add] at this; omega
  refine ⟨hQ, ?_⟩
  have e := sq_add Q (2 ^ p)
  have h1 : W * 2 ^ p < (4 * Q + 2 * 2 ^ p) * 2 ^ p := by
    have : (4 * Q + 2 * 2 ^ p) * 2 ^ p = 2 * ((2 * Q + 2 ^ p) * 2 ^ p) := by
      rw [show 4 * Q + 2 * 2 ^ p = 2 * (2 * Q + 2 ^ p) by omega, Nat.mul_assoc]
    omega
  have h2 := Nat.lt_of_mul_lt_mul_right h1
  have h3 : 2 ^ p ≤ 2 ^ 54 := Nat.pow_le_pow_right (by decide) hp
  omega

open Lua.Num.SfRef in
/-- The root at the bits below `2^c` is the next bit's alignment: its low
words leave room for `2 · 2^(c-1)` (`q1 + r`) and, doubled, for `4 · 2^(c-1)`
(`s1 + 2r`, no carry), but at `c = 32` (one carry into `s0`). -/
theorem sq_align {c Q : Nat} (hc1 : 1 ≤ c) (hc2 : c ≤ 32) (h : 2 ^ c ∣ Q) :
    Q % 2 ^ 32 + 2 * 2 ^ (c - 1) ≤ 2 ^ 32 ∧
      (2 * Q % 2 ^ 32 + 4 * 2 ^ (c - 1) ≤ 2 ^ 32 ∨ (2 * Q % 2 ^ 32 = 0 ∧ 2 ^ (c - 1) = 2 ^ 31)) := by
  obtain ⟨j, rfl⟩ := h
  have e2 : 2 * 2 ^ (c - 1) = 2 ^ c := by rw [← Nat.pow_succ']; congr 1; omega
  have m1 : ∀ d, d ≤ 32 → 2 ^ d * j % 2 ^ 32 + 2 ^ d ≤ 2 ^ 32 := by
    intro d hd
    have e : 2 ^ 32 = 2 ^ d * 2 ^ (32 - d) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, Nat.mul_mod_mul_left]
    have : j % 2 ^ (32 - d) + 1 ≤ 2 ^ (32 - d) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have := Nat.mul_le_mul_left (2 ^ d) this
    rw [Nat.mul_add, Nat.mul_one] at this
    exact this
  refine ⟨by rw [e2]; exact m1 c hc2, ?_⟩
  have e3 : 2 * (2 ^ c * j) = 2 ^ (c + 1) * j := by rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm 2]
  rw [e3]
  by_cases h31 : c ≤ 31
  · left
    have e4 : 4 * 2 ^ (c - 1) = 2 ^ (c + 1) := by
      rw [show (4 : Nat) = 2 ^ 2 from rfl, ← Nat.pow_add]; congr 1; omega
    rw [e4]; exact m1 (c + 1) (by omega)
  · right
    have hc : c = 32 := by omega
    subst hc
    refine ⟨?_, rfl⟩
    rw [show (2 : Nat) ^ (32 + 1) = 2 ^ 32 * 2 by rfl, Nat.mul_assoc]
    exact Nat.mul_mod_right _ _

/-- `xor` with all ones: `not`. -/
theorem xor_m1 (a : Int) : BitVec.ofInt 64 a ^^^ BitVec.ofInt 64 (-1) = BitVec.ofInt 64 (-1 - a) := by
  rw [show BitVec.ofInt 64 (-1) = BitVec.allOnes 64 by decide, BitVec.xor_allOnes, BitVec.not_eq_neg_add,
    show (1#64) = BitVec.ofInt 64 1 by decide, ← BitVec.ofInt_neg, sub64]
  congr 1; omega

/-- `and` of two bits: their product. -/
theorem and01 (a b : Int) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    BitVec.ofInt 64 a &&& BitVec.ofInt 64 b = BitVec.ofInt 64 (a * b) := by
  rcases (show a = 0 ∨ a = 1 by omega) with rfl | rfl <;>
    rcases (show b = 0 ∨ b = 1 by omega) with rfl | rfl <;> decide

/-- The carry `s0 += (t1 & sign) && !(s1 & sign)` as the machine computes it. -/
theorem carry_eq (t1 rr : Int) :
    t1 % 4294967296 / 2147483648 * ((-1 - (t1 + rr).bmod 4294967296) % 4294967296 / 2147483648) =
      if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0 := by
  have := bm_facts (t1 + rr)
  by_cases h1 : 2147483648 ≤ t1 % 4294967296
  · have f1 : t1 % 4294967296 / 2147483648 = 1 := by omega
    by_cases h2 : (t1 + rr) % 4294967296 < 2147483648
    · have f2 : (-1 - (t1 + rr).bmod 4294967296) % 4294967296 / 2147483648 = 1 := by omega
      rw [f1, f2, if_pos ⟨h1, h2⟩]; rfl
    · have f2 : (-1 - (t1 + rr).bmod 4294967296) % 4294967296 / 2147483648 = 0 := by omega
      rw [f1, f2, if_neg (fun h => h2 h.2)]; rfl
  · have f1 : t1 % 4294967296 / 2147483648 = 0 := by omega
    rw [f1, Int.zero_mul, if_neg (fun h => h1 h.1)]

/-- Close an equation of node applications whose `ofInt` arguments agree by
`bm_omega`. -/
macro "sq_close" : tactic => `(tactic| (congr 1 <;> (congr 1; bm_omega)))

section loop1
variable (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame)

theorem st_4c8 (k : Nat) (c ρ S0 L H K q : Int) (hc1 : 1 ≤ c) (hc2 : c ≤ 22) (hρ0 : 0 ≤ ρ)
    (hS0 : 0 ≤ S0) (hS1 : S0 + ρ < 2 ^ 31) (hH0 : 0 ≤ H) (hH1 : H < 2 ^ 31) (hL1 : -2 ^ 31 ≤ L)
    (hL2 : L < 2 ^ 31) :
    (N_8002d4c8 (k + 1) m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      (if H < S0 + ρ then
        N_8002d4e4 k m s r g (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0)
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (L % 4294967296 / 2147483648))
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d4d8 k m s r g (BitVec.ofInt 64 (S0 + ρ)) (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 ρ)
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (L % 4294967296 / 2147483648))
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q))) ∧
    (T_8002d4c8 (k + 1) m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      (if H < S0 + ρ then
        T_8002d4e4 k m s r g (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0)
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (L % 4294967296 / 2147483648))
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d4d8 k m s r g (BitVec.ofInt 64 (S0 + ρ)) (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 ρ)
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 (L % 4294967296 / 2147483648))
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q))) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d4c8] | rw [T_8002d4c8]) <;>
  (
    fm_nf
    by_cases hc : H < S0 + ρ
    · fm_nf; trivial
    · fm_nf; trivial)

theorem st_4d8 (k : Nat) (c ρ T L H b K q : Int) (hρ0 : 0 ≤ ρ) (hT0 : 0 ≤ T) (hT1 : T + ρ < 2 ^ 31)
    (hH0 : T ≤ H) (hH1 : H < 2 ^ 31) (hq0 : 0 ≤ q) (hq1 : q + ρ < 2 ^ 31) :
    (N_8002d4d8 (k + 1) m s r g (BitVec.ofInt 64 T) (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      N_8002d4e4 k m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 (T + ρ))
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - T)) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 (q + ρ))) ∧
    (T_8002d4d8 (k + 1) m s r g (BitVec.ofInt 64 T) (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      T_8002d4e4 k m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 (T + ρ))
        (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - T)) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K)
        (BitVec.ofInt 64 (q + ρ))) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d4d8] | rw [T_8002d4d8]) <;>
  (
    fm_nf)

theorem st_4e4 (k : Nat) (c ρ S0 L H b K q : Int) (hc0 : 0 ≤ c) (hc1 : c ≤ 22) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 2 ^ 31)
    (hH0 : 0 ≤ H) (hH1 : 2 * H + b < 2 ^ 31) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hL1 : -2 ^ 31 ≤ L)
    (hL2 : L < 2 ^ 31) :
    (N_8002d4e4 (k + 1) m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      (if c = 0 then
        N_8002d4f8 m s r g (BitVec.ofInt 64 S0) (BitVec.ofInt 64 ((L * 2).bmod 4294967296))
          (BitVec.ofInt 64 (b + H * 2)) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d4c8 k m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 (ρ / 2)) (BitVec.ofInt 64 S0)
          (BitVec.ofInt 64 ((L * 2).bmod 4294967296)) (BitVec.ofInt 64 (b + H * 2)) (BitVec.ofInt 64 K)
          (BitVec.ofInt 64 q))) ∧
    (T_8002d4e4 (k + 1) m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 ρ) (BitVec.ofInt 64 S0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 b) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      (if c = 0 then
        T_8002d4f8 m s r g (BitVec.ofInt 64 S0) (BitVec.ofInt 64 ((L * 2).bmod 4294967296))
          (BitVec.ofInt 64 (b + H * 2)) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d4c8 k m s r g (BitVec.ofInt 64 c) (BitVec.ofInt 64 (ρ / 2)) (BitVec.ofInt 64 S0)
          (BitVec.ofInt 64 ((L * 2).bmod 4294967296)) (BitVec.ofInt 64 (b + H * 2)) (BitVec.ofInt 64 K)
          (BitVec.ofInt 64 q))) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d4e4] | rw [T_8002d4e4]) <;>
  (
    fm_nf
    have e : ρ % 4294967296 = ρ := by omega
    by_cases hc : c = 0
    · subst hc; fm_nf
    · fm_nf; rw [e])

end loop1

section loop2
variable (m : Mem) (s : Nat) (r : BitVec 64) (g : SFrame)

/-- No bit (`0x8002d5e8`): the remainder doubled, the bit halved. -/
theorem st_5e8 (k : Nat) (s1 rr s0 L H c q1 K q : Int) (hc0 : 1 ≤ c) (hc1 : c ≤ 32) (hH0 : 0 ≤ H)
    (hH1 : H < 2 ^ 29) (hL1 : -2 ^ 31 ≤ L) (hL2 : L < 2 ^ 31) :
    (N_8002d5e8 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if c = 1 then
        N_8002d608 m s r g (BitVec.ofInt 64 (L % 4294967296 / 2147483648 + H * 2))
          (BitVec.ofInt 64 ((L * 2).bmod 4294967296)) (BitVec.ofInt 64 0) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K)
          (BitVec.ofInt 64 q)
      else
        N_8002d544 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 (rr % 4294967296 / 2)) (BitVec.ofInt 64 s0)
          (BitVec.ofInt 64 ((L * 2).bmod 4294967296)) (BitVec.ofInt 64 (L % 4294967296 / 2147483648 + H * 2))
          (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d5e8 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if c = 1 then true
      else
        T_8002d544 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 (rr % 4294967296 / 2)) (BitVec.ofInt 64 s0)
          (BitVec.ofInt 64 ((L * 2).bmod 4294967296)) (BitVec.ofInt 64 (L % 4294967296 / 2147483648 + H * 2))
          (BitVec.ofInt 64 (c - 1)) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d5e8] | rw [T_8002d5e8]) <;> fm_nf <;>
    (by_cases hc : c = 1) <;> fm_nf <;> sq_close

/-- The test `t < ix0` (`0x8002d544`): `t1 = s1 + r` formed. -/
theorem st_544 (k : Nat) (s1 rr s0 L H c q1 K q : Int) (hs0 : 0 ≤ s0) (hs1 : s0 < 2 ^ 31) (hH0 : 0 ≤ H)
    (hH1 : H < 2 ^ 31) :
    (N_8002d544 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if H ≤ s0 then
        N_8002d50c k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 ((rr + s1).bmod 4294967296)) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d54c k m s r g (BitVec.ofInt 64 ((rr + s1).bmod 4294967296)) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d544 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr) (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L)
        (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if H ≤ s0 then
        T_8002d50c k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 ((rr + s1).bmod 4294967296)) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d54c k m s r g (BitVec.ofInt 64 ((rr + s1).bmod 4294967296)) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d544] | rw [T_8002d544]) <;> fm_nf <;>
    (by_cases hc : H ≤ s0) <;> fm_nf <;> sq_close

/-- `t == ix0`? (`0x8002d50c`). -/
theorem st_50c (k : Nat) (s1 t1 rr s0 L H c q1 K q : Int) (hs0 : 0 ≤ s0) (hs1 : s0 < 2 ^ 31) (hH0 : 0 ≤ H)
    (hH1 : H < 2 ^ 31) :
    (N_8002d50c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if H = s0 then
        N_8002d510 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d5e8 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d50c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if H = s0 then
        T_8002d510 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d5e8 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d50c] | rw [T_8002d50c]) <;> fm_nf <;>
    (by_cases hc : H = s0) <;> fm_nf <;> sq_close

/-- `t1 <= ix1`? (`0x8002d510`, unsigned words). -/
theorem st_510 (k : Nat) (s1 t1 rr s0 L H c q1 K q : Int) (ht1 : -2 ^ 31 ≤ t1) (ht2 : t1 < 2 ^ 31)
    (hL1 : -2 ^ 31 ≤ L) (hL2 : L < 2 ^ 31) :
    (N_8002d510 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if L % 4294967296 < t1 % 4294967296 then
        N_8002d5e8 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d514 k m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d510 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if L % 4294967296 < t1 % 4294967296 then
        T_8002d5e8 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d514 k m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  have e : (L % 18446744073709551616 < t1 % 18446744073709551616) ↔ (L % 4294967296 < t1 % 4294967296) := by
    omega
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d510] | rw [T_8002d510]) <;> fm_nf <;> simp only [e] <;>
    (by_cases hc : L % 4294967296 < t1 % 4294967296) <;> fm_nf <;> sq_close

/-- `t == ix0`, `t1 <= ix1` (`0x8002d514`): `s1 = t1 + r`, `ix0 = 0`; the carry test. -/
theorem st_514 (k : Nat) (t1 rr s0 L c q1 K q : Int) (ht1 : -2 ^ 31 ≤ t1) (ht2 : t1 < 2 ^ 31) :
    (N_8002d514 (k + 1) m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if t1 < 0 then
        N_8002d658 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 0) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d520 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 0) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d514 (k + 1) m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if t1 < 0 then
        T_8002d658 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 0) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d520 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 0) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d514] | rw [T_8002d514]) <;> fm_nf <;>
    (by_cases hc : t1 < 0) <;> fm_nf <;> sq_close
/-- The carry test (`0x8002d658`): `s1 = t1 + r` lost the sign bit of `t1`. -/
theorem st_658 (k : Nat) (s1 t1 rr s0 L X c q1 K q : Int) (hs1 : -2 ^ 31 ≤ s1) (hs2 : s1 < 2 ^ 31) :
    (N_8002d658 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if s1 < 0 then
        N_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d65c k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d658 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if s1 < 0 then
        T_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d65c k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d658] | rw [T_8002d658]) <;> fm_nf <;>
    (by_cases hc : s1 < 0) <;> fm_nf <;> sq_close

/-- The carry into `s0` (`0x8002d65c`). -/
theorem st_65c (k : Nat) (s1 t1 rr s0 L X c q1 K q : Int) (hs0 : 0 ≤ s0) (hs1 : s0 < 2 ^ 30) :
    (N_8002d65c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      N_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 (s0 + 1)) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d65c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      T_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 (s0 + 1)) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d65c] | rw [T_8002d65c]) <;> fm_nf <;> sq_close

/-- `ix0 -= t` doubled (`0x8002d650`, no borrow). -/
theorem st_650 (k : Nat) (s1 t1 rr s0 L X c q1 K q : Int) (hX0 : 0 ≤ X) (hX1 : X < 2 ^ 29) :
    (N_8002d650 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      N_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 (2 * X)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d650 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      T_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 (2 * X)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d650] | rw [T_8002d650]) <;> fm_nf <;> sq_close

/-- `ix0 -= t` doubled with the borrow (`0x8002d56c`). -/
theorem st_56c (k : Nat) (s1 t1 rr s0 L X c q1 K q : Int) (hX0 : 1 ≤ X) (hX1 : X < 2 ^ 29) :
    (N_8002d56c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      N_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 (2 * X - 2)) (BitVec.ofInt 64 c)
        (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d56c (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      T_8002d520 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 (2 * X - 2)) (BitVec.ofInt 64 c)
        (BitVec.ofInt 64 q1) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d56c] | rw [T_8002d56c]) <;> fm_nf <;> sq_close

/-- After a bit (`0x8002d520`): `ix1 -= t1`, the remainder doubled, `q1 += r`. -/
theorem st_520 (k : Nat) (s1 t1 rr s0 L X c q1 K q : Int) (hc0 : 1 ≤ c) (hc1 : c ≤ 32) (hX0 : 0 ≤ X)
    (hX1 : X < 2 ^ 30) :
    (N_8002d520 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if c = 1 then
        N_8002d608 m s r g (BitVec.ofInt 64 ((L - t1) % 4294967296 / 2147483648 + X))
          (BitVec.ofInt 64 (((L - t1) * 2).bmod 4294967296)) (BitVec.ofInt 64 0)
          (BitVec.ofInt 64 ((rr + q1).bmod 4294967296)) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d544 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 (rr % 4294967296 / 2)) (BitVec.ofInt 64 s0)
          (BitVec.ofInt 64 (((L - t1) * 2).bmod 4294967296))
          (BitVec.ofInt 64 ((L - t1) % 4294967296 / 2147483648 + X)) (BitVec.ofInt 64 (c - 1))
          (BitVec.ofInt 64 ((rr + q1).bmod 4294967296)) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d520 (k + 1) m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 X) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if c = 1 then true
      else
        T_8002d544 k m s r g (BitVec.ofInt 64 s1) (BitVec.ofInt 64 (rr % 4294967296 / 2)) (BitVec.ofInt 64 s0)
          (BitVec.ofInt 64 (((L - t1) * 2).bmod 4294967296))
          (BitVec.ofInt 64 ((L - t1) % 4294967296 / 2147483648 + X)) (BitVec.ofInt 64 (c - 1))
          (BitVec.ofInt 64 ((rr + q1).bmod 4294967296)) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d520] | rw [T_8002d520]) <;> fm_nf <;>
    (by_cases hc : c = 1) <;> fm_nf <;> sq_close

/-- `t < ix0` (`0x8002d54c`): `s1 = t1 + r` with its carry into `s0`, `ix0 -= t`;
the borrow test `t1 <= ix1`. -/
theorem st_54c (k : Nat) (t1 rr s0 L H c q1 K q : Int) (ht1 : -2 ^ 31 ≤ t1) (ht2 : t1 < 2 ^ 31)
    (hL1 : -2 ^ 31 ≤ L) (hL2 : L < 2 ^ 31) (hs0 : 0 ≤ s0) (hs1 : s0 < 2 ^ 29) (hH0 : s0 < H) (hH1 : H < 2 ^ 29) :
    (N_8002d54c (k + 1) m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if t1 % 4294967296 ≤ L % 4294967296 then
        N_8002d650 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 (s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0))
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - s0)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        N_8002d56c k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 (s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0))
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - s0)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) ∧
    (T_8002d54c (k + 1) m s r g (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
        (BitVec.ofInt 64 s0) (BitVec.ofInt 64 L) (BitVec.ofInt 64 H) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
        (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      if t1 % 4294967296 ≤ L % 4294967296 then
        T_8002d650 k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 (s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0))
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - s0)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)
      else
        T_8002d56c k m s r g (BitVec.ofInt 64 ((t1 + rr).bmod 4294967296)) (BitVec.ofInt 64 t1) (BitVec.ofInt 64 rr)
          (BitVec.ofInt 64 (s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0))
          (BitVec.ofInt 64 L) (BitVec.ofInt 64 (H - s0)) (BitVec.ofInt 64 c) (BitVec.ofInt 64 q1)
          (BitVec.ofInt 64 K) (BitVec.ofInt 64 q)) := by
  have e : (t1 % 18446744073709551616 ≤ L % 18446744073709551616) ↔ (t1 % 4294967296 ≤ L % 4294967296) := by
    omega
  have hcy : ((if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0) + s0).bmod
      4294967296 = s0 + if 2147483648 ≤ t1 % 4294967296 ∧ (t1 + rr) % 4294967296 < 2147483648 then 1 else 0 := by
    split <;> (rw [bmod_small' _ (by omega) (by omega)]; omega)
  refine ⟨?_, ?_⟩ <;> (first | rw [N_8002d54c] | rw [T_8002d54c]) <;> fm_nf <;>
    simp (disch := fm_disch) only [xor_m1] <;> fm_nf <;> simp (disch := fm_disch) only [and01] <;> fm_nf <;>
    simp only [e, carry_eq] <;> rw [hcy]

end loop2

section tail
variable (s : Nat) (r : BitVec 64)

/-- The `.rodata` doubleword at absolute address `a`, as `ld` reads it. -/
def rodQ (a : Nat) : BitVec 64 :=
  (((((((rodB a 7).append (rodB a 6)).append (rodB a 5)).append (rodB a 4)).append (rodB a 3)).append
    (rodB a 2)).append (rodB a 1)).append (rodB a 0)

/-- **A 64-bit `.rodata` constant** read by `ld`. -/
theorem rodQ_eq {m : Mem} (hro : RodataRead m) {a : Nat} (hlo : Image.rodataBase ≤ a)
    (hhi : a + 8 ≤ Image.rodataBase + Image.rodataSize) : bytesT8 m a = rodQ a := by
  have hb : ∀ i, i < 8 → (m[a + i]?).getD 0 = rodB a i := by
    intro i hi
    have := hro (a - Image.rodataBase + i) (by omega)
    rw [show Image.rodataBase + (a - Image.rodataBase + i) = a + i by omega] at this
    exact this
  have h0 : (m[a]?).getD 0 = rodB a 0 := hb 0 (by omega)
  unfold bytesT8 rodQ
  rw [h0, hb 1 (by omega), hb 2 (by omega), hb 3 (by omega), hb 4 (by omega), hb 5 (by omega),
    hb 6 (by omega), hb 7 (by omega)]

/-- fdlibm's `one` (`.rodata` at `0x8005c698`). -/
abbrev oneW : BitVec 64 := 0x3ff0000000000000#64
/-- fdlibm's `tiny = 1.0e-300` (`.rodata` at `0x8005c690`). -/
abbrev tinyW : BitVec 64 := 0x01a56e1fc2f8f359#64

theorem one_ld {m : Mem} (hro : RodataRead m) : bytesT8 m 2147862168 = oneW := by
  rw [rodQ_eq hro (by decide) (by decide)]; decide +kernel
theorem tiny_ld {m : Mem} (hro : RodataRead m) : bytesT8 m 2147862160 = tinyW := by
  rw [rodQ_eq hro (by decide) (by decide)]; decide +kernel

/-- The pack (`e_sqrt.c:187-191`): `ix0 = (q>>1) + 0x3fe00000 + (m<<20)`,
`ix1 = (q1>>1) | (q&1)<<31`. -/
theorem out_614 (a6 K q : Int) (ha0 : 0 ≤ a6) (ha1 : a6 < 2 ^ 31) (hq0 : 2 ^ 21 ≤ q) (hq1 : q ≤ 2 ^ 22)
    (hK0 : -600 ≤ K) (hK1 : K ≤ 600) :
    N_8002d614 s r (BitVec.ofInt 64 a6) (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) =
      BitVec.ofInt 64 ((K + 1022) * 2 ^ 52 + q * 2 ^ 31 + a6) := by
  rw [N_8002d614, N_8002d640]
  fm_nf
  have hb : (q * 2147483648).bmod 4294967296 = q % 2 * 2147483648 - q % 2 * 4294967296 := by
    simp only [Int.bmod]; split <;> omega
  rw [hb, or_low _ _ 31 (by decide) (by omega) ha0 (by omega)]
  fm_nf
  congr 1; omega

theorem sub_one_tiny : Lua.Num.F64.sub oneW tinyW = oneW := by decide +kernel
theorem add_one_tiny : Lua.Num.F64.add oneW tinyW = oneW := by decide +kernel
theorem le_one_one : Lua.Vm.Fn.Ledf2.S oneW oneW = 0#64 := by decide +kernel

/-- The halved, rounded-up root at the halved exponent (`e_sqrt.c:174-191`;
`SfRef.sqrtPack` on the loop's result). -/
def sqOut (K : Int) (W Q : Nat) : BitVec 64 :=
  BitVec.ofInt 64 ((K + 1022) * 2 ^ 52 + (((Q + if W = 0 then 0 else 1) / 2 : Nat) : Int))

theorem tail_608 {m : Mem} (g : SFrame) (hro : RodataRead m) (hs : FnSp s 160) (W Q : Nat) (H L q1 q K : Int)
    (hH : H = (W : Int) / 4294967296) (hL : L % 4294967296 = (W : Int) % 4294967296) (hL1 : -2 ^ 31 ≤ L)
    (hL2 : L < 2 ^ 31) (hW : W < 2 ^ 57) (hq1 : q1 % 4294967296 = (Q : Int) % 4294967296)
    (hq11 : -2 ^ 31 ≤ q1) (hq12 : q1 < 2 ^ 31) (hq : q = (Q : Int) / 4294967296) (hQ1 : 2 ^ 53 ≤ Q)
    (hQ2 : Q < 2 ^ 54) (hK0 : -600 ≤ K) (hK1 : K ≤ 600) :
    N_8002d608 m s r g (BitVec.ofInt 64 H) (BitVec.ofInt 64 L) (BitVec.ofInt 64 0) (BitVec.ofInt 64 q1)
      (BitVec.ofInt 64 K) (BitVec.ofInt 64 q) = sqOut K W Q := by
  rw [N_8002d608]
  fm_nf
  by_cases hW0 : W = 0
  · subst hW0
    rw [if_neg (by omega), N_8002d610]
    fm_nf
    rw [out_614 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hK0 hK1]
    unfold sqOut
    congr 1
    simp only [if_true]
    omega
  · rw [if_pos (by omega)]
    rw [N_8002d664, N_8002d698, N_8002d6a4]
    simp only [BitVec.reduceAppend, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceToNat,
      sign_extend, Sail.BitVec.signExtend]
    fn_sp_facts
    simp (disch := kit_disch) only [Lua.Vm.Sim.sdData_id, BitVec.signExtend_eq, BitVec.add_zero, one_ld hro,
      tiny_ld hro, sub_one_tiny, le_one_one, add_one_tiny, bytesT8_memPatch_out, bytesT8_wm8_far]
    rw [if_neg (by decide), N_8002d6b8]
    simp only [BitVec.reduceAppend, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceToNat,
      sign_extend, Sail.BitVec.signExtend]
    simp (disch := kit_disch) only [BitVec.signExtend_eq, BitVec.add_zero, one_ld hro,
      tiny_ld hro, bytesT8_memPatch_out, bytesT8_wm8_far]
    have hQe : (Q : Int) = q * 4294967296 + q1 % 4294967296 := by omega
    by_cases hm1 : q1 = -1
    · subst hm1
      rw [if_pos (by decide), N_8002d768]
      fm_nf
      rw [out_614 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hK0 hK1]
      unfold sqOut
      congr 1
      rw [if_neg (by omega)]
      bm_omega
    · rw [if_neg (by fm_nf; omega), N_8002d6d0, N_8002d6ec, N_8002d6f8]
      simp only [BitVec.reduceAppend, BitVec.reduceSignExtend, BitVec.reduceAdd, BitVec.reduceToNat,
        sign_extend, Sail.BitVec.signExtend]
      simp (disch := kit_disch) only [Lua.Vm.Sim.sdData_id, BitVec.signExtend_eq, BitVec.add_zero, one_ld hro,
        add_one_tiny, le_one_one, bytesT8_memPatch_out, bytesT8_wm8_far]
      rw [if_pos (by decide), N_8002d720, N_8002d724]
      fm_nf
      rw [out_614 _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) hK0 hK1]
      unfold sqOut
      congr 1
      rw [if_neg (by omega)]
      bm_omega

end tail

end Lua.Vm.Fn.Ieee754Sqrt

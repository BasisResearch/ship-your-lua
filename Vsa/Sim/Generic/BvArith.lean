import Vsa.Sim.ValueSites
import Vsa.Triple

/-!
# Bit-vector arithmetic facts for address and counter updates

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

namespace Vsa.Sim

/-! ### From `Vsa.Sim.StrlenSpec` -/

/-- `v + sext 0 = v`. -/
theorem sext0_add (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/-! ### From `Vsa.Sim.SnprintfSpec5` -/

/-- `v + sext 0xfff = ofNat (v.toNat - 1)` for any `v` with `1 ≤ v.toNat`. -/
theorem sub1_bv_sn5 (v : BitVec 64) (h1 : 1 ≤ v.toNat) :
    (v + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 (v.toNat - 1) := by
  have hlt := v.isLt
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add,
    show (sign_extend (m := 64) (0xfff#12) : BitVec 64).toNat = 2 ^ 64 - 1 from by decide,
    BitVec.toNat_ofNat]
  omega

/-! ### From `Vsa.Sim.SnprintfSpec18` -/

theorem sext1_toNat : (sign_extend (m := 64) (0x001#12) : BitVec 64).toNat = 1 := by decide

/-- `(ofNat n) - 1 = ofNat (n-1)` for the `addi a3,a2,-1` (via `sub1_bv_sn5`,
same kernel-recursion workaround as `ptrSB`). -/
theorem dec1_fwd (n : Nat) (hn : 1 ≤ n) (hlt : n < 2^63) :
    (BitVec.ofNat 64 n + sign_extend (m := 64) (0xfff#12)) = BitVec.ofNat 64 (n-1) := by
  have h1 : (BitVec.ofNat 64 n : BitVec 64).toNat = n :=
    BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (by omega)
  rw [sub1_bv_sn5 _ (by rw [h1]; omega), h1]

/-- `n - 1 + 1 = n` for the `a3` bookkeeping (`1 ≤ n`, `n` small). -/
theorem dec1_back (n : Nat) (hn : 1 ≤ n) (hlt : n < 2^63) :
    (BitVec.ofNat 64 (n-1) + sign_extend (m := 64) (0x001#12)) = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [sext1_toNat]
  omega

/-- Unsigned `≥` introduction: `dst.toNat ≤ src.toNat ⇒ (src ≥ᵤ dst) = true`. -/
theorem bgeu_of_le (a b : BitVec 64) (h : b.toNat ≤ a.toNat) : zopz0zKzJ_u a b = true := by
  unfold zopz0zKzJ_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_true (Int.ofNat_le.mpr h)

/-- Unsigned `<` refutation: `b.toNat ≤ a.toNat ⇒ (a <ᵤ b) = false`. -/
theorem bltu_false_of_ge (a b : BitVec 64) (h : b.toNat ≤ a.toNat) : zopz0zI_u a b = false := by
  unfold zopz0zI_u
  simp only [Sail.BitVec.toNatInt]
  exact decide_eq_false (by intro hc; exact absurd (Int.ofNat_lt.mp hc) (by omega))

theorem beq_false_of_toNat_ne (a b : BitVec 64) (h : a.toNat ≠ b.toNat) : (a == b) = false := by
  cases hb : (a == b) with
  | false => rfl
  | true => rw [beq_iff_eq] at hb; exact absurd (congrArg BitVec.toNat hb) h

theorem li31_val : ((0#64) + sign_extend (m := 64) (0x01f#12) : BitVec 64) = (0x1f#64) := by
  apply BitVec.eq_of_toNat_eq; decide

end Vsa.Sim

import Vsa.Sim.ValueSites
import Vsa.Sim.Generic.MapReads
import Vsa.Triple

/-!
# Little-endian reads of the byte map (`readLE`, `read64`) and their facts

Declarations copied verbatim (names, statements and proofs) from ship-your-interpreter at `46b1eb8e`, out of modules whose imports reach the WHILE semantics or representation. The declarations themselves mention no WHILE type; `experiments/port/port_census.py --copyset` checks that this module's closure is WHILE-free. Their original modules are not copied here, so the names are unique.

`Mem`, `readLE` and `read64` keep their ship-your-interpreter names in the
`Vsa.MemRepr` namespace; the WHILE representation module `Vsa.MemRepr` itself is
not copied.
-/

namespace Vsa.MemRepr

/-! ### From `Vsa.MemRepr` -/

/-- Machine memory: byte-addressed, as in the Sail model. -/
abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- Little-endian read of `n` bytes as a natural number. -/
def readLE (m : Mem) (a : Nat) : Nat → Option Nat
  | 0 => some 0
  | k + 1 => do
    let b ← m[a]?
    let rest ← readLE m (a + 1) k
    pure (b.toNat + 256 * rest)

/-- 8-byte little-endian read (pointers, `long long`). -/
def read64 (m : Mem) (a : Nat) : Option Nat := readLE m a 8

end Vsa.MemRepr

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr

namespace Vsa.Sim

/-! ### From `Vsa.Sim.ValueSpec` -/

/-- `(sdData_val v).toNat = v.toNat`. -/
theorem sdData_toNat (v : BitVec 64) : (sdData_val v).toNat = v.toNat := by
  simp only [sdData_val, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    Nat.shiftRight_zero]
  have hv : v.toNat < 2 ^ 64 := v.isLt
  have key : ∀ W : Nat, (2:Nat) ^ W = 2 ^ 64 → (BitVec.ofNat W v.toNat).toNat = v.toNat := by
    intro W hW; rw [BitVec.toNat_ofNat, hW, Nat.mod_eq_of_lt hv]
  exact key _ (by decide)

/-- `read64` of a freshly `writeMap8`-written window recovers `d.toNat`. -/
theorem read64_writeMap8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) (d : BitVec (8 * 8)) :
    read64 (writeMap8 mem a d) a = some d.toNat := by
  have e0 := getElem_writeMap8_0 mem a d
  have e1 := getElem_writeMap8_1 mem a d
  have e2 := getElem_writeMap8_2 mem a d
  have e3 := getElem_writeMap8_3 mem a d
  have e4 := getElem_writeMap8_4 mem a d
  have e5 := getElem_writeMap8_5 mem a d
  have e6 := getElem_writeMap8_6 mem a d
  have e7 := getElem_writeMap8_7 mem a d
  simp only [read64, readLE, e0, e1, e2, e3, e4, e5, e6, e7, bind, Option.bind, pure]
  simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Option.some.injEq, Nat.reducePow, Nat.pow_zero, Nat.div_one]
  have hd : d.toNat < 2 ^ 64 := by have := d.isLt; simpa using this
  omega

/-! ### From `Vsa.Sim.ValueTruthySpec` -/

/-- From `read64 m a = some p`, extract the eight little-endian bytes as `some`
facts together with the reconstruction equation. -/
theorem read64_bytes (m : Mem) (a p : Nat) (h : read64 m a = some p) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      m[a]? = some b0 ∧ m[a + 1]? = some b1 ∧ m[a + 2]? = some b2 ∧ m[a + 3]? = some b3 ∧
      m[a + 4]? = some b4 ∧ m[a + 5]? = some b5 ∧ m[a + 6]? = some b6 ∧ m[a + 7]? = some b7 ∧
      b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p := by
  simp only [read64, readLE, bind, Option.bind] at h
  match hb0 : m[a]?, hb1 : m[a + 1]?, hb2 : m[a + 2]?, hb3 : m[a + 3]?,
        hb4 : m[a + 4]?, hb5 : m[a + 5]?, hb6 : m[a + 6]?, hb7 : m[a + 7]? with
  | some b0, some b1, some b2, some b3, some b4, some b5, some b6, some b7 =>
      refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h
      have hk := Option.some.inj h
      omega
  | none, _, _, _, _, _, _, _ => rw [hb0] at h; exact absurd h (by simp)
  | some _, none, _, _, _, _, _, _ => rw [hb0, hb1] at h; exact absurd h (by simp)
  | some _, some _, none, _, _, _, _, _ => rw [hb0, hb1, hb2] at h; exact absurd h (by simp)
  | some _, some _, some _, none, _, _, _, _ => rw [hb0, hb1, hb2, hb3] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, none, _, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, none, _, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, none, _ =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6] at h; exact absurd h (by simp)
  | some _, some _, some _, some _, some _, some _, some _, none =>
      rw [hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7] at h; exact absurd h (by simp)

/-! ### From `Vsa.Sim.ReprSurvival` -/

/-- `AgreeP P m m'`: `m` and `m'` hold the same byte at every address satisfying
`P`. The footprint-predicate generalization of `Regions.AgreeOn` (which is the
special case `P a = mem_region a r`). -/
def AgreeP (P : Nat → Prop) (m m' : Mem) : Prop :=
  ∀ a, P a → m[a]? = m'[a]?

/-- `readLE` transfers when `P` holds on the whole `n`-byte window `[a, a+n)`. -/
theorem readLE_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m') :
    ∀ (n a : Nat), (∀ k, k < n → P (a + k)) → readLE m a n = readLE m' a n := by
  intro n
  induction n with
  | zero => intro a _; rfl
  | succ n ih =>
    intro a hP
    have hhead : m[a]? = m'[a]? := by
      have := h a (by simpa using hP 0 (Nat.succ_pos n)); simpa using this
    have htail : readLE m (a + 1) n = readLE m' (a + 1) n := by
      apply ih
      intro k hk
      have := hP (k + 1) (by omega)
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this
    simp only [readLE, hhead, htail]

/-- `read64 m a` is preserved when `P` covers `[a, a+8)`. -/
theorem read64_agreeP {P : Nat → Prop} {m m' : Mem} (h : AgreeP P m m')
    {a : Nat} (hP : ∀ k, k < 8 → P (a + k)) : read64 m a = read64 m' a :=
  readLE_agreeP h 8 a hP

/-! ### From `Vsa.Sim.EnvGetSpec3` -/

/-- `sign_extend` of a 64-bit value is itself. -/
theorem sext64_id_eg4 (d : BitVec (8 * 8)) : (sign_extend (m := 64) d : BitVec 64) = d := by
  simp only [sign_extend, Sail.BitVec.signExtend]
  exact BitVec.signExtend_eq d

/-- The 8-byte LE reconstruction as a `toNat` sum. -/
theorem word8_recon_eg4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
      : BitVec (8 * 8)).toNat
      = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [BitVec.append_eq, BitVec.toNat_append]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega), ← Nat.shiftLeft_add_eq_or_of_lt (by omega),
      ← Nat.shiftLeft_add_eq_or_of_lt (by omega)]
  simp only [Nat.shiftLeft_eq, Nat.reducePow]
  omega

/-- `read64 mem a = some q` exposes the eight LE bytes and the reconstruction. -/
theorem read64_bytes_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem[a]? = some b0 ∧ mem[a+1]? = some b1 ∧ mem[a+2]? = some b2 ∧
      mem[a+3]? = some b3 ∧ mem[a+4]? = some b4 ∧ mem[a+5]? = some b5 ∧
      mem[a+6]? = some b6 ∧ mem[a+7]? = some b7 ∧
      q = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) := by
  simp only [read64, readLE, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨b0, hb0, r1, ⟨b1, hb1, r2, ⟨b2, hb2, r3, ⟨b3, hb3, r4, ⟨b4, hb4, r5,
    ⟨b5, hb5, r6, ⟨b6, hb6, r7, ⟨b7, hb7, r8, hr8, hq7⟩, hq6⟩, hq5⟩, hq4⟩, hq3⟩,
    hq2⟩, hq1⟩, hq0⟩ := h
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hb1
  · simpa using hb2
  · simpa using hb3
  · simpa using hb4
  · simpa using hb5
  · simpa using hb6
  · simpa using hb7
  · subst hr8; simp only [Nat.add_zero, Nat.mul_zero] at *
    omega

/-- `read64 mem a = some q ⇒ q < 2^64` (LE 8-byte value fits in 64 bits). -/
theorem read64_lt_eg4 (mem : Mem) (a q : Nat) (h : read64 mem a = some q) : q < 2^64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hq⟩ := read64_bytes_eg4 mem a q h
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  omega

/-- The `c60` load value `sign_extend (b7 ++ … ++ b0)` equals `ofNat q` when the eight
loaded bytes are the LE bytes of `read64 mem a = some q`. -/
theorem ld_value_eq_read64 (mem : Mem) (a q : Nat)
    (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h : read64 mem a = some q)
    (e0 : mem[a]? = some b0) (e1 : mem[a+1]? = some b1) (e2 : mem[a+2]? = some b2)
    (e3 : mem[a+3]? = some b3) (e4 : mem[a+4]? = some b4) (e5 : mem[a+5]? = some b5)
    (e6 : mem[a+6]? = some b6) (e7 : mem[a+7]? = some b7) :
    (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, f0, f1, f2, f3, f4, f5, f6, f7, hq⟩ :=
    read64_bytes_eg4 mem a q h
  have hb0 : b0 = c0 := by rw [e0] at f0; injection f0
  have hb1 : b1 = c1 := by rw [e1] at f1; injection f1
  have hb2 : b2 = c2 := by rw [e2] at f2; injection f2
  have hb3 : b3 = c3 := by rw [e3] at f3; injection f3
  have hb4 : b4 = c4 := by rw [e4] at f4; injection f4
  have hb5 : b5 = c5 := by rw [e5] at f5; injection f5
  have hb6 : b6 = c6 := by rw [e6] at f6; injection f6
  have hb7 : b7 = c7 := by rw [e7] at f7; injection f7
  subst hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  rw [sext64_id_eg4]
  apply BitVec.eq_of_toNat_eq
  rw [word8_recon_eg4, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (read64_lt_eg4 mem a q h), ← hq]

end Vsa.Sim

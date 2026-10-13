import VsaIris.Vsa.HeapShape
import VsaIris.Vsa.RunBase

/-!
# Small pieces the ported dlmalloc proofs use from WHILE-tainted modules

Declarations copied verbatim from ship-your-interpreter (lane F1-A0-M,
ATTRIBUTION.md) out of modules that are not ported: `physSize`
(`Vsa/AllocResource.lean`), `read64_lt` (`Vsa/Sim/ValueEqualSpec2.lean`), `roundUp16` (`Vsa/While/Cost.lean`, renamed into
`VsaIris.VsaHeap`), the `malloc`/`free` entries (`Vsa/Alloc.lean`, at the Lua
ELF's addresses), and from the WHILE-address fast-path files
`VsaIris/Vsa/MallocFast{Segs,Chain,Heap}.lean`: `and_high_toNat`,
`stackBase`, `or_one_even`, `ChunkWalk.extend`. The term-level census
(`experiments/port/term/term_census.py closure` over `MallocRunAll` and
`FreeRunAll`) lists exactly these as the constants the allocator proofs reach
in those modules.
-/

namespace Vsa.Sim

def physSize (n : Nat) : Nat := max 32 (16 * ((n + 8 + 15) / 16))

theorem physSize_mono {m n : Nat} (h : m ≤ n) : physSize m ≤ physSize n := by
  unfold physSize
  omega

theorem physSize_min (n : Nat) : 32 ≤ physSize n := Nat.le_max_left _ _

open Vsa.MemRepr in
theorem ld_recon_lt (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (p : Nat)
    (hrec : b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
      (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = p) :
    p < 2 ^ 64 := by have := b7.isLt; omega

open Vsa.MemRepr in
theorem read64_lt (m0 : Mem) (a p : Nat) (h : read64 m0 a = some p) : p < 2 ^ 64 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, _, _, _, _, _, _, _, _, hrec⟩ := read64_bytes m0 a p h
  exact ld_recon_lt b0 b1 b2 b3 b4 b5 b6 b7 p hrec

end Vsa.Sim

namespace Vsa.Alloc

/-- `malloc`'s entry in the Lua ELF (`mv a1,a0; ld a0,_impure_ptr; j _malloc_r`). -/
def mallocEntry : Nat := 0x8002fa1c

/-- `free`'s entry in the Lua ELF. -/
def freeEntry : Nat := 0x8002fa28

end Vsa.Alloc

namespace VsaIris.VsaHeap

def roundUp16 (n : Nat) : Nat := (n + 15) / 16 * 16

end VsaIris.VsaHeap

namespace VsaIris.MallocFast

open Vsa.Sim Vsa.MemRepr Vsa.Sim.DlHeap
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem and_high_toNat (a : BitVec 64) (k : Nat) (hk : k < 64) :
    (a &&& (BitVec.allOnes 64 <<< k)).toNat = a.toNat / 2 ^ k * 2 ^ k := by
  have hshift : (a &&& (BitVec.allOnes 64 <<< k)) = (a >>> k) <<< k := by
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < k
    · simp [hi]
    · by_cases hlt : i < 64
      · have h3 : k + (i - k) = i := by omega
        have h2 : i - k < 64 := by omega
        simp [hi, hlt, h2, h3]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp [hi, hlt, hge]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  calc a.toNat / 2 ^ k * 2 ^ k ≤ a.toNat := Nat.div_mul_le_self _ _
    _ < 2 ^ 64 := a.isLt

def stackBase (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) : Mem :=
  (List.range len).foldl (fun m k => m.insert (lo + k) (f (lo + k))) m

theorem stackBase_get (m : Mem) (lo len : Nat) (f : Nat → BitVec 8) (a : Nat) :
    (stackBase m lo len f)[a]? = if lo ≤ a ∧ a < lo + len then some (f a) else m[a]? := by
  unfold stackBase
  induction len generalizing a with
  | zero => simp only [List.range_zero, List.foldl_nil]; rw [ite_eq_right (by omega)]
  | succ len ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Std.ExtHashMap.getElem?_insert]
    by_cases h : lo + len = a
    · subst h; simp
    · rw [ite_eq_right (by simpa using h), ih]
      by_cases h2 : lo ≤ a ∧ a < lo + len
      · rw [ite_eq_left h2, ite_eq_left ⟨h2.1, by omega⟩]
      · rw [ite_eq_right h2, ite_eq_right (by omega)]

theorem or_one_even (x : BitVec 64) (h : x.toNat % 2 = 0) :
    x ||| sign_extend (m := 64) (0x001#12) = x + 1#64 := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 by decide]
  refine (BitVec.add_eq_or_of_and_eq_zero x 1#64 ?_).symm
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 by decide,
    Nat.and_two_pow_sub_one_eq_mod]
  simpa using h

end VsaIris.MallocFast

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.extend {m m' : Mem} {p top top' : Nat}
    {cs ds : List Chunk} (h : ChunkWalk m p top cs)
    (hdr : ∀ c ∈ cs, read64 (m') (c.addr + 8) = read64 m (c.addr + 8))
    (htop : ∀ h1, read64 m (top + 8) = some h1 →
      ∃ h2, read64 (m') (top + 8) = some h2 ∧ prevInuse h2 = prevInuse h1)
    (hds : ChunkWalk (m') top top' ds) : ChunkWalk (m') p top' (cs ++ ds) := by
  induction h with
  | top => exact hds
  | @chunk p top hh h' cs hh0 hlow hmin hal hn rest ih =>
    have hp : read64 (m') (p + 8) = some hh := by
      rw [hdr _ List.mem_cons_self]; exact hh0
    have ih' := ih (fun c hc => hdr c (List.mem_cons_of_mem _ hc)) htop hds
    rcases rest.head_or_top with he | ⟨c, hc, hca⟩
    · obtain ⟨h2, hr2, hpi⟩ := htop h' (he ▸ hn)
      have w := ChunkWalk.chunk (m := m') hp hlow hmin hal (he ▸ hr2) ih'
      rw [hpi] at w
      exact w
    · have hn' : read64 (m') (p + chunkSize hh + 8) = some h' := by
        rw [← hca, hdr c (List.mem_cons_of_mem _ hc), hca]; exact hn
      exact ChunkWalk.chunk hp hlow hmin hal hn' ih'

theorem _root_.Vsa.Sim.DlHeap.ChunkWalk.append_inv {m : Mem} {cs ds : List Chunk} :
    ∀ {p top : Nat}, ChunkWalk m p top (cs ++ ds) →
      ∃ mid, ChunkWalk m p mid cs ∧ ChunkWalk m mid top ds := by
  induction cs with
  | nil => intro p top h; exact ⟨p, .top, h⟩
  | cons c cs ih =>
    intro p top h
    cases h with
    | chunk hh hlow hmin hal hn rest =>
      obtain ⟨mid, h1, h2⟩ := ih rest
      exact ⟨mid, .chunk hh hlow hmin hal hn h1, h2⟩

end VsaIris.VsaHeap

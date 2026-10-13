import VsaIris.Vsa.MallocBlocks2

namespace VsaIris.VsaHeap

open Vsa.MemRepr Vsa.Sim Vsa.Sim.DlHeap VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

theorem mHeap_entry {C : MCtx} {m1 : Mem} {s : BitVec 64} {mv : Nat → BitVec 8} {brkv : Nat}
    {chunks : List Chunk} {bins : Nat → List Nat} (hs0 : C.s = s) (hMt : C.Mt0 = mt0 m1 s mv)
    (hsp : SpOKA s) (him : ImgOn (vsaFoot C.H) mv m1)
    (hheap : PHeapAt m1 C.H C.top0 brkv chunks bins)
    (hdisj : ∀ a, stackWin s allocHeadroom a → ¬ vsaFoot C.H a) (hb0 : C.brk0 = brkv) :
    MHeap C C.Mt0 brkv chunks bins := by
  subst hs0
  have hs : 512 ≤ C.s.toNat := by
    have := hsp.lo; unfold allocHeadroom Vsa.Sim.tohostAddr at this; omega
  have hag : ∀ a, vsaFoot C.H a → C.Mt0[a]? = m1[a]? := by
    intro a ha
    rw [hMt]; unfold mt0
    rw [stackBase_get, ite_eq_right_iff.2 fun h => absurd ha (hdisj a ⟨h.1, by simp only; omega⟩)]
  have H0 := hheap.transport_read (m' := C.Mt0) fun a ha => (hag a ha.1).symm
  refine ⟨H0, fun a ha => by
    rw [hag a ha, him a ha]; rfl, fun a h1 h2 hf => hdisj a ?_ hf, fun a _ => rfl, LiveKeep.of_heap H0,
    ⟨by omega, .inl hb0.symm⟩⟩
  unfold mHead at h1
  refine ⟨?_, ?_⟩ <;> simp only [allocHeadroom]
  · exact Nat.le_trans (Nat.sub_le_sub_left (by decide : 256 ≤ 512) _) h1
  · rw [Nat.sub_add_cancel hs]; exact h2

end VsaIris.VsaHeap

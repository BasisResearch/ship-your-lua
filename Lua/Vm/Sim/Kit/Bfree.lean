import Lua.Vm.AtF.Bfree.Runs
import Lua.Vm.AtF.BfreeNull.Runs
import Lua.Vm.EntryData
import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.AllocHeap
import Vsa.Sim.Generic.MemRead

/-!
# newlib `_Bfree` (`0x8003d700`, nine instructions)

The two runs are generated callee-context paths. NULL does not read memory.
A non-NULL block is pushed into `_freelist[k]`: first its next pointer is
written, then the class slot. No allocator call occurs. The exact memory
and its presence frame are exposed for the bignum ownership proof.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.Sim.AtF
open Vsa.Machine (Config Steps)

/-- The non-NULL branch's address and load obligations. The freelist array
and block header are apart; the class is one of newlib's 65 slots. -/
structure BfreePushIn (reent b fl k : Nat) (head : BitVec 64) (m : Mem) : Prop where
  r_lo : 0x8005c6d0 ≤ reent
  r_hi : reent + 112 ≤ 2 ^ 32
  r_al : reent % 8 = 0
  b_lo : 0x8006ecd0 ≤ b
  b_hi : b + 16 ≤ 2 ^ 32
  b_al : b % 8 = 0
  fl_lo : 0x8006ecd0 ≤ fl
  fl_hi : fl + 520 ≤ 2 ^ 32
  fl_al : fl % 8 = 0
  k_hi : k ≤ 64
  apart : b + 16 ≤ fl ∨ fl + 520 ≤ b
  cls : bytesT4 m (b + 8) = BitVec.ofNat 32 k
  freelist : bytesT8 m (reent + reentFreelistOff) = BitVec.ofNat 64 fl
  slot : bytesT8 m (fl + 8 * k) = head

/-- `_Bfree`'s input. NULL requires no memory or pointer premise. -/
structure BfreeIn (sp reent b fl k : Nat) (r : BitVec 64) (head : BitVec 64) (m : Mem) : Prop where
  sp_hi : sp ≤ 2 ^ 32
  ra : r.toNat % 4 = 0
  push : b ≠ 0 → BfreePushIn reent b fl k head m

/-- The two writes, in instruction order, or the identity for NULL. -/
def bfreeMem (m : Mem) (b fl k : Nat) (head : BitVec 64) : Mem :=
  if b = 0 then m else
    writeMap8 (writeMap8 m b (sdData_val head)) (fl + 8 * k) (sdData_val (BitVec.ofNat 64 b))

/-- The exact presence frame of `_Bfree`. -/
theorem bfreeMem_keep (m : Mem) (b fl k a : Nat) (head : BitVec 64)
    (hb : a < b ∨ b + 8 ≤ a) (hs : a < fl + 8 * k ∨ fl + 8 * k + 8 ≤ a) :
    (bfreeMem m b fl k head)[a]? = m[a]? := by
  unfold bfreeMem
  split
  · rfl
  · rw [getElem?_writeMap8_out _ _ _ _ hs, getElem?_writeMap8_out _ _ _ _ hb]

/-- The pushed block points to the old head and becomes the new slot head. -/
theorem bfreeMem_push {m : Mem} {reent b fl k : Nat} {head : BitVec 64}
    (h : BfreePushIn reent b fl k head m) :
    bytesT8 (bfreeMem m b fl k head) b = head ∧
      bytesT8 (bfreeMem m b fl k head) (fl + 8 * k) = BitVec.ofNat 64 b := by
  have hb : b ≠ 0 := by have := h.b_lo; omega
  simp only [bfreeMem, if_neg hb]
  constructor
  · rw [fw8_wm8 (by have := h.apart; have := h.k_hi; omega), bytesT8_writeMap8, sdData_id]
  · rw [bytesT8_writeMap8, sdData_id]

/-- ABI return, exact post-memory, and the two observable links. -/
structure BfreePost (sp b fl k : Nat) (r head : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (c : Config) : Prop where
  ret : SegSt r (callPre [] sp r f) (ArmPay (bfreeMem m b fl k head) o) c
  keep : ∀ a, (a < b ∨ b + 8 ≤ a) → (a < fl + 8 * k ∨ fl + 8 * k + 8 ≤ a) →
    (bfreeMem m b fl k head)[a]? = m[a]?
  null : b = 0 → bfreeMem m b fl k head = m
  next : b ≠ 0 → bytesT8 (bfreeMem m b fl k head) b = head
  slot : b ≠ 0 → bytesT8 (bfreeMem m b fl k head) (fl + 8 * k) = BitVec.ofNat 64 b

@[at_row] abbrev bfCx (sp reent b fl k : Nat) (r head : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) : FCx :=
  FCx.mk' [sp, reent, b, fl, k]
    [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, head] m o

/-- `_Bfree` on both branches: a generated run, preserving the ABI frame
and console, with exactly the two non-NULL stores. -/
theorem bfree_sum (sp reent b fl k : Nat) (r head : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (hx : BfreeIn sp reent b fl k r head m) :
    Triple (SegSt 0x8003d700#64 (callPre [⟨Register.x10, BitVec.ofNat 64 reent⟩,
        ⟨Register.x11, BitVec.ofNat 64 b⟩] sp r f) (ArmPay m o))
      (BfreePost sp b fl k r head f m o) := by
  intro c h
  simp only [callPre, List.cons_append, List.nil_append] at h
  have hs := hx.sp_hi
  have hr := hx.ra
  let X := bfCx sp reent b fl k r head f m o
  by_cases hb : b = 0
  · subst b
    have hX : Lua.Vm.AtF.BfreeNull.Ok X := by fcx_ok
    obtain ⟨c', acc, hout⟩ := Lua.Vm.AtF.BfreeNull.Runs.run_null X hX c (by
      dsimp only [X]; fcx_unfold
      exact h.repin (by pins_of h))
    dsimp only [X] at hout
    fcx_unfold at hout
    refine ⟨c', acc, ?_⟩
    refine ⟨?_, (fun a => bfreeMem_keep m 0 fl k a head), ?_, fun hn => False.elim (hn rfl),
      fun hn => False.elim (hn rfl)⟩
    · simp only [bfreeMem, ↓reduceIte, callPre, List.nil_append]
      exact hout.repin (by pins_of hout)
    · intro _; simp only [bfreeMem, ↓reduceIte]
  · have hp := hx.push hb
    have hX : Lua.Vm.AtF.Bfree.Ok X := by
      rcases hp with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -, -, -, -⟩
      fcx_ok
    obtain ⟨c', acc, hout⟩ := Lua.Vm.AtF.Bfree.Runs.run_push X hX hp.cls hp.freelist hp.slot c
      (by dsimp only [X]; fcx_unfold; exact h.repin (by pins_of h))
    dsimp only [X] at hout
    fcx_unfold at hout
    refine ⟨c', acc, ?_⟩
    refine ⟨?_, (fun a => bfreeMem_keep m b fl k a head), fun hz => absurd hz hb,
      fun _ => (bfreeMem_push hp).1, fun _ => (bfreeMem_push hp).2⟩
    simp only [bfreeMem, if_neg hb, callPre, List.nil_append]
    exact hout.repin (by pins_of hout)

/-- An owned block to return, apart from the existing chain and its
freelist array. The header contains the class and capacity set by `_Balloc`. -/
structure BfreeOwned (m : Mem) (b fl k : Nat) (bs : List (Nat × Nat)) : Prop where
  cls : rd32 m (b + 8) = some k
  maxwds : rd32 m (b + 12) = some (2 ^ k)
  block_apart : ∀ x ∈ bs, Apart b (bigSize k) x.1 (bigSize x.2)
  array_apart : ∀ x ∈ bs, Apart fl 520 x.1 (bigSize x.2)

/-- The non-NULL branch preserves a word read outside its two stores. -/
theorem bfree_rdLE_keep {m : Mem} {b fl k a n : Nat} {head : BitVec 64}
    (hb : a + n ≤ b ∨ b + 8 ≤ a) (hs : a + n ≤ fl + 8 * k ∨ fl + 8 * k + 8 ≤ a) :
    rdLE (bfreeMem m b fl k head) a n = rdLE m a n :=
  rdLE_congr fun i hi => bfreeMem_keep m b fl k (a + i) head (by omega) (by omega)

/-- The actual stores implement a chain push, including the capacity and
class of every old node, when the returned block is separately owned. -/
theorem bfree_chain {m : Mem} {reent b fl k : Nat} {head : BitVec 64} {bs : List (Nat × Nat)}
    (hp : BfreePushIn reent b fl k head m) (ho : BfreeOwned m b fl k bs)
    (hc : BigChain m head.toNat bs) : BigChain (bfreeMem m b fl k head) b ((b, k) :: bs) := by
  have hb : b ≠ 0 := by have := hp.b_lo; omega
  have ha := hp.apart
  have hk := hp.k_hi
  have hnext : rd64 (bfreeMem m b fl k head) b = some head.toNat := by
    unfold bfreeMem
    rw [if_neg hb]
    rw [show rd64 (writeMap8 (writeMap8 m b (sdData_val head)) (fl + 8 * k)
          (sdData_val (BitVec.ofNat 64 b))) b = rd64 (writeMap8 m b (sdData_val head)) b from
      rdLE_congr fun i hi => getElem?_writeMap8_out _ _ _ _ (by omega)]
    rw [AllocHeap.rd64_eq, read64_writeMap8, sdData_toNat]
  have cls : rd32 (bfreeMem m b fl k head) (b + 8) = some k :=
    (bfree_rdLE_keep (by omega) (by omega)).trans ho.cls
  have maxwds : rd32 (bfreeMem m b fl k head) (b + 12) = some (2 ^ k) :=
    (bfree_rdLE_keep (by omega) (by omega)).trans ho.maxwds
  refine .cons hb hnext cls maxwds hk (hc.congr fun x hx => ?_)
  have hb' := ho.block_apart x hx
  have hf' := ho.array_apart x hx
  simp only [Apart, bigSize] at hb' hf'
  refine ⟨bfree_rdLE_keep (by omega) (by omega),
    bfree_rdLE_keep (by omega) (by omega), bfree_rdLE_keep (by omega) (by omega)⟩

end Lua.Vm.Sim.Kit

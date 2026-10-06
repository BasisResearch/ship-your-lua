import Lua.Vm.Sim.Kit.Stdio
import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.AtF.Memmove

/-!
# `memmove(dst, src, n)` on disjoint ranges (lane F1-8)

`__sfvwrite_r` copies the bytes `print` writes into `stdout`'s buffer with
`memmove` (`0x8003b444`). Its at-lemmas are generated
(`Lua/Vm/AtF/Memmove.lean`, `scripts/gen_lua_at.py --fn memmove`): the entry's
paths, and each of its three copy loops as a root (bytes; 32-byte blocks;
words). This file runs each loop by `seg_loop` with the copy so far as the
invariant (`MoveOut`), and joins them at their arrivals.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-! ## The copy so far -/

/-- **`t` bytes copied** from `S` to `D` over `m`: the moved bytes, and
everything outside `[D, D + t)` as in `m`. -/
structure MoveOut (m M : Mem) (D S t : Nat) : Prop where
  moved : ∀ i, i < t → bytesT1 M (D + i) = bytesT1 m (S + i)
  keep : ∀ a, (a < D ∨ D + t ≤ a) → M[a]? = m[a]?

theorem MoveOut.zero (m : Mem) (D S : Nat) : MoveOut m m D S 0 :=
  ⟨fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- A read outside the copied range. -/
theorem MoveOut.rd1 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a < D ∨ D + t ≤ a) :
    bytesT1 M a = bytesT1 m a := bT1_congr (h.keep a ha)

theorem MoveOut.rd8 {m M : Mem} {D S t a : Nat} (h : MoveOut m M D S t) (ha : a + 8 ≤ D ∨ D + t ≤ a) :
    bytesT8 M a = bytesT8 m a := bT8_congr fun _ _ => h.keep _ (by omega)

/-- The byte lanes of two equal words (in two memories). -/
theorem lanes8 {m1 m2 : Mem} {a b : Nat} (h : bytesT8 m1 a = bytesT8 m2 b) :
    ∀ k, k < 8 → bytesT1 m1 (a + k) = bytesT1 m2 (b + k) := by
  intro k hk
  simp only [bytesT8] at h
  obtain ⟨h, h0⟩ := append_inj' h
  obtain ⟨h, h1⟩ := append_inj' h
  obtain ⟨h, h2⟩ := append_inj' h
  obtain ⟨h, h3⟩ := append_inj' h
  obtain ⟨h, h4⟩ := append_inj' h
  obtain ⟨h, h5⟩ := append_inj' h
  obtain ⟨h7, h6⟩ := append_inj' h
  simp only [bytesT1]
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simpa

/-- `sb` of a loaded byte (`lbu`'s zero extension, then the low byte). -/
theorem stData_zext (b : BitVec 8) : stData 1 (zero_extend (m := 64) (b : BitVec (8 * 1))) = b := by
  revert b; decide

/-- One byte more. -/
theorem MoveOut.ins {m M : Mem} {D S t a : Nat} {b : BitVec 8} (h : MoveOut m M D S t) (ha : a = D + t)
    (hb : b = bytesT1 m (S + t)) : MoveOut m (M.insert a b) D S (t + 1) := by
  subst ha hb
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · by_cases e : i = t
    · subst e; exact fw1_same rfl
    · rw [fw1_ins (by omega)]; exact h.moved i (by omega)
  · rw [ins_out _ _ _ _ (by omega)]; exact h.keep x (by omega)

/-- One word more. -/
theorem MoveOut.wm8 {m M : Mem} {D S t a : Nat} {v : BitVec 64} (h : MoveOut m M D S t) (ha : a = D + t)
    (hv : v = bytesT8 m (S + t)) : MoveOut m (writeMap8 M a (sdData_val v)) D S (t + 8) := by
  subst ha hv
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · by_cases e : i < t
    · rw [fw1_wm8 (by omega)]; exact h.moved i e
    · have := lanes8 (fw8_same (m := M) (a := D + t) (x := D + t) (v := bytesT8 m (S + t)) rfl) (i - t) (by omega)
      rwa [show D + t + (i - t) = D + i by omega, show S + t + (i - t) = S + i by omega] at this
  · rw [getElem?_writeMap8_out _ _ _ _ (by omega)]; exact h.keep x (by omega)

/-- The copy's end: `n` bytes copied, the memory equal off `[D, D + n)`. -/
theorem MoveOut.mono {m M : Mem} {D S t t' : Nat} (h : MoveOut m M D S t) (e : t = t') : MoveOut m M D S t' :=
  e ▸ h

/-! ## The return -/

/-- `memmove`'s return: `a0 = dst`, `sp`, `gp` and the caller's frame. -/
abbrev mmRet (r : BitVec 64) (sp : Nat) (a0 : BitVec 64) (f : AbiFrame) (M : Mem) (o : Array String) :
    Config → Prop :=
  SegSt r (⟨Register.x10, a0⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ ::
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩ :: f.pins) (ArmPay M o)

/-- A context of `memmove`'s rows: `sp`, the Nat atoms, `ra`, the frame, `a0`. -/
@[at_row] abbrev mmCx (ns : List Nat) (r : BitVec 64) (f : AbiFrame) (a0 : BitVec 64) (M : Mem) (o : Array String) :
    FCx :=
  FCx.mk' ns [r, f.s0, f.s1, f.s2, f.s3, f.s4, f.s5, f.s6, f.s7, f.s8, f.s9, f.s10, f.s11, a0] M o

/-- The ranges of a copy phase: `[d, d + k)` and `[s, s + k)` apart, in RAM,
off `tohost`. -/
structure MmSpan (d s k : Nat) : Prop where
  d_lo : 0x8005c6d0 ≤ d
  s_lo : 0x80000000 ≤ s
  disj : d + k ≤ s ∨ s + k ≤ d
  d_hi : d + k ≤ 2 ^ 32
  s_hi : s + k ≤ 2 ^ 32
  s_th : s + k ≤ 0x8005c6c0 ∨ 0x8005c6c8 ≤ s

/-! ## The byte loop (`0x8003b48c`) -/

/-- **The byte loop** from `i` of `k` bytes copied (the phase's bases `d = D + T`,
`s = S + T`): the rest copied, then the return. -/
theorem mm_bytes (sp d s k D S T : Nat) (r a0 : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hd : d = D + T) (hs : s = S + T) (hk : MmSpan d s k) (hsp : sp ≤ 2 ^ 32) (hra : r.toNat % 4 = 0)
    (hsd : S + (T + k) ≤ D ∨ D + (T + k) ≤ S) :
    ∀ i M, i < k → MoveOut m M D S (T + i) →
      Triple (SegSt 0x8003b48c#64 (Lua.Vm.AtF.Memmove.r10 (mmCx [sp, d, s, k, i] r f a0 M o))
          (ArmPay (mmCx [sp, d, s, k, i] r f a0 M o).m (mmCx [sp, d, s, k, i] r f a0 M o).o))
        (fun c => ∃ M', mmRet r sp a0 f M' o c ∧ MoveOut m M' D S (T + k)) := by
  intro i₀ M₀ hi₀ hM₀ c₀ h₀
  have := hk.d_lo; have := hk.s_lo; have := hk.disj; have := hk.d_hi; have := hk.s_hi; have := hk.s_th
  refine seg_loop (S := fun (p : Nat × Mem) c => p.1 < k ∧ MoveOut m p.2 D S (T + p.1) ∧
      SegSt 0x8003b48c#64 (Lua.Vm.AtF.Memmove.r10 (mmCx [sp, d, s, k, p.1] r f a0 p.2 o))
        (ArmPay (mmCx [sp, d, s, k, p.1] r f a0 p.2 o).m (mmCx [sp, d, s, k, p.1] r f a0 p.2 o).o) c)
    (fun p => k - p.1) (fun ⟨i, M⟩ c ⟨hi, hM, h⟩ => ?_) (i₀, M₀) c₀ ⟨hi₀, hM₀, h₀⟩
  have hX : Lua.Vm.AtF.Memmove.Ok_B (mmCx [sp, d, s, k, i] r f a0 M o) :=
    ⟨hk.d_lo, hk.s_lo, hsp, hra, hk.disj, hk.d_hi, hk.s_hi, hk.s_th, hi⟩
  have acc := Steps.refl c
  -- the byte read is the source's
  have hb : bytesT1 M (s + i) = bytesT1 m (S + (T + i)) := by
    rw [hM.rd1 (by omega), hs, Nat.add_assoc]
  have hM' := hM.ins (a := d + i) (b := bytesT1 m (S + (T + i))) (by omega) rfl
  by_cases he : i + 1 = k
  · fat_run Lua.Vm.AtF.Memmove h acc
    fcx_unfold at h
    rw [hb, stData_zext] at h
    exact ⟨_, acc, .inr ⟨_, h.repin (by pins_of h), hM'.mono (by omega)⟩⟩
  · fat_run Lua.Vm.AtF.Memmove h acc until [0x8003b48c]
    fcx_unfold at h
    rw [hb, stData_zext] at h
    refine ⟨_, acc, .inl ⟨(i + 1, _), by simp only; omega, by simp only; omega, hM'.mono (by omega), ?_⟩⟩
    fcx_unfold
    exact h.repin (by pins_of h)

end Lua.Vm.Sim.Kit

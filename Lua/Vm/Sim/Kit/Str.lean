import Lua.Vm.Sim.Kit.Scan
import Lua.Vm.Sim.Entry

/-!
# Live string facts (round-4 bake-off, S-SCAN: M-str)

`ValRepr.str` describes a register's string in the complement memory `w.mo`
only (`TStringRepr`, partial reads). The string callees (`luaS_eqlngstr`,
`memcmp`, `l_strcmp`, `strcmp`, `strlen`) read the live memory with total
reads. This file moves the facts across once:

* **The footprint, per variant** (`StrFoot`): what the callees read of a
  `TString` (`TStringRepr`'s read list): `shrlen` at `+11`, a long string's
  `lnglen` at `+16..23` (a short string's `+16` is `hnext`, written by the
  string table, and not in its footprint), the contents and the terminator.
* **The view** (`StrView`): those reads, total, plus the object's bounds.
  `TStringRepr.view` builds it in `w.mo`; `StrView.frame` carries it to any
  memory that agrees on the footprint.
* **Unsealing** (`Core.unseal`): a register's or constant's owned string
  object (`StrOwned`, BASE-S) is outside the window, so any memory that
  agrees with the machine's outside the window (an arm's run to a call:
  `savestate`, callee frames) holds the view, and the object lies apart from
  the C stack below `sp` (`StrApart`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config Steps)

/-- **The footprint of a string object, per variant**: the bytes the string
callees read. -/
def StrFoot (ts : Nat) (s : List UInt8) (x : Nat) : Prop :=
  x = ts + tstringShrlenOff ∨
  (maxShortLen < s.length ∧ ts + tstringLnglenOff ≤ x ∧ x < ts + tstringLnglenOff + 8) ∨
  (ts + tstringContentsOff ≤ x ∧ x ≤ ts + tstringContentsOff + s.length)

/-- **The live view of a string object**: its footprint as total reads, and
its bounds (in RAM, apart from `tohost`). -/
structure StrView (m : Mem) (ts : Nat) (s : List UInt8) : Prop where
  lo : tohostAddr + 16 ≤ ts
  hi : ts + tstringContentsOff + s.length + 1 ≤ DlHeap.heapEnd + 8
  bytes : ∀ i (h : i < s.length),
    bytesT1 m (ts + tstringContentsOff + i) = BitVec.ofNat 8 (s[i]'h).toNat
  term : bytesT1 m (ts + tstringContentsOff + s.length) = 0#8
  shrlen : bytesT1 m (ts + tstringShrlenOff) =
    if maxShortLen < s.length then 0xFF#8 else BitVec.ofNat 8 s.length
  lnglen : maxShortLen < s.length → bytesT8 m (ts + tstringLnglenOff) = BitVec.ofNat 64 s.length

theorem bytesT1_of_some {m : Mem} {a : Nat} {b : BitVec 8} (h : m[a]? = some b) : bytesT1 m a = b := by
  simp [bytesT1, h]

/-- The view in the memory `TStringRepr` describes. -/
theorem _root_.Lua.Vm.TStringRepr.view {m : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr m ts s)
    (hlo : tohostAddr + 16 ≤ ts) (hhi : ts + tstringContentsOff + s.length + 1 ≤ DlHeap.heapEnd + 8) :
    StrView m ts s := by
  cases h with
  | short _ hl hsh hb ht =>
    refine ⟨hlo, hhi, fun i hi => bytesT1_of_some (hb i hi), bytesT1_of_some ht, ?_, fun h => ?_⟩
    · rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), bytesT1_of_rd8 hsh]
    · exact absurd h (by omega)
  | long _ hl hlen hb ht hsh =>
    refine ⟨hlo, hhi, fun i hi => bytesT1_of_some (hb i hi), bytesT1_of_some ht, ?_, fun _ => ?_⟩
    · rw [bytesT1_of_rd8 hsh]; simp only [hl, ite_true]
    · exact bytesT8_of_rd64 hlen

/-- **The view travels with the footprint.** -/
theorem StrView.frame {m m' : Mem} {ts : Nat} {s : List UInt8} (h : StrView m ts s)
    (hf : ∀ x, StrFoot ts s x → bytesT1 m' x = bytesT1 m x) : StrView m' ts s where
  lo := h.lo
  hi := h.hi
  bytes i hi := (hf _ (.inr (.inr ⟨by omega, by omega⟩))).trans (h.bytes i hi)
  term := (hf _ (.inr (.inr ⟨by omega, by omega⟩))).trans h.term
  shrlen := (hf _ (.inl rfl)).trans h.shrlen
  lnglen hl := (bytesT8_congrT fun i hi => hf _ (.inr (.inl ⟨hl, by omega, by omega⟩))).trans (h.lnglen hl)

/-- The object `[ts, ts + 24 + |s| + 1)` lies apart from `[lo, hi)`. -/
def StrApart (ts : Nat) (s : List UInt8) (lo hi : Nat) : Prop :=
  ts + tstringContentsOff + s.length + 1 ≤ lo ∨ hi ≤ ts

/-- A store in `[a, a + 8)` inside `[lo, hi)` misses an object apart from it. -/
theorem StrView.wm8 {m : Mem} {ts : Nat} {s : List UInt8} (h : StrView m ts s) {lo hi a : Nat}
    (hap : StrApart ts s lo hi) (h1 : lo ≤ a) (h2 : a + 8 ≤ hi) (d : BitVec (8 * 8)) :
    StrView (writeMap8 m a d) ts s :=
  h.frame fun x hx => by
    simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff, StrApart] at hx hap
    exact bytesT1_writeMap8_out m a d (by omega)

/-- The view in any memory that agrees with `m` outside `[lo, hi)`. -/
theorem StrView.agree {m m' : Mem} {ts : Nat} {s : List UInt8} (h : StrView m ts s) {lo hi : Nat}
    (hap : StrApart ts s lo hi) (ha : AgreeOut m' m lo hi) : StrView m' ts s :=
  h.frame fun x hx => by
    simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff, StrApart] at hx hap
    simp only [bytesT1, ha x (by omega)]

/-! ## The allocator's chunks lie in the heap -/

theorem _root_.Lua.Vm.DlHeap.ChunkWalk.le {m : Mem} :
    ∀ {p top : Nat} {cs : List DlHeap.Chunk}, DlHeap.ChunkWalk m p top cs → p ≤ top
  | _, _, _, .top => Nat.le_refl _
  | _, _, _, .chunk _ _ _ _ _ hw => by have := DlHeap.ChunkWalk.le hw; omega

theorem _root_.Lua.Vm.DlHeap.ChunkWalk.bound {m : Mem} :
    ∀ {p top : Nat} {cs : List DlHeap.Chunk}, DlHeap.ChunkWalk m p top cs →
      ∀ c ∈ cs, p ≤ c.addr ∧ c.addr + c.size ≤ top
  | _, _, _, .top => fun _ h => absurd h List.not_mem_nil
  | _, _, _, .chunk _ _ _ _ _ hw => fun c hc => by
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ⟨Nat.le_refl _, DlHeap.ChunkWalk.le hw⟩
    · have := DlHeap.ChunkWalk.bound hw c hc; omega

/-- A byte of a string, as the machine reads it, determines the byte. -/
theorem u8_ofNat_inj {a b : UInt8} (h : BitVec.ofNat 8 a.toNat = BitVec.ofNat 8 b.toNat) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt a.toNat_lt, Nat.mod_eq_of_lt b.toNat_lt] at this
  exact UInt8.toNat_inj.1 this

/-- **Two viewed strings of one length are equal iff their contents agree
byte for byte** (what `memcmp` decides). -/
theorem StrView.eq_iff {m : Mem} {t1 t2 : Nat} {s1 s2 : List UInt8} (h1 : StrView m t1 s1)
    (h2 : StrView m t2 s2) (hl : s1.length = s2.length) :
    s1 = s2 ↔ ∀ j, j < s1.length →
      bytesT1 m (t1 + tstringContentsOff + j) = bytesT1 m (t2 + tstringContentsOff + j) := by
  constructor
  · rintro rfl j hj; rw [h1.bytes j hj, h2.bytes j hj]
  · intro h
    refine List.ext_getElem hl fun j hj1 hj2 => u8_ofNat_inj ?_
    rw [← h1.bytes j hj1, ← h2.bytes j hj2]; exact h j hj1

/-- Two viewed long strings of different lengths have different `lnglen`s. -/
theorem StrView.lnglen_eq {m : Mem} {t1 t2 : Nat} {s1 s2 : List UInt8} (h1 : StrView m t1 s1)
    (h2 : StrView m t2 s2) (l1 : maxShortLen < s1.length) (l2 : maxShortLen < s2.length) :
    bytesT8 m (t1 + tstringLnglenOff) = bytesT8 m (t2 + tstringLnglenOff) ↔ s1.length = s2.length := by
  rw [h1.lnglen l1, h2.lnglen l2]
  have := h1.hi; have := h2.hi
  simp only [DlHeap.heapEnd, symHeapEnd, tstringContentsOff] at *
  constructor
  · intro e; have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  · intro e; rw [e]

/-- `StrApart` for a smaller interval. -/
theorem StrApart.mono {ts : Nat} {s : List UInt8} {lo hi lo' hi' : Nat} (h : StrApart ts s lo hi)
    (h1 : lo ≤ lo') (h2 : hi' ≤ hi) : StrApart ts s lo' hi' := by
  simp only [StrApart] at h ⊢; omega

/-- **A live string**: its view in `m`, and the object apart from `[lo, hi)`. -/
structure StrAt (m : Mem) (ts : Nat) (s : List UInt8) (lo hi : Nat) : Prop where
  view : StrView m ts s
  apart : StrApart ts s lo hi

theorem _root_.Lua.Vm.Sim.ValRepr.tsr {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64} {str : List UInt8}
    (h : ValRepr mo ι t x (.str str)) : TStringRepr mo x.toNat str := by
  cases h with
  | str hts _ _ => exact hts

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- An owned object lies in the heap `[_end, __heap_end)` (`HeapAt`'s walk). -/
theorem Complement.own_bounds (hc : Complement p w) {ts : Nat} {str : List UInt8}
    (ho : StrOwned p w ts str) :
    tohostAddr + 16 ≤ ts ∧ ts + tstringContentsOff + str.length + 1 ≤ DlHeap.heapEnd + 8 := by
  obtain ⟨ch, hch⟩ := ho
  have hh := hc.runtime.heap
  have hb := DlHeap.ChunkWalk.bound hh.walk ch hch.walk
  have := hh.top_le; have := hh.brk_le; have := hch.lo; have := hch.hi
  simp only [DlHeap.heapStart, symEnd] at hb
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  omega

/-- An owned object lies apart from the C stack the arms' callees use,
`[spEntry - cStackBudget, sp + execFrame)` (`Scratch` and `luaV_execute`'s
frame, both in the window). -/
theorem Ranges.own_apart (hr : Ranges p w) {ts : Nat} {str : List UInt8} (ho : StrOwned p w ts str) :
    StrApart ts str (RuntimeData.spEntry - cStackBudget) (w.sp + execFrame) := by
  have hout := ho.out
  have hsp := hr.sp_eq
  simp only [StrApart]
  by_cases h1 : ts < RuntimeData.spEntry - cStackBudget
  · left
    refine Nat.not_lt.1 fun h2 => hout (RuntimeData.spEntry - cStackBudget) (by omega) h2 ?_
    exact .inr (.inr (.inr (.inr ⟨Nat.le_refl _, by
      simp only [RuntimeData.spEntry, cStackBudget, execFrame] at hsp ⊢; omega⟩)))
  · right
    refine Nat.not_lt.1 fun h2 => hout ts (Nat.le_refl _) (by omega) ?_
    by_cases h3 : ts < w.sp
    · exact .inr (.inr (.inr (.inr ⟨by omega, h3⟩)))
    · exact .inr (.inl ⟨by omega, h2⟩)

/-- **Unsealing (M-str)**: an owned string object, described in the
complement, is viewed in any memory that agrees with the machine's outside
the window. -/
theorem Core.unseal (hc : Core p c s w) {ts : Nat} {str : List UInt8} (ho : StrOwned p w ts str)
    (hts : TStringRepr w.mo ts str) {m : Mem} (hm : ∀ x, ¬ Win p w x → m[x]? = c.σ.mem[x]?) :
    StrView m ts str := by
  obtain ⟨hlo, hhi⟩ := hc.comp.own_bounds ho
  refine (hts.view hlo hhi).frame fun x hx => ?_
  simp only [StrFoot, tstringShrlenOff, tstringLnglenOff, tstringContentsOff] at hx
  have hw := ho.out x (by omega) (by simp only [tstringContentsOff]; omega)
  simp only [bytesT1, hm x hw]
  exact hc.frame x hw


/-- **A represented string is live** (M-str), in any memory that agrees with
the machine's outside `Scratch` (an arm's run to a call). -/
theorem Core.str_at (hc : Core p c s w) {t : BitVec 8} {x : BitVec 64} {str : List UInt8}
    (hv : ValRepr w.mo w.ι t x (.str str)) {m : Mem} (hm : ∀ a, ¬ Scratch w a → m[a]? = c.σ.mem[a]?) :
    StrAt m x.toNat str (RuntimeData.spEntry - cStackBudget) (w.sp + execFrame) :=
  have ho := hv.owned hc.comp
  ⟨hc.unseal ho hv.tsr fun a ha => hm a fun h => ha (.inr (.inr h)), hc.ranges.own_apart ho⟩

end

end Lua.Vm.Sim

import Lua.Vm.Sim.Kit.TolStr
import Lua.Vm.Sim.Kit.PrintRel

/-!
# `TolStr_Statement` (lane F1-17)

`luaL_tolstring` on a string argument in `luaB_print`'s loop (`TolArg IsStr`),
from the machine runs of `Kit/TolStr.lean` (`tol_s_pre`/`tol_s_mid`/`tol_tail_s`
for a short string, `tol_l_*` for a long one) and `luaB_print`'s entry facts
(`PrintIn`).

The argument's string is read where it lies. `PrintIn` freezes the arguments
on the bytes the caller keeps (`G`) and their slots, so every byte the
string's representation pins is among them (`Frozen.mem_of_det`, `str_foot`):
the string's bytes are kept by the run (`notW_of_keep`), its contents are in
chunks in use (`PrintIn.args_heap` rules out the static image), and its
length is read off the representation at the tail's memory.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## A frozen fact pins the bytes it reads -/

/-- A stored byte is present in the fill. -/
theorem fill_insert_self (m : Mem) (a : Nat) (v : BitVec 8) : (fillZeroMem (m.insert a v))[a]? = some v := by
  rw [fillZeroMem_get]; split <;> simp

/-- **A frozen fact pins each byte it determines**: if every memory that
differs from `m` only at `a` and still satisfies `P` holds `w` there (in its
fill), then `a` is in the footprint. -/
theorem Frozen.mem_of_det {F : Nat → Prop} {P : Mem → Prop} {m : Mem} (h : Frozen F P m) {a : Nat}
    {w : BitVec 8} (hw : ∀ v : BitVec 8, P (m.insert a v) → (fillZeroMem (m.insert a v))[a]? = some w) : F a := by
  by_cases hn : F a
  · exact hn
  · have hP : P (m.insert a (w + 1#8)) := h _ fun b hb => by
      have : b ≠ a := fun e => hn (e ▸ hb)
      exact bT1_congr (ins_out m a _ b (by omega))
    have e := hw _ hP
    rw [fill_insert_self, Option.some.injEq] at e
    have e2 := congrArg BitVec.toNat e
    have := w.isLt
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at e2
    omega

/-- A represented string value's object and tag. -/
theorem _root_.Lua.Vm.Sim.ValRepr.str_repr {mo : Mem} {ι : Strs} {t : BitVec 8} {x : BitVec 64}
    {s : List UInt8} (h : ValRepr mo ι t x (.str s)) : TStringRepr mo x.toNat s ∧ t = BitVec.ofNat 8 (strTag s) := by
  cases h with
  | str hr _ _ => exact ⟨hr, rfl⟩

/-- A represented string's contents. -/
theorem _root_.Lua.Vm.TStringRepr.bytes {m : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr m ts s) :
    BytesAt m (ts + tstringContentsOff) s ∧ m[ts + tstringContentsOff + s.length]? = some 0 := by
  cases h with
  | short _ _ _ hb ht => exact ⟨hb, ht⟩
  | long _ _ _ hb ht _ => exact ⟨hb, ht⟩

/-- **The bytes an argument's string pins are frozen**: any byte at which
every representation of the string `s` at the argument's pointer holds the
same value lies in `PrintIn`'s footprint (the kept bytes `G` or the slots). -/
theorem str_foot {G : Nat → Prop} {func n : Nat} {ι : Strs} {args : List Value} {M : Mem}
    (hfz : Frozen (fun a => G a ∨ ArgSlot func n a) (ArgsAt func ι args) M) {i : Nat} {s : List UInt8}
    (hv : args[i]? = some (.str s)) (hi : i < n) {a : Nat} {w : BitVec 8}
    (hw : ∀ M', TStringRepr (fillZeroMem M') (slotVal M (func + 16 * (i + 1))).toNat s →
      (fillZeroMem M')[a]? = some w) : G a ∨ ArgSlot func n a := by
  by_cases ha : ArgSlot func n a
  · exact .inr ha
  · refine hfz.mem_of_det (w := w) fun v hA => hw _ ?_
    have hval := hA i (.str s) hv
    have hsv : slotVal (M.insert a v) (func + 16 * (i + 1)) = slotVal M (func + 16 * (i + 1)) :=
      bytesT8_congrT fun j hj => bT1_congr (ins_out M a v _ (by
        simp only [ArgSlot, tvalueValOff, not_and, Nat.not_lt] at ha ⊢; omega))
    rw [hsv] at hval
    exact hval.str_repr.1

/-- **The contents and terminator of an argument's string are frozen.** -/
theorem str_foot_contents {G : Nat → Prop} {func n : Nat} {ι : Strs} {args : List Value} {M : Mem}
    (hfz : Frozen (fun a => G a ∨ ArgSlot func n a) (ArgsAt func ι args) M) {i : Nat} {s : List UInt8}
    (hv : args[i]? = some (.str s)) (hi : i < n) :
    ∀ k, k ≤ s.length → G ((slotVal M (func + 16 * (i + 1))).toNat + 24 + k) ∨
      ArgSlot func n ((slotVal M (func + 16 * (i + 1))).toNat + 24 + k) := by
  intro k hk
  rcases Nat.lt_or_ge k s.length with hk' | hk'
  · exact str_foot hfz hv hi (w := BitVec.ofNat 8 (s[k]'hk').toNat) fun M' hr => hr.bytes.1 k hk'
  · have e : k = s.length := by omega
    subst e
    exact str_foot hfz hv hi (w := 0#8) fun M' hr => hr.bytes.2

/-! ## `luaL_tolstring`'s facts at `luaB_print`'s state -/

/-- **The facts `tol_s_pre` and `tol_l_pre` need**, at `luaB_print`'s state of
`n` values, for argument `i` (its string at `ts`, in the heap, its slot's tag
`tag`). -/
theorem tolS_in {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m : Mem}
    {i : Nat} {r : BitVec 64} {ts : Nat} {tag : BitVec 8}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G FL M0 ph0 H0 i n ph H m) (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hr : r.toNat % 4 = 0) (hts : heapStart ≤ ts) (hts' : ts + 64 ≤ 2 ^ 32)
    (htag : slotTag m (func + 16 * i) = tag) (hval : slotVal m (func + 16 * i) = BitVec.ofNat 64 ts) :
    TolNums (sp0 - 64) L i (sp0 - 56) nci func (func + 16 * n + 16) g ts r ∧
    TolSCells m L i nci func (func + 16 * n + 16) g ts tag ∧
    TolSIn m (sp0 - 64) L i nci func (func + 16 * n + 16) g sl tbc ls FL := by
  have q := hn.ok
  have q1 := q.sp_lo; have q2 := q.sp_hi; have q3 := q.sp_al; have q4 := q.L_al
  have q5 := hn.sp_big; have q6 := hn.n_small; have q7 := hn.sep
  have hp := hIn.placed
  have hl := hS.lits
  have htos : ls.tos ∈ ls.strs := by simp [LitPtrs.strs]
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ls.tos htos
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  have hga := hIn.g_al; have hfa := hIn.f_al
  have kG : ∀ a, Rng (L + stateGOff) 8 a → bytesT1 m a = bytesT1 M0 a := fun a h => hS.keep a (.inr (.inr (.inr
    (.inr (.inr (.inl h))))))
  have hapi := hS.api
  have htbc := hapi.tbc_lt
  refine ⟨?_, ⟨hapi.ci_w, hapi.func_w, hapi.top_w, ?_, ?_, ?_⟩, ⟨?_, by pr_omega, by pr_omega, by pr_omega,
    by pr_omega, hga, by pr_omega, by pr_omega, by omega, by simp only [Apart]; pr_omega, by simp only [Apart]; pr_omega,
    by simp only [Apart]; pr_omega, by simp only [Apart]; pr_omega, by simp only [Apart]; pr_omega,
    by simp only [Apart]; pr_omega, by pr_omega, hapi.tbc_w, by omega, fun o ho => ?_, hl.facts,
    fun a ha => ⟨(hl.kept a ha).hi, ?_⟩, fun a ha => ?_, hl.cache, ?_, by pr_omega, by simp only [Apart]; pr_omega,
    by simp only [Apart]; pr_omega, by simp only [Apart]; pr_omega, ?_, by simp only [Apart]; pr_omega,
    by simp only [Apart]; pr_omega, ?_⟩⟩
  · constructor <;> first | exact hr | pr_omega
  · exact (bytesT8_congrT fun j _ => kG _ (by simp only [Rng, stateGOff]; omega)).trans hIn.g_w
  · rw [show 16 * i + func + 8 = func + 16 * i + tvalueTagOff by simp only [tvalueTagOff]; omega]; exact htag
  · rw [show 16 * i + func = func + 16 * i + tvalueValOff by simp only [tvalueValOff]; omega]; exact hval
  · pr_omega
  · exact (hS.keep _ (.inr (.inr (.inl ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ho _⟩)))).trans (hIn.ro o ho)
  · intro hr'
    apply hl.apart a ha
    apply hIn.dirty a
    simp only [Rng, gEnd, gStrcacheOff, strcacheN, strcacheM] at hr' ⊢
    exact .inr (.inr (.inr (.inr ⟨by omega, by omega⟩)))
  · have hd : ¬ D a := hl.apart a ha
    have hm := hl.marks ls.tos htos
    intro hw
    rcases hw with hw | hw | hw | hw | hw
    · exact hd (hIn.dirty a (.inl (by simpa only [stateTopOff] using hw)))
    · exact hd (hIn.dirty a (.inr (.inl (by simp only [Rng] at hw; omega))))
    · exact hd (hIn.dirty a (.inr (.inr (.inl hw))))
    · exact hd (hIn.dirty a (.inr (.inr (.inr (.inl hw)))))
    · exact hm (hw ▸ ha)
  · exact (hS.keep _ (.inr (.inr (.inr (.inl ⟨Nat.le_refl _, Nat.lt_succ_self _⟩))))).trans hIn.gcstp
  · have := hIn.objs.lit_nci ls.tos htos; simp only [Apart] at this ⊢; pr_omega
  · have := hIn.objs.lit_stack ls.tos htos; simp only [Apart] at this ⊢; pr_omega

/-! ## What the run keeps, by category -/

/-- **A byte off `TolSW`**: below the heap's end, off `L->top`, the slots
`[top, top + 32)`, `g`'s cache, `totalbytes`/`GCdebt` and `"__tostring"`'s mark. -/
theorem notTolSW_of {sp L lenp g top a : Nat} {ls : LitPtrs} (hsp : heapEnd + 16384 + 256 + 64 ≤ sp) (hl : sp ≤ lenp)
    (ha : a < heapEnd + 32) (h1 : ¬ Rng (L + 16) 8 a) (h2 : ¬ Rng top 32 a)
    (h3 : ¬ (g + gStrcacheOff ≤ a ∧ a < g + gEnd)) (h4 : ¬ Rng (g + 16) 16 a) (h5 : a ≠ ls.tos + gcMarkedOff) :
    ¬ TolSW sp L lenp g top ls a := by
  simp only [TolSW, Rng, gEnd, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff, gcMarkedOff,
    not_or, not_and, Nat.not_lt] at h1 h2 h3 h4 h5 ⊢
  refine ⟨fun _ => by omega, fun _ => by omega, h1, h2, h3, fun e => by have := h4 (by omega); omega,
    fun e => by have := h4 (by omega); omega, fun e => by omega⟩

/-- **`luaB_print`'s kept bytes and the argument slots are off `TolSW`.** -/
theorem notW_of_keep {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    {a : Nat} (ha : G a ∨ ArgSlot func n a) : ¬ TolSW (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ls a := by
  have hp := hIn.placed
  have htos : ls.tos ∈ ls.strs := by simp [LitPtrs.strs]
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ls.tos htos
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp
  rcases ha with hG | hA
  · obtain ⟨g1, g2, g3, g4, g5⟩ := hIn.keep_apart a hG
    have hlo : a < heapEnd := (hIn.keep_in a hG).elim (fun k => k.hi) fun k => by
      simp only [PrintStatic, Rng, symTohost, symAtexit] at k; omega
    exact notTolSW_of (by homega) (by omega) (by omega) (by simpa only [stateTopOff] using g1)
      (by simp only [Rng] at g2 ⊢; omega) g4 (by simp only [Rng] at g3 ⊢; omega) (g5 _ htos)
  · simp only [ArgSlot] at hA
    have hlo := (hIn.stack_in a (by omega) (by omega)).hi
    refine notTolSW_of (by homega) (by omega) (by omega) ?_ ?_ ?_ ?_ ?_ <;> pr_omega

/-- **An argument's string bytes are in chunks in use**: frozen
(`str_foot_contents`), in the heap (`PrintIn.args_heap`), so not static. -/
theorem str_kept {L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) {i : Nat} {s : List UInt8}
    (hv : args[i]? = some (.str s)) (hi : i < n) :
    ∀ k, k ≤ s.length → Kept H0 ph0 ((slotVal M0 (func + 16 * (i + 1))).toNat + 24 + k) := by
  intro k hk
  have hh := hIn.args_heap i s hv
  have hHS : heapStart = 0x8006ecd0 := rfl
  rcases str_foot_contents hIn.args_fz hv hi k hk with hG | hA
  · exact (hIn.keep_in _ hG).elim id fun h => by
      simp only [PrintStatic, Rng, symTohost, symAtexit] at h; omega
  · have hp := hIn.placed
    simp only [ArgSlot] at hA
    exact hIn.stack_in _ (by omega) (by have := hp.room; omega)

/-! ## `TolPost` from the run -/

/-- The bytes a string value prints. -/
theorem argBytes_str (s : List UInt8) : argBytes (.str s) = s.map fun c => BitVec.ofNat 8 c.toNat := by
  simp only [argBytes, Value.show, bytesToString, String.toList_ofList, List.map_map]
  apply List.map_congr_left
  intro b _
  have := UInt8.toNat_lt b
  simp only [Function.comp]
  rw [show (Char.ofNat b.toNat).toNat = b.toNat by rw [Char.ofNat, dif_pos (Or.inl (by omega))]; rfl]

/-- (lane F1-18) **A string's `luaL_tolstring` keeps `g->strt`'s words**
(`nuse`, `size`): they are none of its stores (`TolSW`). -/
theorem TolStrPost.strt {m m' : Mem} {sp L lenp g top : Nat} {ls : LitPtrs} {len : Nat}
    (hT : TolStrPost m m' sp L lenp g top ls len) (hsp : g + 64 + 16384 + 256 ≤ sp) (hlp : sp ≤ lenp)
    (hL : L + 24 ≤ g ∨ g + 64 ≤ L + 16) (htop : top + 32 ≤ g ∨ g + 64 ≤ top)
    (hts : ls.tos + 10 ≤ g ∨ g + 64 ≤ ls.tos + 9)
    (hlo : 0x8005e7d8 ≤ L ∧ 0x8005e7d8 ≤ top ∧ 0x8005e7d8 ≤ ls.tos ∧ 0x8005e7d8 ≤ g) :
    ∀ a, PrStatic g a → bytesT1 m' a = bytesT1 m a := by
  intro a ha
  simp only [PrStatic, AllocStaticFoot, Rng, gStrtNuseOff] at ha
  refine hT.keep a ?_
  simp only [TolSW, Rng, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff, gcMarkedOff, not_or,
    not_and, Nat.not_lt]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => by omega, fun _ => by omega, fun _ => by omega,
    fun _ => by omega, fun _ => by omega, fun _ => by omega⟩

/-- **`TolPost` from a string's `luaL_tolstring`** (`TolStrPost`): the state
with one more value (the string at the top), `stdout` as it was, the frame
but the length word, the length, the string's bytes (read off its
representation at the final memory, which keeps `PrintIn`'s footprint), where
they lie (in chunks in use: `str_kept`). -/
theorem prStrPost {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m m' : Mem}
    {i j : Nat} {s : List UInt8}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    (hS : PrSt L nci func tbc sl g n ls args D G FL M0 ph0 H0 j n ph H m) (hP : PrintSt m ph H)
    (hT : TolStrPost m m' (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ls s.length)
    (hv : args[i]? = some (.str s)) (hin : i < n) (hj : j = i + 1) :
    TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (j + 1)) (argBytes (.str s)) ph m m'
      ((slotVal M0 (func + 16 * (i + 1))).toNat + 24) H H := by
  have q := hn.ok
  have hp := hIn.placed
  have hp' := hp
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, -⟩ := hp'
  have hsb := hn.sp_big
  have hHE : heapEnd = 0x87800000 := rfl
  have hHS : heapStart = 0x8006ecd0 := rfl
  have htos : ls.tos ∈ ls.strs := by simp [LitPtrs.strs]
  obtain ⟨tl1, tl2, tlL, tlg, tln, tls⟩ := hp.lits ls.tos htos
  have hl := hS.lits
  have kW := hT.keep
  have hsp : heapEnd + 16384 + 256 + 64 ≤ sp0 - 64 := by homega
  -- the literals' footprint is off the run's stores
  have kFL : ∀ a, FL a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have hd : ∀ x, D x → ¬ FL x := fun x hx hf => hl.apart x hf hx
    refine kW a (notTolSW_of hsp (by omega) (by have := (hl.kept a ha).hi; omega)
      (fun h => hd a (hIn.dirty a (.inl (by simpa only [stateTopOff] using h))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inl (by simp only [Rng] at h; have := hp.room; omega)))) ha)
      (fun h => hd a (hIn.dirty a (.inr (.inr (.inr (.inr h))))) ha)
      (fun h => ?_) (fun h => hl.marks ls.tos htos (h ▸ ha)))
    simp only [Rng] at h
    by_cases e : a < g + 24
    · exact hd a (hIn.dirty a (.inr (.inr (.inl (by simp only [Rng, gTotalbytesOff]; omega))))) ha
    · exact hd a (hIn.dirty a (.inr (.inr (.inr (.inl (by simp only [Rng, gGCdebtOff]; omega)))))) ha
  have hl' : LitsFoot g sl ls H ph D FL m' :=
    ⟨hl.facts.trans kFL, hl.kept, hl.apart, hl.strs, hl.marks, hT.cache⟩
  -- (lane F1-18) `g->strt`'s words are off them
  have kT := hT.strt (by homega) (by omega) (by simp only [stateSize, gEnd, gStrcacheOff, strcacheN, strcacheM] at p10; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at p12; have := hp.room; omega)
    (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at tlg; omega)
    ⟨by have : heapStart = 0x8006ecd0 := rfl; omega, by have : heapStart = 0x8006ecd0 := rfl; omega,
      by have : heapStart = 0x8006ecd0 := rfl; omega, by have : heapStart = 0x8006ecd0 := rfl; omega⟩
  -- the kept bytes are off them
  have kK : ∀ a, PrKeep L g func n G a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have hsym : symTohost = 0x8005c6c0 := rfl
    rcases ha with h | h | h | h | h | h | h
    · exact kW a (notW_of_keep hIn hn (.inl h))
    · exact kW a (notW_of_keep hIn hn (.inr h))
    all_goals exact kW a (notTolSW_of hsp (by omega) (by pr_omega) (by pr_omega) (by pr_omega) (by pr_omega)
      (by pr_omega) (by pr_omega))
  -- the API frame is off them
  have kA : ∀ a, ApiFoot L nci a → ¬ Rng (L + 16) 8 a → bytesT1 m' a = bytesT1 m a := by
    intro a ha h1
    have := hn.sep
    exact kW a (notTolSW_of hsp (by omega) (by pr_omega) h1 (by pr_omega) (by pr_omega) (by pr_omega)
      (by pr_omega))
  -- `stdout`'s footprint is off them
  have kP : ∀ a, PrintFoot ph H a → bytesT1 m' a = bytesT1 m a := by
    intro a ha
    have nK : ∀ {x}, Kept H0 ph0 x → ¬ PrintFoot ph H x := fun h => (hS.kept h).not_printFoot
    have hlo : a < heapEnd + 32 := by
      rcases ha with hg | hb | ⟨hr, _⟩ | hr
      · simp only [StdioGlob] at hg; omega
      · have := hP.io.buf_hi a hb; omega
      · simp only [HeapReads] at hr
        have e4 : symMallocAv = 0x8005c6d0 := rfl
        have e5 : symMallocSbrkBase = 0x8005d388 := rfl
        have e6 : symBrk = 0x8005d3b8 := rfl
        have e7 : symMallocTopPad = 0x8005d3d8 := rfl
        have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
        have e9 : symMallocMallinfo = 0x8005e560 := rfl
        omega
      · omega
    refine kW a (notTolSW_of hsp (by omega) hlo (fun h => nK (hIn.L_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.stack_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.g_in a (by pr_omega) (by pr_omega)) ha)
      (fun h => nK (hIn.g_in a (by pr_omega) (by pr_omega)) ha) fun h => ?_)
    have := hl.strs ls.tos htos a (by simp only [gcMarkedOff] at h; omega) (by simp only [gcMarkedOff] at h; omega)
    exact this.not_printFoot ha
  -- the string, at `m'`: its representation (the footprint kept), its bytes, where they lie
  have hAm' : ArgsAt func ι args m' := hIn.args_fz m' fun a ha => (kW a (notW_of_keep hIn hn ha)).trans
    (hS.keep a (ha.elim (fun h => .inl h) fun h => .inr (.inl h)))
  have hslot : slotVal m' (func + 16 * (i + 1)) = slotVal M0 (func + 16 * (i + 1)) :=
    bytesT8_congrT fun j hj => (kW _ (notW_of_keep hIn hn (.inr (by simp only [ArgSlot, tvalueValOff]; omega)))).trans
      (hS.keep _ (.inr (.inl (by simp only [ArgSlot, tvalueValOff]; omega))))
  have hrep := (hAm' i (.str s) hv).str_repr.1
  rw [hslot] at hrep
  have hb := bytesAt_of_repr hrep
  have hk := str_kept hIn hv hin
  generalize (slotVal M0 (func + 16 * (i + 1))).toNat = ts at hb hk ⊢
  have hk0 := (hk 0 (by omega)).lo
  have hkn := (hk s.length (by omega)).hi
  have hapi := hS.api
  have hlen' : (argBytes (.str s)).length = s.length := by simp [argBytes_str]
  refine
    { lua := ⟨FL, hS.next0 (by omega) (by subst hj; simpa using hv) rfl ⟨?_, ?_, ?_, ?_, by have := hapi.tbc_lt; omega⟩
        hl' (fun a ha => (kK a ha).trans (hS.keep a ha)) kFL kT⟩
      io := hP.keep kP
      kept := fun c hc _ => hc
      frame := fun a h1 h2 => kW a fun hw => by
        simp only [TolSW, Rng, gStrcacheOff, strcacheN, strcacheM, gTotalbytesOff, gGCdebtOff, gcMarkedOff,
          gEnd] at hw p6
        rcases hw with hw | hw | hw | hw | hw | hw | hw | hw <;> omega
      len := by rw [hT.len_w, hlen']
      bytes := by rw [hlen', argBytes_str]; exact hb
      src_lo := SrcLo.of_hi (by have : errnoAddr = 0x8005d408 := rfl; homega)
      src_hi := by rw [hlen']; homega
      src_ok := fun a h1 h2 => ?_
      src_out := by rw [hlen']; have : stdoutFile = 0x8005e668 := rfl; have : fileSize = 184 := rfl; omega
      src_buf := fun a h1 h2 => ?_ }
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inl ⟨by omega, by omega⟩)) (by simp only [Rng]; omega)).trans
      hapi.ci_w
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inr ⟨by omega, by omega⟩))) (by
      have := hn.sep; simp only [Rng]; omega)).trans hapi.func_w
  · rw [hT.top_w]; congr 1
  · exact (bytesT8_congrT fun j _ => kA _ (.inr (.inr (.inl ⟨by omega, by omega⟩))) (by
      simp only [Rng]; omega)).trans hapi.tbc_w
  · rw [hlen'] at h2
    have hk' := hS.kept (hk (a - ts - 24) (by omega))
    rw [show ts + 24 + (a - ts - 24) = a by omega] at hk'
    have hsp' : heapEnd + 4096 ≤ sp0 - 64 := by homega
    exact ⟨fun hg => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp' (fun _ h => .inl h) (.inl (.inl hg)),
      fun hm => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp' (fun _ h => .inl h) (.inl (.inr (.inl hm))),
      fun hs => hk'.not_printW (sp := sp0 - 64) (ph' := ph) hsp' (fun _ h => .inl h) (.inl (.inr (.inr (.inl hs))))⟩
  · rw [hlen'] at h2
    have hk' := hS.kept (hk (a - ts - 24) (by omega))
    rw [show ts + 24 + (a - ts - 24) = a by omega] at hk'
    exact hk'.nbuf

/-! ## `TolStr_Statement` -/

/-- `lua_pushvalue`'s stores keep every byte off `TolSW`. -/
theorem TolPushMem.keep {M : Mem} {sp L lenp g top ts : Nat} {ls : LitPtrs} {tag : BitVec 64} {a : Nat}
    (ha : ¬ TolSW sp L lenp g top ls a) : bytesT1 (TolPushMem M L top ts tag) a = bytesT1 M a := by
  simp only [TolSW, Rng, not_or, not_and, Nat.not_lt] at ha
  obtain ⟨-, -, h3, h4, -⟩ := ha
  have e1 := rng_split h3; have e2 := rng_split h4
  rw [fw1_wm8 e1, fw1_ins (by omega), fw1_wm8 (by omega)]

/-- **An argument's string at a later memory**: one that keeps `TolSW`'s
complement of `luaB_print`'s state keeps `PrintIn`'s footprint, so the
string's representation (at the slot's pointer of the entry). -/
theorem str_repr_at {sp0 L nci func tbc sl g n : Nat} {ls : LitPtrs} {args : List Value} {ι : Strs}
    {D G FL : Nat → Prop} {M0 : Mem} {ph0 : StdoutPh} {H0 : HeapIx} {ph : StdoutPh} {H : HeapIx} {m M : Mem}
    {i : Nat} {s : List UInt8}
    (hIn : PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0) (hn : PrNums sp0 L nci func n 0x8000ac8c#64)
    {j k : Nat} (hS : PrSt L nci func tbc sl g n ls args D G FL M0 ph0 H0 j k ph H m)
    (hv : args[i]? = some (.str s)) (hin : i < n)
    (hk : ∀ a, ¬ TolSW (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ls a → bytesT1 M a = bytesT1 m a) :
    TStringRepr (fillZeroMem M) (slotVal M0 (func + 16 * (i + 1))).toNat s := by
  have hag : ∀ a, (G a ∨ ArgSlot func n a) → bytesT1 M a = bytesT1 M0 a := fun a ha =>
    (hk a (notW_of_keep hIn hn ha)).trans (hS.keep a (ha.elim (fun h => .inl h) fun h => .inr (.inl h)))
  have hA : ArgsAt func ι args M := hIn.args_fz M hag
  have hslot : slotVal M (func + 16 * (i + 1)) = slotVal M0 (func + 16 * (i + 1)) :=
    bytesT8_congrT fun j hj => hag _ (.inr (by simp only [ArgSlot, tvalueValOff]; omega))
  have := (hA i (.str s) hv).str_repr.1
  rwa [hslot] at this

/-- **`luaL_tolstring` on a string argument in `luaB_print`'s loop**
(`TolStr_Statement`): a short string by `tol_s_pre`, `tol_s_mid`,
`tol_tail_s`, a long one by `tol_l_pre`, `tol_l_mid`, `tol_tail_l`, the
string's facts from `PrintIn` (`tolS_in`, `str_repr_at`), `TolPost` by
`prStrPost`. -/
theorem tolStr_proved : TolStr_Statement := by
  intro sp0 L nci func n tbc sl g ls args ι D G FL ph0 H0 M0 i v hIn hn hv hC hi1 hin ph H m o r f hS hP hr
  cases v with
  | str s =>
    have hi' : i - 1 < n := by omega
    have hidx : func + 16 * (i - 1 + 1) = func + 16 * i := by congr 1; omega
    -- the string at `m`, its pointer the entry's
    have hrm := str_repr_at hIn hn hS hv hi' (M := m) fun _ _ => rfl
    have hA : ArgsAt func ι args m := hIn.args_fz m fun a ha =>
      hS.keep a (ha.elim (fun h => .inl h) fun h => .inr (.inl h))
    obtain ⟨-, htag⟩ := (hA (i - 1) (.str s) hv).str_repr
    have hslot : slotVal m (func + 16 * (i - 1 + 1)) = slotVal M0 (func + 16 * (i - 1 + 1)) :=
      bytesT8_congrT fun j hj => hS.keep _ (.inr (.inl (by simp only [ArgSlot, tvalueValOff]; omega)))
    have hk := str_kept hIn hv hi'
    have hh := hIn.args_heap (i - 1) s hv
    rw [hidx] at htag hslot hk hh hrm
    generalize hts : (slotVal M0 (func + 16 * i)).toNat = ts at hk hh hrm
    have hk0 := (hk 0 (by omega)).hi
    have hval : slotVal m (func + 16 * i) = BitVec.ofNat 64 ts := by rw [hslot, ← hts]; simp
    have hHE : heapEnd = 0x87800000 := rfl
    have hHS : heapStart = 0x8006ecd0 := rfl
    have hpost : ∀ {m' : Mem} {c' : Config},
        wrRet r (sp0 - 64) (ts + 24) f m' o c' →
        TolStrPost m m' (sp0 - 64) L (sp0 - 56) g (func + 16 * n + 16) ls s.length →
        ∃ m'' s' H', wrRet r (sp0 - 64) s' f m'' o c' ∧
          TolPost sp0 n (PrSt' L nci func tbc sl g n ls args D G M0 ph0 H0 (i + 1)) (argBytes (.str s)) ph m m''
            s' H H' := by
      intro m' c' hret hT
      refine ⟨m', ts + 24, H, hret, ?_⟩
      have := prStrPost hIn hn hS hP hT hv hi' (by omega)
      rwa [hidx, hts] at this
    by_cases hsh : s.length ≤ maxShortLen
    · have htag' : slotTag m (func + 16 * i) = 0x44#8 := by rw [htag]; simp [strTag, hsh, vShrStr]
      obtain ⟨hx, hc, hT⟩ := tolS_in hIn hn hS hi1 hin hr (by omega) (by omega) htag' hval
      intro c h
      obtain ⟨c1, s1, M3, hmid, h1⟩ := tol_s_pre hx hc hT c h
      obtain ⟨c2, s2, h2⟩ := tol_s_mid hx hT hmid c1 h1
      have hR := str_repr_at hIn hn hS hv hi' (M := TolPushMem M3 L (func + 16 * n + 16) ts 0x44#64)
        fun a ha => (TolPushMem.keep ha).trans (hmid.keep a ha)
      rw [hidx, hts] at hR
      have hlen : bytesT1 (TolPushMem M3 L (func + 16 * n + 16) ts 0x44#64) (ts + 11) =
          BitVec.ofNat 8 s.length := by
        cases hR with
        | short _ _ hl _ _ => rw [← bytesT1_fill]; exact bytesT1_of_rd8 hl
        | long _ hl' => exact absurd hl' (by omega)
      obtain ⟨c3, s3, m', hret, hT'⟩ := tol_tail_s hx hT hmid hlen (by simp only [maxShortLen] at hsh; omega) c2 h2
      obtain ⟨m'', s', H', hret', hP'⟩ := hpost hret hT'
      exact ⟨c3, s1.trans (s2.trans s3), m'', s', H', hret', hP'⟩
    · have htag' : slotTag m (func + 16 * i) = 0x54#8 := by rw [htag]; simp [strTag, hsh, vLngStr]
      obtain ⟨hx, hc, hT⟩ := tolS_in hIn hn hS hi1 hin hr (by omega) (by omega) htag' hval
      intro c h
      obtain ⟨c1, s1, M3, hmid, h1⟩ := tol_l_pre hx hc hT c h
      obtain ⟨c2, s2, h2⟩ := tol_l_mid hx hT hmid c1 h1
      have hR := str_repr_at hIn hn hS hv hi' (M := TolPushMem M3 L (func + 16 * n + 16) ts 0x54#64)
        fun a ha => (TolPushMem.keep ha).trans (hmid.keep a ha)
      rw [hidx, hts] at hR
      have hl2 : bytesT1 (TolPushMem M3 L (func + 16 * n + 16) ts 0x54#64) (ts + 11) = 0xff#8 ∧
          bytesT8 (TolPushMem M3 L (func + 16 * n + 16) ts 0x54#64) (ts + 16) = BitVec.ofNat 64 s.length := by
        cases hR with
        | short _ hl' => exact absurd hl' hsh
        | long _ _ hl _ _ hs =>
          exact ⟨by rw [← bytesT1_fill]; exact bytesT1_of_rd8 hs, bT8_of_fill (bytesT8_of_rd64 hl)⟩
      obtain ⟨c3, s3, m', hret, hT'⟩ := tol_tail_l hx hT hmid hl2.1 hl2.2 c2 h2
      obtain ⟨m'', s', H', hret', hP'⟩ := hpost hret hT'
      exact ⟨c3, s1.trans (s2.trans s3), m'', s', H', hret', hP'⟩
  | nil => exact absurd hC id
  | bool _ => exact absurd hC id
  | int _ => exact absurd hC id
  | flt _ _ => exact absurd hC id
  | builtin _ => exact absurd hC id

/-- **`luaB_print` on the C frame** from `CALL`'s open part (lane F1-15;
F1-17; F1-18): `lua_pushstring` of the literals proved (`pushLit_proved`),
`luaL_tolstring` on strings proved (`tolStr_proved`), `_malloc_r` proved
(lane F1-A0-M, `AllocProof.mallocR_proved`); the allocating classes by
`CallOpen`'s fields: integers per argument (`tolInt`), floats (`printFlt`),
functions (`printFn`), integer lists off the per-argument route
(`allocOff`). -/
theorem CallOpen.print (O : CallOpen) : PrintRel_Statement :=
  printRel_of AllocProof.mallocR_proved pushLit_proved tolStr_proved O.tolInt O.printFlt O.printFn O.allocOff

end Lua.Vm.Sim.Kit

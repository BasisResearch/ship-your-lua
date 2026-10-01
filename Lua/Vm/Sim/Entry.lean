import Lua.Vm.Sim.Dispatch
import Lua.Vm.Arms.Prologue

/-!
# The entry lemma: from `luaV_execute`'s entry to the fetch head in `VmRel` (A1)

`vmRel_entry` discharges `vmRel_entry_Statement`: from `VmLoaded luaLayout p c`,
`luaV_execute`'s prologue runs to the fetch head `Arms.headPc` in
`VmRel p c' State.init`. The run is the two generated segments of the prologue
(`Lua/Vm/Arms/Prologue.lean`, `scripts/gen_lua_arms.py`):

* `seg_8001bf68_8001bfb0`: `addi sp,sp,-176`, the saves of `ra`, `s0 … s11`,
  s0 = `L`, s7 = `ci`, s8 = the jump table. All its side conditions are ground
  (`sp` is `RuntimeData.spEntry`), one `decide` each.
* `seg_8001bfb0_8001bfe4` (`startfunc`): `ci->func`, `trap = L->hookmask`,
  `pc = ci->u.l.savedpc`, the closure and its `k`, s1 = 81, s2 = 3, the `trap`
  check not taken, `base = ci->func + 1`. Its side conditions close by one
  normalising `simp` over the prologue's reads (`hR*`) and `omega` over
  `VmRegionsAt`.

The memory frame is `AgreeOut` (the stores all lie in the 176-byte C frame);
the pointers of `VmEntryData` and of the witness `RtPtrs` are identified by
their common reads. The relation's pointers are `VmEntryData`'s, its
complement memory `mo` is the entry memory.

`rdLE_spec` turns the representation predicates' `rd32`/`rd64` into the total
reads `bytesT4`/`bytesT8` the segments use.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout

/-- `rdLE` byte by byte, from the lowest address. -/
theorem rdLE_succ (m : Mem) (a n : Nat) :
    rdLE m a (n + 1) = (do
      let b ← m[a]?
      let r ← rdLE m (a + 1) n
      pure (b.toNat + 256 * r)) := by
  simp only [rdLE, List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  funext b
  congr 1
  congr 1
  funext i acc
  rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- **A little-endian read is the total read**, and fits its width. -/
theorem rdLE_spec : ∀ (n : Nat) (m : Mem) (a x : Nat), rdLE m a n = some x →
    x < 2 ^ (8 * n) ∧ bytesT m a n = BitVec.ofNat (8 * n) x
  | 0, m, a, x, h => by
    simp [rdLE] at h
    subst h
    exact ⟨by decide, rfl⟩
  | n + 1, m, a, x, h => by
    rw [rdLE_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, r, hr, rfl⟩ := h
    obtain ⟨hlt, hbt⟩ := rdLE_spec n m (a + 1) r hr
    have hb8 := b.isLt
    have hbound : b.toNat + 256 * r < 2 ^ (8 * (n + 1)) := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      have : (r + 1) * 2 ^ 8 ≤ 2 ^ (8 * n) * 2 ^ 8 := Nat.mul_le_mul_right _ hlt
      simp only [Nat.add_mul, Nat.one_mul] at this
      omega
    refine ⟨hbound, ?_⟩
    simp only [bytesT, hbt, hb, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat (8 * n) r ++ b).toNat = _
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      ← Nat.shiftLeft_add_eq_or_of_lt hb8, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbound]
    omega

/-- `rd64` as `ld` reads it. -/
theorem bytesT8_of_rd64 {m : Mem} {a x : Nat} (h : rd64 m a = some x) :
    bytesT8 m a = BitVec.ofNat 64 x := by
  rw [← bytesT_eight_eq]; exact (rdLE_spec 8 m a x h).2

/-- `rd32` as `lw` reads it. -/
theorem bytesT4_of_rd32 {m : Mem} {a x : Nat} (h : rd32 m a = some x) :
    bytesT4 m a = BitVec.ofNat 32 x := by
  rw [← bytesT_four_eq]; exact (rdLE_spec 4 m a x h).2

theorem rd64_lt {m : Mem} {a x : Nat} (h : rd64 m a = some x) : x < 2 ^ 64 :=
  (rdLE_spec 8 m a x h).1

/-- `ld` of a 64-bit value: the sign extension is the identity. -/
theorem sext64 (x : BitVec 64) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- **`m'` agrees with `m` outside `[lo, hi)`**: the memory frame of a run whose
stores all lie in `[lo, hi)` (the prologue's C frame). -/
def AgreeOut (m' m : Mem) (lo hi : Nat) : Prop :=
  ∀ a, a < lo ∨ hi ≤ a → m'[a]? = m[a]?

theorem AgreeOut.refl (m : Mem) (lo hi : Nat) : AgreeOut m m lo hi := fun _ _ => rfl

theorem AgreeOut.writeMap8 {m' m : Mem} {lo hi k : Nat} (h : AgreeOut m' m lo hi)
    (d : BitVec (8 * 8)) (hk : lo ≤ k) (hk' : k + 8 ≤ hi) :
    AgreeOut (Vsa.Sim.writeMap8 m' k d) m lo hi := fun a ha => by
  rw [getElem?_writeMap8_out m' k d a (by omega)]; exact h a ha

theorem AgreeOut.bytesT8 {m' m : Mem} {lo hi : Nat} (h : AgreeOut m' m lo hi) {a : Nat}
    (ha : a + 8 ≤ lo ∨ hi ≤ a) : bytesT8 m' a = bytesT8 m a :=
  bytesT8_congr fun i _ => h _ (by omega)

theorem AgreeOut.bytesT4 {m' m : Mem} {lo hi : Nat} (h : AgreeOut m' m lo hi) {a : Nat}
    (ha : a + 4 ≤ lo ∨ hi ≤ a) : bytesT4 m' a = bytesT4 m a :=
  bytesT4_congr fun i _ => h _ (by omega)

/-- The code array of a represented `Proto`: its length and its words.
(`ProtoRepr` has one constructor with 18 premises; this is its one destructuring
lemma for the code.) -/
theorem _root_.Lua.Vm.ProtoRepr.code {m : Mem} {pa ca : Nat} {p : Proto} (h : ProtoRepr m pa p)
    (hc : rd64 m (pa + protoCodeOff) = some ca) :
    rd32 m (pa + protoSizecodeOff) = some p.code.length ∧
      ∀ i (hi : i < p.code.length), rd32 m (ca + 4 * i) = some (p.code[i]'hi).toNat := by
  match h with
  | .mk _ _ _ _ hsz hca hw _ _ _ _ _ _ _ _ _ _ _ =>
    rw [hca, Option.some.injEq] at hc
    subst hc
    exact ⟨hsz, hw⟩

theorem bytesT1_of_rd8 {m : Mem} {a t : Nat} (h : rd8 m a = some t) :
    bytesT1 m a = BitVec.ofNat 8 t := by
  simp only [rd8, rdLE, List.range_one, List.foldr_cons, List.foldr_nil, Nat.add_zero,
    Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    Option.bind_some] at h
  obtain ⟨b, hb, rfl⟩ := h
  simp [bytesT1, hb]

theorem slotTag_of_tagAt {m : Mem} {a t : Nat} (h : tagAt m a = some t) :
    slotTag m a = BitVec.ofNat 8 t := bytesT1_of_rd8 h

theorem slotVal_of_rd64 {m : Mem} {a x : Nat} (h : rd64 m (a + tvalueValOff) = some x) :
    slotVal m a = BitVec.ofNat 64 x := bytesT8_of_rd64 h

/-- A represented non-nil `TValue`, as the arms read it, for an intern map `ι`
that a short string's pointer agrees with. (A table's nil may be any variant
of type 0; a register's is exactly `LUA_VNIL`.) -/
theorem _root_.Lua.Vm.TValueRepr.valRepr {m : Mem} {a : Nat} {v : Value} {ι : List UInt8 → Nat}
    (h : TValueRepr m a v) (hnil : v ≠ .nil)
    (hι : ∀ s ts, v = .str s → rd64 m (a + tvalueValOff) = some ts → s.length ≤ maxShortLen →
      ts = ι s) :
    ValRepr m ι (slotTag m a) (slotVal m a) v := by
  cases h with
  | nil => exact absurd rfl hnil
  | false_ ht => rw [slotTag_of_tagAt ht]; exact .false_
  | true_ ht => rw [slotTag_of_tagAt ht]; exact .true_
  | int ht hv => rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact .int
  | str ht hv hts =>
    rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv]
    have hlt := rd64_lt hv
    refine .str ?_ fun hl => ?_ <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · exact hts
    · exact hι _ _ rfl hv hl
  | print ht hv => rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv]; exact .print rfl

/-- A represented constant, as the `K` arms read it. -/
theorem _root_.Lua.Vm.ConstRepr.valRepr {m : Mem} {a : Nat} {c : Const} {v : Value}
    {ι : List UInt8 → Nat} (h : ConstRepr m a c) (hv : c.toValue? = some v)
    (hι : ∀ s ts, c = .str s → rd64 m (a + tvalueValOff) = some ts → s.length ≤ maxShortLen →
      ts = ι s) :
    ValRepr m ι (slotTag m a) (slotVal m a) v := by
  cases h with
  | nil ht =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    rw [slotTag_of_tagAt ht]; exact .nil
  | bool h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) (by simp)
  | int h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) (by simp)
  | float => simp [Const.toValue?] at hv
  | str h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) fun s ts e => hι s ts (by cases e; rfl)

/-- **An intern map** for a relation `P` that is functional in its second
argument: the witness `RelPtrs.ι` from `KInterned`. -/
theorem exists_intern {α β : Type} [Inhabited β] (P : α → β → Prop)
    (hu : ∀ a x y, P a x → P a y → x = y) : ∃ ι : α → β, ∀ a x, P a x → x = ι a := by
  classical
  refine ⟨fun a => if h : ∃ x, P a x then h.choose else default, fun a x hx => ?_⟩
  have h : ∃ x, P a x := ⟨x, hx⟩
  simp only [h, dif_pos]
  exact hu a x _ hx h.choose_spec

/-- The constant array of a represented `Proto`; if its short strings are
interned (`KInterned`), some intern map `ι` represents every constant. -/
theorem _root_.Lua.Vm.ProtoRepr.kArr {m : Mem} {pa ka : Nat} {p : Proto} (h : ProtoRepr m pa p)
    (hk : rd64 m (pa + protoKOff) = some ka) :
    rd32 m (pa + protoSizekOff) = some p.k.length ∧
      (KInterned m ka p.k.length → ∃ ι : List UInt8 → Nat, ∀ i v, kval p i = some v →
        ValRepr m ι (slotTag m (ka + stackValueSize * i)) (slotVal m (ka + stackValueSize * i)) v) := by
  obtain ⟨hsk, hks⟩ : rd32 m (pa + protoSizekOff) = some p.k.length ∧
      ∀ i (h : i < p.k.length), ConstRepr m (ka + tvalueSize * i) (p.k[i]'h) := by
    match h with
    | .mk _ _ _ _ _ _ _ hsk hka hks _ _ _ _ _ _ _ _ =>
      rw [hka, Option.some.injEq] at hk
      subst hk
      exact ⟨hsk, hks⟩
  refine ⟨hsk, fun hI => ?_⟩
  -- the short strings of the constant array, by content
  let P : List UInt8 → Nat → Prop := fun s x => ∃ i, i < p.k.length ∧
    tagAt m (ka + tvalueSize * i) = some vShrStr ∧ rd64 m (ka + tvalueSize * i + tvalueValOff) = some x ∧
    s.length ≤ maxShortLen ∧ TStringRepr m x s
  obtain ⟨ι, hι⟩ := exists_intern P fun s x y ⟨i, hi, hti, hxi, hl, hsx⟩ ⟨j, hj, htj, hyj, _, hsy⟩ =>
    hI i j x y s hi hj hti htj hxi hyj hl hsx hsy
  refine ⟨ι, fun i v hv => ?_⟩
  simp only [kval, Proto.const, Option.bind_eq_some_iff] at hv
  obtain ⟨c, hc, hcv⟩ := hv
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.1 hc
  refine (hks i hi).valRepr hcv fun s ts e hts hl => ?_
  have hr := hks i hi
  rw [e] at hr
  cases hr with
  | str hr =>
    cases hr with
    | str ht hv' hts' =>
      rw [hts, Option.some.injEq] at hv'
      subst hv'
      exact hι s _ ⟨i, hi, by rw [ht, strTag, if_pos hl], hts, hl, hts'⟩

/-- **The relation's address facts** (`Ranges`) from the entry's
`VmRegionsAt`, for pointers whose `ci->func`, code and constant arrays are the
witness's and whose `sp` is `luaV_execute`'s frame below the entry `sp`. The
scratch words lie in the `lua_State` and the `CallInfo` (`L_sep_ci`,
`code_sep_*`, `k_sep_*`) and the callee frames above the heap
(`cstack_room`). -/
theorem Ranges.of_regions {m : Mem} {p : Proto} {w : RelPtrs} {rt : RtPtrs}
    (hrg : VmRegionsAt m w.L w.ci rt) (hsp : w.sp = RuntimeData.spEntry - execFrame)
    (hfunc : w.func = rt.func) (hcode : w.code = rt.code) (hk : w.k = rt.k)
    (hsz : rt.sizecode = p.code.length) (hszk : rt.sizek = p.k.length) (hsle : rt.stack ≤ rt.func)
    (hfits : w.func + stackValueSize * (1 + p.maxstacksize) ≤ rt.stackLast) : Ranges p w := by
  obtain ⟨hLlo, hLhi, hcilo, hcihi, hstlo, hsthi, hfal, hcisep, -, -, -, -, -, -, -, -, hcdlo,
    hcdhi, hcdsep, -, -, hklo, hkhi, hkal, hksep, hLci, hcdL, hcdci, hkL, hkci, hLst, hLal, hcial⟩ := hrg
  obtain ⟨L, ci, func, pa, code, k, sp, mo, ι⟩ := w
  simp only at hsp hfunc hcode hk hfits hLlo hLhi hcilo hcihi hcisep hLci hcdL hcdci hkL hkci hLst hLal hcial ⊢
  subst hsp hfunc hcode hk
  rw [hsz] at hcdhi hcdsep hcdL hcdci
  rw [hszk] at hkhi hksep hkL hkci
  have hroom := cstack_room
  simp only [symEnd, symHeapEnd, stateSize, ciSize, tvalueSize, stackValueSize, cStackBudget,
    RuntimeData.spEntry] at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun a h1 h2 hw => ?_, fun a h1 h2 h3 hw => ?_, ?_,
    ?_, ?_, fun a h1 h2 hw => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, ciSavedpcOff, ciSize,
    stateTopOff, stateSize, cStackBudget, execFrame, tohostAddr, RuntimeData.spEntry] at *
  all_goals omega

set_option linter.unusedSimpArgs false in
/-- **The entry lemma (A1).** The prologue runs from the entry to the fetch
head, in the relation with the initial state. -/
theorem vmRel_entry : vmRel_entry_Statement := by
  intro p c hS hL
  obtain ⟨L, ci, e, hM, hE, rt, hRt⟩ := hL
  have hcs := hRt.cstack
  obtain ⟨v8, h8⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 8 (by decide))
  obtain ⟨v9, h9⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 9 (by decide))
  obtain ⟨v18, h18⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 18 (by decide))
  obtain ⟨v19, h19⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 19 (by decide))
  obtain ⟨v20, h20⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 20 (by decide))
  obtain ⟨v21, h21⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 21 (by decide))
  obtain ⟨v22, h22⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 22 (by decide))
  obtain ⟨v23, h23⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 23 (by decide))
  obtain ⟨v24, h24⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 24 (by decide))
  obtain ⟨v25, h25⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 25 (by decide))
  obtain ⟨v26, h26⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 26 (by decide))
  obtain ⟨v27, h27⟩ := Option.isSome_iff_exists.1 (hcs.callee_saved 27 (by decide))
  -- the frame: `addi sp,sp,-176` and the saves of `ra`, `s0 … s11`
  have H1 := Arms.seg_8001bf68_8001bfb0 (BitVec.ofNat 64 RuntimeData.spEntry) v8 v23 v24
    (BitVec.ofNat 64 RuntimeData.retCcall) v9 v18 v19 v20 v21 v22 v25 v26 v27
    (BitVec.ofNat 64 L) (BitVec.ofNat 64 ci) (BitVec.ofNat 64 symGlobalPointer)
    c.σ.mem c.σ.sailOutput
  repeat (specialize H1 (by decide))
  obtain ⟨c1, hs1, hq1⟩ := H1 c ⟨hM.good, hM.pc,
    ⟨hcs.sp, h8, h23, h24, hcs.ra, h9, h18, h19, h20, h21, h22, h25, h26, h27, hM.a0, hM.a1,
      hcs.gp, trivial⟩, hM.good.minstret, hRt.harness.tick, ⟨hM.text, rfl, rfl, hM.regs⟩⟩
  have hA1 : AgreeOut c1.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry := by
    rw [hq1.armMem]
    repeat (refine AgreeOut.writeMap8 ?_ _ (by decide) (by decide))
    exact AgreeOut.refl _ _ _
  -- where things are
  have hrg := hRt.regions
  have hlua := hRt.lua
  have hTH : tohostAddr = 0x8005c6c0 := rfl
  have hSP : RuntimeData.spEntry = 0x87fffe20 := rfl
  have hEF : execFrame = 176 := rfl
  have hLlo := hrg.L_lo
  have hLhi := hrg.L_hi
  have hcilo := hrg.ci_lo
  have hcihi := hrg.ci_hi
  have hstlo := hrg.stack_lo
  have hsthi := hrg.stack_hi
  have hcllo := hrg.cl_lo
  have hclhi := hrg.cl_hi
  have hprlo := hrg.proto_lo
  have hprhi := hrg.proto_hi
  have hcdlo := hrg.code_lo
  have hcdhi := hrg.code_hi
  have hcisep := hrg.ci_sep
  have hcdsep := hrg.code_sep
  have hfal := hrg.func_al
  have hsle := hlua.stack_le
  have hfits := hE.frame_fits
  simp only [symEnd, symHeapEnd, stateSize, ciSize] at hLlo hLhi hcilo hcihi hstlo hsthi hcisep
  simp only [symEnd, symHeapEnd, lclosureUpvalsOff, protoCodeOff] at hcllo hclhi hprlo hprhi
  simp only [symEnd, symHeapEnd] at hcdlo hcdhi
  -- the entry data's pointers are the witness's
  have efunc : e.func = rt.func := Option.some.inj (hE.ci_func.symm.trans hlua.func)
  have esl : e.stackLast = rt.stackLast :=
    Option.some.inj (hE.stack_last.symm.trans hlua.stack_last)
  have ecl : e.cl = rt.cl := by
    have h := hE.func_val; rw [efunc, hrg.cl] at h; exact (Option.some.inj h).symm
  have epa : e.pa = rt.proto := by
    have h := hE.cl_proto; rw [ecl, hrg.proto] at h; exact (Option.some.inj h).symm
  have ecode : e.code = rt.code := by
    have h := hE.proto_code; rw [epa, hrg.code] at h; exact (Option.some.inj h).symm
  obtain ⟨hsz, hwords⟩ := hE.proto.code hE.proto_code
  obtain ⟨hszk, hkc⟩ := hE.proto.kArr (ka := rt.k) (by rw [epa]; exact hrg.kArr)
  have esizek : rt.sizek = p.k.length := by
    have h := hrg.sizek; rw [← epa, hszk] at h; exact (Option.some.inj h).symm
  obtain ⟨ι, hkι⟩ := hkc (by rw [← esizek]; exact hRt.interned)
  have esz : rt.sizecode = p.code.length := by
    have h := hrg.sizecode; rw [← epa, hsz] at h; exact (Option.some.inj h).symm
  rw [← efunc] at hsle hfal
  rw [← esl] at hsthi hcisep hcdsep
  rw [← ecl] at hcllo hclhi
  rw [← epa] at hprlo hprhi
  rw [← ecode] at hcdlo
  rw [← ecode, esz] at hcdhi hcdsep
  -- what the prologue's loads read (the C frame's stores miss them)
  have hRci : bytesT8 c1.σ.mem ci = BitVec.ofNat 64 e.func := by
    rw [hA1.bytesT8 (by omega), ← bytesT8_of_rd64 hE.ci_func, ciFuncOff, Nat.add_zero]
  have hRpc : bytesT8 c1.σ.mem (ci + 32) = BitVec.ofNat 64 e.code := by
    rw [hA1.bytesT8 (by omega), ← bytesT8_of_rd64 hE.savedpc, ciSavedpcOff]
  have hRhook : bytesT4 c1.σ.mem (L + 192) = 0#32 := by
    have h := bytesT4_of_rd32 hlua.hookmask
    rw [stateHookmaskOff] at h
    rw [hA1.bytesT4 (by omega), h]
  have hRfunc : bytesT8 c1.σ.mem e.func = BitVec.ofNat 64 e.cl := by
    rw [hA1.bytesT8 (by omega), ← bytesT8_of_rd64 hE.func_val, tvalueValOff, Nat.add_zero]
  have hRcl : ∀ d, bytesT8 (Vsa.Sim.writeMap8 c1.σ.mem (RuntimeData.spEntry - execFrame + 8) d)
      (e.cl + 24) = BitVec.ofNat 64 e.pa := fun d => by
    rw [(hA1.writeMap8 d (by omega) (by omega)).bytesT8 (by omega),
      ← bytesT8_of_rd64 hE.cl_proto, lclosureProtoOff]
  have hRk : ∀ d, bytesT8 (Vsa.Sim.writeMap8 c1.σ.mem (RuntimeData.spEntry - execFrame + 8) d)
      (e.pa + 56) = BitVec.ofNat 64 rt.k := fun d => by
    rw [(hA1.writeMap8 d (by omega) (by omega)).bytesT8 (by omega), epa,
      ← bytesT8_of_rd64 hrg.kArr, protoKOff]
  -- `startfunc`: the loads, s1 = 81, s2 = 3, the `trap` check, `base`
  have hp1 := hq1.pins
  have hx24 : c1.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 Arms.jtBase) := by
    have h := pinsHold_get hp1 0 (by simp)
    simp only [List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx23 : c1.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 ci) := by
    have h := pinsHold_get hp1 1 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [add_imm _ 0 (by decide), Nat.add_zero] at h; exact h
  have hx8 : c1.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 L) := by
    have h := pinsHold_get hp1 2 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [add_imm _ 0 (by decide), Nat.add_zero] at h; exact h
  have hx2 : c1.σ.regs.get? Register.x2 =
      some (BitVec.ofNat 64 (RuntimeData.spEntry - execFrame)) := by
    have h := pinsHold_get hp1 3 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have H2 := Arms.seg_8001bfb0_8001bfe4 (BitVec.ofNat 64 ci) (BitVec.ofNat 64 L)
    (BitVec.ofNat 64 (RuntimeData.spEntry - execFrame)) (BitVec.ofNat 64 symGlobalPointer)
    (BitVec.ofNat 64 Arms.jtBase) c1.σ.mem c1.σ.sailOutput
  repeat (specialize H2 (by
    first
      | (simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
          Nat.mod_eq_of_lt, hRci, hRpc, hRhook, hRfunc, hRcl, hTH]; omega)
      | decide
      | (simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
          Nat.mod_eq_of_lt, hRci, hRpc, hRhook, hRfunc, hRcl, hTH]; decide)))
  obtain ⟨c2, hs2, hq2⟩ := H2 c1 ⟨hq1.good, hq1.pcAt,
    ⟨hx23, hx8, hx2, pinsHold_get hp1 16 (by simp), hx24, trivial⟩,
    hq1.minstret, hq1.tick, ⟨hq1.armText, rfl, rfl, hq1.armOk⟩⟩
  -- the fetch-head registers
  have hp2 := hq2.pins
  have hx25 : c2.σ.regs.get? Register.x25 = some (BitVec.ofNat 64 (e.func + 16)) := by
    have h := pinsHold_get hp2 0 (by simp)
    simp (disch := omega) only [List.getElem_cons_zero, add_imm, BitVec.toNat_ofNat,
      Nat.add_zero, sext64, Nat.mod_eq_of_lt, hRci] at h
    exact h
  have hx18 : c2.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 vNumInt) := by
    have h := pinsHold_get hp2 2 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx9 : c2.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 (Arms.jtEntries - 1)) := by
    have h := pinsHold_get hp2 3 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx21 : c2.σ.regs.get? Register.x21 = some (0#64) := by
    have h := pinsHold_get hp2 4 (by simp)
    simp (disch := omega) only [List.getElem_cons_succ, List.getElem_cons_zero, add_imm,
      BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt, hRhook] at h
    exact h.trans (congrArg some (by decide))
  have hx27 : c2.σ.regs.get? Register.x27 = some (BitVec.ofNat 64 (e.code + 4 * 0)) := by
    have h := pinsHold_get hp2 5 (by simp)
    simp (disch := omega) only [List.getElem_cons_succ, List.getElem_cons_zero, add_imm,
      BitVec.toNat_ofNat, Nat.add_zero, sext64, Nat.mod_eq_of_lt, hRpc] at h
    exact h
  -- the memory frame: every store of the prologue is in its C frame
  have hA2 : AgreeOut c2.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry := by
    rw [hq2.armMem]
    exact (hA1.writeMap8 _ (by decide) (by decide)).writeMap8 _ (by decide) (by decide)
  -- `0(sp)` holds `k`
  have hkp : bytesT8 c2.σ.mem (RuntimeData.spEntry - execFrame) = BitVec.ofNat 64 rt.k := by
    rw [hq2.armMem]
    simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
      Nat.mod_eq_of_lt, hRci, hRfunc, hRcl, hRk, bytesT8_writeMap8, sdData_id]
  simp only [stackValueSize] at hfits
  refine ⟨c2, hs1.trans hs2, ⟨L, ci, e.func, e.pa, e.code, rt.k, RuntimeData.spEntry - execFrame,
    c.σ.mem, ι⟩, ⟨hq2.good, hq2.minstret, hq2.tick,
    ⟨pinsHold_get hp2 10 (by simp), pinsHold_get hp2 11 (by simp), pinsHold_get hp2 9 (by simp),
      hx9, hx18, hx21, pinsHold_get hp2 8 (by simp), pinsHold_get hp2 12 (by simp), hx25, hx27⟩,
    (output_congr (hq2.armOut.trans hq1.armOut)).trans hRt.harness.console, hq2.armOk, hq2.armText,
    fun a ha => congrArg (Option.getD · 0) (hA2 a ?_), hkp, fun j v _ h => ?_,
    ⟨hM.text, hM.rodata, hE.proto, hE.proto_code, fun i ins hf => ?_, bytesT8_of_rd64 hE.ci_func,
      ?_, ⟨rt, efunc.symm, hlua, hRt.heap, hRt.error_jmp⟩, hkι⟩,
    Ranges.of_regions hrg rfl efunc ecode rfl esz esizek hlua.stack_le
      (by rw [← esl]; exact hE.frame_fits)⟩, hq2.pcAt⟩
  · simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize] at ha; omega
  · simp [State.init] at h
  · obtain ⟨hlt, hi⟩ := List.getElem?_eq_some_iff.1 hf
    rw [bytesT4_of_rd32 (hwords i hlt), hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [bytesT4_of_rd32 hlua.trap]; rfl

end Lua.Vm.Sim

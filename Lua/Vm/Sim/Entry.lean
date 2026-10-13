import Lua.Vm.Sim.Dispatch
import Lua.Vm.Arms.Prologue
import Lua.Vm.Sim.Kit.Exit

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

/-- A represented non-nil `TValue`, as the arms read it, for strings `ι` whose
intern map a short string's pointer agrees with and which own its object.
(A table's nil may be any variant of type 0; a register's is exactly
`LUA_VNIL`.) -/
theorem _root_.Lua.Vm.TValueRepr.valRepr {m : Mem} {a : Nat} {v : Value} {ι : Strs}
    (h : TValueRepr m a v) (hnil : v ≠ .nil)
    (hι : ∀ s ts, v = .str s → rd64 m (a + tvalueValOff) = some ts → s.length ≤ maxShortLen →
      ts = ι.ptr s)
    (hown : ∀ s ts, v = .str s → rd64 m (a + tvalueValOff) = some ts → ι.own ts s) :
    ValRepr m ι (slotTag m a) (slotVal m a) v := by
  cases h with
  | nil => exact absurd rfl hnil
  | false_ ht => rw [slotTag_of_tagAt ht]; exact .false_
  | true_ ht => rw [slotTag_of_tagAt ht]; exact .true_
  | int ht hv => rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv, BitVec.ofNat_toNat, BitVec.setWidth_eq]; exact .int
  | str ht hv hts =>
    rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv]
    have hlt := rd64_lt hv
    refine .str ?_ (fun hl => ?_) ?_ <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
    · exact hts
    · exact hι _ _ rfl hv hl
    · exact hown _ _ rfl hv
  | print ht hv => rw [slotTag_of_tagAt ht, slotVal_of_rd64 hv]; exact .print rfl

/-- A represented constant, as the `K` arms read it. -/
theorem _root_.Lua.Vm.ConstRepr.valRepr {m : Mem} {a : Nat} {c : Const} {v : Value}
    {ι : Strs} (h : ConstRepr m a c) (hv : c.toValue? = some v)
    (hι : ∀ s ts, c = .str s → rd64 m (a + tvalueValOff) = some ts → s.length ≤ maxShortLen →
      ts = ι.ptr s)
    (hown : ∀ s ts, c = .str s → rd64 m (a + tvalueValOff) = some ts → ι.own ts s) :
    ValRepr m ι (slotTag m a) (slotVal m a) v := by
  cases h with
  | nil ht =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    rw [slotTag_of_tagAt ht]; exact .nil
  | bool h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) (by simp) (by simp)
  | int h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) (by simp) (by simp)
  | float ht hb =>
    simp only [Const.toValue?] at hv
    split at hv
    · cases hv
    · simp only [Option.some.injEq] at hv; subst hv
      rw [slotTag_of_tagAt ht, slotVal_of_rd64 hb, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact .flt
  | str h =>
    simp only [Const.toValue?, Option.some.injEq] at hv; subst hv
    exact h.valRepr (by simp) (fun s ts e => hι s ts (by cases e; rfl))
      (fun s ts e => hown s ts (by cases e; rfl))

/-- **An intern map** for a relation `P` that is functional in its second
argument: the witness `RelPtrs.ι` from `KInterned`. -/
theorem exists_intern {α β : Type} [Inhabited β] (P : α → β → Prop)
    (hu : ∀ a x y, P a x → P a y → x = y) : ∃ ι : α → β, ∀ a x, P a x → x = ι a := by
  classical
  refine ⟨fun a => if h : ∃ x, P a x then h.choose else default, fun a x hx => ?_⟩
  have h : ∃ x, P a x := ⟨x, hx⟩
  simp only [h, dif_pos]
  exact hu a x _ hx h.choose_spec

/-- **The string objects of the constant array** (`Strs.own` at the entry):
`ts` holding `s` is some string constant `k[i]`. -/
def KStrIn (m : Mem) (k sizek ts : Nat) (s : List UInt8) : Prop := ∃ i, KStrAt m k sizek i ts s

/-- The constant array of a represented `Proto`; if its short strings are
interned (`KInterned`), some intern map `ι` represents every constant, with
the string constants as the owned strings (`KStrIn`). -/
theorem _root_.Lua.Vm.ProtoRepr.kArr {m : Mem} {pa ka : Nat} {p : Proto} (h : ProtoRepr m pa p)
    (hk : rd64 m (pa + protoKOff) = some ka) :
    rd32 m (pa + protoSizekOff) = some p.k.length ∧
      (KInterned m ka p.k.length → ∃ ι : List UInt8 → Nat, ∀ i v, kval p i = some v →
        ValRepr m ⟨ι, KStrIn m ka p.k.length⟩ (slotTag m (ka + stackValueSize * i))
          (slotVal m (ka + stackValueSize * i)) v) := by
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
  refine (hks i hi).valRepr hcv (fun s ts e hts hl => ?_) (fun s ts e hts => ?_)
  · have hr := hks i hi
    rw [e] at hr
    cases hr with
    | str hr =>
      cases hr with
      | str ht hv' hts' =>
        rw [hts, Option.some.injEq] at hv'
        subst hv'
        exact hι s _ ⟨i, hi, by rw [ht, strTag, if_pos hl], hts, hl, hts'⟩
  · have hr := hks i hi
    rw [e] at hr
    cases hr with
    | str hr =>
      cases hr with
      | str ht hv' hts' =>
        rw [hts, Option.some.injEq] at hv'
        subst hv'
        exact ⟨i, hi, ht, hts, hts'⟩

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
  obtain ⟨L, ci, func, pa, code, k, sp, mo, ι, rt'⟩ := w
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

/-- **A string constant's chunk owns it in the relation**: the entry's
`StrChunkAt` (heap, apart from the Lua stack, `L` and `ci`) puts the chunk
apart from the window, whose slots lie in the Lua stack, whose scratch words
lie in `L` and `ci`, and whose C frames lie above the heap (`cstack_room`). -/
theorem chunkOwns_of_strChunkAt {p : Proto} {w : RelPtrs} {c : DlHeap.Chunk} {ts : Nat}
    {s : List UInt8} (h : StrChunkAt w.L w.ci w.rt c ts s.length)
    (hsp : w.sp = RuntimeData.spEntry - execFrame) (hst : w.rt.stack ≤ w.func)
    (hfits : w.func + stackValueSize * (1 + p.maxstacksize) ≤ w.rt.stackLast) :
    ChunkOwns p w c ts s := by
  refine ⟨h.walk, h.inuse, h.lo, h.hi, fun a h1 h2 hw => ?_⟩
  have := h.heap; have := h.stack_sep; have := h.L_sep; have := h.ci_sep
  have hroom := cstack_room
  simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, execFrame, ciSavedpcOff, ciSize,
    stateTopOff, stateSize, cStackBudget, symHeapEnd, RuntimeData.spEntry] at *
  omega

/-- **An object of `_ENV` in the relation** (lane F1-7): the boot witness's
`HeapApart` (heap, apart from the Lua stack above `f0 ≤ func`, `L` and `ci`)
puts the range outside the window. -/
theorem heapRead_of_apart {p : Proto} {w : RelPtrs} {f0 lo n : Nat}
    (h : HeapApart w.L w.ci f0 w.rt.stackLast lo n) (hsp : w.sp = RuntimeData.spEntry - execFrame)
    (hf0 : f0 ≤ w.func) (hfits : w.func + stackValueSize * (1 + p.maxstacksize) ≤ w.rt.stackLast) :
    HeapRead p w lo n := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hroom := cstack_room
  simp only [symEnd, symHeapEnd, cStackBudget, RuntimeData.spEntry, stateSize, ciSize] at h1 h2 h4 h5 hroom
  refine ⟨by simp only [tohostAddr]; omega, by simp only [cStackBudget, RuntimeData.spEntry]; omega,
    fun a ha1 ha2 hw => ?_⟩
  simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize, execFrame, ciSavedpcOff, ciSize,
    stateTopOff, stateSize, cStackBudget, RuntimeData.spEntry] at *
  omega

/-- **`_ENV.print` from the entry data** (`VmEntryData.env_get`), in any
memory `m` that agrees with the entry memory off `luaT_adjustvarargs`'s
stores, for the constant array `k` that `m` holds: every string constant
`"print"` finds `print` (`EnvMem`, `EnvGetAt.envMem`). -/
theorem envMem_of_entry {m0 m : Mem} {L ci : Nat} {p : Proto} {e : EntryPtrs}
    (hE : VmEntryData m0 L ci p e) (hm : ∀ a, ¬ VarargDirty ci e.func a → m[a]? = m0[a]?) {k : Nat}
    (hk : rd64 m (e.pa + protoKOff) = some k) :
    ∀ ts, KStrIn m k p.k.length ts printKey → EnvMem m e.cl ts (HeapApart L ci e.func e.stackLast) := by
  rintro ts ⟨i, hi⟩
  have ht := hi.tag
  rw [show strTag printKey = vShrStr by decide] at ht
  obtain ⟨s, hs⟩ := hE.env_get m hm k i ts hk hi.lt ht hi.ptr hi.str
  exact hs.envMem

/-- **`Complement.own` at the entry**: the owned strings are the string
constants (`KStrIn`), each in a chunk the boot witness found (`KOwned`). -/
theorem own_of_kowned {p : Proto} {w : RelPtrs} {n : Nat} (hk : KOwned w.mo w.L w.ci w.rt)
    (hown : w.ι.own = KStrIn w.mo w.rt.k n) (hn : w.rt.sizek = n)
    (hsp : w.sp = RuntimeData.spEntry - execFrame) (hst : w.rt.stack ≤ w.func)
    (hfits : w.func + stackValueSize * (1 + p.maxstacksize) ≤ w.rt.stackLast) :
    ∀ ts s, w.ι.own ts s → StrOwned p w ts s := by
  intro ts s h
  rw [hown] at h
  obtain ⟨i, hi⟩ := h
  obtain ⟨c, hc⟩ := hk i ts s (by rw [hn]; exact hi)
  exact ⟨c, chunkOwns_of_strChunkAt hc hsp hst hfits⟩

/-- `p->maxstacksize` of a represented `Proto`. -/
theorem _root_.Lua.Vm.ProtoRepr.maxstack {m : Mem} {pa : Nat} {p : Proto} (h : ProtoRepr m pa p) :
    rd8 m (pa + protoMaxstacksizeOff) = some p.maxstacksize := by
  match h with
  | .mk _ _ _ hms _ _ _ _ _ _ _ _ _ _ _ _ _ _ => exact hms

/-! ## The `CALL` invariant from the boot contract (lane F1-13)

`callInv_boot`: `CallInv` at the relation's pointers from `VmEntryData`'s
`CALL` facts (the objects a `print` leaves alone frozen on `e.foot`, the
literals on `e.litFoot`, their places, the room) and `RuntimeReadyAt`'s
`StdioBoot`/`MemfsBoot`/heap, for any memory that agrees with the boot memory
off `OP_VARARGPREP`'s stores (the entry itself, and after `VARARGPREP`). -/

/-- A dense memory's RAM byte is its total read. -/
theorem get_of_dense {m : Mem}
    (hd : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize → (m[a]?).isSome)
    {a : Nat} (h1 : 0x80000000 ≤ a) (h2 : a < 0x88000000) : m[a]? = some (bytesT1 m a) := by
  have := hd a (by simp only [Vsa.Densify.ramBase]; omega)
    (by simp only [Vsa.Densify.ramBase, Vsa.Densify.ramSize]; omega)
  cases hm : m[a]? with
  | none => rw [hm] at this; cases this
  | some b => simp [bytesT1, hm]

/-- A zero fill's RAM byte is the total read. -/
theorem fill_get (M : Mem) {a : Nat} (h1 : 0x80000000 ≤ a) (h2 : a < 0x88000000) :
    (Vsa.Densify.fillZeroMem M)[a]? = some (bytesT1 M a) :=
  Vsa.Densify.fillZeroMem_ram M (by simp only [Vsa.Densify.ramBase]; omega)
    (by simp only [Vsa.Densify.ramBase, Vsa.Densify.ramSize]; omega)

/-- The zero fill is idempotent. -/
theorem fill_fill (M : Mem) :
    Vsa.Densify.fillZeroMem (Vsa.Densify.fillZeroMem M) = Vsa.Densify.fillZeroMem M :=
  Vsa.Densify.fillZeroMem_eq_of_dense fun a h1 h2 => by rw [Vsa.Densify.fillZeroMem_ram M h1 h2]; rfl

/-- The literals' facts of a fill are the memory's (`LitInterned` reads the fill). -/
theorem _root_.Lua.Vm.LitInterned.of_fill {M : Mem} {rt : RtPtrs} {seed : UInt32} {b : List UInt8} {ts : Nat}
    (h : LitInterned (Vsa.Densify.fillZeroMem M) rt seed b ts) : LitInterned M rt seed b ts := by
  have e := fill_fill M
  exact ⟨e ▸ h.repr, h.short, e ▸ h.strt, e ▸ h.cache, e ▸ h.seed_w, fun hl => e ▸ h.bucket hl⟩

/-- `TStringRepr` depends only on the object's bytes. -/
theorem _root_.Lua.Vm.TStringRepr.congr {m m' : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr m ts s)
    (hk : ∀ a, ts ≤ a → a < ts + tstringContentsOff + s.length + 1 → m'[a]? = m[a]?) :
    TStringRepr m' ts s := by
  have r : ∀ {o n : Nat}, o + n ≤ tstringContentsOff → rdLE m' (ts + o) n = rdLE m (ts + o) n :=
    fun {o n} h => rdLE_congr fun i hi => hk _ (by omega) (by simp only [tstringContentsOff] at h ⊢; omega)
  have hb : ∀ {bs : List UInt8}, bs.length = s.length → BytesAt m (ts + tstringContentsOff) bs →
      BytesAt m' (ts + tstringContentsOff) bs := fun hl hb i hi =>
    (hk _ (by omega) (by omega)).trans (hb i hi)
  have hz : m[ts + tstringContentsOff + s.length]? = some 0 → m'[ts + tstringContentsOff + s.length]? = some 0 :=
    fun hz => (hk _ (by omega) (by omega)).trans hz
  cases h with
  | short ht hl hs hbs hn =>
    exact .short ((r (by simp only [gcTtOff, tstringContentsOff]; omega)).trans ht) hl
      ((r (by simp only [tstringShrlenOff, tstringContentsOff]; omega)).trans hs) (hb rfl hbs) (hz hn)
  | long ht hl hs hbs hn hf =>
    exact .long ((r (by simp only [gcTtOff, tstringContentsOff]; omega)).trans ht) hl
      ((r (by simp only [tstringLnglenOff, tstringContentsOff]; omega)).trans hs) (hb rfl hbs) (hz hn)
      ((r (by simp only [tstringShrlenOff, tstringContentsOff]; omega)).trans hf)

/-- **The `CALL` invariant from the boot contract** (lane F1-13): at the
pointers of a relation whose memory `m` agrees with the boot memory `m0` off
`OP_VARARGPREP`'s stores, with `ci->next` NULL and `stdout` before its first
write. -/
theorem callInv_boot {m0 m : Mem} {L ci func sp : Nat} {p : Proto} {e : EntryPtrs} {rt0 rt : RtPtrs}
    {ι : Strs} (hE : VmEntryData m0 L ci p e) (hS : StdioBoot m0) (hFs : MemfsBoot m0) (hro : RodataLoaded m0)
    (hej : ErrorJmpAt m0 L) (hlua : LuaStateAt m0 L ci rt0)
    (hheap : DlHeap.HeapAt m0 rt.top rt.brkv rt.chunks (fun i => rt.bins.getD i []))
    (hdense : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize → (m0[a]?).isSome)
    (hm : ∀ a, ¬ VarargDirty ci e.func a → m[a]? = m0[a]?) (hnext : rd64 m (ci + ciNextOff) = some 0)
    (hmd : ∀ a, 0x80000000 ≤ a → a < 0x88000000 → (m[a]?).isSome)
    (hko : KOwned m L ci rt) (hreg : VmRegionsAt m L ci rt) (hι : ι.own = KStrIn m rt.k p.k.length)
    (hszk : rt.sizek = p.k.length) (hka : rd64 m0 (e.pa + protoKOff) = some rt.k)
    (hst : rt.stack = rt0.stack) (hsl : rt.stackLast = rt0.stackLast) (hg : rt.g = rt0.g)
    (heg : e.g = rt.g) (hesl : e.stackLast = rt.stackLast) (hecl : e.cl = rt.cl) (hfunc : e.func ≤ func)
    (hsp : sp = RuntimeData.spEntry - execFrame)
    (hfits : func + stackValueSize * (1 + p.maxstacksize) ≤ rt.stackLast) :
    CallInv p ⟨L, ci, func, e.pa, e.code, rt.k, sp, m, ι, rt⟩ := by
  have hvr := hE.vararg_room
  have hsle : rt.stack ≤ e.func := by
    have h1 := hlua.func; rw [hE.ci_func] at h1
    rw [hst, Option.some.inj h1]; exact hlua.stack_le
  have hTH : symTohost = 0x8005c6c0 := rfl
  have hHE : symHeapEnd = 0x87800000 := rfl
  have hHS : symEnd = 0x8006ecd0 := rfl
  -- `OP_VARARGPREP`'s stores lie in the `CallInfo` and the Lua stack above `ci->func`
  have hvd : ∀ a, VarargDirty ci e.func a → (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast) := by
    intro a h
    simp only [VarargDirty, stackValueSize, tvalueTagOff] at h hvr
    omega
  -- the footprints: RAM, off `OP_VARARGPREP`'s stores, present in the boot memory
  have hRam : ∀ a, 0x80000000 ≤ a ∧ a < 0x88000000 → m0[a]? = some (bytesT1 m0 a) :=
    fun a ha => get_of_dense hdense ha.1 ha.2
  have hFm : ∀ a, InRanges e.foot a → m[a]? = m0[a]? := fun a ha => hm a fun hv => hE.foot_apart a ha (by
    rcases hvd a hv with h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h))))
  have hLm : ∀ a, InRanges e.litFoot a → m[a]? = m0[a]? := fun a ha => hm a fun hv => hE.lits_apart a ha (by
    rcases hvd a hv with h | h
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr h)))
  have hP : ∀ M : Mem, (∀ a, InRanges e.foot a → bytesT1 M a = bytesT1 m a) →
      ∀ a, InRanges e.foot a → (Vsa.Densify.fillZeroMem M)[a]? = m0[a]? := fun M hM a ha => by
    have hr := hE.foot_ram a ha
    rw [fill_get M hr.1 hr.2, hRam a hr, hM a ha]
    simp only [bytesT1, hFm a ha]
  have hPL : ∀ M : Mem, (∀ a, InRanges e.litFoot a → bytesT1 M a = bytesT1 m a) →
      ∀ a, InRanges e.litFoot a → (Vsa.Densify.fillZeroMem M)[a]? = m0[a]? := fun M hM a ha => by
    have hr := hE.lits_ram a ha
    rw [fill_get M hr.1 hr.2, hRam a hr, hM a ha]
    simp only [bytesT1, hLm a ha]
  -- where the objects lie
  have hpl := hE.placed rt.top rt.chunks hheap.top_ptr hheap.walk
  have kept : ∀ {a}, HeapIn rt.chunks a → Kit.Kept rt.hix .boot a := fun h =>
    ⟨h.inuse, h.lo, h.hi, fun hb => hb⟩
  -- a string constant's object and slot lie off `OP_VARARGPREP`'s stores
  have kslot : ∀ i j, i < p.k.length → j < tvalueSize → ¬ VarargDirty ci e.func (rt.k + tvalueSize * i + j) := by
    intro i j hi hj hv
    have := hreg.k_sep; have := hreg.k_sep_ci; rw [hszk] at *
    have hi' : tvalueSize * i + j < tvalueSize * p.k.length := by
      simp only [tvalueSize] at hj ⊢; omega
    rcases hvd _ hv with h | h
    · simp only [ciSize, tvalueSize] at *; omega
    · simp only [ciSize, tvalueSize] at *; omega
  have kstr : ∀ i ts s, KStrAt m rt.k p.k.length i ts s → ∀ a, ts ≤ a →
      a < ts + tstringContentsOff + s.length + 1 → ¬ VarargDirty ci e.func a := by
    intro i ts s hk a h1 h2 hv
    obtain ⟨c, hc⟩ := hko i ts s (by rw [hszk]; exact hk)
    have := hc.lo; have := hc.hi; have := hc.stack_sep; have := hc.ci_sep
    rcases hvd _ hv with h | h
    · simp only [ciSize] at *; omega
    · omega
  have kat : ∀ i ts s, KStrAt m rt.k p.k.length i ts s → KStrAt m0 rt.k p.k.length i ts s := by
    intro i ts s hk
    refine ⟨hk.lt, ?_, ?_, hk.str.congr fun a h1 h2 => (hm a (kstr i ts s hk a h1 h2)).symm⟩
    · rw [← hk.tag]; simp only [tagAt, rd8]
      exact rdLE_congr fun j hj => (hm _ (by
        have := kslot i (tvalueTagOff + j) hk.lt (by simp only [tvalueTagOff, tvalueSize]; omega)
        rwa [Nat.add_assoc])).symm
    · rw [← hk.ptr]; simp only [rd64]
      exact rdLE_congr fun j hj => (hm _ (by
        have := kslot i (tvalueValOff + j) hk.lt (by simp only [tvalueValOff, tvalueSize]; omega)
        rwa [Nat.add_assoc])).symm
  -- below the heap, `m` is the boot memory, and both are present
  have hlo0 : ∀ a, a < symEnd → ¬ VarargDirty ci e.func a := fun a ha hv => by
    have := hreg.ci_lo; have := hreg.stack_lo
    rcases hvd a hv with h | h <;> omega
  have hm0 : ∀ a, 0x80000000 ≤ a → a < 0x8006ecd0 → m[a]? = some (bytesT1 m0 a) := fun a h1 h2 =>
    (hm a (hlo0 a (by rw [hHS]; exact h2))).trans (hRam a ⟨h1, by omega⟩)
  have hlow : ∀ a, 0x80000000 ≤ a → a < 0x8006ecd0 → (Vsa.Densify.fillZeroMem m)[a]? = m0[a]? :=
    fun a h1 h2 => by
      rw [Vsa.Densify.fillZeroMem_some (hm0 a h1 h2), hRam a ⟨h1, by omega⟩]
  refine ⟨.boot, fun a => InRanges e.foot a ∨ (Image.rodataBase ≤ a ∧ a < Image.rodataBase + Image.rodataSize),
    InRanges e.litFoot, e.lits, ?_⟩
  have hroom := hE.room rt.brkv hheap.brk
  refine
    { dense := hmd
      io := .boot ?_ ?_ (by simp only [RtPtrs.hix, DlHeap.heapEnd, firstRoom] at hroom ⊢; omega)
      pend := rfl
      cells := ?_
      room := fun _ => hroom
      atexit := ?_
      stat := fun M hM => ?_
      stat_in := fun a ha => ha.elim (fun ha => (hpl.foot a ha).imp kept id) fun ha => .inr ⟨by
        have : Image.rodataBase = 0x8004ecc8 := rfl; omega, by
        have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl; omega⟩
      stat_apart := fun a ha hd => ha.elim (fun ha => hE.foot_apart a ha ?_) fun ha => ?_
      kslots := fun j hj => .inl ((hE.foot_k rt.k hka).2 j hj)
      lits := fun M hM => ?_
      lits_in := fun a ha => kept (hpl.litFoot a ha)
      lits_apart := fun a ha hd => hE.lits_apart a ha ?_
      lit_strs := fun ts hts a h1 h2 => kept (hpl.lit_strs ts hts a h1 h2)
      marks := fun ts hts hf => hf.elim (hE.marks ts hts) fun hr => by
        have := (hpl.lit_strs ts hts ts (Nat.le_refl _) (by omega)).lo
        have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl
        simp only [DlHeap.heapStart, symEnd] at *; omega
      L_in := fun a h1 h2 => kept (hpl.L a h1 h2)
      g_in := fun a h1 h2 => kept (hpl.g a (by rw [heg]; exact h1) (by rw [heg]; exact h2))
      ci_in := fun a h1 h2 => kept (hpl.ci a h1 h2)
      stack_in := fun a h1 h2 => kept (hpl.stack a (Nat.le_trans hfunc h1) (by rw [hesl]; exact h2))
      nci := fun nci h h0 => absurd (Option.some.inj (h.symm.trans hnext)) h0
      objs := ?_ }
  · exact hS.congr fun a ha => hlow a (by simp only [Kit.StdioGlob] at ha; omega)
      (by simp only [Kit.StdioGlob] at ha; omega)
  · exact hFs.congr fun a ha => hlow a (by simp only [Kit.StdioGlob] at ha; omega)
      (by simp only [Kit.StdioGlob] at ha; omega)
  · have h8 : ∀ {a x : Nat}, 0x80000000 ≤ a → a + 8 ≤ 0x8006ecd0 → rd64 m0 a = some x →
        bytesT8 m a = BitVec.ofNat 64 x := fun {a x} h1 h2 hx => by
      rw [← bytesT8_of_rd64 hx]
      exact bytesT8_congrT fun j hj => by
        show (m[a + j]?).getD 0 = (m0[a + j]?).getD 0
        rw [hm0 (a + j) (by omega) (by omega), hRam (a + j) ⟨by omega, by omega⟩]
    have h1 : ∀ {a o : Nat}, a = Image.rodataBase + o → o < Image.rodataSize →
        Kit.bytesAt m a 1 = [Image.rodataByte o] := fun {a o} ha ho => by
      subst ha
      have hb : Image.rodataBase = 0x8004ecc8 := rfl
      have hz : Image.rodataSize = 55776 := rfl
      have e1 := hm0 (Image.rodataBase + o) (by omega) (by omega)
      simp only [Kit.bytesAt, List.range_one, List.map_cons, List.map_nil, Nat.add_zero, bytesT1, e1,
        Option.getD_some, hro o ho]
    exact ⟨h8 (by decide) (by decide) hS.impure_ptr, h8 (by decide) (by decide) hS.stdout,
      (h1 (o := 4728) rfl (by decide)).trans (by decide : [Image.rodataByte 4728] = [0x09#8]),
      (h1 (o := 3712) rfl (by decide)).trans (by decide : [Image.rodataByte 3712] = [0x0a#8])⟩
  · rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, ← bytesT8_of_rd64 hS.atexit]
    exact bytesT8_congrT fun j hj => by
      have : symAtexit = 0x8005d450 := rfl
      show (m[symAtexit + j]?).getD 0 = (m0[symAtexit + j]?).getD 0
      rw [hm0 (symAtexit + j) (by omega) (by omega), hRam (symAtexit + j) ⟨by omega, by omega⟩]
  · -- the objects frozen on `e.foot`
    have Fr := hE.frozen _ (hP M (fun a ha => hM a (.inl ha)))
    have hstr : ∀ ts s, ι.own ts s → TStringRepr (Vsa.Densify.fillZeroMem M) ts s := by
      intro ts s hown
      rw [hι] at hown
      obtain ⟨i, hk⟩ := hown
      have hk0 := kat i ts s hk
      exact hE.frozen_strs _ (hP M (fun a ha => hM a (.inl ha))) rt.k i ts s hka hk0.lt hk0.tag hk0.ptr hk0.str
    have rdF : ∀ r ∈ luaStaticWords L e.g, rdLE (Vsa.Densify.fillZeroMem M) r.1 r.2 = rdLE m0 r.1 r.2 :=
      fun r hr => rdLE_congr fun j hj => hP M (fun a ha => hM a (.inl ha)) _ (hE.foot_lua r hr j hj)
    have rdW : ∀ {a n x : Nat}, (a, n) ∈ luaStaticWords L e.g → rdLE m0 a n = some x →
        rdLE (Vsa.Densify.fillZeroMem M) a n = some x := fun hr hx => (rdF _ hr).trans hx
    rw [heg] at rdW
    refine
      { rodata := fun o ho => by
          have hb : Image.rodataBase = 0x8004ecc8 := rfl
          have hz : Image.rodataSize = 55776 := rfl
          have e1 := hm0 (Image.rodataBase + o) (by omega) (by omega)
          rw [fill_get M (a := Image.rodataBase + o) (by omega) (by omega), hM _ (.inr ⟨by omega, by omega⟩)]
          simp only [bytesT1, e1, Option.getD_some, hro o ho]
        proto := Fr.proto
        proto_code := Fr.proto_code
        strs := hstr
        env := fun ts hown => ?_
        lua := ?_ }
    · have hown' := hown
      rw [hι] at hown'
      obtain ⟨i, hk⟩ := hown'
      have hk0 := kat i ts printKey hk
      have hkp : rd64 (Vsa.Densify.fillZeroMem M) (e.pa + protoKOff) = some rt.k := by
        rw [← hka]; simp only [rd64]
        exact rdLE_congr fun j hj => hP M (fun a ha => hM a (.inl ha)) _ ((hE.foot_k rt.k hka).1 j hj)
      have hsl : ∀ o n, o + n ≤ tvalueSize →
          rdLE (Vsa.Densify.fillZeroMem M) (rt.k + tvalueSize * i + o) n = rdLE m0 (rt.k + tvalueSize * i + o) n :=
        fun o n hon => rdLE_congr fun j hj => hP M (fun a ha => hM a (.inl ha)) _ (by
          have := (hE.foot_k rt.k hka).2 (tvalueSize * i + (o + j)) (by
            have := hk0.lt; simp only [tvalueSize] at hon ⊢; omega)
          rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)
      have htag : tagAt (Vsa.Densify.fillZeroMem M) (rt.k + tvalueSize * i) = some vShrStr := by
        have := hk0.tag
        rw [show strTag printKey = vShrStr by decide] at this
        simp only [tagAt, rd8] at this ⊢
        rw [hsl tvalueTagOff 1 (by decide)]; exact this
      have hptr : rd64 (Vsa.Densify.fillZeroMem M) (rt.k + tvalueSize * i + tvalueValOff) = some ts := by
        simp only [rd64] at hk0 ⊢
        rw [hsl tvalueValOff 8 (by decide)]; exact hk0.ptr
      obtain ⟨s', hs'⟩ := Fr.env_get rt.k i ts hkp hk0.lt htag hptr (hstr ts printKey hown)
      have he := hs'.envMem
      rw [hecl, hesl] at he
      exact he.mono fun _ _ h => heapRead_of_apart h hsp hfunc hfits
    · exact ⟨rdW (by simp [luaStaticWords]) hlua.hookmask, rdW (by simp [luaStaticWords]) hlua.errfunc,
        rdW (by simp [luaStaticWords]) hlua.nCcalls, rdW (by simp [luaStaticWords]) hlua.openupval,
        hst ▸ rdW (by simp [luaStaticWords]) hlua.tbclist, hst ▸ rdW (by simp [luaStaticWords]) hlua.stack,
        hsl ▸ rdW (by simp [luaStaticWords]) hlua.stack_last, hg ▸ rdW (by simp [luaStaticWords]) hlua.g,
        rdW (by simp [luaStaticWords]) (hg ▸ hlua.mt_nil), rdW (by simp [luaStaticWords]) (hg ▸ hlua.mt_boolean),
        rdW (by simp [luaStaticWords]) (hg ▸ hlua.mt_number), rdW (by simp [luaStaticWords]) hej.ptr⟩
  · simp only [CallDirty, EntryDirty] at hd ⊢
    rw [heg, hesl]; omega
  · have := hreg.ci_lo; have := hreg.L_lo; have := hreg.stack_lo
    have : Image.rodataBase = 0x8004ecc8 := rfl; have : Image.rodataSize = 55776 := rfl
    have := hpl.g e.g (Nat.le_refl _) (by simp only [gEnd, gStrcacheOff, strcacheN, strcacheM]; omega)
    have := this.lo
    simp only [CallDirty, DlHeap.heapStart, symEnd] at *
    rw [← heg] at hd; omega
  · obtain ⟨rt', hL⟩ := hE.lits (Vsa.Densify.fillZeroMem M) (hPL M hM)
    rw [heg, hesl] at hL
    exact ⟨rt', hL.g, hL.sl, hL.nil.of_fill, hL.tru.of_fill, hL.fls.of_fill⟩
  · simp only [CallLitDirty, LitDirty] at hd ⊢
    rw [hesl]; omega
  · have ho := hE.objs
    have hcs := hreg.ci_sep
    refine ⟨by show Apart rt.g _ _ _; rw [← heg]; exact ho.g_L, by show Apart rt.g _ _ _; rw [← heg]; exact ho.g_ci,
      ?_, ?_, ho.lit_L, fun ts hts => by show Apart _ _ rt.g _; rw [← heg]; exact ho.lit_g ts hts, ho.lit_ci,
      fun ts hts => ?_⟩
    · have := ho.g_stack; show Apart rt.g _ _ _; simp only [Apart] at this ⊢; rw [← heg, ← hesl]; omega
    · show Apart _ _ _ (rt.stackLast - func); simp only [Apart]; omega
    · have := ho.lit_stack ts hts; show Apart _ _ _ (rt.stackLast - func); simp only [Apart] at this ⊢
      rw [← hesl]; omega

/-- **The relation's complement and ranges**, named (`relParts`). -/
structure RelParts (p : Proto) (w : RelPtrs) : Prop where
  comp : Complement p w
  ranges : Ranges p w

/-- **`exit(0)` from a quiet complement** (no `atexit`, no stdio exit
handler): the two words lie in `.bss`, below every heap object. -/
theorem exitOk_entry {m : Mem} {L ci func pa code sp : Nat} {p : Proto} {rt : RtPtrs} {ι : Strs}
    (hat : rd64 m symAtexit = some 0) (hsx : rd64 m symStdioExitHandler = some 0)
    (hrg : VmRegionsAt m L ci rt) (hfunc : rt.func = func) (hle : rt.stack ≤ rt.func) :
    ExitOk p ⟨L, ci, func, pa, code, rt.k, sp, m, ι, rt⟩ := by
  refine Ret.exitOk_of_quiet (bytesT8_of_rd64 hat) (bytesT8_of_rd64 hsx) fun i hi => ?_
  have a1 := hrg.L_lo; have a2 := hrg.ci_lo; have a3 := hrg.stack_lo
  simp only [ExitFree, Slots, RelPtrs.base, stackValueSize, symEnd, symAtexit, symStdioExitHandler,
    RuntimeData.spEntry, cStackBudget, stateSize, ciSize] at a1 a2 a3 ⊢
  omega

/-- **The complement and the ranges from the runtime's memory structures**: a
memory `m` holding the image, the prototype (`ProtoAt`) and the structures of
`RtPostAt` (the heap, the Lua state with `ci->func = func`, the error handler,
the regions, the interned and owned string constants) is the complement of a
relation at those pointers, with `luaV_execute`'s frame below the entry `sp`.
Used at the entry (`entry_at`) and after `OP_VARARGPREP`'s stores
(`Lua.Vm.Sim.entrySim`). -/
theorem relParts {m : Mem} {L ci func pa code sp : Nat} {p : Proto} {rt : RtPtrs}
    (htext : Arms.TextLoaded m) (hro : RodataLoaded m) (hpr : ProtoAt m pa p code)
    (hrt : RtPostAt m L ci rt) (hfunc : rt.func = func) (hpa : rt.proto = pa)
    (hsp : sp = RuntimeData.spEntry - execFrame)
    (hfits : func + stackValueSize * (1 + p.maxstacksize) ≤ rt.stackLast)
    (hcall : SegsAt m RuntimeData.callerFrames)
    (hcL : ∀ a ∈ RuntimeData.callerLSlots, bytesT8 m a = BitVec.ofNat 64 L)
    (hat : rd64 m symAtexit = some 0) (hsx : rd64 m symStdioExitHandler = some 0)
    (hci : rd64 m (L + stateCiOff) = some ci) {f0 : Nat} (hf0 : f0 ≤ func)
    (henv : ∀ ts, KStrIn m rt.k p.k.length ts printKey →
      EnvMem m rt.cl ts (HeapApart L ci f0 rt.stackLast))
    (hcinv : ∀ ι : Strs, ι.own = KStrIn m rt.k p.k.length → CallInv p ⟨L, ci, func, pa, code, rt.k, sp, m, ι, rt⟩) :
    ∃ ι : Strs, RelParts p ⟨L, ci, func, pa, code, rt.k, sp, m, ι, rt⟩ := by
  have hrg := hrt.regions
  have hlua := hrt.lua
  have ecode : code = rt.code := by
    have h := hrg.code; rw [hpa, hpr.code] at h; exact Option.some.inj h
  obtain ⟨hsz, hwords⟩ := hpr.proto.code hpr.code
  obtain ⟨hszk, hkc⟩ := hpr.proto.kArr (ka := rt.k) (by rw [← hpa]; exact hrg.kArr)
  have esizek : rt.sizek = p.k.length := by
    have h := hrg.sizek; rw [hpa, hszk] at h; exact (Option.some.inj h).symm
  obtain ⟨ι, hkι⟩ := hkc (by rw [← esizek]; exact hrt.interned)
  have esz : rt.sizecode = p.code.length := by
    have h := hrg.sizecode; rw [hpa, hsz] at h; exact (Option.some.inj h).symm
  have hsle : rt.stack ≤ func := hfunc ▸ hlua.stack_le
  subst hsp
  refine ⟨⟨ι, KStrIn m rt.k p.k.length⟩, ⟨⟨htext, hro, hpr.proto, hpr.code, fun i ins hf => ?_,
    ?_, ?_, ⟨hfunc, hlua.rel hci, hrt.heap, hrt.error_jmp⟩, hkι,
    own_of_kowned hrt.kowned rfl esizek rfl hsle hfits, hcall, hcL,
    exitOk_entry hat hsx hrg hfunc hlua.stack_le,
    fun ts hts => (henv ts hts).mono fun _ _ h => heapRead_of_apart h rfl hf0 hfits, hcinv _ rfl⟩,
    Ranges.of_regions hrg rfl hfunc.symm ecode rfl esz esizek hlua.stack_le hfits⟩⟩
  · obtain ⟨hlt, hi⟩ := List.getElem?_eq_some_iff.1 hf
    rw [bytesT4_of_rd32 (hwords i hlt), hi, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [← hfunc]; exact bytesT8_of_rd64 hlua.func
  · rw [bytesT4_of_rd32 hlua.trap]; rfl

/-- A read of a store chain at the stored address. -/
theorem bytesT8_wm8_hitE {m : Mem} {a x : Nat} {d : BitVec 64} (h : a = x) :
    bytesT8 (writeMap8 m a (sdData_val d)) x = d := by
  subst h; rw [bytesT8_writeMap8, sdData_id]

/-- A read of a store chain past a store it misses. -/
theorem bytesT8_wm8_missE {m : Mem} {a x : Nat} {d : BitVec (8 * 8)} (h : x + 8 ≤ a ∨ a + 8 ≤ x) :
    bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
  bytesT8_congr fun _ _ => getElem?_writeMap8_out m a d _ (by omega)

/-- **The entry run's facts** (`entry_at`): the prologue's run from `c` to the
fetch head `c'` in the relation with pointers `w`, the entry data `e` and the
witness `w.rt` at `c`, the complement memory `c`'s, and the prologue's stores
in its C frame (with the closure saved at `8(sp)`). -/
structure EntryAt (p : Proto) (c c' : Vsa.Machine.Config) (w : RelPtrs) (e : EntryPtrs) : Prop where
  steps : Vsa.Machine.Steps c c'
  rel : VmRelAt p c' State.init w
  entry : VmEntryData c.σ.mem w.L w.ci p e
  ready : RuntimeReadyAt c w.L w.ci w.rt
  mo : w.mo = c.σ.mem
  sp : w.sp = RuntimeData.spEntry - execFrame
  efunc : e.func = w.func
  rt_func : w.rt.func = w.func
  epa : e.pa = w.pa
  rt_proto : w.rt.proto = w.pa
  rt_k : w.k = w.rt.k
  ecode : e.code = w.code
  ecl : e.cl = w.rt.cl
  esl : e.stackLast = w.rt.stackLast
  agree : AgreeOut c'.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry
  clslot : bytesT8 c'.σ.mem (w.sp + 8) = BitVec.ofNat 64 w.rt.cl

/-- **The prologue's first segment** (`seg_8001bf68_8001bfb0`, to `startfunc`):
the frame `addi sp,sp,-176`, the saves of `ra`, `s0 … s11` (their values the
callers', `CStackAt`), `L`, `ci` and the jump table in `s0`, `s7`, `s8`. -/
structure EntryHead (c c1 : Vsa.Machine.Config) (L ci : Nat) : Prop where
  steps : Vsa.Machine.Steps c c1
  seg : SegSt 0x8001bfb0#64 [⟨Register.x23, BitVec.ofNat 64 ci⟩, ⟨Register.x8, BitVec.ofNat 64 L⟩,
    ⟨Register.x2, BitVec.ofNat 64 (RuntimeData.spEntry - execFrame)⟩,
    ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩, ⟨Register.x24, BitVec.ofNat 64 Arms.jtBase⟩]
    (ArmPay c1.σ.mem c.σ.sailOutput) c1
  agree : AgreeOut c1.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry
  ra : bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + 168) = BitVec.ofNat 64 RuntimeData.retCcall
  s0 : bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + 160) = BitVec.ofNat 64 L
  saved : ∀ (r v : Nat), (r, v) ∈ RuntimeData.calleeSavedEntry →
    bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + savedOff r) = BitVec.ofNat 64 v

-- discipline: allow(R7-conj-tower-def) the one existential is the run's end
-- state, its facts the named-field structure `EntryHead`
/-- **The first segment of the prologue runs** (`EntryHead`). -/
theorem entry_head {c : Vsa.Machine.Config} {L ci : Nat} (hM : MachineAt c L ci)
    (hcs : CStackAt c.σ) (htick : c.tick < 2) : ∃ c1, EntryHead c c1 L ci := by
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
      hcs.gp, trivial⟩, hM.good.minstret, htick, ⟨hM.text, rfl, rfl, hM.regs⟩⟩
  have hA1 : AgreeOut c1.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry := by
    rw [hq1.armMem]
    repeat (refine AgreeOut.writeMap8 ?_ _ (by decide) (by decide))
    exact AgreeOut.refl _ _ _
  have hp1 := hq1.pins
  have hx24 : c1.σ.regs.get? Register.x24 = some (BitVec.ofNat 64 Arms.jtBase) := by
    have h := pinsHold_get hp1 0 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx23 : c1.σ.regs.get? Register.x23 = some (BitVec.ofNat 64 ci) := by
    have h := pinsHold_get hp1 1 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [add_imm _ 0 (by decide), Nat.add_zero] at h; exact h
  have hx8 : c1.σ.regs.get? Register.x8 = some (BitVec.ofNat 64 L) := by
    have h := pinsHold_get hp1 2 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [add_imm _ 0 (by decide), Nat.add_zero] at h; exact h
  have hx2 : c1.σ.regs.get? Register.x2 =
      some (BitVec.ofNat 64 (RuntimeData.spEntry - execFrame)) := by
    have h := pinsHold_get hp1 3 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have e8 : v8 = BitVec.ofNat 64 L := Option.some.inj (h8.symm.trans (hcs.s0.trans hM.a0))
  have esv : ∀ (r v : Nat) (x : BitVec 64), (r, v) ∈ RuntimeData.calleeSavedEntry →
      gprGet c.σ r = some x → x = BitVec.ofNat 64 v := fun r v x hm hx =>
    Option.some.inj (hx.symm.trans (hcs.saved (r, v) hm))
  have e9 := esv 9 0 v9 (by decide) h9
  have e18 := esv 18 0x10 v18 (by decide) h18
  have e19 := esv 19 0x8006ed48 v19 (by decide) h19
  have e20 := esv 20 1 v20 (by decide) h20
  have e21 := esv 21 0 v21 (by decide) h21
  have e22 := esv 22 0 v22 (by decide) h22
  have e23 := esv 23 0 v23 (by decide) h23
  have e24 := esv 24 0 v24 (by decide) h24
  have e25 := esv 25 0 v25 (by decide) h25
  have e26 := esv 26 0 v26 (by decide) h26
  have e27 := esv 27 0 v27 (by decide) h27
  have hsv1 : ∀ (r v : Nat), (r, v) ∈ RuntimeData.calleeSavedEntry →
      bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + savedOff r) = BitVec.ofNat 64 v := by
    intro r v hrv
    simp only [RuntimeData.calleeSavedEntry, List.mem_cons, List.not_mem_nil, or_false,
      Prod.mk.injEq] at hrv
    rw [hq1.armMem]
    rcases hrv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals simp (disch := decide) only [bytesT8_wm8_hitE, bytesT8_wm8_missE, e9, e18, e19,
      e20, e21, e22, e23, e24, e25, e26, e27]
  have hra1 : bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + 168) =
      BitVec.ofNat 64 RuntimeData.retCcall := by
    rw [hq1.armMem]
    simp (disch := decide) only [bytesT8_wm8_hitE, bytesT8_wm8_missE]
  have hs01 : bytesT8 c1.σ.mem (RuntimeData.spEntry - execFrame + 160) = BitVec.ofNat 64 L := by
    rw [hq1.armMem]
    simp (disch := decide) only [bytesT8_wm8_hitE, bytesT8_wm8_missE, e8]
  refine ⟨c1, hs1, ?_, hA1, hra1, hs01, hsv1⟩
  exact ⟨hq1.good, hq1.pcAt, ⟨hx23, hx8, hx2, pinsHold_get hp1 16 (by simp only [List.length_cons, List.length_nil]; omega), hx24, trivial⟩,
    hq1.minstret, hq1.tick, ⟨hq1.armText, rfl, hq1.armOut, hq1.armOk⟩⟩

set_option linter.unusedSimpArgs false in
/-- **The entry run (A1).** The prologue runs from the entry to the fetch
head, in the relation with the initial state (`EntryAt`). -/
theorem entry_at {p : Proto} {c : Vsa.Machine.Config} (hL : VmLoaded luaLayout p c) :
    ∃ c' w e, EntryAt p c c' w e := by
  obtain ⟨L, ci, e, hM, hE, rt, hRt⟩ := hL
  have hcs := hRt.cstack
  obtain ⟨c1, hH⟩ := entry_head hM hcs hRt.harness.tick
  have hs1 := hH.steps
  have hA1 := hH.agree
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
  have esz : rt.sizecode = p.code.length := by
    have h := hrg.sizecode; rw [← epa, hsz] at h; exact (Option.some.inj h).symm
  have eg : e.g = rt.g := Option.some.inj (hE.l_G.symm.trans hlua.g)
  have hszk : rt.sizek = p.k.length := by
    have h := hrg.sizek; rw [← epa, (hE.proto.kArr (by rw [epa]; exact hrg.kArr)).1] at h
    exact (Option.some.inj h).symm
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
  have H2 := Arms.seg_8001bfb0_8001bfe4 (BitVec.ofNat 64 ci) (BitVec.ofNat 64 L)
    (BitVec.ofNat 64 (RuntimeData.spEntry - execFrame)) (BitVec.ofNat 64 symGlobalPointer)
    (BitVec.ofNat 64 Arms.jtBase) c1.σ.mem c.σ.sailOutput
  repeat (specialize H2 (by
    first
      | (simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
          Nat.mod_eq_of_lt, hRci, hRpc, hRhook, hRfunc, hRcl, hTH]; omega)
      | decide
      | (simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
          Nat.mod_eq_of_lt, hRci, hRpc, hRhook, hRfunc, hRcl, hTH]; decide)))
  obtain ⟨c2, hs2, hq2⟩ := H2 c1 hH.seg
  -- the fetch-head registers
  have hp2 := hq2.pins
  have hx25 : c2.σ.regs.get? Register.x25 = some (BitVec.ofNat 64 (e.func + 16)) := by
    have h := pinsHold_get hp2 0 (by simp only [List.length_cons, List.length_nil]; omega)
    simp (disch := omega) only [List.getElem_cons_zero, add_imm, BitVec.toNat_ofNat,
      Nat.add_zero, sext64, Nat.mod_eq_of_lt, hRci] at h
    exact h
  have hx18 : c2.σ.regs.get? Register.x18 = some (BitVec.ofNat 64 vNumInt) := by
    have h := pinsHold_get hp2 2 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx9 : c2.σ.regs.get? Register.x9 = some (BitVec.ofNat 64 (Arms.jtEntries - 1)) := by
    have h := pinsHold_get hp2 3 (by simp only [List.length_cons, List.length_nil]; omega)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    exact h.trans (congrArg some (by decide))
  have hx21 : c2.σ.regs.get? Register.x21 = some (0#64) := by
    have h := pinsHold_get hp2 4 (by simp only [List.length_cons, List.length_nil]; omega)
    simp (disch := omega) only [List.getElem_cons_succ, List.getElem_cons_zero, add_imm,
      BitVec.toNat_ofNat, Nat.add_zero, Nat.mod_eq_of_lt, hRhook] at h
    exact h.trans (congrArg some (by decide))
  have hx27 : c2.σ.regs.get? Register.x27 = some (BitVec.ofNat 64 (e.code + 4 * 0)) := by
    have h := pinsHold_get hp2 5 (by simp only [List.length_cons, List.length_nil]; omega)
    simp (disch := omega) only [List.getElem_cons_succ, List.getElem_cons_zero, add_imm,
      BitVec.toNat_ofNat, Nat.add_zero, sext64, Nat.mod_eq_of_lt, hRpc] at h
    exact h
  -- the memory frame: every store of the prologue is in its C frame
  have hA2 : AgreeOut c2.σ.mem c.σ.mem (RuntimeData.spEntry - execFrame) RuntimeData.spEntry := by
    rw [hq2.armMem]
    exact (hA1.writeMap8 _ (by decide) (by decide)).writeMap8 _ (by decide) (by decide)
  -- the saved words: only the prologue's first segment writes `72…175(sp)`
  have hA12 : AgreeOut c2.σ.mem c1.σ.mem (RuntimeData.spEntry - execFrame)
      (RuntimeData.spEntry - execFrame + 16) := by
    rw [hq2.armMem]
    exact ((AgreeOut.refl _ _ _).writeMap8 _ (by decide) (by decide)).writeMap8 _ (by decide)
      (by decide)
  have hfr12 : ∀ x, RuntimeData.spEntry - execFrame + 72 ≤ x →
      x < RuntimeData.spEntry - execFrame + execFrame → c2.σ.mem[x]? = c1.σ.mem[x]? :=
    fun x h1 _ => hA12 x (.inr (by omega))
  -- `0(sp)` holds `k`
  have hkp : bytesT8 c2.σ.mem (RuntimeData.spEntry - execFrame) = BitVec.ofNat 64 rt.k := by
    rw [hq2.armMem]
    simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
      Nat.mod_eq_of_lt, hRci, hRfunc, hRcl, hRk, bytesT8_writeMap8, sdData_id]
  simp only [stackValueSize] at hfits
  obtain ⟨ι', hP⟩ := relParts (L := L) (ci := ci) (sp := RuntimeData.spEntry - execFrame)
    hM.text hM.rodata ⟨hE.proto, hE.proto_code⟩
    ⟨hRt.heap, hlua, hRt.error_jmp, hrg, hRt.interned, hRt.kowned⟩ efunc.symm epa.symm rfl
    (by rw [← esl]; exact hE.frame_fits) hRt.cstack.callers
    (fun a ha => bytesT8_of_rd64 (hRt.callerL a ha)) hRt.stdio.atexit hRt.stdio.exit_handler hE.ci_eq
    (f0 := e.func) (Nat.le_refl _) (by
      rw [← ecl, ← esl]
      exact envMem_of_entry hE (fun _ _ => rfl) (by rw [epa]; exact hrg.kArr))
    (fun ι hι => callInv_boot hE hRt.stdio hRt.memfs hM.rodata hRt.error_jmp hlua hRt.heap hcs.dense
      (fun _ _ => rfl) hlua.next (fun a h1 h2 => hcs.dense a h1 h2) hRt.kowned hrg hι hszk (by rw [epa]; exact hrg.kArr) rfl rfl rfl eg esl ecl
      (Nat.le_refl _) rfl (by rw [← esl]; exact hE.frame_fits))
  have hwo : ∀ {m : Mem} {a x : Nat} {d : BitVec (8 * 8)}, x + 8 ≤ a ∨ a + 8 ≤ x →
      bytesT8 (writeMap8 m a d) x = bytesT8 m x :=
    fun h => bytesT8_congr fun _ _ => getElem?_writeMap8_out _ _ _ _ (by omega)
  have hcl8 : bytesT8 c2.σ.mem (RuntimeData.spEntry - execFrame + 8) = BitVec.ofNat 64 rt.cl := by
    rw [hq2.armMem]
    simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
      Nat.mod_eq_of_lt, hRci, hRfunc]
    rw [hwo (by simp only [RuntimeData.spEntry, execFrame]; omega), bytesT8_writeMap8, sdData_id]
    simp (disch := omega) only [add_imm, BitVec.toNat_ofNat, Nat.add_zero, sext64,
      Nat.mod_eq_of_lt, hRci, hRfunc, ecl]
  refine ⟨c2, ⟨L, ci, e.func, e.pa, e.code, rt.k, RuntimeData.spEntry - execFrame,
    c.σ.mem, ι', rt⟩, e,
    { steps := hs1.trans hs2
      rel := ⟨⟨hq2.good, hq2.minstret, hq2.tick,
        ⟨pinsHold_get hp2 10 (by simp only [List.length_cons, List.length_nil]; omega), pinsHold_get hp2 11 (by simp only [List.length_cons, List.length_nil]; omega),
          pinsHold_get hp2 9 (by simp only [List.length_cons, List.length_nil]; omega), hx9, hx18, hx21, pinsHold_get hp2 8 (by simp only [List.length_cons, List.length_nil]; omega),
          pinsHold_get hp2 12 (by simp only [List.length_cons, List.length_nil]; omega), hx25, hx27⟩,
        (output_congr hq2.armOut).trans hRt.harness.console, hq2.armOk,
        hq2.armText, fun a ha => congrArg (Option.getD · 0) (hA2 a ?_), hkp,
        hcl8, fun j v _ h => ?_, hP.comp, hP.ranges,
        SavedAt.congr (w := ⟨L, ci, e.func, e.pa, e.code, rt.k, RuntimeData.spEntry - execFrame,
          c.σ.mem, ι', rt⟩) ⟨hH.ra, hH.s0, fun rv hrv => hH.saved rv.1 rv.2 hrv⟩ hfr12⟩, hq2.pcAt⟩
      entry := hE
      ready := hRt
      mo := rfl
      sp := rfl
      efunc := rfl
      rt_func := efunc.symm
      epa := rfl
      rt_proto := epa.symm
      rt_k := rfl
      ecode := rfl
      ecl := ecl
      esl := esl
      agree := hA2
      clslot := hcl8 }⟩
  · simp only [Win, Slots, Scratch, RelPtrs.base, stackValueSize] at ha; omega
  · simp [State.init] at h

/-- **The entry lemma (A1).** The prologue runs from the entry to the fetch
head, in the relation with the initial state. -/
theorem vmRel_entry : vmRel_entry_Statement := fun _ _ _ hL =>
  let ⟨c', w, _, h⟩ := entry_at hL
  ⟨c', h.steps, w, h.rel⟩

end Lua.Vm.Sim

import Lua.Vm.Boot.Heap
import Lua.Vm.Boot.Image
import Lua.Vm.Runtime

/-!
# One Bool check per structure of `VmLoaded luaLayout` over a byte view

The kernel side of the boot witness (PHASES A0.6). Each checker below decides
one structure of `VmEntryData` (`Lua/Vm/Repr.lean`) or `RuntimeReadyAt`
(`Lua/Vm/Runtime.lean`) over a byte view `v` (`Lua/Vm/Boot/View.lean`), and its
soundness lemma turns a passing check into the structure for every memory `m`
with `PartialView m v`. A program's witness (`Lua/Vm/Boot/Witness/<Prog>.lean`,
generated) is then one `decide +kernel` per checker at `bootView chunk runs`,
never a reduction of a memory image.

* `readsOk`: a list of little-endian reads `(addr, width, value)`; most fields
  are one read each (`PartialView.reads`).
* `tstrCheck`, `constCheck`, `protoCheck`: `TStringRepr`, `ConstRepr`,
  `ProtoRepr` (no nested prototypes: F1's chunks have none).
* `strNe`/`strDiff`: the view shows two short strings differ, which is how
  `KInterned` and `VmEntryData.env_print_ptr` (pointer equality of interned
  strings) are decided: a pair with distinct pointers must differ in bytes.
* `entryCheck`, `errorJmpCheck`, `stdioCheck`, `memfsCheck`, `luaStateCheck`,
  `regionsCheck`, `internedCheck`, `heapCheck`: the structures.
* `runsAvoid`: no boot store lands in `.text`/`.rodata`, so the view there is
  the loader's (`MachineAt.text`/`rodata`).
-/

namespace Lua.Vm.Boot

open Lua.Vm Lua.Vm.Layout Lua.Bytecode

abbrev r8 (v : View) (a : Nat) : Option Nat := rdLEf v a 1
abbrev r16 (v : View) (a : Nat) : Option Nat := rdLEf v a 2
abbrev r32 (v : View) (a : Nat) : Option Nat := rdLEf v a 4

/-! ## Reads -/

/-- Each `(a, n, x)` reads `x` from the `n` bytes at `a`. -/
def readsOk (v : View) (rs : List (Nat × Nat × Nat)) : Bool :=
  rs.all fun r => rdLEf v r.1 r.2.1 == some r.2.2

theorem _root_.Lua.Vm.PartialView.reads {m : Mem} {v : View} (h : PartialView m v)
    {rs : List (Nat × Nat × Nat)} (hc : readsOk v rs = true) {a n x : Nat}
    (hm : (a, n, x) ∈ rs) : rdLE m a n = some x :=
  h.rdLE (by simpa using List.all_eq_true.mp hc _ hm)

/-- Find a triple in a literal list of reads. -/
syntax "mem_tac" : tactic
macro_rules
  | `(tactic| mem_tac) =>
    `(tactic| first | exact List.Mem.head _ | (apply List.Mem.tail; mem_tac))

theorem rd8_of_get {m : Mem} {a : Nat} {b : BitVec 8} (h : m[a]? = some b) :
    rd8 m a = some b.toNat := by
  simp [rd8, rdLE, h]

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## Strings -/

/-- `TStringRepr m ts s` over the view. -/
def tstrCheck (v : View) (ts : Nat) (s : List UInt8) : Bool :=
  (if s.length ≤ maxShortLen then
    readsOk v [(ts + gcTtOff, 1, gcShrStr), (ts + tstringShrlenOff, 1, s.length)]
  else
    readsOk v [(ts + gcTtOff, 1, gcLngStr), (ts + tstringLnglenOff, 8, s.length)]) &&
  bytesOk v (ts + tstringContentsOff) s && v (ts + tstringContentsOff + s.length) == some 0

theorem tstrCheck_sound {m : Mem} {v : View} (h : PartialView m v) {ts : Nat} {s : List UInt8}
    (hc : tstrCheck v ts s = true) : TStringRepr m ts s := by
  simp only [tstrCheck, Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hr, hb⟩, hz⟩ := hc
  have hbytes := h.bytesAt hb
  have hzero := h _ _ hz
  split at hr
  · exact .short (h.reads hr (by mem_tac)) ‹_› (h.reads hr (by mem_tac)) hbytes hzero
  · exact .long (h.reads hr (by mem_tac)) (by omega) (h.reads hr (by mem_tac)) hbytes hzero

theorem _root_.Lua.Vm.TStringRepr.short_len {m : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr m ts s)
    (hs : s.length ≤ maxShortLen) : rd8 m (ts + tstringShrlenOff) = some s.length := by
  cases h with
  | short _ _ hl _ _ => exact hl
  | long _ hlt _ _ _ => omega

theorem _root_.Lua.Vm.TStringRepr.byte {m : Mem} {ts : Nat} {s : List UInt8} (h : TStringRepr m ts s)
    {j : Nat} (hj : j < s.length) :
    rd8 m (ts + tstringContentsOff + j) = some (s[j]).toNat := by
  have hb : BytesAt m (ts + tstringContentsOff) s := by
    cases h with
    | short _ _ _ hb _ => exact hb
    | long _ _ _ hb _ => exact hb
  rw [rd8_of_get (hb j hj), BitVec.toNat_ofNat, Nat.mod_eq_of_lt (UInt8.toNat_lt _)]

/-- The view shows that the short string at `ts` is not `s`: a different
length, or a different byte. -/
def strNe (v : View) (ts : Nat) (s : List UInt8) : Bool :=
  match r8 v (ts + tstringShrlenOff) with
  | some n => n != s.length || (List.range n).any fun j =>
      match r8 v (ts + tstringContentsOff + j) with
      | some b => b != (s.getD j 0).toNat
      | none => false
  | none => false

theorem strNe_sound {m : Mem} {v : View} (h : PartialView m v) {ts : Nat} {s : List UInt8}
    (hc : strNe v ts s = true) (hs : s.length ≤ maxShortLen) (hr : TStringRepr m ts s) : False := by
  unfold strNe at hc
  split at hc
  · rename_i n hn
    obtain rfl := Option.some.inj ((h.rd8 hn).symm.trans (hr.short_len hs))
    simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, List.mem_range] at hc
    obtain ⟨j, hj, hb⟩ := hc
    split at hb
    · rename_i b hbv
      obtain rfl := Option.some.inj ((h.rd8 hbv).symm.trans (hr.byte hj))
      rw [getD_of_lt _ hj] at hb
      simp at hb
    · cases hb
  · cases hc

/-- The view shows that the short strings at `x` and `y` differ. -/
def strDiff (v : View) (x y : Nat) : Bool :=
  match r8 v (x + tstringShrlenOff), r8 v (y + tstringShrlenOff) with
  | some n, some n' => n != n' || (List.range n).any fun j =>
      match r8 v (x + tstringContentsOff + j), r8 v (y + tstringContentsOff + j) with
      | some a, some b => a != b
      | _, _ => false
  | _, _ => false

theorem strDiff_sound {m : Mem} {v : View} (h : PartialView m v) {x y : Nat} {s : List UInt8}
    (hc : strDiff v x y = true) (hs : s.length ≤ maxShortLen)
    (hx : TStringRepr m x s) (hy : TStringRepr m y s) : False := by
  unfold strDiff at hc
  split at hc
  · rename_i n n' hn hn'
    obtain rfl := Option.some.inj ((h.rd8 hn).symm.trans (hx.short_len hs))
    obtain rfl := Option.some.inj ((h.rd8 hn').symm.trans (hy.short_len hs))
    simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, List.mem_range] at hc
    obtain ⟨j, hj, hb⟩ := hc
    split at hb
    · rename_i a b ha hb'
      obtain rfl := Option.some.inj ((h.rd8 ha).symm.trans (hx.byte hj))
      obtain rfl := Option.some.inj ((h.rd8 hb').symm.trans (hy.byte hj))
      simp at hb
    · cases hb
  · cases hc

/-- The `TValue` at `a` over the view: `some none` if it is not a short string,
`some (some x)` if it is the short string at `x`, `none` if bytes are missing. -/
def shrAt (v : View) (a : Nat) : Option (Option Nat) :=
  match r8 v (a + tvalueTagOff) with
  | some t => if t = vShrStr then (r64 v (a + tvalueValOff)).map some else some none
  | none => none

theorem shrAt_sound {m : Mem} {v : View} (h : PartialView m v) {a x : Nat} {o : Option Nat}
    (hc : shrAt v a = some o) (ht : tagAt m a = some vShrStr)
    (hx : rd64 m (a + tvalueValOff) = some x) : o = some x := by
  unfold shrAt at hc
  split at hc
  · rename_i t htv
    obtain rfl := Option.some.inj ((h.rd8 htv).symm.trans ht)
    rw [if_pos rfl] at hc
    cases hv : r64 v (a + tvalueValOff) with
    | none => rw [hv] at hc; cases hc
    | some x' =>
      rw [hv] at hc
      obtain rfl := Option.some.inj ((h.rd64 hv).symm.trans hx)
      exact (Option.some.inj hc).symm
  · cases hc

/-! ## Prototypes -/

def upvalCheck (v : View) (a : Nat) (u : UpvalDesc) : Bool :=
  readsOk v [(a + upvaldescInstackOff, 1, if u.instack then 1 else 0),
    (a + upvaldescIdxOff, 1, u.idx), (a + upvaldescKindOff, 1, u.kind)]

theorem upvalCheck_sound {m : Mem} {v : View} (h : PartialView m v) {a : Nat} {u : UpvalDesc}
    (hc : upvalCheck v a u = true) : UpvalDescRepr m a u :=
  ⟨h.reads hc (by mem_tac), h.reads hc (by mem_tac), h.reads hc (by mem_tac)⟩

/-- `ConstRepr m a c` over the view. -/
def constCheck (v : View) (a : Nat) : Const → Bool
  | .nil => readsOk v [(a + tvalueTagOff, 1, vNil)]
  | .bool true => readsOk v [(a + tvalueTagOff, 1, vTrue)]
  | .bool false => readsOk v [(a + tvalueTagOff, 1, vFalse)]
  | .int i => readsOk v [(a + tvalueTagOff, 1, vNumInt), (a + tvalueValOff, 8, i.toNat)]
  | .float b => readsOk v [(a + tvalueTagOff, 1, vNumFlt), (a + tvalueValOff, 8, b.toNat)]
  | .str s => readsOk v [(a + tvalueTagOff, 1, strTag s)] &&
      match r64 v (a + tvalueValOff) with
      | some ts => tstrCheck v ts s
      | none => false

theorem constCheck_sound {m : Mem} {v : View} (h : PartialView m v) {a : Nat} :
    ∀ {c : Const}, constCheck v a c = true → ConstRepr m a c
  | .nil, hc => .nil (h.reads hc (by mem_tac))
  | .bool true, hc => .bool (.true_ (h.reads hc (by mem_tac)))
  | .bool false, hc => .bool (.false_ (h.reads hc (by mem_tac)))
  | .int _, hc => .int (.int (h.reads hc (by mem_tac)) (h.reads hc (by mem_tac)))
  | .float _, hc => .float (h.reads hc (by mem_tac)) (h.reads hc (by mem_tac))
  | .str s, hc => by
    simp only [constCheck, Bool.and_eq_true] at hc
    obtain ⟨hr, hs⟩ := hc
    cases hts : r64 v (a + tvalueValOff) with
    | none => rw [hts] at hs; cases hs
    | some ts =>
      rw [hts] at hs
      exact .str (.str (h.reads hr (by mem_tac)) (h.rd64 hts) (tstrCheck_sound h hs))

/-- `ProtoRepr m pa p` over the view, for a prototype without nested ones. -/
def protoCheck (v : View) (pa : Nat) : Proto → Bool
  | .mk np va ms code k ups protos =>
    protos.isEmpty &&
    readsOk v [(pa + gcTtOff, 1, 10), (pa + protoNumparamsOff, 1, np),
      (pa + protoIsVarargOff, 1, if va then 1 else 0), (pa + protoMaxstacksizeOff, 1, ms),
      (pa + protoSizecodeOff, 4, code.length), (pa + protoSizekOff, 4, k.length),
      (pa + protoSizeupvaluesOff, 4, ups.length), (pa + protoSizepOff, 4, 0)] &&
    (match r64 v (pa + protoCodeOff) with
     | some ca => (List.range code.length).all fun i =>
         r32 v (ca + 4 * i) == some (code.getD i 0).toNat
     | none => false) &&
    (match r64 v (pa + protoKOff) with
     | some ka => (List.range k.length).all fun i =>
         constCheck v (ka + tvalueSize * i) (k.getD i .nil)
     | none => false) &&
    (match r64 v (pa + protoUpvaluesOff) with
     | some ua => (List.range ups.length).all fun i =>
         upvalCheck v (ua + upvaldescSize * i) (ups.getD i default)
     | none => false) &&
    (r64 v (pa + protoPOff)).isSome

theorem protoCheck_sound {m : Mem} {v : View} (h : PartialView m v) {pa : Nat} {p : Proto}
    (hc : protoCheck v pa p = true) : ProtoRepr m pa p := by
  obtain ⟨np, va, ms, code, k, ups, protos⟩ := p
  cases protos with
  | cons => simp [protoCheck] at hc
  | nil =>
    simp only [protoCheck, List.isEmpty_nil, Bool.true_and, Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨hr, hcode⟩, hk⟩, hu⟩, hp⟩ := hc
    cases hca : r64 v (pa + protoCodeOff) with
    | none => rw [hca] at hcode; cases hcode
    | some ca =>
    cases hka : r64 v (pa + protoKOff) with
    | none => rw [hka] at hk; cases hk
    | some ka =>
    cases hua : r64 v (pa + protoUpvaluesOff) with
    | none => rw [hua] at hu; cases hu
    | some ua =>
    cases hpp : r64 v (pa + protoPOff) with
    | none => rw [hpp] at hp; cases hp
    | some pp =>
    rw [hca] at hcode
    rw [hka] at hk
    rw [hua] at hu
    refine ProtoRepr.mk (ca := ca) (ka := ka) (ua := ua) (pp := pp) (ptrs := [])
      (h.reads hr (by mem_tac)) (h.reads hr (by mem_tac)) (h.reads hr (by mem_tac))
      (h.reads hr (by mem_tac)) (h.reads hr (by mem_tac)) (h.rd64 hca) ?_
      (h.reads hr (by mem_tac)) (h.rd64 hka) ?_
      (h.reads hr (by mem_tac)) (h.rd64 hua) ?_
      (h.reads hr (by mem_tac)) (h.rd64 hpp) rfl (fun i hi => absurd hi (by simp)) .nil
    · intro i hi
      have := List.all_eq_true.mp hcode i (List.mem_range.mpr hi)
      rw [getD_of_lt _ hi] at this
      exact h.rd32 (by simpa using this)
    · intro i hi
      have := List.all_eq_true.mp hk i (List.mem_range.mpr hi)
      rw [getD_of_lt _ hi] at this
      exact constCheck_sound h this
    · intro i hi
      have := List.all_eq_true.mp hu i (List.mem_range.mpr hi)
      rw [getD_of_lt _ hi] at this
      exact upvalCheck_sound h this

/-! ## `VmEntryData` -/

/-- `_ENV`'s node `i` of `2^lsz` at `node` has the key pointer `ts` and `print`. -/
def slotCheck (v : View) (t lsz node i ts : Nat) : Bool :=
  decide (i < 2 ^ lsz) &&
  readsOk v [(t + tableLsizenodeOff, 1, lsz), (t + tableNodeOff, 8, node),
    (node + nodeSize * i + nodeKeyTtOff, 1, vShrStr), (node + nodeSize * i + nodeKeyValOff, 8, ts),
    (node + nodeSize * i + tvalueTagOff, 1, vLcf), (node + nodeSize * i + tvalueValOff, 8, symLuaBPrint)]

theorem slotCheck_ptr {m : Mem} {v : View} (h : PartialView m v) {t lsz node i ts : Nat}
    (hc : slotCheck v t lsz node i ts = true) : TableHasShortKeyPtr m t ts (.builtin .print) := by
  simp only [slotCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hi, hr⟩ := hc
  exact ⟨lsz, node, i, h.reads hr (by mem_tac), h.reads hr (by mem_tac), hi,
    h.reads hr (by mem_tac), h.reads hr (by mem_tac),
    .print (h.reads hr (by mem_tac)) (h.reads hr (by mem_tac))⟩

theorem slotCheck_key {m : Mem} {v : View} (h : PartialView m v) {t lsz node i ts : Nat}
    (hc : slotCheck v t lsz node i ts = true) (hs : tstrCheck v ts printKey = true) :
    TableHasShortKey m t printKey (.builtin .print) := by
  obtain ⟨lsz, node, i, h1, h2, h3, h4, h5, h6⟩ := slotCheck_ptr h hc
  exact ⟨lsz, node, i, ts, h1, h2, h3, h4, h5, tstrCheck_sound h hs, h6⟩

/-- Every short-string constant of the prototype at `pa` (`sizek` constants)
is the pointer `ts`, or the view shows its bytes are not `"print"`. -/
def printPtrCheck (v : View) (pa sizek ts : Nat) : Bool :=
  match r64 v (pa + protoKOff) with
  | some ka => (List.range sizek).all fun i =>
      match shrAt v (ka + tvalueSize * i) with
      | some none => true
      | some (some x) => x == ts || strNe v x printKey
      | none => false
  | none => false

theorem printKey_short : printKey.length ≤ maxShortLen := by decide

theorem printPtrCheck_sound {m : Mem} {v : View} (h : PartialView m v) {pa sizek ts : Nat}
    (hc : printPtrCheck v pa sizek ts = true) {ka i x : Nat}
    (hka : rd64 m (pa + protoKOff) = some ka) (hi : i < sizek)
    (ht : tagAt m (ka + tvalueSize * i) = some vShrStr)
    (hx : rd64 m (ka + tvalueSize * i + tvalueValOff) = some x)
    (hs : TStringRepr m x printKey) : x = ts := by
  unfold printPtrCheck at hc
  split at hc
  · rename_i ka' hka'
    obtain rfl := Option.some.inj ((h.rd64 hka').symm.trans hka)
    have hi' := List.all_eq_true.mp hc i (List.mem_range.mpr hi)
    split at hi'
    · rename_i hsh
      cases shrAt_sound h hsh ht hx
    · rename_i x' hsh
      obtain rfl := Option.some.inj (shrAt_sound h hsh ht hx)
      simp only [Bool.or_eq_true, beq_iff_eq] at hi'
      rcases hi' with hi' | hi'
      · exact hi'
      · exact (strNe_sound h hi' printKey_short hs).elim
    · cases hi'
  · cases hc

/-- `_ENV.print`'s node: `(lsizenode, node array, index, key string)`. -/
structure PrintSlot where
  lsz : Nat
  node : Nat
  idx : Nat
  ts : Nat

/-- Every field of `VmEntryData m L ci p e` over the view. -/
def entryCheck (v : View) (L ci : Nat) (p : Proto) (e : EntryPtrs) (slot : PrintSlot) : Bool :=
  readsOk v [(L + stateCiOff, 8, ci), (ci + ciFuncOff, 8, e.func), (e.func + tvalueTagOff, 1, vLcl),
    (e.func + tvalueValOff, 8, e.cl), (e.cl + lclosureProtoOff, 8, e.pa),
    (e.pa + protoCodeOff, 8, e.code), (ci + ciSavedpcOff, 8, e.code),
    (e.cl + lclosureUpvalsOff, 8, e.uv), (e.uv + upvalVOff, 8, e.envv),
    (e.envv + tvalueTagOff, 1, vTable), (e.envv + tvalueValOff, 8, e.env), (L + stateGOff, 8, e.g),
    (e.g + gGcstpOff, 1, gcstpUsr), (L + stateStackLastOff, 8, e.stackLast)] &&
  protoCheck v e.pa p &&
  slotCheck v e.env slot.lsz slot.node slot.idx slot.ts &&
  tstrCheck v slot.ts printKey &&
  printPtrCheck v e.pa p.k.length slot.ts &&
  decide (e.func + stackValueSize * (1 + p.maxstacksize) ≤ e.stackLast)

theorem entryCheck_sound {m : Mem} {v : View} (h : PartialView m v) {L ci : Nat} {p : Proto}
    {e : EntryPtrs} {slot : PrintSlot} (hc : entryCheck v L ci p e slot = true) :
    VmEntryData m L ci p e := by
  simp only [entryCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨⟨hr, hp⟩, hslot⟩, hkey⟩, hptr⟩, hfit⟩ := hc
  exact
    { ci_eq := h.reads hr (by mem_tac)
      ci_func := h.reads hr (by mem_tac)
      func_tag := h.reads hr (by mem_tac)
      func_val := h.reads hr (by mem_tac)
      cl_proto := h.reads hr (by mem_tac)
      proto := protoCheck_sound h hp
      proto_code := h.reads hr (by mem_tac)
      savedpc := h.reads hr (by mem_tac)
      cl_upval0 := h.reads hr (by mem_tac)
      uv_v := h.reads hr (by mem_tac)
      env_tag := h.reads hr (by mem_tac)
      env_val := h.reads hr (by mem_tac)
      env_print := slotCheck_key h hslot hkey
      env_print_ptr := fun _ _ _ hka hi ht hx hs => by
        rw [printPtrCheck_sound h hptr hka hi ht hx hs]
        exact slotCheck_ptr h hslot
      l_G := h.reads hr (by mem_tac)
      gc_stopped := h.reads hr (by mem_tac)
      stack_last := h.reads hr (by mem_tac)
      frame_fits := hfit }

/-! ## `luaRuntimeReady`'s memory structures -/

def errorJmpCheck (v : View) (L : Nat) : Bool :=
  readsOk v [(L + stateErrorJmpOff, 8, RuntimeData.ljAddr),
    (RuntimeData.ljAddr + ljPreviousOff, 8, 0),
    (RuntimeData.ljAddr + ljBOff + 8 * RuntimeData.jbRa, 8, RuntimeData.setjmpRet),
    (RuntimeData.ljAddr + ljBOff + 8 * RuntimeData.jbSp, 8, RuntimeData.rawrunSp)] &&
  (List.range 12).all fun i =>
    (r64 v (RuntimeData.ljAddr + ljBOff + 8 * (RuntimeData.jbS0 + i))).isSome

theorem errorJmpCheck_sound {m : Mem} {v : View} (h : PartialView m v) {L : Nat}
    (hc : errorJmpCheck v L = true) : ErrorJmpAt m L := by
  simp only [errorJmpCheck, Bool.and_eq_true] at hc
  obtain ⟨hr, hs⟩ := hc
  exact ⟨h.reads hr (by mem_tac), h.reads hr (by mem_tac), h.reads hr (by mem_tac),
    h.reads hr (by mem_tac), fun i hi => h.isSome (List.all_eq_true.mp hs i (List.mem_range.mpr hi))⟩

def stdioCheck (v : View) : Bool :=
  readsOk v [(symStdioExitHandler, 8, 0), (symImpurePtr, 8, symImpureData),
    (symImpureData + reentStdinOff, 8, symSf), (symImpureData + reentStdoutOff, 8, symSf + fileSize),
    (symImpureData + reentStderrOff, 8, symSf + 2 * fileSize), (symSglue + glueNextOff, 8, 0),
    (symSglue + glueNiobsOff, 4, 3), (symSglue + glueIobsOff, 8, symSf)] &&
  zeroOk v symSf symSfSize

theorem stdioCheck_sound {m : Mem} {v : View} (h : PartialView m v)
    (hc : stdioCheck v = true) : StdioBoot m := by
  simp only [stdioCheck, Bool.and_eq_true] at hc
  obtain ⟨hr, hz⟩ := hc
  exact ⟨h.reads hr (by mem_tac), h.reads hr (by mem_tac), h.reads hr (by mem_tac),
    h.reads hr (by mem_tac), h.reads hr (by mem_tac), h.reads hr (by mem_tac),
    h.reads hr (by mem_tac), h.reads hr (by mem_tac), h.zeroAt hz⟩

def memfsCheck (v : View) : Bool :=
  readsOk v [(symFsReady, 4, 0)] && zeroOk v symFds symFdsSize && zeroOk v symFiles symFilesSize

theorem memfsCheck_sound {m : Mem} {v : View} (h : PartialView m v)
    (hc : memfsCheck v = true) : MemfsBoot m := by
  simp only [memfsCheck, Bool.and_eq_true] at hc
  obtain ⟨⟨hr, h1⟩, h2⟩ := hc
  exact ⟨h.reads hr (by mem_tac), h.zeroAt h1, h.zeroAt h2⟩

/-- Bucket `i`'s chain from `ts`, with `fuel` links at most. -/
def strChainCheck (v : View) (size i : Nat) : Nat → Nat → Bool
  | 0, ts => ts == 0
  | f + 1, ts => ts == 0 ||
      (r8 v (ts + gcTtOff) == some gcShrStr &&
       (match r32 v (ts + tstringHashOff) with
        | some hh => hh % size == i
        | none => false) &&
       (match r64 v (ts + tstringLnglenOff) with
        | some nx => strChainCheck v size i f nx
        | none => false))

theorem strChainCheck_sound {m : Mem} {v : View} (h : PartialView m v) {size i : Nat} :
    ∀ {f ts : Nat}, strChainCheck v size i f ts = true → StrChain m size i ts
  | 0, ts, hc => by
    simp only [strChainCheck, beq_iff_eq] at hc
    subst hc; exact .nil
  | f + 1, ts, hc => by
    simp only [strChainCheck, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hc
    rcases hc with rfl | ⟨⟨htag, hh⟩, hn⟩
    · exact .nil
    · by_cases h0 : ts = 0
      · subst h0; exact .nil
      cases hhv : r32 v (ts + tstringHashOff) with
      | none => rw [hhv] at hh; cases hh
      | some hv =>
      cases hnx : r64 v (ts + tstringLnglenOff) with
      | none => rw [hnx] at hn; cases hn
      | some nx =>
      rw [hhv] at hh
      rw [hnx] at hn
      exact .cons h0 (h.rd8 htag) (h.rd32 hhv) (by simpa using hh) (h.rd64 hnx)
        (strChainCheck_sound h hn)

def strtCheck (v : View) (w : RtPtrs) : Bool :=
  readsOk v [(w.g + gStrtHashOff, 8, w.strtHash), (w.g + gStrtSizeOff, 4, w.strtSize),
    (w.g + gStrtNuseOff, 4, w.strtNuse)] &&
  decide (w.strtNuse ≤ w.strtSize ∧ 0 < w.strtSize ∧ w.strtSize &&& (w.strtSize - 1) = 0 ∧
    w.strtHeads.length = w.strtSize) &&
  (List.range w.strtHeads.length).all fun i =>
    r64 v (w.strtHash + 8 * i) == some (w.strtHeads.getD i 0) &&
    strChainCheck v w.strtSize i (w.strtNuse + 1) (w.strtHeads.getD i 0)

theorem strtCheck_sound {m : Mem} {v : View} (h : PartialView m v) {w : RtPtrs}
    (hc : strtCheck v w = true) : StrtAt m w := by
  simp only [strtCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨hr, hle, hpos, hpow, hlen⟩, hb⟩ := hc
  have hb' : ∀ i (hi : i < w.strtHeads.length),
      r64 v (w.strtHash + 8 * i) = some w.strtHeads[i] ∧
      strChainCheck v w.strtSize i (w.strtNuse + 1) w.strtHeads[i] = true := by
    intro i hi
    have := List.all_eq_true.mp hb i (List.mem_range.mpr hi)
    rw [getD_of_lt _ hi] at this
    simpa using this
  exact ⟨h.reads hr (by mem_tac), h.reads hr (by mem_tac), h.reads hr (by mem_tac), hle, hpos, hpow,
    hlen, fun i hi => h.rd64 (hb' i hi).1, fun i hi => strChainCheck_sound h (hb' i hi).2⟩

def strcacheCheck (v : View) (w : RtPtrs) : Bool :=
  decide (w.strcache.length = strcacheN * strcacheM) &&
  (List.range w.strcache.length).all fun i =>
    r64 v (w.g + gStrcacheOff + 8 * i) == some (w.strcache.getD i 0) &&
    (r8 v (w.strcache.getD i 0 + gcTtOff) == some gcShrStr ||
     r8 v (w.strcache.getD i 0 + gcTtOff) == some gcLngStr)

theorem strcacheCheck_sound {m : Mem} {v : View} (h : PartialView m v) {w : RtPtrs}
    (hc : strcacheCheck v w = true) : StrCacheAt m w := by
  simp only [strcacheCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hlen, hall⟩ := hc
  have hb : ∀ i (hi : i < w.strcache.length),
      r64 v (w.g + gStrcacheOff + 8 * i) = some w.strcache[i] ∧
      (r8 v (w.strcache[i] + gcTtOff) = some gcShrStr ∨
       r8 v (w.strcache[i] + gcTtOff) = some gcLngStr) := by
    intro i hi
    have := List.all_eq_true.mp hall i (List.mem_range.mpr hi)
    rw [getD_of_lt _ hi] at this
    simpa using this
  refine ⟨hlen, fun i hi => h.rd64 (hb i hi).1, fun i hi => ?_⟩
  rcases (hb i hi).2 with ht | ht
  · exact .inl (h.rd8 ht)
  · exact .inr (h.rd8 ht)

def luaStateCheck (v : View) (L ci : Nat) (w : RtPtrs) : Bool :=
  readsOk v [(L + stateHookmaskOff, 4, 0), (ci + ciTrapOff, 4, 0), (L + stateErrfuncOff, 8, 0),
    (L + stateNCcallsOff, 4, RuntimeData.nCcallsEntry), (L + stateOpenupvalOff, 8, 0),
    (L + stateTbclistOff, 8, w.stack), (L + stateStackOff, 8, w.stack),
    (L + stateStackLastOff, 8, w.stackLast), (ci + ciFuncOff, 8, w.func), (ci + ciTopOff, 8, w.ciTop),
    (ci + ciCallstatusOff, 2, cistFresh), (ci + ciNresultsOff, 2, 0),
    (ci + ciPreviousOff, 8, L + stateBaseCiOff), (ci + ciNextOff, 8, 0), (L + stateGOff, 8, w.g),
    (w.g + gMtOff + 8 * luaTnil, 8, 0), (w.g + gMtOff + 8 * luaTboolean, 8, 0),
    (w.g + gMtOff + 8 * luaTnumber, 8, 0)] &&
  decide (w.stack ≤ w.func ∧ w.ciTop ≤ w.stackLast) &&
  strtCheck v w && strcacheCheck v w

theorem luaStateCheck_sound {m : Mem} {v : View} (h : PartialView m v) {L ci : Nat} {w : RtPtrs}
    (hc : luaStateCheck v L ci w = true) : LuaStateAt m L ci w := by
  simp only [luaStateCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨hr, hle1, hle2⟩, hs⟩, hcache⟩ := hc
  exact
    { hookmask := h.reads hr (by mem_tac)
      trap := h.reads hr (by mem_tac)
      errfunc := h.reads hr (by mem_tac)
      nCcalls := h.reads hr (by mem_tac)
      openupval := h.reads hr (by mem_tac)
      tbclist := h.reads hr (by mem_tac)
      stack := h.reads hr (by mem_tac)
      stack_last := h.reads hr (by mem_tac)
      func := h.reads hr (by mem_tac)
      stack_le := hle1
      ci_top := h.reads hr (by mem_tac)
      ci_top_le := hle2
      callstatus := h.reads hr (by mem_tac)
      nresults := h.reads hr (by mem_tac)
      previous := h.reads hr (by mem_tac)
      next := h.reads hr (by mem_tac)
      g := h.reads hr (by mem_tac)
      mt_nil := h.reads hr (by mem_tac)
      mt_boolean := h.reads hr (by mem_tac)
      mt_number := h.reads hr (by mem_tac)
      strt := strtCheck_sound h hs
      strcache := strcacheCheck_sound h hcache }

/-- The address facts of `VmRegionsAt` (no memory). -/
def RegionsArith (L ci : Nat) (w : RtPtrs) : Prop :=
  symEnd ≤ L ∧ L + stateSize ≤ symHeapEnd ∧ symEnd ≤ ci ∧ ci + ciSize ≤ symHeapEnd ∧
  symEnd ≤ w.stack ∧ w.stackLast ≤ symHeapEnd ∧ w.func % 8 = 0 ∧
  (ci + ciSize ≤ w.stack ∨ w.stackLast ≤ ci) ∧
  symEnd ≤ w.cl ∧ w.cl + lclosureUpvalsOff ≤ symHeapEnd ∧
  symEnd ≤ w.proto ∧ w.proto + protoCodeOff + 8 ≤ symHeapEnd ∧
  symEnd ≤ w.code ∧ w.code + 4 * w.sizecode ≤ symHeapEnd ∧
  (w.code + 4 * w.sizecode ≤ w.stack ∨ w.stackLast ≤ w.code) ∧
  symEnd ≤ w.k ∧ w.k + tvalueSize * w.sizek ≤ symHeapEnd ∧ w.k % 8 = 0 ∧
  (w.k + tvalueSize * w.sizek ≤ w.stack ∨ w.stackLast ≤ w.k) ∧
  (L + stateSize ≤ ci ∨ ci + ciSize ≤ L) ∧
  (w.code + 4 * w.sizecode ≤ L ∨ L + stateSize ≤ w.code) ∧
  (w.code + 4 * w.sizecode ≤ ci ∨ ci + ciSize ≤ w.code) ∧
  (w.k + tvalueSize * w.sizek ≤ L ∨ L + stateSize ≤ w.k) ∧
  (w.k + tvalueSize * w.sizek ≤ ci ∨ ci + ciSize ≤ w.k) ∧
  (L + stateSize ≤ w.stack ∨ w.stackLast ≤ L) ∧ L % 8 = 0 ∧ ci % 8 = 0

instance (L ci : Nat) (w : RtPtrs) : Decidable (RegionsArith L ci w) := by
  unfold RegionsArith; infer_instance

def regionsCheck (v : View) (L ci : Nat) (w : RtPtrs) : Bool :=
  readsOk v [(w.func + tvalueValOff, 8, w.cl), (w.cl + lclosureProtoOff, 8, w.proto),
    (w.proto + protoCodeOff, 8, w.code), (w.proto + protoSizecodeOff, 4, w.sizecode),
    (w.proto + protoKOff, 8, w.k), (w.proto + protoSizekOff, 4, w.sizek)] &&
  decide (RegionsArith L ci w)

theorem regionsCheck_sound {m : Mem} {v : View} (h : PartialView m v) {L ci : Nat} {w : RtPtrs}
    (hc : regionsCheck v L ci w = true) : VmRegionsAt m L ci w := by
  simp only [regionsCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hr, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21, a22, a23, a24, a25, a26, a27⟩ := hc
  exact
    { L_lo := a1, L_hi := a2, ci_lo := a3, ci_hi := a4, stack_lo := a5, stack_hi := a6
      func_al := a7, ci_sep := a8
      cl := h.reads hr (by mem_tac)
      cl_lo := a9, cl_hi := a10
      proto := h.reads hr (by mem_tac)
      proto_lo := a11, proto_hi := a12
      code := h.reads hr (by mem_tac)
      sizecode := h.reads hr (by mem_tac)
      code_lo := a13, code_hi := a14, code_sep := a15
      kArr := h.reads hr (by mem_tac)
      sizek := h.reads hr (by mem_tac)
      k_lo := a16, k_hi := a17, k_al := a18, k_sep := a19
      L_sep_ci := a20, code_sep_L := a21, code_sep_ci := a22, k_sep_L := a23, k_sep_ci := a24
      L_sep_stack := a25, L_al := a26, ci_al := a27 }

/-- `KInterned m k sizek`: every pair of short-string constants is one pointer,
or the view shows their bytes differ. -/
def internedCheck (v : View) (k sizek : Nat) : Bool :=
  (List.range sizek).all fun i => (List.range sizek).all fun j =>
    match shrAt v (k + tvalueSize * i), shrAt v (k + tvalueSize * j) with
    | some (some x), some (some y) => x == y || strDiff v x y
    | some _, some _ => true
    | _, _ => false

theorem internedCheck_sound {m : Mem} {v : View} (h : PartialView m v) {k sizek : Nat}
    (hc : internedCheck v k sizek = true) : KInterned m k sizek := by
  intro i j x y s hi hj hti htj hx hy hs hrx hry
  have hij := List.all_eq_true.mp (List.all_eq_true.mp hc i (List.mem_range.mpr hi)) j
    (List.mem_range.mpr hj)
  split at hij
  · rename_i x' y' hsx hsy
    obtain rfl := Option.some.inj (shrAt_sound h hsx hti hx)
    obtain rfl := Option.some.inj (shrAt_sound h hsy htj hy)
    simp only [Bool.or_eq_true, beq_iff_eq] at hij
    rcases hij with hij | hij
    · exact hij
    · exact (strDiff_sound h hij hs hrx hry).elim
  · rename_i o o' hne hsx hsy
    obtain rfl := shrAt_sound h hsx hti hx
    obtain rfl := shrAt_sound h hsy htj hy
    exact (hne x y rfl rfl).elim
  · cases hij

/-- Every memory structure of `RuntimeReadyAt c L ci w` over the view, one
Bool each (the generated witness decides each with its own `decide +kernel`). -/
structure RtChecks (v : View) (L ci : Nat) (w : RtPtrs) : Prop where
  callers : segsOk v RuntimeData.callerFrames = true
  errorJmp : errorJmpCheck v L = true
  stdio : stdioCheck v = true
  memfs : memfsCheck v = true
  heap : heapCheck v w.top w.brkv w.chunks w.bins = true
  lua : luaStateCheck v L ci w = true
  top : readsOk v [(L + stateTopOff, 8, w.func + stackValueSize)] = true
  regions : regionsCheck v L ci w = true
  interned : internedCheck v w.k w.sizek = true

/-! ## The chunked log check -/

theorem chunks_zero {p : Nat × Nat → Prop} {lo size : Nat} : ∀ c ∈ chunks lo size 0, p c :=
  fun _ h => nomatch h

theorem chunks_cons {p : Nat × Nat → Prop} {lo size k : Nat} (h0 : p (lo, size))
    (h : ∀ c ∈ chunks (lo + size) size k, p c) : ∀ c ∈ chunks lo size (k + 1), p c := by
  intro c hc
  simp only [chunks, List.mem_cons] at hc
  rcases hc with rfl | hc
  · exact h0
  · exact h c hc

/-- `LogOk` from the chunk checks: `K` store chunks and `J` run chunks. -/
theorem logOk_of_chunks {L : PackedLog} {t : RunTree} {S K R J : Nat}
    (hs : ∀ c ∈ chunks 0 S K, storesIn L t c.1 c.2 = true)
    (hr : ∀ c ∈ chunks 0 R J, runsIn L t.runs c.1 c.2 = true)
    (hlen : L.len ≤ S * K) (hrl : t.runs.length ≤ R * J) : LogOk L t :=
  ⟨fun _ hi => chunks_cover hs (Nat.zero_le _) (by omega), all_runs_of_chunks hr hrl⟩

/-! ## The fixed image -/

/-- No run of the final byte map meets `[lo, hi)`. -/
def runsAvoid (t : RunTree) (lo hi : Nat) : Bool :=
  t.runs.all fun r => r.base + r.len ≤ lo || hi ≤ r.base

theorem runsAvoid_fin {t : RunTree} {lo hi : Nat} (hc : runsAvoid t lo hi = true) {x : Nat}
    (hlo : lo ≤ x) (hhi : x < hi) : t.fin x = none := by
  unfold RunTree.fin
  cases hcell : (t.find x).cell x with
  | none => rfl
  | some c =>
    have hr := Run.cell_range hcell
    have := List.all_eq_true.mp hc _ (t.find_mem x)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at this
    omega

/-- `.text` and `.rodata` lie in the loaded segment, in this order before the data bytes. -/
theorem image_geometry :
    segBase ≤ Image.textBase ∧ Image.textBase + Image.textSize ≤ Image.rodataBase ∧
    Image.rodataBase + Image.rodataSize ≤ dataBase ∧ dataBase ≤ segBase + segSize := by
  decide

theorem text_of_view {m : Mem} {chunk : Nat} {t : RunTree} (h : PartialView m (bootView chunk t))
    (hc : runsAvoid t Image.textBase (Image.rodataBase + Image.rodataSize) = true) :
    Vsa.Sim.Code.FixedBytesLoaded Image.textBase Image.textSize Image.textByte m := by
  intro o ho
  obtain ⟨g1, g2, g3, g4⟩ := image_geometry
  apply h
  simp only [bootView, logView, runsAvoid_fin hc (x := Image.textBase + o) (by omega) (by omega),
    imageView, imageByte]
  simp only [show Image.textBase + o < Image.rodataBase by omega,
    show segBase ≤ Image.textBase + o ∧ Image.textBase + o < segBase + segSize by omega,
    and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem rodata_of_view {m : Mem} {chunk : Nat} {t : RunTree} (h : PartialView m (bootView chunk t))
    (hc : runsAvoid t Image.textBase (Image.rodataBase + Image.rodataSize) = true) :
    Vsa.Sim.Code.FixedBytesLoaded Image.rodataBase Image.rodataSize Image.rodataByte m := by
  intro o ho
  obtain ⟨g1, g2, g3, g4⟩ := image_geometry
  apply h
  simp only [bootView, logView, runsAvoid_fin hc (x := Image.rodataBase + o) (by omega) (by omega),
    imageView, imageByte]
  simp only [show ¬ Image.rodataBase + o < Image.rodataBase by omega,
    show Image.rodataBase + o < dataBase by omega,
    show segBase ≤ Image.rodataBase + o ∧ Image.rodataBase + o < segBase + segSize by omega,
    and_self, ↓reduceIte, Nat.add_sub_cancel_left]

end Lua.Vm.Boot

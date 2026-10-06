import Std.Data.ExtHashMap
import Lua.Bytecode.Semantics
import Lua.Vm.Layout
import Lua.Vm.LayoutRt

/-!
# Representation predicates for Lua VM state in RV64 memory (skeleton)

Inductive relations saying when the bytes of the machine's memory hold the C
structures of Lua 5.4.7 (`lobject.h`, `lstate.h`) that represent a
deep-embedded value, prototype, or VM frame. Offsets and tags are the
compiler's own (`Lua/Vm/Layout.lean`, generated from `offsetof`), so these
are statements about the bare-metal ELF's data layout, not about C source.

These are the analogue of ship-your-interpreter's `Vsa/MemRepr.lean`
(`ProgramRepr`) for the Lua VM. They are *definitions only*: the lemmas that
the compiled `luaV_execute` preserves them are Layer A's work (PHASES.md).
-/

namespace Lua.Vm

open Lua.Bytecode Layout

/-- Machine memory: byte-addressed, partial (the Sail model's `mem`). -/
abbrev Mem := Std.ExtHashMap Nat (BitVec 8)

/-- Little-endian unsigned read of `n` bytes at `a` (`none` if any byte is
absent). -/
def rdLE (m : Mem) (a n : Nat) : Option Nat :=
  (List.range n).foldr (fun i acc => do
    let b ← m[a + i]?
    let r ← acc
    pure (b.toNat + 256 * r)) (some 0)

def rd8 (m : Mem) (a : Nat) : Option Nat := rdLE m a 1
def rd16 (m : Mem) (a : Nat) : Option Nat := rdLE m a 2
def rd32 (m : Mem) (a : Nat) : Option Nat := rdLE m a 4
def rd64 (m : Mem) (a : Nat) : Option Nat := rdLE m a 8

/-- The `tt_` byte of the `TValue` at `a`. -/
def tagAt (m : Mem) (a : Nat) : Option Nat := rd8 m (a + tvalueTagOff)

/-- `bs` are the bytes at `a, a+1, …`. -/
def BytesAt (m : Mem) (a : Nat) (bs : List UInt8) : Prop :=
  ∀ i (h : i < bs.length), m[a + i]? = some (BitVec.ofNat 8 (bs[i]'h).toNat)

/-- A `TString` at `ts` holding the bytes `s`: short strings (header tag
`LUA_VSHRSTR`, `shrlen`) up to `LUAI_MAXSHORTLEN`, long strings otherwise
(header tag `LUA_VLNGSTR`, `u.lnglen`, and `shrlen = 0xFF`, which
`luaS_createlngstrobj` stores and `l_strcmp` branches on at `0x8001a720`);
contents are NUL-terminated. The
header tag is `GCObject.tt`, which `luaC_newobj` stores without
`BIT_ISCOLLECTABLE` (`gcShrStr = 4`, not the `TValue` tag `vShrStr = 68`). -/
inductive TStringRepr (m : Mem) : Nat → List UInt8 → Prop where
  | short {ts s} : rd8 m (ts + gcTtOff) = some gcShrStr → s.length ≤ maxShortLen →
      rd8 m (ts + tstringShrlenOff) = some s.length →
      BytesAt m (ts + tstringContentsOff) s → m[ts + tstringContentsOff + s.length]? = some 0 →
      TStringRepr m ts s
  | long {ts s} : rd8 m (ts + gcTtOff) = some gcLngStr → maxShortLen < s.length →
      rd64 m (ts + tstringLnglenOff) = some s.length →
      BytesAt m (ts + tstringContentsOff) s → m[ts + tstringContentsOff + s.length]? = some 0 →
      rd8 m (ts + tstringShrlenOff) = some 0xFF →
      TStringRepr m ts s

/-- The `TValue` tag of a string with bytes `s`: the variant is determined by
the length (`luaS_newlstr`: short iff `l ≤ LUAI_MAXSHORTLEN`), so equal
contents never sit under different variants. -/
def strTag (s : List UInt8) : Nat := if s.length ≤ maxShortLen then vShrStr else vLngStr

/-- The `TValue` at `a` represents the F1 value `v`. Nil is any variant of
type 0 (`ttisnil` tests `novariant(tt) == 0`: `LUA_VNIL`, `LUA_VEMPTY`,
`LUA_VABSTKEY`); a register's nil is exactly `LUA_VNIL` (`Lua.Vm.Sim.ValRepr`).
A string's tag is `strTag` of its bytes. `print` is a light C function (`LUA_VLCF`) whose pointer is
`luaB_print`. -/
inductive TValueRepr (m : Mem) : Nat → Value → Prop where
  | nil {a t} : tagAt m a = some t → t % 16 = 0 → TValueRepr m a .nil
  | false_ {a} : tagAt m a = some vFalse → TValueRepr m a (.bool false)
  | true_ {a} : tagAt m a = some vTrue → TValueRepr m a (.bool true)
  | int {a} {i : BitVec 64} : tagAt m a = some vNumInt → rd64 m (a + tvalueValOff) = some i.toNat →
      TValueRepr m a (.int i)
  | str {a ts s} : tagAt m a = some (strTag s) →
      rd64 m (a + tvalueValOff) = some ts → TStringRepr m ts s → TValueRepr m a (.str s)
  | print {a} : tagAt m a = some vLcf → rd64 m (a + tvalueValOff) = some symLuaBPrint →
      TValueRepr m a (.builtin .print)

/-- A constant-table entry (`Proto.k[i]`) at `a` represents `c`. -/
inductive ConstRepr (m : Mem) : Nat → Const → Prop where
  | nil {a} : tagAt m a = some vNil → ConstRepr m a .nil
  | bool {a b} : TValueRepr m a (.bool b) → ConstRepr m a (.bool b)
  | int {a i} : TValueRepr m a (.int i) → ConstRepr m a (.int i)
  | float {a} {bits : BitVec 64} : tagAt m a = some vNumFlt →
      rd64 m (a + tvalueValOff) = some bits.toNat → ConstRepr m a (.float bits)
  | str {a s} : TValueRepr m a (.str s) → ConstRepr m a (.str s)

/-- An `Upvaldesc` at `a`. -/
def UpvalDescRepr (m : Mem) (a : Nat) (u : UpvalDesc) : Prop :=
  rd8 m (a + upvaldescInstackOff) = some (if u.instack then 1 else 0) ∧
  rd8 m (a + upvaldescIdxOff) = some u.idx ∧ rd8 m (a + upvaldescKindOff) = some u.kind

mutual
/-- **A `Proto` at `pa` represents the prototype `p`**: header bytes, the
code array (one little-endian word per instruction), the constant array,
the upvalue descriptors and, recursively, the nested prototypes. Debug
fields (`lineinfo`, `locvars`, …) are unconstrained (`luac -s`). -/
inductive ProtoRepr (m : Mem) : Nat → Proto → Prop where
  | mk {pa numparams isVararg maxstack code k ups protos ca ka ua pp ptrs} :
      rd8 m (pa + gcTtOff) = some 10 →  -- LUA_VPROTO
      rd8 m (pa + protoNumparamsOff) = some numparams →
      rd8 m (pa + protoIsVarargOff) = some (if isVararg then 1 else 0) →
      rd8 m (pa + protoMaxstacksizeOff) = some maxstack →
      rd32 m (pa + protoSizecodeOff) = some code.length →
      rd64 m (pa + protoCodeOff) = some ca →
      (∀ i (h : i < code.length), rd32 m (ca + 4 * i) = some (code[i]'h).toNat) →
      rd32 m (pa + protoSizekOff) = some k.length →
      rd64 m (pa + protoKOff) = some ka →
      (∀ i (h : i < k.length), ConstRepr m (ka + tvalueSize * i) (k[i]'h)) →
      rd32 m (pa + protoSizeupvaluesOff) = some ups.length →
      rd64 m (pa + protoUpvaluesOff) = some ua →
      (∀ i (h : i < ups.length), UpvalDescRepr m (ua + upvaldescSize * i) (ups[i]'h)) →
      rd32 m (pa + protoSizepOff) = some protos.length →
      rd64 m (pa + protoPOff) = some pp →
      ptrs.length = protos.length →
      (∀ i (h : i < ptrs.length), rd64 m (pp + 8 * i) = some (ptrs[i]'h)) →
      ProtoListRepr m ptrs protos →
      ProtoRepr m pa (.mk numparams isVararg maxstack code k ups protos)

/-- Pointwise `ProtoRepr` over the `Proto.p` array. -/
inductive ProtoListRepr (m : Mem) : List Nat → List Proto → Prop where
  | nil : ProtoListRepr m [] []
  | cons {a as p ps} : ProtoRepr m a p → ProtoListRepr m as ps → ProtoListRepr m (a :: as) (p :: ps)
end

/-- The register window: `R[j]` is the `TValue` at `base + 16 j`, for
`j < n`. -/
def FrameRepr (m : Mem) (base : Nat) (regs : Nat → Value) (n : Nat) : Prop :=
  ∀ j, j < n → TValueRepr m (base + stackValueSize * j) (regs j)

/-- A table at `t` has, in its hash part, the short-string key `key`
mapped to a value represented as `v` (a skeleton of `luaH_getshortstr`'s
view: some node of the `2^lsizenode` nodes holds the pair). -/
def TableHasShortKey (m : Mem) (t : Nat) (key : List UInt8) (v : Value) : Prop :=
  ∃ lsz node i ts, rd8 m (t + tableLsizenodeOff) = some lsz ∧
    rd64 m (t + tableNodeOff) = some node ∧ i < 2 ^ lsz ∧
    rd8 m (node + nodeSize * i + nodeKeyTtOff) = some vShrStr ∧
    rd64 m (node + nodeSize * i + nodeKeyValOff) = some ts ∧ TStringRepr m ts key ∧
    TValueRepr m (node + nodeSize * i) v

/-- `luaH_getshortstr`'s view of a table at `t`: some node of the `2^lsizenode`
nodes has the short-string key *pointer* `ts` and a value represented as `v`.
`luaH_getshortstr` compares key pointers (`eqshrstr`), not contents. -/
def TableHasShortKeyPtr (m : Mem) (t ts : Nat) (v : Value) : Prop :=
  ∃ lsz node i, rd8 m (t + tableLsizenodeOff) = some lsz ∧
    rd64 m (t + tableNodeOff) = some node ∧ i < 2 ^ lsz ∧
    rd8 m (node + nodeSize * i + nodeKeyTtOff) = some vShrStr ∧
    rd64 m (node + nodeSize * i + nodeKeyValOff) = some ts ∧
    TValueRepr m (node + nodeSize * i) v

/-! ## The stores of `OP_VARARGPREP` at the entry

`luaT_adjustvarargs(L, 0, ci, p)` with `L->top = ci->func + 1` (no arguments)
writes `ci->u.l.nextraargs = 0`, copies the function's `TValue` one slot up
(`setobjs2s(L, L->top++, ci->func)`: payload and tag), and moves `ci->func`
and `ci->top` up by one slot. (It also writes `L->top` and its own frame below
`sp`, which A1's relation leaves free.) -/

/-- `n` little-endian bytes of `x` at `a`. -/
def writeLE (m : Mem) (a : Nat) : Nat → Nat → Mem
  | 0, _ => m
  | n + 1, x => (writeLE m a n x).insert (a + n) (BitVec.ofNat 8 (x / 256 ^ n))

theorem getElem?_writeLE (m : Mem) (a : Nat) : ∀ (n x k : Nat),
    (writeLE m a n x)[k]? =
      if a ≤ k ∧ k < a + n then some (BitVec.ofNat 8 (x / 256 ^ (k - a))) else m[k]?
  | 0, x, k => by simp [writeLE]; omega
  | n + 1, x, k => by
    simp only [writeLE, Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    by_cases hk : a + n = k
    · subst hk; simp
    · rw [if_neg hk, getElem?_writeLE m a n x k]
      by_cases h : a ≤ k ∧ k < a + n
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]

/-- **The bytes around `luaT_adjustvarargs`'s stores at the entry**
(`VarargDirty`): the whole `CallInfo` (it writes `ci->func`, `ci->top` and
`ci->u.l.nextraargs`; `OP_VARARGPREP`'s `savepc` writes `ci->u.l.savedpc`)
and the payload and tag of the slot above `ci->func`. -/
def VarargDirty (ci func a : Nat) : Prop :=
  (ci ≤ a ∧ a < ci + ciSize) ∨
  (func + stackValueSize ≤ a ∧ a < func + stackValueSize + tvalueTagOff + 1)

instance (ci func a : Nat) : Decidable (VarargDirty ci func a) := by
  unfold VarargDirty; infer_instance

/-- **The memory after `luaT_adjustvarargs` at the entry**, for the function
slot `func`, its closure `cl` and `ci->top = top`. -/
def varargMemV (m : Mem) (ci func cl top : Nat) : Mem :=
  writeLE (writeLE (writeLE (writeLE (writeLE m (ci + ciNextraargsOff) 4 0)
    (func + stackValueSize) 8 cl) (func + stackValueSize + tvalueTagOff) 1 vLcl)
    (ci + ciFuncOff) 8 (func + stackValueSize)) (ci + ciTopOff) 8 (top + stackValueSize)

/-- `varargMemV` changes only the bytes of `VarargDirty`. -/
theorem varargMemV_out (m : Mem) (ci func cl top : Nat) {a : Nat} (h : ¬ VarargDirty ci func a) :
    (varargMemV m ci func cl top)[a]? = m[a]? := by
  simp only [VarargDirty, ciSize, stackValueSize, tvalueTagOff, not_or, not_and, Nat.not_lt] at h
  simp only [varargMemV, getElem?_writeLE, ciFuncOff, ciTopOff, ciNextraargsOff, stackValueSize,
    tvalueTagOff]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- **The prototype after `OP_VARARGPREP`'s stores** (as `ProtoRepr` and the
code pointer `lw` follows). -/
structure ProtoAt (m : Mem) (pa : Nat) (p : Proto) (code : Nat) : Prop where
  proto : ProtoRepr m pa p
  code : rd64 m (pa + protoCodeOff) = some code

/-- The pointers `VmEntryData` names. -/
structure EntryPtrs where
  func : Nat
  cl : Nat
  pa : Nat
  code : Nat
  uv : Nat
  envv : Nat
  env : Nat
  g : Nat
  stackLast : Nat

/-- The Lua-side facts at `luaV_execute(L, ci)`'s entry for the main
closure of prototype `p`:

* `L->ci = ci`, the `CallInfo` is a Lua call (`savedpc` at the first
  instruction), and `ci->func` is the stack slot holding the `LClosure`;
* the closure's prototype is represented by `ProtoRepr`;
* its upvalue 0 (`_ENV`) points to the globals table, which maps `"print"`
  to `luaB_print`;
* the collector is stopped (`gcstp = GCSTPUSR`, `main.c`);
* the frame `[func+1, func+1+maxstacksize)` lies below `L->stack_last`.

Register *contents* are deliberately unconstrained: at entry they are
stale stack values, which `Supported`'s definite-initialisation check makes
irrelevant. -/
structure VmEntryData (m : Mem) (L ci : Nat) (p : Proto) (e : EntryPtrs) : Prop where
  ci_eq : rd64 m (L + stateCiOff) = some ci
  ci_func : rd64 m (ci + ciFuncOff) = some e.func
  func_tag : tagAt m e.func = some vLcl
  func_val : rd64 m (e.func + tvalueValOff) = some e.cl
  cl_proto : rd64 m (e.cl + lclosureProtoOff) = some e.pa
  proto : ProtoRepr m e.pa p
  proto_code : rd64 m (e.pa + protoCodeOff) = some e.code
  savedpc : rd64 m (ci + ciSavedpcOff) = some e.code
  cl_upval0 : rd64 m (e.cl + lclosureUpvalsOff) = some e.uv
  uv_v : rd64 m (e.uv + upvalVOff) = some e.envv
  env_tag : tagAt m e.envv = some vTable
  env_val : rd64 m (e.envv + tvalueValOff) = some e.env
  env_print : TableHasShortKey m e.env printKey (.builtin .print)
  /-- **`GETTABUP _ENV "print"` finds `print` by pointer.** Every short-string
  constant whose bytes are `"print"` is the key pointer of `_ENV`'s `print`
  node: `lundump`'s `loadStringN` and `luaL_openlibs`' `lua_setfield` both
  intern `"print"` (`luaS_newlstr` → `internshrstr`), and `luaH_getshortstr`
  compares pointers. `env_print` alone compares contents. -/
  env_print_ptr : ∀ ka i x, rd64 m (e.pa + protoKOff) = some ka → i < p.k.length →
    tagAt m (ka + tvalueSize * i) = some vShrStr →
    rd64 m (ka + tvalueSize * i + tvalueValOff) = some x →
    TStringRepr m x printKey → TableHasShortKeyPtr m e.env x (.builtin .print)
  l_G : rd64 m (L + stateGOff) = some e.g
  gc_stopped : rd8 m (e.g + gGcstpOff) = some gcstpUsr
  stack_last : rd64 m (L + stateStackLastOff) = some e.stackLast
  frame_fits : e.func + stackValueSize * (1 + p.maxstacksize) ≤ e.stackLast
  /-- `OP_VARARGPREP` → `luaT_adjustvarargs` → `luaD_checkstack(L, maxstacksize + 1)`
  with `L->top = func + 1` does not grow the stack (`L->stack_last - L->top >
  maxstacksize + 1` slots) -/
  vararg_room : e.func + stackValueSize * (3 + p.maxstacksize) ≤ e.stackLast
  /-- the prototype and its code pointer lie apart from the bytes
  `luaT_adjustvarargs` writes (`VarargDirty`): they hold in every memory that
  agrees with this one elsewhere -/
  vararg_proto : ∀ m' : Mem, (∀ a, ¬ VarargDirty ci e.func a → m'[a]? = m[a]?) →
    ProtoAt m' e.pa p e.code

end Lua.Vm

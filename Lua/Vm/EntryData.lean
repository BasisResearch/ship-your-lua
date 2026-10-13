import Lua.Vm.Repr
import Lua.Vm.DlHeap
import Lua.Vm.Image
import Vsa.Densify.Transport
import Vsa.Sim.MemLoadTotal

/-!
# `VmEntryData`: the Lua-side data at `luaV_execute`'s entry

`VmEntryData m L ci p e` (`VmLoaded`'s Lua part): the `CallInfo`, the closure,
`ProtoRepr` of `p`, `_ENV.print`, the stopped collector, and (lane F1-13) what
`OP_CALL print` needs of the boot to keep `VmRel`'s complement:

* `frozen`: the objects a `print` never writes (the prototype, its constants
  and their strings, `_ENV`'s chain to `print`) are read from the byte ranges
  `e.foot`, so they hold in every memory that agrees with this one there;
  `foot_apart` keeps `e.foot` off what a `CALL` writes inside the heap
  (`EntryDirty`: `L->top`, `L->ci`, the `CallInfo`, the Lua stack above
  `func`, `g`'s first words and its string cache) and `placed` puts it in
  chunks in use (or the image);
* `lits`: the reserved words `"nil"`, `"true"`, `"false"` are interned
  (`LitInterned`), read from `e.litFoot`, in chunks in use;
* `room`: the heap has room for the first `print`'s allocations.

The string table and its cache (`StrtAt`, `StrCacheAt`, read by `LitInterned`)
and the witness `RtPtrs` are here, below `VmEntryData`, for that.
-/

namespace Lua.Vm

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Densify (fillZeroMem)
open Vsa.Sim (bytesT4)

/-- A bucket of the short-string table: interned strings chained by
`u.hnext`, each in the bucket of its hash (`lmod(h, size)`). -/
inductive StrChain (m : Mem) (size i : Nat) : Nat → Prop where
  | nil : StrChain m size i 0
  | cons {ts h nx : Nat} : ts ≠ 0 → rd8 m (ts + gcTtOff) = some gcShrStr →
      rd32 m (ts + tstringHashOff) = some h → h % size = i →
      rd64 m (ts + tstringLnglenOff) = some nx → StrChain m size i nx →
      StrChain m size i ts

/-- The pointers and shapes `luaRuntimeReady` names, chosen per program. -/
structure RtPtrs where
  /-- `ci->func`, `L->stack`, `L->stack_last`, `ci->top`, `L->l_G`. -/
  func : Nat
  stack : Nat
  stackLast : Nat
  ciTop : Nat
  g : Nat
  /-- `g->strt`: bucket array, size, count, and each bucket's first string. -/
  strtHash : Nat
  strtSize : Nat
  strtNuse : Nat
  strtHeads : List Nat
  /-- `g->strcache`, row-major. -/
  strcache : List Nat
  /-- dlmalloc: the top chunk, the break, the chunk walk, the bin lists. -/
  top : Nat
  brkv : Nat
  chunks : List DlHeap.Chunk
  bins : List (List Nat)
  /-- The main closure (`ci->func`'s value), its `Proto`, and the proto's
  `code` array and `sizecode`, its constant array `k` and `sizek`
  (`VmRegionsAt`). -/
  cl : Nat
  proto : Nat
  code : Nat
  sizecode : Nat
  k : Nat
  sizek : Nat

/-- `g->strt` (lstring.c), read by `luaS_newlstr` → `internshrstr` for every
new short string: `print`'s `luaL_tolstring` → `lua_pushfstring` →
`luaO_pushvfstring` creates the integer's decimal string, and grows the table
(`luaS_resize`) when `nuse ≥ size`. -/
structure StrtAt (m : Mem) (w : RtPtrs) : Prop where
  hash : rd64 m (w.g + gStrtHashOff) = some w.strtHash
  size : rd32 m (w.g + gStrtSizeOff) = some w.strtSize
  nuse : rd32 m (w.g + gStrtNuseOff) = some w.strtNuse
  nuse_le : w.strtNuse ≤ w.strtSize
  /-- `lmod` is a mask: the size is a power of two. -/
  size_pos : 0 < w.strtSize
  size_pow2 : w.strtSize &&& (w.strtSize - 1) = 0
  heads_len : w.strtHeads.length = w.strtSize
  bucket : ∀ i (h : i < w.strtHeads.length), rd64 m (w.strtHash + 8 * i) = some w.strtHeads[i]
  chain : ∀ i (h : i < w.strtHeads.length), StrChain m w.strtSize i w.strtHeads[i]

/-- `g->strcache` (lstring.c), read by `luaS_new` for every
`lua_pushstring` of a C string (`luaL_tolstring`'s `"true"`/`"false"`/`"nil"`),
which compares the cached strings' contents: every entry is a string. -/
structure StrCacheAt (m : Mem) (w : RtPtrs) : Prop where
  len : w.strcache.length = strcacheN * strcacheM
  ptr : ∀ i (h : i < w.strcache.length), rd64 m (w.g + gStrcacheOff + 8 * i) = some w.strcache[i]
  tag : ∀ i (h : i < w.strcache.length),
    rd8 m (w.strcache[i] + gcTtOff) = some gcShrStr ∨ rd8 m (w.strcache[i] + gcTtOff) = some gcLngStr

/-- The bytes of `"nil"`. -/
def nilB : List UInt8 := [0x6e, 0x69, 0x6c]

/-- The bytes of `"true"`. -/
def trueB : List UInt8 := [0x74, 0x72, 0x75, 0x65]

/-- The bytes of `"false"`. -/
def falseB : List UInt8 := [0x66, 0x61, 0x6c, 0x73, 0x65]

/-- `luaS_hash` (`lstring.c`): `h = seed ^ l`, then for each byte from the
last, `h ^= (h << 5) + (h >> 2) + byte`, in 32 bits. -/
def luaHash (seed : UInt32) (b : List UInt8) : UInt32 :=
  b.foldr (fun c h => h ^^^ ((h <<< 5) + (h >>> 2) + c.toUInt32)) (seed ^^^ b.length.toUInt32)

/-- The chain of `g->strt`'s bucket from `p` (`u.hnext`) reaches `ts`. -/
inductive ChainHas (m : Mem) (ts : Nat) : Nat → Prop where
  | here : ChainHas m ts ts
  | next {p nx : Nat} : p ≠ 0 → rd64 m (p + tstringLnglenOff) = some nx → ChainHas m ts nx → ChainHas m ts p

/-- **The literal's string is interned** in `g->strt` (`rt`'s table, of the
memory's zero fill): the one `TString` `ts` of the short bytes `b`, in the
chain of the bucket of `b`'s hash with the state's seed. What `luaS_new` →
`internshrstr` needs to return it without allocating (`luaX_init` interns the
reserved words `nil`, `true`, `false` at boot; nothing is ever collected); the
string cache `g->strcache` holds strings (`StrCacheAt`), which a hit
returns only if equal (`strcmp`). -/
structure LitInterned (m : Mem) (rt : RtPtrs) (seed : UInt32) (b : List UInt8) (ts : Nat) : Prop where
  repr : TStringRepr (fillZeroMem m) ts b
  short : b.length ≤ maxShortLen
  strt : StrtAt (fillZeroMem m) rt
  cache : StrCacheAt (fillZeroMem m) rt
  seed_w : rd32 (fillZeroMem m) (rt.g + gSeedOff) = some seed.toNat
  bucket : ∀ (h : (luaHash seed b).toNat % rt.strtSize < rt.strtHeads.length),
    ChainHas (fillZeroMem m) ts rt.strtHeads[(luaHash seed b).toNat % rt.strtSize]

/-- **A `TString` holds one content**: the length (`shrlen`/`lnglen`) and the
bytes are read off the object, so pointer equality of represented strings is
content equality. -/
theorem TStringRepr.inj {m : Mem} {ts : Nat} {s s' : List UInt8}
    (h : TStringRepr m ts s) (h' : TStringRepr m ts s') : s = s' := by
  have hb : BytesAt m (ts + tstringContentsOff) s → BytesAt m (ts + tstringContentsOff) s' →
      s.length = s'.length → s = s' := fun hb hb' hl =>
    List.ext_getElem hl fun i h1 h2 => by
      have e := (hb i h1).symm.trans (hb' i h2)
      simp only [Option.some.injEq] at e
      have e2 := congrArg BitVec.toNat e
      simp only [BitVec.toNat_ofNat] at e2
      rw [Nat.mod_eq_of_lt (UInt8.toNat_lt _), Nat.mod_eq_of_lt (UInt8.toNat_lt _)] at e2
      exact UInt8.toNat_inj.mp e2
  cases h with
  | short ht _ hl hs _ =>
    cases h' with
    | short _ _ hl' hs' _ => exact hb hs hs' (by have := hl.symm.trans hl'; simpa using this)
    | long ht' => have := ht.symm.trans ht'; simp [gcShrStr, gcLngStr] at this
  | long ht _ hl hs _ =>
    cases h' with
    | short ht' => have := ht.symm.trans ht'; simp [gcShrStr, gcLngStr] at this
    | long _ _ hl' hs' _ => exact hb hs hs' (by have := hl.symm.trans hl'; simpa using this)

/-- **A byte of a chunk in use**: its payload `[addr + 16, addr + size + 8)`
(the last 8 bytes are the next chunk's `prev_size`, which only a free
predecessor's footer writes). -/
def InUse (chunks : List DlHeap.Chunk) (a : Nat) : Prop :=
  ∃ c ∈ chunks, c.inuse = true ∧ c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8

/-- `a` lies in the footprint `t`. -/
def InRanges (t : RTree) (a : Nat) : Prop := t.mem a = true

instance (t : RTree) (a : Nat) : Decidable (InRanges t a) := by
  unfold InRanges; infer_instance

/-- **The reserved literals interned** in a memory `M` (lane F1-13), for some
string table `rt` of `G(L) = g` and stack end `sl`. -/
structure LitsIn (M : Mem) (g sl : Nat) (ls : LitPtrs) (rt : RtPtrs) : Prop where
  g : rt.g = g
  sl : rt.stackLast = sl
  nil : LitInterned M rt ls.seed nilB ls.nil
  tru : LitInterned M rt ls.seed trueB ls.tru
  fls : LitInterned M rt ls.seed falseB ls.fls

/-- **The reserved literals are interned** in `M`, for some string table. -/
def LitsHold (M : Mem) (g sl : Nat) (ls : LitPtrs) : Prop := ∃ rt, LitsIn M g sl ls rt

/-- `g`'s words up to the end of its string cache. -/
def gEnd : Nat := gStrcacheOff + 8 * strcacheN * strcacheM

/-- **What a `CALL print` writes inside the heap's chunks in use** (lane
F1-13): `L->top`, `L->ci`, the Lua `CallInfo` (and `OP_VARARGPREP`'s stores
there), the Lua stack above `ci->func`, `g`'s first words (the GC debt, the
string table's header) and its string cache. -/
def EntryDirty (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L + stateTopOff ≤ a ∧ a < L + stateTopOff + 8) ∨ (L + stateCiOff ≤ a ∧ a < L + stateCiOff + 8) ∨
  (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast) ∨ (e.g ≤ a ∧ a < e.g + 64) ∨
  (e.g + gStrcacheOff ≤ a ∧ a < e.g + gEnd)

/-- **What the literals' facts must stay apart from**: the words
`luaD_precall`/`luaD_poscall` write (`L->top`, `L->ci`, the Lua `CallInfo`)
and the Lua stack above `ci->func`. -/
def LitDirty (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L + stateTopOff ≤ a ∧ a < L + stateTopOff + 8) ∨ (L + stateCiOff ≤ a ∧ a < L + stateCiOff + 8) ∨
  (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast)

/-- The heap room the first `print` may claim: per first-use allocation
(`luaE_extendCI`'s `CallInfo`, `stdout`'s buffer, `"__tostring"`, one more)
one `_malloc_r` with its `_sbrk` (the request, the 16 KiB top pad, a page). -/
def firstRoom : Nat := 4 * (16384 + 4096 + 1024 + 128)

/-- **The static words of the `lua_State` and `g`** a `print` keeps
(`LuaStateAt`'s `hookmask`, `errfunc`, `nCcalls`, `openupval`, `tbclist`,
`stack`, `stack_last`, `l_G`, `errorJmp`, `G(L)->mt[nil, boolean, number]`):
`(address, width)`. -/
def luaStaticWords (L g : Nat) : List (Nat × Nat) :=
  [(L + stateHookmaskOff, 4), (L + stateErrfuncOff, 8), (L + stateNCcallsOff, 4),
   (L + stateOpenupvalOff, 8), (L + stateTbclistOff, 8), (L + stateStackOff, 8),
   (L + stateStackLastOff, 8), (L + stateGOff, 8), (L + stateErrorJmpOff, 8),
   (g + gMtOff + 8 * luaTnil, 8), (g + gMtOff + 8 * luaTboolean, 8), (g + gMtOff + 8 * luaTnumber, 8)]

/-- **The objects a `CALL print` leaves alone** (lane F1-13), in a memory `M`:
the prototype, its code pointer, and `_ENV`'s chain to `print` for every
short-string constant `"print"`. -/
structure EntryFrozen (M : Mem) (L ci : Nat) (p : Proto) (e : EntryPtrs) : Prop where
  proto : ProtoRepr M e.pa p
  proto_code : rd64 M (e.pa + protoCodeOff) = some e.code
  env_get : ∀ ka i x, rd64 M (e.pa + protoKOff) = some ka → i < p.k.length →
    tagAt M (ka + tvalueSize * i) = some vShrStr →
    rd64 M (ka + tvalueSize * i + tvalueValOff) = some x →
    TStringRepr M x printKey → ∃ s, EnvGetAt M L ci e x s

/-- **A heap byte of a chunk in use** of `cs`, in the arena `[_end, __heap_end)`. -/
structure HeapIn (cs : List DlHeap.Chunk) (a : Nat) : Prop where
  inuse : InUse cs a
  lo : DlHeap.heapStart ≤ a
  hi : a < DlHeap.heapEnd

/-- `[a, a + n)` and `[b, b + k)` are disjoint. -/
def Apart (a n b k : Nat) : Prop := a + n ≤ b ∨ b + k ≤ a

instance (a n b k : Nat) : Decidable (Apart a n b k) := by unfold Apart; infer_instance

/-- **The objects a `CALL print` writes are apart** (lane F1-13): `g` up to
its string cache, the literals' objects, the `lua_State`, the `CallInfo` and
the Lua stack above `ci->func`. -/
structure ObjsApart (L ci : Nat) (e : EntryPtrs) : Prop where
  g_L : Apart e.g gEnd L stateSize
  g_ci : Apart e.g gEnd ci ciSize
  g_stack : Apart e.g gEnd e.func (e.stackLast - e.func)
  lit_L : ∀ ts ∈ e.lits.strs, Apart ts 30 L stateSize
  lit_g : ∀ ts ∈ e.lits.strs, Apart ts 30 e.g gEnd
  lit_ci : ∀ ts ∈ e.lits.strs, Apart ts 30 ci ciSize
  lit_stack : ∀ ts ∈ e.lits.strs, Apart ts 30 e.func (e.stackLast - e.func)

/-- **Where the objects a `CALL print` reads lie** (lane F1-13), for the
chunks `cs` of the heap's walk: `e.foot` in chunks in use or in the image
below the HTIF mailbox, `e.litFoot` and the literals' objects in chunks in
use, and the `lua_State`, `g` up to its string cache, the `CallInfo` and the
Lua stack above `ci->func` in chunks in use. -/
structure CallPlaced (cs : List DlHeap.Chunk) (L ci : Nat) (e : EntryPtrs) : Prop where
  foot : ∀ a, InRanges e.foot a → HeapIn cs a ∨ (0x80000000 ≤ a ∧ a < symTohost)
  litFoot : ∀ a, InRanges e.litFoot a → HeapIn cs a
  lit_strs : ∀ ts ∈ e.lits.strs, ∀ a, ts ≤ a → a < ts + 30 → HeapIn cs a
  L : ∀ a, L ≤ a → a < L + stateSize → HeapIn cs a
  g : ∀ a, e.g ≤ a → a < e.g + gEnd → HeapIn cs a
  ci : ∀ a, ci ≤ a → a < ci + ciSize → HeapIn cs a
  stack : ∀ a, e.func ≤ a → a < e.stackLast → HeapIn cs a

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
  /-- **`GETTABUP _ENV "print"`'s walk** (lane F1-7): for every short-string
  constant `"print"`, `luaH_getshortstr`'s chain from its main position
  reaches `print`'s node (`EnvGetAt`). `env_print_ptr` places the key in some
  node; the machine needs it on the chain. Stated, as `vararg_proto`, in every
  memory that agrees with this one off the bytes `luaT_adjustvarargs` writes. -/
  env_get : ∀ m' : Mem, (∀ a, ¬ VarargDirty ci e.func a → m'[a]? = m[a]?) →
    ∀ ka i x, rd64 m' (e.pa + protoKOff) = some ka → i < p.k.length →
    tagAt m' (ka + tvalueSize * i) = some vShrStr →
    rd64 m' (ka + tvalueSize * i + tvalueValOff) = some x →
    TStringRepr m' x printKey → ∃ s, EnvGetAt m' L ci e x s
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
  /-- **(lane F1-13) The objects a `CALL print` leaves alone** hold in every
  memory that agrees with this one on `e.foot` (`EntryFrozen`) -/
  frozen : ∀ M : Mem, (∀ a, InRanges e.foot a → M[a]? = m[a]?) → EntryFrozen M L ci p e
  /-- the string constants' objects hold there too -/
  frozen_strs : ∀ M : Mem, (∀ a, InRanges e.foot a → M[a]? = m[a]?) → ∀ ka i ts s,
    rd64 m (e.pa + protoKOff) = some ka → i < p.k.length → tagAt m (ka + tvalueSize * i) = some (strTag s) →
    rd64 m (ka + tvalueSize * i + tvalueValOff) = some ts → TStringRepr m ts s → TStringRepr M ts s
  /-- the static words of `L` and `g` (`luaStaticWords`) are in `e.foot` -/
  foot_lua : ∀ r ∈ luaStaticWords L e.g, ∀ j, j < r.2 → InRanges e.foot (r.1 + j)
  /-- the constant array and its pointer are in `e.foot` -/
  foot_k : ∀ ka, rd64 m (e.pa + protoKOff) = some ka → (∀ j, j < 8 → InRanges e.foot (e.pa + protoKOff + j)) ∧
    ∀ j, j < tvalueSize * p.k.length → InRanges e.foot (ka + j)
  /-- `e.foot` lies in RAM -/
  foot_ram : ∀ a, InRanges e.foot a → 0x80000000 ≤ a ∧ a < 0x88000000
  /-- `e.foot` is apart from what a `CALL` writes in the heap (`EntryDirty`) -/
  foot_apart : ∀ a, InRanges e.foot a → ¬ EntryDirty L ci e a
  /-- **(lane F1-13) The reserved literals are interned** (`LitsIn`), in every
  memory that agrees with this one on `e.litFoot` -/
  lits : ∀ M : Mem, (∀ a, InRanges e.litFoot a → M[a]? = m[a]?) → LitsHold M e.g e.stackLast e.lits
  /-- `e.litFoot` lies in RAM -/
  lits_ram : ∀ a, InRanges e.litFoot a → 0x80000000 ≤ a ∧ a < 0x88000000
  /-- `e.litFoot` is apart from what `luaD_precall`/`luaD_poscall` write (`LitDirty`) -/
  lits_apart : ∀ a, InRanges e.litFoot a → ¬ LitDirty L ci e a
  /-- no literal's mark byte (`luaS_new`'s `changewhite`) is in `e.foot` -/
  marks : ∀ ts ∈ e.lits.strs, ¬ InRanges e.foot (ts + gcMarkedOff)
  /-- the objects' chunks (`CallPlaced`), for the heap's chunk walk -/
  placed : ∀ top cs, rd64 m DlHeap.topAddr = some top → DlHeap.ChunkWalk m DlHeap.heapStart top cs →
    CallPlaced cs L ci e
  /-- the heap has room for the first `print`'s allocations (`firstRoom`) -/
  room : ∀ b, rd64 m symBrk = some b → b + firstRoom ≤ symHeapEnd
  /-- the objects a `CALL` writes are apart (`ObjsApart`) -/
  objs : ObjsApart L ci e

end Lua.Vm

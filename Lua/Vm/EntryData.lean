import Lua.Vm.Repr
import Lua.Vm.DlHeap
import Lua.Vm.Image
import Vsa.Densify.Transport
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RamReadLoad

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

/-- `rdLE` byte by byte, from the lowest address. (Lane F1-15: moved here from
`Lua/Vm/Sim/Env.lean`, for the boot checks' `LitCache`.) -/
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
    x < 2 ^ (8 * n) ∧ Vsa.Sim.bytesT m a n = BitVec.ofNat (8 * n) x
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
    simp only [Vsa.Sim.bytesT, hbt, hb, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat (8 * n) r ++ b).toNat = _
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      ← Nat.shiftLeft_add_eq_or_of_lt hb8, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbound]
    omega

/-- (lane F1-15) A 64-bit little-endian read is the total eight-byte read. -/
theorem toNat_bytesT8_of_rd64 {m : Mem} {a x : Nat} (h : rd64 m a = some x) :
    (Vsa.Sim.bytesT8 m a).toNat = x := by
  obtain ⟨hlt, hb⟩ := rdLE_spec 8 m a x h
  rw [← Vsa.Sim.bytesT_eight_eq, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

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

/-- The bytes of `"__tostring"`. -/
def tosB : List UInt8 := [0x5f, 0x5f, 0x74, 0x6f, 0x73, 0x74, 0x72, 0x69, 0x6e, 0x67]

/-- (lane F1-15) **`internshrstr`'s test fails at `p`** for the bytes `b`: the
length byte (`lbu a5, 11(s0)`) is not `|b|`, or a content byte differs
(`memcmp`). -/
def NoMatch (m : Mem) (p : Nat) (b : List UInt8) : Prop :=
  rd8 m (p + tstringShrlenOff) ≠ some b.length ∨
    ∃ i, i < b.length ∧ rd8 m (p + tstringContentsOff + i) ≠ some (b.getD i 0).toNat

/-- (lane F1-15) **`internshrstr`'s walk meets `ts` first**: the chain from `p`
(`u.hnext`) reaches `ts` through strings, in RAM above the HTIF mailbox, whose
test fails (`NoMatch`). So the walk returns `ts`, the string interned at boot
(`ChainHas` only says `ts` is on the chain). -/
inductive ChainFirst (m : Mem) (b : List UInt8) (ts : Nat) : Nat → Prop where
  | here : ChainFirst m b ts ts
  | next {p nx : Nat} : p ≠ 0 → p ≠ ts → symTohost + 16 ≤ p → p + 64 ≤ 2 ^ 32 →
      rd64 m (p + tstringLnglenOff) = some nx → NoMatch m p b → ChainFirst m b ts nx → ChainFirst m b ts p

/-- **The literal's string is interned** in `g->strt` (`rt`'s table, of the
memory's zero fill): the one `TString` `ts` of the short bytes `b`, in the
chain of the bucket of `b`'s hash with the state's seed. What `luaS_new` →
`internshrstr` needs to return it without allocating (`luaX_init` interns the
reserved words `nil`, `true`, `false` at boot; nothing is ever collected).
Lane F1-15: the walk meets it first (`first`), it lies in RAM, and the string
cache is no longer read here (`LitCache`, the cache's own fact: `luaS_new`
writes it). -/
structure LitInterned (m : Mem) (rt : RtPtrs) (seed : UInt32) (b : List UInt8) (ts : Nat) : Prop where
  repr : TStringRepr (fillZeroMem m) ts b
  short : b.length ≤ maxShortLen
  strt : StrtAt (fillZeroMem m) rt
  seed_w : rd32 (fillZeroMem m) (rt.g + gSeedOff) = some seed.toNat
  bucket : ∀ (h : (luaHash seed b).toNat % rt.strtSize < rt.strtHeads.length),
    ChainHas (fillZeroMem m) ts rt.strtHeads[(luaHash seed b).toNat % rt.strtSize]
  /-- (lane F1-15) the walk meets `ts` first -/
  first : ∀ (h : (luaHash seed b).toNat % rt.strtSize < rt.strtHeads.length),
    ChainFirst (fillZeroMem m) b ts rt.strtHeads[(luaHash seed b).toNat % rt.strtSize]
  ts_lo : symTohost + 16 ≤ ts
  ts_hi : ts + 64 ≤ 2 ^ 32

/-! ## The string cache and the C literals (lane F1-15)

`lua_pushstring(L, s)` → `luaS_new(L, s)` looks `s` up in the row
`point2uint(s) % STRCACHE_N` of `g->strcache` by `strcmp` against each entry's
contents, and on a miss shifts the row and stores the string `internshrstr`
returns. So a push of a literal is correct only if no entry of its row other
than its own string compares equal (`CDiffers`), and every push keeps that:
the cache's words are always *candidates* of their row (`LitCache`), whose
contents are frozen with the string table (`CandOk`, in `LitsIn`). -/

/-- **A C string literal `luaL_tolstring` pushes**: its `.rodata` address (the
`s` that `luaS_new` hashes into the cache), its bytes, its interned `TString`. -/
structure CLit where
  addr : Nat
  bytes : List UInt8
  ts : Nat

/-- `"nil"` in `.rodata` (`luaL_tolstring`'s `lua_pushliteral(L, "nil")`). -/
def litNilAddr : Nat := 0x8004f2b8
/-- `"true"` in `.rodata`. -/
def litTrueAddr : Nat := 0x8004f2e8
/-- `"false"` in `.rodata`. -/
def litFalseAddr : Nat := 0x8004f280
/-- `"__tostring"` in `.rodata` (`luaL_callmeta(L, idx, "__tostring")`). -/
def litTosAddr : Nat := 0x8004fd20

/-- **The C literals** `luaL_tolstring` pushes on its nil, boolean and string paths. -/
def LitPtrs.table (ls : LitPtrs) : List CLit :=
  [⟨litNilAddr, nilB, ls.nil⟩, ⟨litTrueAddr, trueB, ls.tru⟩, ⟨litFalseAddr, falseB, ls.fls⟩,
   ⟨litTosAddr, tosB, ls.tos⟩]

/-- **`strcmp(s, getstr(p)) ≠ 0`** for the C string `b` (no NUL inside): the
contents at `p` and `b` with its terminator agree before some `k ≤ |b|` and
differ at `k`. -/
def CDiffers (m : Mem) (p : Nat) (b : List UInt8) : Prop :=
  ∃ k, k ≤ b.length ∧ (∀ i, i < k → rd8 m (p + tstringContentsOff + i) = some (b.getD i 0).toNat) ∧
    rd8 m (p + tstringContentsOff + k) ≠ some ((b ++ [0]).getD k 0).toNat

/-- **A candidate `p` of the cache's row `r`**: in RAM above the HTIF mailbox,
and for every literal of that row, its own string or `strcmp`-different. -/
structure CandOk (m : Mem) (lits : List CLit) (r p : Nat) : Prop where
  lo : symTohost + 16 ≤ p
  hi : p + 64 ≤ 2 ^ 32
  ok : ∀ l ∈ lits, l.addr % strcacheN = r → p = l.ts ∨ CDiffers m p l.bytes

/-- **`g->strcache` holds candidates**: word `i` (row `i / STRCACHE_M`) is the
pointer of a candidate of its row. Read off the cache's own words (total
reads), which only `luaS_new` writes. -/
def LitCache (m : Mem) (g : Nat) (ls : LitPtrs) : Prop :=
  ∀ i, i < strcacheN * strcacheM →
    (i / strcacheM, (Vsa.Sim.bytesT8 m (g + gStrcacheOff + 8 * i)).toNat) ∈ ls.cands

/-- **`luaH_getshortstr`'s walk misses `ts`** from node `n` of the array `[lo,
hi)`: past keys that are not the short string `ts` (`lbu a5, 9(a0)`; `ld a5,
16(a0)` only on a short-string tag), to a node whose `gnext` is 0
(`absentkey`). -/
inductive NodeMiss (m : Mem) (ts lo hi : Nat) : Nat → Prop where
  | last {n : Nat} : lo ≤ n → n + nodeSize ≤ hi →
      (rd8 m (n + nodeKeyTtOff) ≠ some vShrStr ∨ ∃ kv, rd64 m (n + nodeKeyValOff) = some kv ∧ kv ≠ ts) →
      rd32 m (n + nodeNextOff) = some 0 → NodeMiss m ts lo hi n
  | next {n g : Nat} : lo ≤ n → n + nodeSize ≤ hi →
      (rd8 m (n + nodeKeyTtOff) ≠ some vShrStr ∨ ∃ kv, rd64 m (n + nodeKeyValOff) = some kv ∧ kv ≠ ts) →
      rd32 m (n + nodeNextOff) = some g → g ≠ 0 → NodeMiss m ts lo hi (nodeNext n g) → NodeMiss m ts lo hi n

/-- **The string library's metatable has no `"__tostring"`** (lane F1-15):
`G(L)->mt[LUA_TSTRING]` is the table `smt` (`lstrlib.c`'s `createmetatable`:
the arithmetic metamethods and `__index`), and `luaH_get(smt, ts)`'s walk from
`ts`'s main position misses. So `luaL_tolstring`'s `luaL_callmeta(L, idx,
"__tostring")` on a string returns 0. -/
structure StrMtMiss (m : Mem) (g ts smt node lsz h : Nat) : Prop where
  mt_w : rd64 m (g + gMtOff + 8 * luaTstring) = some smt
  ne : smt ≠ 0
  lsz_w : rd8 m (smt + tableLsizenodeOff) = some lsz
  node_w : rd64 m (smt + tableNodeOff) = some node
  hash_w : rd32 m (ts + tstringHashOff) = some h
  lsz_lt : lsz < 31
  smt_lo : symTohost + 16 ≤ smt
  smt_hi : smt + 32 ≤ 2 ^ 32
  node_lo : symTohost + 16 ≤ node
  node_hi : node + nodeSize * 2 ^ lsz ≤ 2 ^ 32
  miss : NodeMiss m ts node (node + nodeSize * 2 ^ lsz) (node + nodeSize * (h % 2 ^ lsz))

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
  /-- (lane F1-15) `"__tostring"` -/
  tos : LitInterned M rt ls.seed tosB ls.tos
  /-- (lane F1-15) the string cache's candidates -/
  cands : ∀ c ∈ ls.cands, CandOk (fillZeroMem M) ls.table c.1 c.2
  /-- (lane F1-15) the string metatable misses `"__tostring"` -/
  strmt : StrMtMiss (fillZeroMem M) rt.g ls.tos ls.smt ls.smtNode ls.smtLsz ls.tosHash

/-- **The reserved literals are interned** in `M`, for some string table. -/
def LitsHold (M : Mem) (g sl : Nat) (ls : LitPtrs) : Prop := ∃ rt, LitsIn M g sl ls rt

/-- `g`'s words up to the end of its string cache. -/
def gEnd : Nat := gStrcacheOff + 8 * strcacheN * strcacheM

/-- **What a `CALL print` writes inside the heap's chunks in use** (lane
F1-13): `L->top`, `L->ci`, the Lua `CallInfo` (and `OP_VARARGPREP`'s stores
there), the Lua stack above `ci->func`, `g`'s first words (the GC debt, the
string table's header) and its string cache, and `L->nci` (`luaE_extendCI`). -/
def EntryDirty (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L + stateTopOff ≤ a ∧ a < L + stateTopOff + 8) ∨ (L + stateCiOff ≤ a ∧ a < L + stateCiOff + 8) ∨
  (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast) ∨ (e.g + 16 ≤ a ∧ a < e.g + 64) ∨
  (e.g + gStrcacheOff ≤ a ∧ a < e.g + gEnd) ∨ (L + stateNciOff ≤ a ∧ a < L + stateNciOff + 2)

/-- **What the literals' facts must stay apart from**: the words
`luaD_precall`/`luaD_poscall` write (`L->top`, `L->ci`, the Lua `CallInfo`)
and the Lua stack above `ci->func`; (lane F1-15) what `lua_pushstring` writes
in `g`: `luaE_setdebt`'s `totalbytes` beside `GCdebt`, and the string cache. -/
def LitDirty (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L + stateTopOff ≤ a ∧ a < L + stateTopOff + 8) ∨ (L + stateCiOff ≤ a ∧ a < L + stateCiOff + 8) ∨
  (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast) ∨ (L + stateNciOff ≤ a ∧ a < L + stateNciOff + 2) ∨
  (e.g + gGCdebtOff ≤ a ∧ a < e.g + gGCdebtOff + 8) ∨ (e.g + gTotalbytesOff ≤ a ∧ a < e.g + gTotalbytesOff + 8) ∨
  (e.g + gStrcacheOff ≤ a ∧ a < e.g + gEnd)

/-- The heap room the first `print` may claim: per first-use allocation
(`luaE_extendCI`'s `CallInfo`, `stdout`'s buffer, `"__tostring"`, one more)
one `_malloc_r` with its `_sbrk` (the request, the 16 KiB top pad, a page). -/
def firstRoom : Nat := 4 * (16384 + 4096 + 1024 + 128)

/-- **The static words of the `lua_State` and `g`** a `print` keeps
(`LuaStateAt`'s `hookmask`, `errfunc`, `nCcalls`, `openupval`, `tbclist`,
`stack`, `stack_last`, `l_G`, `errorJmp`, `G(L)->mt[nil, boolean, number]`;
lane F1-14: `g->frealloc`, which `luaE_extendCI`'s `luaM_malloc_` calls):
`(address, width)`. -/
def luaStaticWords (L g : Nat) : List (Nat × Nat) :=
  [(L + stateHookmaskOff, 4), (L + stateErrfuncOff, 8), (L + stateNCcallsOff, 4),
   (L + stateOpenupvalOff, 8), (L + stateTbclistOff, 8), (L + stateStackOff, 8),
   (L + stateStackLastOff, 8), (L + stateGOff, 8), (L + stateErrorJmpOff, 8),
   (g + gMtOff + 8 * luaTnil, 8), (g + gMtOff + 8 * luaTboolean, 8), (g + gMtOff + 8 * luaTnumber, 8),
   (g, 8), (g + gGcstpOff, 1)]

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
  /-- (lane F1-14) `g->frealloc` is main.c's `l_alloc` -/
  frealloc : rd64 m e.g = some symLAlloc
  gc_stopped : rd8 m (e.g + gGcstpOff) = some gcstpUsr
  stack_last : rd64 m (L + stateStackLastOff) = some e.stackLast
  frame_fits : e.func + stackValueSize * (1 + p.maxstacksize) ≤ e.stackLast
  /-- `OP_VARARGPREP` → `luaT_adjustvarargs` → `luaD_checkstack(L, maxstacksize + 1)`
  with `L->top = func + 1` does not grow the stack (`L->stack_last - L->top >
  maxstacksize + 1` slots) -/
  vararg_room : e.func + stackValueSize * (3 + p.maxstacksize) ≤ e.stackLast
  /-- (lane F1-14) `OP_CALL print` from the frame, before or after
  `OP_VARARGPREP` (which moves `ci->func` one slot up), does not grow the
  stack: `luaD_precall`'s `checkstackGCp(L, LUA_MINSTACK)` finds more than 20
  slots above any `L->top` inside the frame -/
  call_room : e.func + stackValueSize * (2 + p.maxstacksize) + 320 < e.stackLast
  /-- (lane F1-14) `g` is 8-aligned (`luaM_malloc_`'s `sd` to `g->GCdebt`) -/
  g_al : e.g % 8 = 0
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
  /-- (lane F1-15) nor in `e.litFoot` -/
  lit_marks : ∀ ts ∈ e.lits.strs, ¬ InRanges e.litFoot (ts + gcMarkedOff)
  /-- (lane F1-15) the string cache holds candidates (`LitCache`) -/
  lit_cache : LitCache m e.g e.lits
  /-- the objects' chunks (`CallPlaced`), for the heap's chunk walk -/
  placed : ∀ top cs, rd64 m DlHeap.topAddr = some top → DlHeap.ChunkWalk m DlHeap.heapStart top cs →
    CallPlaced cs L ci e
  /-- the heap has room for the first `print`'s allocations (`firstRoom`) -/
  room : ∀ b, rd64 m symBrk = some b → b + firstRoom ≤ symHeapEnd
  /-- the objects a `CALL` writes are apart (`ObjsApart`) -/
  objs : ObjsApart L ci e

end Lua.Vm

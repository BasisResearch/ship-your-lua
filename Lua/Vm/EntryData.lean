import Lua.Vm.Repr
import Lua.Vm.DlHeap
import Lua.Vm.Image
import Vsa.Densify.Transport
import Vsa.Sim.MemLoadTotal
import Vsa.Sim.RamReadLoad
import Lua.Vm.LayoutPrint

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
  | next {p nx : Nat} : p ≠ 0 → p ≠ ts → symTohost + 16 ≤ p → p + 128 ≤ symHeapEnd →
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
  ts_hi : ts + 128 ≤ symHeapEnd

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
  hi : p + 64 ≤ symHeapEnd
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

/-! ## The string table's own words apart (lane F1-20)

A new short string (`internshrstr`'s miss) is linked at its bucket's head and
counted (`nuse`), and `luaC_newobj` links it at `g->allgc`: three words the
literals' facts read (the first two) or may not be apart from. So the facts
those words do not belong to must not read them: the chains' nodes, the
literals' objects, the cache's candidates and the string metatable lie apart
from the bucket array and `g` (`StrtOff`). And `internshrstr`'s hit on a dead
string writes its mark (`changewhite`); with the collector stopped no string
but a literal is dead (the literals' marks the facts never read). -/

/-- (lane F1-20) **The table's words**: the bucket array and `g` up to its
string cache. -/
def TabW (rt : RtPtrs) (a : Nat) : Prop :=
  (rt.strtHash ≤ a ∧ a < rt.strtHash + 8 * rt.strtSize) ∨
    (rt.g ≤ a ∧ a < rt.g + (gStrcacheOff + 8 * strcacheN * strcacheM))

/-- (lane F1-23) **`g->strt`'s words, as a memory `m` reads them**: its header
(`hash`, `nuse`, `size`) and the bucket array the header points to. A new
string's insertion writes a bucket's word and `nuse` (`TabWr`), so the
literals' footprint must hold them; the `CALL` invariant keeps them in it
(`CallInvAt.tab_fl`, boot-checked: `VmEntryData.lits_tab`), and so apart
from what a `CALL` writes. -/
def TabFoot (m : Mem) (g a : Nat) : Prop :=
  (g + gStrtHashOff ≤ a ∧ a < g + gStrtHashOff + 16) ∨
    ((Vsa.Sim.bytesT8 m (g + gStrtHashOff)).toNat ≤ a ∧
      a < (Vsa.Sim.bytesT8 m (g + gStrtHashOff)).toNat + 8 * (Vsa.Sim.bytesT4 m (g + gStrtSizeOff)).toNat)

/-- (lane F1-20) **A chain's nodes apart from the table's words, and alive**:
each node's object `[ts, ts + 24 + shrlen + 1)` off `T`, and, unless it is one
of `lits`, not dead (`isdead`: `marked & (currentwhite ^ WHITEBITS)` zero for
the current white `cw`, `lbu`, `xori 24`, `and`). -/
-- discipline: allow(R7-conj-tower-def) the existentials are single witnesses inside named fields (a chain node's mark, the current white), not ∃/∧ towers
inductive ChainOff (m : Mem) (T : Nat → Prop) (cw : Nat) (lits : List Nat) : Nat → Prop where
  | nil : ChainOff m T cw lits 0
  | cons {ts nx l : Nat} : ts ≠ 0 → rd8 m (ts + tstringShrlenOff) = some l →
      rd64 m (ts + tstringLnglenOff) = some nx →
      (∀ a, ts ≤ a → a < ts + tstringContentsOff + l + 1 → ¬ T a) →
      (ts ∉ lits → ∃ mk, rd8 m (ts + gcMarkedOff) = some mk ∧ mk &&& (cw ^^^ 24) = 0) →
      ChainOff m T cw lits nx → ChainOff m T cw lits ts

/-- (lane F1-20) **What the literals' facts read is apart from the table's
words** (but the table's own reads): every chain alive and off them
(`ChainOff`, at `g->currentwhite`), the literals' objects, the cache's
candidates' contents (`CDiffers`), the string metatable and its node array. -/
structure StrtOff (m : Mem) (ls : LitPtrs) (rt : RtPtrs) : Prop where
  white : ∃ cw, rd8 m (rt.g + gCurrentwhiteOff) = some cw ∧
    ∀ j (h : j < rt.strtHeads.length), ChainOff m (TabW rt) cw ls.strs rt.strtHeads[j]
  lits : ∀ ts ∈ ls.strs, ∀ a, ts ≤ a → a < ts + 40 → ¬ TabW rt a
  cands : ∀ c ∈ ls.cands, ∀ a, c.2 + tstringContentsOff ≤ a → a < c.2 + tstringContentsOff + 11 → ¬ TabW rt a
  smt : ∀ a, ls.smt ≤ a → a < ls.smt + 64 → ¬ TabW rt a
  node : ∀ a, ls.smtNode ≤ a → a < ls.smtNode + nodeSize * 2 ^ ls.smtLsz → ¬ TabW rt a
  /-- the bucket array 8-aligned (`sd` of the new head) -/
  hash_al : rt.strtHash % 8 = 0

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
  /-- (lane F1-15) the bucket array in RAM, its size a 32-bit `int` (`internshrstr`'s `lw`) -/
  hash_lo : symTohost + 16 ≤ rt.strtHash
  hash_hi : rt.strtHash + 8 * rt.strtSize ≤ symHeapEnd
  size_hi : rt.strtSize < 2 ^ 30
  /-- (lane F1-15) every literal's string is a candidate of its row (`luaS_new`'s miss stores it) -/
  lit_cands : ∀ l ∈ ls.table, (l.addr % strcacheN, l.ts) ∈ ls.cands
  /-- (lane F1-20) what the facts read apart from the table's words, no string dead -/
  off : StrtOff (fillZeroMem M) ls rt

/-- **The reserved literals are interned** in `M`, for some string table. -/
def LitsHold (M : Mem) (g sl : Nat) (ls : LitPtrs) : Prop := ∃ rt, LitsIn M g sl ls rt

/-- `g`'s words up to the end of its string cache. -/
def gEnd : Nat := gStrcacheOff + 8 * strcacheN * strcacheM

/-- **What a `CALL print` writes inside the heap's chunks in use** (lane
F1-13): `L->top`, `L->ci`, the Lua `CallInfo` (and `OP_VARARGPREP`'s stores
there), the Lua stack above `ci->func`, `g`'s first words (the GC debt, the
string table's header) and its string cache, and `L->nci` (`luaE_extendCI`);
(lane F1-19) `g->allgc`, which `luaC_newobj` links a new string to. -/
def EntryDirty (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L + stateTopOff ≤ a ∧ a < L + stateTopOff + 8) ∨ (L + stateCiOff ≤ a ∧ a < L + stateCiOff + 8) ∨
  (ci ≤ a ∧ a < ci + ciSize) ∨ (e.func ≤ a ∧ a < e.stackLast) ∨ (e.g + 16 ≤ a ∧ a < e.g + 64) ∨
  (e.g + gStrcacheOff ≤ a ∧ a < e.g + gEnd) ∨ (L + stateNciOff ≤ a ∧ a < L + stateNciOff + 2) ∨
  (e.g + gAllgcOff ≤ a ∧ a < e.g + gAllgcOff + 8)

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
lane F1-14: `g->frealloc`, which `luaE_extendCI`'s `luaM_malloc_` calls;
lane F1-19: `G(L)->mt[LUA_TFUNCTION]`, and the `.data` words `snprintf` reads,
`LocaleWords`): `(address, width)`. -/
def luaStaticWords (L g : Nat) : List (Nat × Nat) :=
  [(L + stateHookmaskOff, 4), (L + stateErrfuncOff, 8), (L + stateNCcallsOff, 4),
   (L + stateOpenupvalOff, 8), (L + stateTbclistOff, 8), (L + stateStackOff, 8),
   (L + stateStackLastOff, 8), (L + stateGOff, 8), (L + stateErrorJmpOff, 8),
   (g + gMtOff + 8 * luaTnil, 8), (g + gMtOff + 8 * luaTboolean, 8), (g + gMtOff + 8 * luaTnumber, 8),
   (g, 8), (g + gGcstpOff, 1), (g + gMtOff + 8 * luaTfunction, 8),
   (symImpurePtr, 8), (0x8005d0f0, 8), (0x8005d0d8, 8), (0x8005d150, 1)]

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

/-! ## What an allocating `print` must find apart (lane F1-19)

`OP_CALL print` on an allocating argument writes inside the string table (a
bucket's head, `internshrstr` on a miss; a dead string's mark, `changewhite`
on a hit), links the new string at `g->allgc` (`EntryDirty`), and on a float
reuses `_dtoa_r`'s bignums (`_REENT->_result`, `_p5s`, `_freelist`). The
relation keeps both apart from what the caller needs: the table's safety
(`StrtSafe`) and the bignums (`ReentMp`), checked at the boot (`strt_safe`,
`reent`) and re-established by every `print` (`CallInvAt.alloc`). -/

/-- **A bucket's chain, readable and apart** (`internshrstr`'s walk on any
contents; lane F1-18, moved here and given `W`): each string short (`shrlen ≤
LUAI_MAXSHORTLEN`), its object `[ts, ts + 24 + shrlen + 1)` (the header the
walk reads, the contents `memcmp` reads) in `K` and off `W` (what a `print`
writes outside the table: `_dtoa_r`'s bignums), and the bytes a `print` may
write in it off `X` (what the caller keeps): the mark (`changewhite` of a
dead string found) and `u.hnext` (`luaS_resize`'s rehash). -/
inductive StrChainK (m : Mem) (K X W : Nat → Prop) (size i : Nat) : Nat → Prop where
  | nil : StrChainK m K X W size i 0
  | cons {ts h nx l : Nat} : ts ≠ 0 → rd8 m (ts + gcTtOff) = some gcShrStr →
      rd8 m (ts + tstringShrlenOff) = some l → l ≤ maxShortLen → rd32 m (ts + tstringHashOff) = some h →
      h % size = i → rd64 m (ts + tstringLnglenOff) = some nx →
      (∀ a, ts ≤ a → a < ts + tstringContentsOff + l + 1 → K a ∧ ¬ W a) → ¬ X (ts + gcMarkedOff) →
      (∀ a, ts + tstringLnglenOff ≤ a → a < ts + tstringLnglenOff + 8 → ¬ X a) →
      StrChainK m K X W size i nx → StrChainK m K X W size i ts

/-- **`g->strt` readable and apart** (`internshrstr` on any short contents):
the bucket array (`tb->hash[h] = ts` on a miss) in `K`, off `X` and `W`, and
every chain (`StrChainK`). -/
structure StrtSafe (m : Mem) (rt : RtPtrs) (K X W : Nat → Prop) : Prop where
  hash : ∀ a, rt.strtHash ≤ a → a < rt.strtHash + 8 * rt.strtSize → K a ∧ ¬ X a ∧ ¬ W a
  chains : ∀ j (h : j < rt.strtHeads.length), StrChainK m K X W rt.strtSize j rt.strtHeads[j]

/-- A chain's safety with more bytes in `K` and fewer kept (`X`) and written
(`W`) among them. -/
theorem StrChainK.weaken {m : Mem} {K K' X X' W W' : Nat → Prop} {size i p : Nat}
    (h : StrChainK m K X W size i p) (hK : ∀ a, K a → K' a) (hX : ∀ a, K a → X' a → X a)
    (hW : ∀ a, K a → W' a → W a) : StrChainK m K' X' W' size i p := by
  induction h with
  | nil => exact .nil
  | @cons ts h0 nx l h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ ih =>
    have hc : tstringContentsOff = 24 := rfl
    have hm : gcMarkedOff = 9 := rfl
    have hn : tstringLnglenOff = 16 := rfl
    refine .cons h1 h2 h3 h4 h5 h6 h7 (fun a l1 l2 => ⟨hK a (h8 a l1 l2).1, fun hw =>
      (h8 a l1 l2).2 (hW a (h8 a l1 l2).1 hw)⟩) (fun hx => h9 (hX _ (h8 _ (by omega) (by omega)).1 hx))
      (fun a l1 l2 hx => h10 a l1 l2 (hX a (h8 a (by omega) (by omega)).1 hx)) ih

/-- The table's safety with more bytes in `K` and fewer kept (`X`) and written
(`W`) among them. -/
theorem StrtSafe.weaken {m : Mem} {rt : RtPtrs} {K K' X X' W W' : Nat → Prop} (h : StrtSafe m rt K X W)
    (hK : ∀ a, K a → K' a) (hX : ∀ a, K a → X' a → X a) (hW : ∀ a, K a → W' a → W a) :
    StrtSafe m rt K' X' W' :=
  ⟨fun a l u => ⟨hK a (h.hash a l u).1, fun hx => (h.hash a l u).2.1 (hX a (h.hash a l u).1 hx),
      fun hw => (h.hash a l u).2.2 (hW a (h.hash a l u).1 hw)⟩,
    fun j hj => (h.chains j hj).weaken hK hX hW⟩

/-- **`_REENT`'s `_dtoa_r` words** (`_result`, `_result_k`, `_p5s`,
`_freelist`). -/
def ReentWord (a : Nat) : Prop := symImpureData + reentResultOff ≤ a ∧ a < symImpureData + reentFreelistOff + 8

/-- The bytes of `_Balloc(k)`'s block (`_calloc_r(_REENT, 1, 28 + 4·2^k)`:
`_next` 0, `_k` 8, `_maxwds` 12, `_sign` 16, `_wds` 20, `_x` 24). -/
def bigSize (k : Nat) : Nat := 28 + 4 * 2 ^ k

/-- **A chain of `_Bigint`s through `_next`** (`_freelist[k]`, `_p5s`) with
their classes: `_k` and `_maxwds = 2^k` as `_Balloc` set them. -/
inductive BigChain (m : Mem) : Nat → List (Nat × Nat) → Prop where
  | nil : BigChain m 0 []
  | cons {b nx k : Nat} {bs : List (Nat × Nat)} : b ≠ 0 → rd64 m b = some nx → rd32 m (b + 8) = some k →
      rd32 m (b + 12) = some (2 ^ k) → k ≤ 64 → BigChain m nx bs → BigChain m b ((b, k) :: bs)

/-- The header reads a bignum chain needs in another memory. -/
structure BigHeaderKeep (m m' : Mem) (b : Nat) : Prop where
  next : rd64 m' b = rd64 m b
  cls : rd32 m' (b + 8) = rd32 m (b + 8)
  maxwds : rd32 m' (b + 12) = rd32 m (b + 12)

/-- Transport a chain through stores apart from its headers. -/
theorem BigChain.congr {m m' : Mem} {hd : Nat} {bs : List (Nat × Nat)}
    (h : BigChain m hd bs) (hk : ∀ x ∈ bs, BigHeaderKeep m m' x.1) : BigChain m' hd bs := by
  induction h with
  | nil => exact .nil
  | @cons b nx k bs hn hnext hcls hmax hbound htail ih =>
    have hh := hk (b, k) (List.mem_cons_self ..)
    exact .cons hn (hh.next.trans hnext) (hh.cls.trans hcls) (hh.maxwds.trans hmax) hbound
      (ih fun x hx => hk x (List.mem_cons_of_mem _ hx))

/-- The value of a bignum: `_wds` words of `_x`, base `2^32`. -/
def bigVal (m : Mem) (b : Nat) : Option Nat :=
  (rd32 m (b + 20)).bind fun wds => (List.range wds).foldr
    (fun i acc => (rd32 m (b + 24 + 4 * i)).bind fun x => acc.map fun r => x + 2 ^ 32 * r) (some 0)

/-- The blocks of `_dtoa_r`'s bignums: the free lists' array (65 pointers,
`_calloc_r(_REENT, 8, 65)`), the last result (its digits overwrite its
header), every listed bignum. -/
def bigBlocks (fl res rk : Nat) (lists : List (List (Nat × Nat))) (ps : List (Nat × Nat)) : List (Nat × Nat) :=
  (if fl = 0 then [] else [(fl, 8 * 65)]) ++ (if res = 0 then [] else [(res, bigSize rk)]) ++
    (lists.flatten ++ ps).map fun x => (x.1, bigSize x.2)

/-- **`_dtoa_r`'s bignums in `_REENT`**, at the array `fl`, the result `res`
of class `rk`, the free lists' heads `hds` and nodes `lists`, and the cache
`_p5s` (`ps`): `_Balloc` pops `_freelist[k]` (`ld a5,104(a0)`), `_Bfree`
pushes by `_k`, `_dtoa_r` frees `_result` on entry after restoring its `_k`
and `_maxwds` from `_result_k`, `__pow5mult` multiplies by the cached
`5^(4·2^j)`; every block apart from the others, in `B`. -/
structure ReentMpAt (m : Mem) (B : Nat → Prop) (fl res rk p5 : Nat) (hds : List Nat)
    (lists : List (List (Nat × Nat))) (ps : List (Nat × Nat)) : Prop where
  res_w : rd64 m (symImpureData + reentResultOff) = some res
  rk_w : res ≠ 0 → rd32 m (symImpureData + reentResultKOff) = some rk
  p5_w : rd64 m (symImpureData + reentP5sOff) = some p5
  fl_w : rd64 m (symImpureData + reentFreelistOff) = some fl
  /-- no array, no bignum (`_Balloc` makes the array first) -/
  fl_zero : fl = 0 → res = 0 ∧ p5 = 0 ∧ ∀ l ∈ lists, l = []
  hds_len : hds.length = 65
  lists_len : lists.length = 65
  heads : fl ≠ 0 → ∀ k (h : k < hds.length), rd64 m (fl + 8 * k) = some hds[k]
  chains : fl ≠ 0 → ∀ k (h1 : k < hds.length) (h2 : k < lists.length), BigChain m hds[k] lists[k]
  classes : ∀ k (h : k < lists.length), ∀ x ∈ lists[k], x.2 = k
  res_k : res ≠ 0 → rk ≤ 64
  p5s : BigChain m p5 ps
  p5v : ∀ j x, ps[j]? = some x → bigVal m x.1 = some (5 ^ (4 * 2 ^ j))
  apart : (bigBlocks fl res rk lists ps).Pairwise fun x y => Apart x.1 x.2 y.1 y.2
  inB : ∀ x ∈ bigBlocks fl res rk lists ps, ∀ a, x.1 ≤ a → a < x.1 + x.2 → B a

/-- **`_dtoa_r`'s bignums in `_REENT`**, in `B` (`ReentMpAt` for some lists). -/
inductive ReentMp (m : Mem) (B : Nat → Prop) : Prop where
  | intro (fl res rk p5 : Nat) (hds : List Nat) (lists : List (List (Nat × Nat))) (ps : List (Nat × Nat))
      (h : ReentMpAt m B fl res rk p5 hds lists ps)

/-- **No bignum yet**: `_result`, `_p5s` and `_freelist` NULL. -/
structure ReentBoot (m : Mem) : Prop where
  res : rd64 m (symImpureData + reentResultOff) = some 0
  p5 : rd64 m (symImpureData + reentP5sOff) = some 0
  fl : rd64 m (symImpureData + reentFreelistOff) = some 0

/-- With no bignum, `ReentMp` holds in any region. -/
theorem ReentBoot.mp {m : Mem} (h : ReentBoot m) (B : Nat → Prop) : ReentMp m B := by
  refine .intro 0 0 0 0 (List.replicate 65 0) (List.replicate 65 []) [] ⟨h.res, fun h0 => absurd rfl h0, h.p5,
    h.fl, fun _ => ⟨rfl, rfl, fun l hl => List.eq_of_mem_replicate hl⟩, by simp, by simp,
    fun h0 => absurd rfl h0, fun h0 => absurd rfl h0, fun k hk x hx => ?_, fun h0 => absurd rfl h0, .nil,
    fun j x hx => by simp at hx, ?_, fun x hx => ?_⟩
  · simp only [List.getElem_replicate] at hx; cases hx
  · simp [bigBlocks]
  · simp [bigBlocks] at hx

/-- (lane F1-19) **The `.data` words `snprintf` reads** (`_svfprintf_r`,
`_localeconv_r`, `__locale_mb_cur_max`; Sail trace, lane F1-19): `_impure_ptr`,
the C locale's `decimal_point` (`__global_locale + 0x100`), its `mbtowc`
hook (`+ 0xe8`) and `__mb_cur_max` (`+ 0x160`). -/
structure LocaleWords (m : Mem) : Prop where
  impure : rd64 m symImpurePtr = some symImpureData
  decpt : rd64 m 0x8005d0f0 = some 0x8004fb10
  mbtowc : rd64 m 0x8005d0d8 = some 0x8003cd58
  mbmax : rd8 m 0x8005d150 = some 1

/-- The bytes `LocaleWords` reads. -/
def LocaleW (a : Nat) : Prop :=
  (symImpurePtr ≤ a ∧ a < symImpurePtr + 8) ∨ (0x8005d0f0 ≤ a ∧ a < 0x8005d0f0 + 8) ∨
    (0x8005d0d8 ≤ a ∧ a < 0x8005d0d8 + 8) ∨ a = 0x8005d150

/-- **What the caller of a `print` keeps, at the boot** (`StrtSafe`'s `X`):
`e.foot`, the `lua_State`, `g` up to its string cache, the `CallInfo`, the Lua
stack above `ci->func`'s slot, and everything below the heap. -/
def EntryX (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  InRanges e.foot a ∨ (L ≤ a ∧ a < L + stateSize) ∨ (e.g ≤ a ∧ a < e.g + gEnd) ∨ (ci ≤ a ∧ a < ci + ciSize) ∨
    (e.func + 16 ≤ a ∧ a < e.stackLast) ∨ a < DlHeap.heapStart

/-- (lane F1-23) **The Lua objects a `CALL print` writes in, at the boot's
places** (`StrtSafe`'s `W`): the `lua_State`, `g` up to its string cache, the
`CallInfo`, the Lua stack from `ci->func`. No string of the table lies there
(`luaL_tolstring`'s push writes `L->top` and the stack's top slot after
`internshrstr` finds a string, whose bytes `luaB_print` then writes). -/
def EntryW (L ci : Nat) (e : EntryPtrs) (a : Nat) : Prop :=
  (L ≤ a ∧ a < L + stateSize) ∨ (e.g ≤ a ∧ a < e.g + gEnd) ∨ (ci ≤ a ∧ a < ci + ciSize) ∨
    (e.func ≤ a ∧ a < e.stackLast)

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
  foot : ∀ a, InRanges e.foot a → HeapIn cs a ∨ (0x80000000 ≤ a ∧ a < symTohost) ∨ LocaleW a
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
  /-- (lane F1-19) `G(L)->mt[LUA_TFUNCTION]` is NULL: `luaL_tolstring` of a
  function prints `"function: %p"` -/
  mt_fn : rd64 m (e.g + gMtOff + 8 * luaTfunction) = some 0
  /-- (lane F1-19) the `.data` words `snprintf` reads (`LocaleWords`) -/
  locale : LocaleWords m
  /-- (lane F1-19) no bignum of `_dtoa_r` yet (`ReentBoot`) -/
  reent : ReentBoot m
  /-- (lane F1-19) **the string table's chains readable and apart**
  (`StrtSafe`, at the boot's places `EntryX`), in every memory that agrees
  with this one on `e.litFoot`, for the heap's chunk walk -/
  strt_safe : ∀ top cs, rd64 m DlHeap.topAddr = some top → DlHeap.ChunkWalk m DlHeap.heapStart top cs →
    ∀ M : Mem, (∀ a, InRanges e.litFoot a → M[a]? = m[a]?) → ∀ rt, LitsIn M e.g e.stackLast e.lits rt →
    StrtSafe (fillZeroMem M) rt (HeapIn cs) (EntryX L ci e) (EntryW L ci e)
  /-- (lane F1-23) **`g->strt`'s words in `e.litFoot`** (`TabFoot`): the
  literals' check reads the header and every bucket through the footprint -/
  lits_tab : ∀ a, TabFoot m e.g a → InRanges e.litFoot a

end Lua.Vm

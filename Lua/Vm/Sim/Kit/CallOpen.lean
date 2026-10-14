import Lua.Vm.Sim.Kit.CallArm
import Lua.Vm.Sim.Kit.PrintS
import Lua.Vm.Sim.Kit.RetPoscall
import Lua.Vm.Sim.Kit.Tolstring

/-!
# `OP_CALL print`'s open parts, in the relation's terms (lane F1-13)

`PrintCall_Statement CallInv` (the premise of `sim_CALL_of` on the `CALL`
invariant) is proved in `Kit/CallPrint.lean` (`printCall_of`) from
`luaD_precall`'s C path (`precall_reuse`, `precall_ext`), `luaD_poscall` with
`C = 1` (`poscall_sum`) and the relation's region facts, over the named
premise collected here (`CallOpen`: `printAlloc`) and the theorems
it composes:

* `PrintRel_Statement`: `luaB_print` on the C frame `luaD_precall` builds,
  stated over the regions it keeps (`PrintIn`/`PrintOut`): the line on the
  console, `stdout` set up and flushed, the bytes `G` the caller needs kept,
  the interned literals again. Proved (`CallOpen.print`, `Kit/PrintRel.lean`,
  lane F1-15) from `print_sum` (lane F1-11) with `luaL_tolstring` per value
  class: nil/booleans over `pushLit_proved`, strings `TolStr_Statement`
  (`tolStr_proved`, lane F1-17), the allocating classes `PrintAlloc_Statement` (field
  `printAlloc`), and `_malloc_r` (`AllocProof.mallocR_proved`, lane F1-A0-M);
* `ExtendCI_Statement`: `luaE_extendCI` (`ci->next` NULL at the first
  `print`), `extendCI_proved`;
* `PoscallN_Statement`: `luaD_poscall` with `C ≥ 2` (`wanted ≥ 1` nils);
* `PrintGrow_Statement`: `luaD_precall`'s stack growth (`L->stack_last - L->top
  ≤ LUA_MINSTACK`), `printGrow_none`;
* `ExitUp_Statement`: `exit(0)` once `stdout` is set up (the post-print
  `ExitOk`), `exitUp_proved` from `_free_r` (`AllocProof.freeR_proved`, lane
  F1-A0-M) by `exitUp_of_free` (`Kit/ExitUp.lean`, lane F1-14).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-! ## `luaB_print` on the C frame -/

/-- The bytes no `print` writes outside the heap: the image below the HTIF
mailbox and `__atexit`. -/
def PrintStatic (a : Nat) : Prop := (0x80000000 ≤ a ∧ a < symTohost) ∨ Rng symAtexit 8 a

/-- **The literals interned** at a `print`'s state: frozen on `FL`, in chunks
in use, apart from `D`, the literals' objects in chunks in use. -/
structure LitsFoot (g sl : Nat) (ls : LitPtrs) (H : HeapIx) (ph : StdoutPh) (D FL : Nat → Prop) (m : Mem) :
    Prop where
  facts : Frozen FL (fun M => LitsHold M g sl ls) m
  kept : ∀ a, FL a → Kept H ph a
  apart : ∀ a, FL a → ¬ D a
  strs : ∀ ts ∈ ls.strs, ∀ a, ts ≤ a → a < ts + 30 → Kept H ph a
  /-- (lane F1-15) no literal's mark byte in `FL` -/
  marks : ∀ ts ∈ ls.strs, ¬ FL (ts + gcMarkedOff)
  /-- (lane F1-15) the string cache holds candidates -/
  cache : LitCache m g ls

/-- `[a, a + n)` and `[b, b + k)` apart, the other way round. -/
theorem _root_.Lua.Vm.Apart.symm {a n b k : Nat} (h : Apart a n b k) : Apart b k a n := Or.symm h

/-- (lane F1-15) **Where `luaB_print`'s Lua objects lie, apart**: the
`lua_State`, the C `CallInfo`, the Lua stack above `func`, `g` up to its
string cache and the literals' objects. -/
structure PrintObjs (L nci func sl g : Nat) (ls : LitPtrs) : Prop where
  L_g : Apart L stateSize g gEnd
  nci_g : Apart nci ciSize g gEnd
  stack_g : Apart func (sl - func) g gEnd
  L_stack : Apart L stateSize func (sl - func)
  nci_stack : Apart nci ciSize func (sl - func)
  lit_L : ∀ ts ∈ ls.strs, Apart ts 30 L stateSize
  lit_g : ∀ ts ∈ ls.strs, Apart ts 30 g gEnd
  lit_nci : ∀ ts ∈ ls.strs, Apart ts 30 nci ciSize
  lit_stack : ∀ ts ∈ ls.strs, Apart ts 30 func (sl - func)

/-- The slots of `print`'s `n` arguments above `func`. -/
def ArgSlot (func n a : Nat) : Prop := func + 16 ≤ a ∧ a < func + 16 * (n + 1)

/-- **The arguments represented** in a memory: argument `i` in the slot
`func + 16 (i + 1)`. -/
def ArgsAt (func : Nat) (ι : Strs) (args : List Value) (M : Mem) : Prop :=
  ∀ i v, args[i]? = some v →
    ValRepr (fillZeroMem M) ι (slotTag M (func + 16 * (i + 1))) (slotVal M (func + 16 * (i + 1))) v

/-- **`luaB_print`'s entry** from `luaD_precall`'s C path: the API frame of `n`
arguments above `func` (`L->ci` the C `CallInfo` `nci`), `stdout` with
nothing pending and the heap, the arguments represented (`ι` the intern map),
the stack room `precallC` checked, `G(L)` with no metatables for nil, booleans
and numbers, the interned literals (apart from `D`), and the bytes `G` the
caller needs kept: in chunks in use or static, apart from `L->top`, the
stack above the arguments, `g`'s first words and string cache, and the
literals' mark bytes. Lane F1-15: where the Lua objects lie (in chunks in use,
apart: `PrintObjs`), the arguments frozen on `G` and their slots, the
collector stopped, `.rodata`. -/
structure PrintIn (L nci func n tbc sl g : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs)
    (D G : Nat → Prop) (ph : StdoutPh) (H : HeapIx) (M : Mem) : Prop where
  api : ApiAt M L nci func n tbc
  st : PrintSt M ph H
  pend : ph.pend = []
  len : args.length = n
  /-- (lane F1-17) the arguments' strings lie in the heap (`Complement.own`:
  an in-use chunk of the allocator's walk), not in the image -/
  args_heap : ∀ (i : Nat) (s : List UInt8), args[i]? = some (Value.str s) →
    heapStart ≤ (slotVal M (func + 16 * (i + 1))).toNat
  /-- (lane F1-15) the arguments, in every memory agreeing on `G` and their slots -/
  args_fz : Frozen (fun a => G a ∨ ArgSlot func n a) (ArgsAt func ι args) M
  args : ArgsAt func ι args M
  /-- (lane F1-15) `func` aligned (`L->top`'s slots, `lua_pushstring`'s stores) -/
  f_al : func % 8 = 0
  room : func + 16 * n + 16 + 320 < sl
  g_w : bytesT8 M (L + stateGOff) = BitVec.ofNat 64 g
  mt : ∀ t ∈ [luaTnil, luaTboolean, luaTnumber], bytesT8 M (g + gMtOff + 8 * t) = 0#64
  hook : bytesT4 M (L + stateHookmaskOff) = 0#32
  lits : ∃ FL, LitsFoot g sl ls H ph D FL M
  keep_in : ∀ a, G a → Kept H ph a ∨ PrintStatic a
  keep_apart : ∀ a, G a → ¬ Rng (L + stateTopOff) 8 a ∧ ¬ (func + 16 * n + 16 ≤ a ∧ a < sl) ∧
    ¬ Rng (g + 16) 48 a ∧ ¬ (g + gStrcacheOff ≤ a ∧ a < g + gEnd) ∧ ∀ ts ∈ ls.strs, a ≠ ts + gcMarkedOff
  /-- (lane F1-15) the Lua objects in chunks in use -/
  L_in : ∀ a, L ≤ a → a < L + stateSize → Kept H ph a
  g_in : ∀ a, g ≤ a → a < g + gEnd → Kept H ph a
  nci_in : ∀ a, nci ≤ a → a < nci + ciSize → Kept H ph a
  stack_in : ∀ a, func ≤ a → a < sl → Kept H ph a
  objs : PrintObjs L nci func sl g ls
  gcstp : bytesT1 M (g + gGcstpOff) = BitVec.ofNat 8 gcstpUsr
  ro : RodataRead M
  g_al : g % 8 = 0
  /-- (lane F1-15) `D` holds what a literal push writes: `L->top`, the Lua
  stack above `func`, `totalbytes`, `GCdebt`, the string cache -/
  dirty : ∀ a, Rng (L + stateTopOff) 8 a ∨ (func ≤ a ∧ a < sl) ∨ Rng (g + gTotalbytesOff) 8 a ∨
    Rng (g + gGCdebtOff) 8 a ∨ (g + gStrcacheOff ≤ a ∧ a < g + gEnd) → D a

/-- **What `luaB_print` leaves** for its caller: the console's bytes are the
line, `stdout` set up and flushed with the heap (the chunks in use kept, the
buffer the old one or a fresh block), the literals interned again (apart from
`D`), the bytes `G` and the frames from its `sp` up kept. -/
structure PrintOut (sp0 g sl : Nat) (ls : LitPtrs) (args : List Value) (D G : Nat → Prop) (ph : StdoutPh)
    (H : HeapIx) (M m' : Mem) (out : List (BitVec 8)) : Prop where
  line : charsOf out = printLine binaryHost args
  st : ∃ buf H' FL, PrintSt m' (.up buf []) H' ∧ (∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks) ∧
    BufFrom ph (.up buf []) H ∧ LitsFoot g sl ls H' (.up buf []) D FL m'
  keep : ∀ a, G a → bytesT1 m' a = bytesT1 M a
  above : ∀ a, sp0 ≤ a → bytesT1 m' a = bytesT1 M a

/-- The heap a first-use allocation of `luaD_precall` claims (`luaE_extendCI`'s
`CallInfo`: one `_malloc_r` with its `_sbrk`). -/
def extRoom : Nat := 16384 + 4096 + 128

/-- **`luaB_print` on the C frame, for the argument lists `Q`** (`0x80022f18`,
called by `precallC`'s `jalr a7` with `ra = 0x8000ac8c` and `sp - 96`), from
`PrintIn` and, when an argument allocates, the heap room of `CALL print` less
the `CallInfo`'s (`callBudget`, `extRoom`): `PrintOut`. -/
def PrintRelOn (Q : List Value → Prop) : Prop :=
  ∀ (sp L nci func n tbc sl g ss : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs) (D G : Nat → Prop)
    (ph : StdoutPh) (H : HeapIx) (f : AbiFrame) (M : Mem) (o : Array String), Q args →
    PrintIn L nci func n tbc sl g ls args ι D G ph H M → PrNums (sp - 96) L nci func n 0x8000ac8c#64 →
    (AnyAlloc args → H.brk + callBudget args ss ≤ heapEnd + extRoom) →
    Triple (SegSt 0x80022f18#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp - 96) 0x8000ac8c#64 (pcFr L f))
        (ArmPay M o))
      (fun c => ∃ m' out, wrRet 0x8000ac8c#64 (sp - 96) 0 (pcFr L f) m' (pushes o out) c ∧
        PrintOut (sp - 96) g sl ls args D G ph H M m' out)

/-- **`luaB_print` on the C frame** (every argument list): `PrintRelOn` of
all. Lane F1-15: proved (`printRel_of`, `Kit/PrintRel.lean`) from the
allocating lists' `PrintAlloc_Statement`, the literal classes over
`PushLit_Statement` and the strings over `TolStr_Statement`. -/
def PrintRel_Statement : Prop := PrintRelOn fun _ => True

/-- **Named premise: `luaB_print` when some argument allocates** (lane F1-15:
an integer, a float or a function, `Allocates`): `luaL_tolstring` →
`lua_pushfstring` → `luaO_pushvfstring` (`lua_integer2str` =
`IntegerToStr_Statement`, `%.14g` = `G14From`, `"%s: %p"`) → `luaS_newlstr` →
`internshrstr` creating a string (`luaC_newobj` → `_malloc_r`; `luaS_resize`
when the table is full). Coarse because `print_sum`'s Lua state `S k ph H m`
does not know the argument's index, so it cannot carry a per-argument heap
budget, and a write's post (`PrintPost`) bounds no break; and a new string
changes the string table the literals' facts read (a new `FL`). -/
def PrintAlloc_Statement : Prop := PrintRelOn AnyAlloc

/-! ## `luaB_print`'s Lua state (lane F1-15) -/

/-- **The bytes `luaB_print`'s Lua state keeps from its entry memory**: `G`,
the arguments' slots, `.rodata`, `g->gcstp`, `G(L)->mt[nil … number]`,
`L->l_G`, `L->hookmask`. -/
def PrKeep (L g func n : Nat) (G : Nat → Prop) (a : Nat) : Prop :=
  G a ∨ ArgSlot func n a ∨ (Image.rodataBase ≤ a ∧ a < Image.rodataBase + Image.rodataSize) ∨
    Rng (g + gGcstpOff) 1 a ∨ Rng (g + gMtOff) 32 a ∨ Rng (L + stateGOff) 8 a ∨ Rng (L + stateHookmaskOff) 4 a

/-- **`luaB_print`'s Lua state** (`print_sum`'s `S k ph H m`, lane F1-15): the
API frame of `k` values, the literals (frozen on `FL`, the cache's
candidates), the bytes `PrKeep` of the entry memory `M0`, the buffer the
entry's or fresh, the entry's chunks in use kept. -/
structure PrSt (L nci func tbc sl g n : Nat) (ls : LitPtrs) (D G FL : Nat → Prop) (M0 : Mem) (ph0 : StdoutPh)
    (H0 : HeapIx) (k : Nat) (ph : StdoutPh) (H : HeapIx) (m : Mem) : Prop where
  api : ApiAt m L nci func k tbc
  lits : LitsFoot g sl ls H ph D FL m
  keep : ∀ a, PrKeep L g func n G a → bytesT1 m a = bytesT1 M0 a
  buf : BufFrom ph0 ph H0
  chunks : ∀ c ∈ H0.chunks, c.inuse = true → c ∈ H.chunks

/-- The bytes argument `v` prints (`Value.show`, one byte per character). -/
def argBytes (v : Value) : List (BitVec 8) :=
  (Value.show binaryHost v).toList.map fun c => BitVec.ofNat 8 c.toNat

/-- A string value. -/
def IsStr : Value → Prop
  | .str _ => True
  | _ => False

/-- **`luaL_tolstring(L, i, &l)` in `luaB_print`'s loop on an argument of
class `C`** (lane F1-15): from `luaB_print`'s entry facts (`PrintIn`,
`PrNums`) and its Lua state of `n` values (`PrSt`), `TolPost`: the state with
one more value, the argument's bytes. -/
def TolArg (C : Value → Prop) : Prop :=
  ∀ (sp0 L nci func n tbc sl g : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs) (D G FL : Nat → Prop)
    (ph0 : StdoutPh) (H0 : HeapIx) (M0 : Mem) (i : Nat) (v : Value),
    PrintIn L nci func n tbc sl g ls args ι D G ph0 H0 M0 → PrNums sp0 L nci func n 0x8000ac8c#64 →
    args[i - 1]? = some v → C v → 1 ≤ i → i ≤ n →
    ∀ (ph : StdoutPh) (H : HeapIx) (m : Mem) (o : Array String) (r : BitVec 64) (f : AbiFrame),
    PrSt L nci func tbc sl g n ls D G FL M0 ph0 H0 n ph H m → PrintSt m ph H → r.toNat % 4 = 0 →
    Triple (SegSt 0x80021b2c#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩, ⟨Register.x11, BitVec.ofNat 64 i⟩,
        ⟨Register.x12, BitVec.ofNat 64 (sp0 - 56)⟩] (sp0 - 64) r f) (ArmPay m o))
      (fun c => ∃ m' s H', wrRet r (sp0 - 64) s f m' o c ∧
        TolPost sp0 n (PrSt L nci func tbc sl g n ls D G FL M0 ph0 H0) (argBytes v) ph m m' s H H')

/-- **`luaL_tolstring` on a string argument** (lane F1-15; proved, lane
F1-17: `tolStr_proved`, `Kit/TolStrProof.lean`):
`luaL_callmeta(L, idx, "__tostring")` → `lua_getmetatable` (the string
library's metatable) → `luaL_getmetafield` → `lua_pushstring("__tostring")`
(`PushLit_Statement`: the literal and the cache's candidates in `LitsIn`) →
`lua_rawget` → `luaH_get`'s walk misses (`StrMtMiss`) → `lua_settop(L, -3)`;
`lua_type`; `lua_pushvalue(L, idx)`; the tail `lua_tolstring(L, -1, &l)` of
the argument's short or long string. -/
def TolStr_Statement : Prop := TolArg IsStr

/-! ## `luaE_extendCI` -/

/-- **What `luaE_extendCI(L)` leaves** (`ci->next` NULL): a fresh `CallInfo`
block `nci` of the arena in use, linked after `ci` (`ci->next = nci`,
`nci->previous = ci`), the heap `H'` with at most `extRoom` more break, the
chunks in use kept, every byte kept off the allocator's writes (`MallocW`),
the block, `ci->next`, `L->nci` and its callees' stack, and `stdout`'s state
with the new heap (the allocator's globals lie among the stdio globals, so this
is the premise's, not a frame lemma's). -/
structure ExtPost (M m' : Mem) (sp L ci g : Nat) (H H' : HeapIx) (nci : Nat) : Prop where
  heap : HeapAt (fillZeroMem m') H'.top H'.brk H'.chunks H'.bins
  brk : H'.brk ≤ H.brk + extRoom
  kept : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks
  nci_in : ∀ a, nci ≤ a → a < nci + ciSize → InUse H'.chunks a
  fresh : ∀ a, nci ≤ a → a < nci + ciSize → ¬ InUse H.chunks a ∧ heapStart ≤ a ∧ a < heapEnd
  next : bytesT8 m' (ci + ciNextOff) = BitVec.ofNat 64 nci
  prev : bytesT8 m' (nci + ciPreviousOff) = BitVec.ofNat 64 ci
  al : nci % 8 = 0
  /-- (lane F1-14) also off `g->GCdebt`, which `luaM_malloc_` advances -/
  keep : ∀ a, ¬ (MallocW H.chunks a ∨ (nci ≤ a ∧ a < nci + ciSize) ∨ Rng (ci + ciNextOff) 8 a ∨
    Rng (L + stateNciOff) 2 a ∨ Below (sp - 96) 4096 a ∨ Rng (g + gGCdebtOff) 8 a) → bytesT1 m' a = bytesT1 M a
  /-- (lane F1-14) given `stdout`'s buffer apart from the objects written -/
  stdio : ∀ ph, PrintSt M ph H →
    (∀ a, ph.Buf a → ¬ (Rng L stateSize a ∨ Rng ci ciSize a ∨ Rng (g + gGCdebtOff) 8 a)) →
    ((∀ buf pend, ph ≠ .up buf pend) → H'.brk + 1024 + 16384 ≤ heapEnd) → PrintSt m' ph H'

/-- **Where `luaE_extendCI`'s objects lie** (lane F1-14): the `lua_State`,
the `CallInfo` and `g` in the arena, aligned, `L` apart from `g->GCdebt`
(`luaM_malloc_` writes it before `L->ci`, `L->nci` are read), and what is read
or written after the allocation in chunks in use. -/
structure ExtCx (L ci g : Nat) (H : HeapIx) : Prop where
  L_lo : heapStart ≤ L
  L_hi : L + stateSize ≤ heapEnd
  L_al : L % 8 = 0
  ci_lo : heapStart ≤ ci
  ci_hi : ci + ciSize ≤ heapEnd
  ci_al : ci % 8 = 0
  g_lo : heapStart ≤ g
  g_hi : g + 64 ≤ heapEnd
  g_al : g % 8 = 0
  L_g : L + stateSize ≤ g + gGCdebtOff ∨ g + gGCdebtOff + 8 ≤ L
  /-- `L` apart from the `CallInfo` (`ci->next` is written before `L->nci`) -/
  L_ci : L + stateSize ≤ ci ∨ ci + ciSize ≤ L
  live : ∀ a, Rng L stateSize a ∨ Rng ci ciSize a ∨ Rng (g + gGCdebtOff) 8 a → InUse H.chunks a

/-- **Named premise: `luaE_extendCI(L)`** (`0x80016a5c`, from `next_ci` with
`ci->next` NULL): from the heap with room for one `_malloc_r`, `L->ci = ci`,
its `next` NULL, no hook, `G(L) = g` with `g->frealloc` main.c's `l_alloc`
(`luaM_malloc_` calls it through a `jalr`), `_impure_ptr` (`realloc`'s
`_REENT`), and the `lua_State`, the `CallInfo` and `g->GCdebt` (read or
written after the allocation) in chunks in use: `PcExt` with
`ExtPost`. Proved from `MallocR_Statement` (`extendCI_of_malloc`,
`Kit/ExtendCI.lean`: `luaM_malloc_` → `l_alloc` → `realloc` →
`_realloc_r(NULL)` → `_malloc_r`). Lane F1-14: the earlier
form did not constrain `g->frealloc` and claimed `g->GCdebt` kept, so it
was false. -/
def ExtendCI_Statement : Prop :=
  ∀ (sp L ci g : Nat) (f : AbiFrame) (M : Mem) (o : Array String) (H : HeapIx),
    HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins → H.brk + extRoom ≤ heapEnd →
    bytesT8 M (L + stateCiOff) = BitVec.ofNat 64 ci → bytesT8 M (ci + ciNextOff) = 0#64 →
    bytesT4 M (L + stateHookmaskOff) = 0#32 →
    bytesT8 M (L + stateGOff) = BitVec.ofNat 64 g → bytesT8 M g = BitVec.ofNat 64 symLAlloc →
    bytesT8 M symImpurePtr = BitVec.ofNat 64 symImpureData → ExtCx L ci g H →
    heapEnd + 8192 ≤ sp - 96 → sp ≤ 2 ^ 32 → sp % 16 = 0 →
    PcExt sp L f M o (fun nci m' => ∃ H', ExtPost M m' sp L ci g H H' nci)

/-! ## `luaD_poscall` with results -/

/-- **What `luaD_poscall(L, ci, 0)` leaves** with `ci->nresults = w`: the
`w` results nil (`setnilvalue`, the tag byte) from `res = ci->func`,
`L->top = res + w`, `L->ci = ci->previous`, every byte kept off its frame,
`L->top`, `L->ci` and the result tags. -/
structure PoscallPost (m m' : Mem) (L ci sp w : Nat) : Prop where
  lci : bytesT8 m' (L + stateCiOff) = bytesT8 m (ci + ciPreviousOff)
  nil : ∀ j, j < w → bytesT1 m' ((bytesT8 m (ci + ciFuncOff)).toNat + 16 * j + tvalueTagOff) =
    BitVec.ofNat 8 vNil
  keep : ∀ a, ¬ (Rng (sp - 64) 64 a ∨ Rng (L + stateTopOff) 8 a ∨ Rng (L + stateCiOff) 8 a ∨
      ∃ j, j < w ∧ a = (bytesT8 m (ci + ciFuncOff)).toNat + 16 * j + tvalueTagOff) →
    bytesT1 m' a = bytesT1 m a

/-- What `luaD_poscall(L, ci, 0)` reads (`Ret.PcCx` with `ci->nresults = w`). -/
structure PcCxW (L ci sp : Nat) (r : BitVec 64) (m : Mem) (w : Nat) : Prop where
  ra : r.toNat % 4 = 0
  sp_lo : tohostAddr + 16 + 64 ≤ sp
  sp_hi : sp ≤ 2 ^ 32
  sp_al : sp % 8 = 0
  L_lo : tohostAddr + 16 ≤ L
  L_hi : L + stateSize + 64 ≤ sp
  ci_lo : tohostAddr + 16 ≤ ci
  ci_hi : ci + ciSize + 64 ≤ sp
  ci_al : ci % 8 = 0
  L_al : L % 8 = 0
  hook : bytesT4 m (L + stateHookmaskOff) = 0#32
  nres : bytesT2 m (ci + ciNresultsOff) = BitVec.ofNat 16 w
  /-- (lane F1-14) the `w` result slots from `res = ci->func`: in RAM, below
  `luaD_poscall`'s frame, apart from the `CallInfo` and `L->top`/`L->ci` -/
  res_lo : tohostAddr + 16 ≤ (bytesT8 m (ci + ciFuncOff)).toNat
  res_hi : (bytesT8 m (ci + ciFuncOff)).toNat + 16 * w + 64 ≤ sp
  res_ci : (bytesT8 m (ci + ciFuncOff)).toNat + 16 * w ≤ ci ∨ ci + ciSize ≤ (bytesT8 m (ci + ciFuncOff)).toNat
  res_L : (bytesT8 m (ci + ciFuncOff)).toNat + 16 * w ≤ L ∨ L + stateSize ≤ (bytesT8 m (ci + ciFuncOff)).toNat

/-- **`luaD_poscall(L, ci, 0)` with `wanted ≥ 1`** (`C ≥ 2`, `moveresults`'
fill with nils after a C function that returned no result, `n = 0`): the
summary in `poscall_sum`'s shape, post `PoscallPost`. Proved (lane F1-14):
`poscallN`, `Kit/PoscallN.lean`. With `n ≠ 0` the results would be copied,
so the statement is stated at `luaB_print`'s `0`. -/
def PoscallN_Statement : Prop :=
  ∀ {L ci sp w : Nat} {r : BitVec 64} {m : Mem}, PcCxW L ci sp r m w → 1 ≤ w → w < 2 ^ 15 →
    ∀ (f : Ret.RFrame) (o : Array String),
    Triple (SegSt 0x8000a39c#64 (⟨Register.x10, BitVec.ofNat 64 L⟩ ::
        ⟨Register.x11, BitVec.ofNat 64 ci⟩ :: ⟨Register.x12, 0x0#64⟩ ::
        ⟨Register.x1, r⟩ :: ⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay m o))
      (fun c => ∃ m', SegSt r (⟨Register.x2, BitVec.ofNat 64 sp⟩ :: f.pins) (ArmPay m' o) c ∧
        PoscallPost m m' L ci sp w)

/-! ## The stack growth and the exit -/

/-- **Named premise: `luaD_precall`'s stack growth** (`L->stack_last - L->top
≤ LUA_MINSTACK`: `luaD_growstack`, a stop of the generator at `0x8000abe4`):
`PrintCall` on those states. -/
def PrintGrow_Statement (I : Proto → RelPtrs → Prop) : Prop :=
  PrintCallOn I fun _ w ins => ¬ (w.slot ins.a + 16 * ins.b + 320 < w.rt.stackLast)

/-- **`exit(0)` once `stdout` is set up** (after a `print`:
`__stdio_exit_handler` = `stdio_exit_handler` runs `_fwalk_sglue(_fclose_r)`
over the standard streams: `__sflush_r` with nothing pending, htif.c's
`_close`, `_free_r` of the buffer), from the `CALL` invariant at the phase
`.up buf []` (`stdout`, the other streams as `__sinit`'s `std()` left them,
`atexit`, where the Lua objects lie) and the heap: `ExitOk`. Proved from
`FreeR_Statement` (`exitUp_of_free`, `Kit/ExitUp.lean`). Lane F1-14: the
earlier form, over `StdoutIn` alone, left `stdin`, `stderr`, `__sglue` and the
handler unconstrained (`exit` jumps through their hooks), so the invariant
carries them now (`StdioRest`, `StdoutTail`, `FdsStd`). -/
def ExitUp_Statement : Prop :=
  ∀ (p : Proto) (w : RelPtrs) (buf : Nat) (F FL : Nat → Prop) (ls : LitPtrs),
    CallInvAt p w (.up buf []) F FL ls →
    HeapAt w.mo w.rt.top w.rt.brkv w.rt.chunks (fun i => w.rt.bins.getD i []) → ExitOk p w

/-- **`OP_CALL print`'s open parts** on the `CALL` invariant (lane F1-13). -/
structure CallOpen : Prop where
  /-- (lane F1-15) `luaB_print` when an argument allocates -/
  printAlloc : PrintAlloc_Statement

/-- **`luaD_precall` never grows the stack for `print`** (lane F1-14): the
`CALL` invariant keeps `LUA_MINSTACK` slots above the frame (`growFree`, from
the entry contract's `call_room`), and the call's arguments lie inside the
frame (`call_bounds`), so the growth path's states do not occur. -/
theorem printGrow_none : PrintGrow_Statement CallInv := by
  intro p c s w ins args f o hS hR hI hf hop hb hcc hregs hbud hq
  obtain ⟨ph, F, FL, ls, hI⟩ := hI
  have hB := call_bounds hS hf hop hb hcc
  have h1 := hI.growFree
  have h2 := hB.ab
  exact absurd (by simp only [RelPtrs.slot, RelPtrs.base, stackValueSize] at h1 ⊢; omega) hq

/-- `CALL`'s growth path, discharged (lane F1-14). -/
theorem CallOpen.grow (_O : CallOpen) : PrintGrow_Statement CallInv := printGrow_none

end Lua.Vm.Sim.Kit

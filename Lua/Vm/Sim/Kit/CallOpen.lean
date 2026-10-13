import Lua.Vm.Sim.Kit.CallArm
import Lua.Vm.Sim.Kit.PrintS
import Lua.Vm.Sim.Kit.RetPoscall

/-!
# `OP_CALL print`'s open parts, in the relation's terms (lane F1-13)

`PrintCall_Statement CallInv` (the premise of `sim_CALL_of` on the `CALL`
invariant) is proved in `Kit/CallPrint.lean` (`printCall_of`) from
`luaD_precall`'s C path (`precall_reuse`, `precall_ext`), `luaD_poscall` with
`C = 1` (`poscall_sum`) and the relation's region facts, over the named
premises collected here (`CallOpen`):

* `PrintRel_Statement`: `luaB_print` on the C frame `luaD_precall` builds,
  stated over the regions it keeps (`PrintIn`/`PrintOut`): the line on the
  console, `stdout` set up and flushed, the bytes `G` the caller needs kept,
  the interned literals again. It is `print_sum` (lane F1-11) with
  `luaL_tolstring` per value class (`PushLit_Statement` for nil/booleans, the
  string, integer (`IntegerToStr_Statement`), float (`G14From`) and function
  classes) and the heap room of `MallocR_Statement`;
* `ExtendCI_Statement`: `luaE_extendCI` (`ci->next` NULL at the first `print`);
* `PoscallN_Statement`: `luaD_poscall` with `C ≥ 2` (`wanted ≥ 1` nils);
* `PrintGrow_Statement`: `luaD_precall`'s stack growth (`L->stack_last - L->top
  ≤ LUA_MINSTACK`);
* `FreeR_Statement`: `_free_r` (A0, as `MallocR_Statement`), which `exit`'s
  `_fclose_r(stdout)` calls on `stdout`'s buffer; `exit(0)` once `stdout` is
  set up (`ExitUp_Statement`, the post-print `ExitOk`) is proved from it
  (`exitUp_of_free`, `Kit/ExitUp.lean`, lane F1-14).
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

/-- **`luaB_print`'s entry** from `luaD_precall`'s C path: the API frame of `n`
arguments above `func` (`L->ci` the C `CallInfo` `nci`), `stdout` with
nothing pending and the heap, the arguments represented (`ι` the intern map),
the stack room `precallC` checked, `G(L)` with no metatables for nil, booleans
and numbers, the interned literals (apart from `D`), and the bytes `G` the
caller needs kept: in chunks in use or static, apart from `L->top`, the
stack above the arguments, `g`'s first words and string cache, and the
literals' mark bytes. -/
structure PrintIn (L nci func n tbc sl g : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs)
    (D G : Nat → Prop) (ph : StdoutPh) (H : HeapIx) (M : Mem) : Prop where
  api : ApiAt M L nci func n tbc
  st : PrintSt M ph H
  pend : ph.pend = []
  len : args.length = n
  args : ∀ i v, args[i]? = some v →
    ValRepr (fillZeroMem M) ι (slotTag M (func + 16 * (i + 1))) (slotVal M (func + 16 * (i + 1))) v
  room : func + 16 * n + 16 + 320 < sl
  g_w : bytesT8 M (L + stateGOff) = BitVec.ofNat 64 g
  mt : ∀ t ∈ [luaTnil, luaTboolean, luaTnumber], bytesT8 M (g + gMtOff + 8 * t) = 0#64
  hook : bytesT4 M (L + stateHookmaskOff) = 0#32
  lits : ∃ FL, LitsFoot g sl ls H ph D FL M
  keep_in : ∀ a, G a → Kept H ph a ∨ PrintStatic a
  keep_apart : ∀ a, G a → ¬ Rng (L + stateTopOff) 8 a ∧ ¬ (func + 16 * n + 16 ≤ a ∧ a < sl) ∧
    ¬ Rng (g + 16) 48 a ∧ ¬ (g + gStrcacheOff ≤ a ∧ a < g + gEnd) ∧ ∀ ts ∈ ls.strs, a ≠ ts + gcMarkedOff

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

/-- **Named premise: `luaB_print` on the C frame** (`0x80022f18`, called by
`precallC`'s `jalr a7` with `ra = 0x8000ac8c` and `sp - 96`), from `PrintIn`
and, when an argument allocates, the heap room of `CALL print` less the
`CallInfo`'s (`callBudget`, `extRoom`): `PrintOut`. Its parts: `print_sum`
(proved from `MallocR_Statement` and `PrintLua`), `luaL_tolstring` per value
class (nil and booleans proved over `PushLit_Statement`; strings, integers
over `IntegerToStr_Statement`, floats over `G14From`, functions open), the
Lua state `S` carrying `G` and the literals across each call. -/
def PrintRel_Statement : Prop :=
  ∀ (sp L nci func n tbc sl g ss : Nat) (ls : LitPtrs) (args : List Value) (ι : Strs) (D G : Nat → Prop)
    (ph : StdoutPh) (H : HeapIx) (f : AbiFrame) (M : Mem) (o : Array String),
    PrintIn L nci func n tbc sl g ls args ι D G ph H M → PrNums (sp - 96) L nci func n 0x8000ac8c#64 →
    (AnyAlloc args → H.brk + callBudget args ss ≤ heapEnd + extRoom) →
    Triple (SegSt 0x80022f18#64 (callPre [⟨Register.x10, BitVec.ofNat 64 L⟩] (sp - 96) 0x8000ac8c#64 (pcFr L f))
        (ArmPay M o))
      (fun c => ∃ m' out, wrRet 0x8000ac8c#64 (sp - 96) 0 (pcFr L f) m' (pushes o out) c ∧
        PrintOut (sp - 96) g sl ls args D G ph H M m' out)

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
  stdio : ∀ ph, PrintSt M ph H → ((∀ buf pend, ph ≠ .up buf pend) → H'.brk + 1024 + 16384 ≤ heapEnd) →
    PrintSt m' ph H'

/-- **Named premise: `luaE_extendCI(L)`** (`0x80016a5c`, from `next_ci` with
`ci->next` NULL): from the heap with room for one `_malloc_r`, `L->ci = ci`,
its `next` NULL, no hook, `G(L) = g` with `g->frealloc` main.c's `l_alloc`
(`luaM_malloc_` calls it through a `jalr`), `_impure_ptr` (`realloc`'s
`_REENT`), and the `lua_State`, the `CallInfo` and `g->GCdebt` (read or
written after the allocation) in chunks in use: `PcExt` with
`ExtPost`. Open: its at-lemmas and `luaM_malloc_` → `l_alloc` → `realloc` →
`_realloc_r(NULL)` → `_malloc_r` (`MallocR_Statement`). Lane F1-14: the earlier
form did not constrain `g->frealloc` and claimed `g->GCdebt` kept, so it
was false. -/
def ExtendCI_Statement : Prop :=
  ∀ (sp L ci g : Nat) (f : AbiFrame) (M : Mem) (o : Array String) (H : HeapIx),
    HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins → H.brk + extRoom ≤ heapEnd →
    bytesT8 M (L + stateCiOff) = BitVec.ofNat 64 ci → bytesT8 M (ci + ciNextOff) = 0#64 →
    bytesT4 M (L + stateHookmaskOff) = 0#32 →
    bytesT8 M (L + stateGOff) = BitVec.ofNat 64 g → bytesT8 M g = BitVec.ofNat 64 symLAlloc →
    bytesT8 M symImpurePtr = BitVec.ofNat 64 symImpureData →
    (∀ a, Rng L stateSize a ∨ Rng ci ciSize a ∨ Rng (g + gGCdebtOff) 8 a → InUse H.chunks a) →
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
  print : PrintRel_Statement
  extendCI : ExtendCI_Statement
  freeR : FreeR_Statement

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

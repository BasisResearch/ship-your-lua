import Lua.Vm.Runtime
import Lua.Vm.Host
import Lua.Vm.RegsOk
import Lua.Vm.Sim.Mem
import Lua.Vm.Sim.Env
import Lua.Vm.Sim.StdioState
import Lua.Vm.Sim.Step
import Vsa.Sim.SegState

/-!
# `VmRel`: the machine at `luaV_execute`'s fetch head represents a `BcSem` state (A1)

`VmRel p c s` relates a machine configuration `c` to a bytecode state `s` of
the main chunk `p` when `c` sits at the fetch head of `luaV_execute`
(`Lua.Vm.Arms.headPc`, the `bnez s5` before `lw s4,0(s11)`) about to execute
instruction `s.pc`. It is `∃ w, VmRelAt p c s w` over the pointers `w`
(`RelPtrs`), and every part is a named field:

* **Registers** (`Pins`). `luaV_execute` keeps its state in callee-saved
  registers at the head: s0 = `L`, s7 = `ci`, s8 = the jump table, s1 = 81
  (the last opcode in the table), s2 = 3 (`LUA_VNUMINT`), s5 = `trap` (0: no
  hooks), s9 = `base`, s11 = the cached `pc` (`code + 4·s.pc`; the
  `ci->u.l.savedpc` in memory is only written back by `savepc` before calls,
  so the relation pins the register, not the memory word), plus `sp` and `gp`.
* **Registers of the chunk** (`Core.stack`). Every register `j <
  maxstacksize` that holds a value (`s.regs j = some v`) is represented by
  the stack slot `base + 16·j` (`ValRepr` of its tag byte and payload). The
  kernel semantics already marks the registers the definite-initialisation
  analysis cannot see as ⊥ (`none`: stale, kill ports), so this is the
  `FrameRepr` of the defined registers: at a reachable state it covers
  `defMask p s.pc` (`Lua/FragmentSound.lean`), and it holds of the entry
  state (all ⊥) for any stack contents. `ValRepr` is tight enough for
  `luaV_equalobj`: nil is exactly `LUA_VNIL`, a string's tag follows its
  length, and a short string's pointer is the intern map's `w.ι.ptr s`.
* **Output** (`Core.out`): the HTIF console so far is `s.out`.
* **Registers present, mailbox idle** (`Core.ok`, `RegsOk`): every GPR holds a
  value and no `tohost` word is half-written (ship-your-interpreter's `VsaOk`
  register half), established by `MachineAt.regs` and threaded by every
  segment (`gen_segment.py`'s `"ok"` option).
* **Frame** (`Core.frame`, `Complement`). Outside the window `Win` (the
  register slots, `luaV_execute`'s own C frame, and the `Scratch` words that
  arms write with no head invariant: `ci->u.l.savedpc`, `L->top`, the callee
  frames below `sp`) the memory reads TOTALLY
  (`bytesT1`, the model's `getD 0`) as a fixed complement `w.mo`: presence is
  never demanded, since the densification (`Vsa.Densify`) already gives it.
  The one presence the relation carries is `.text` (`Core.text`), which the
  segments' instruction fetches demand (`SegSt`'s `TextLoaded`). Of `w.mo`,
  `Complement` states the image (`.text`, `.rodata`), the prototype (`ProtoRepr`, and its code words as `lw` reads
  them), `ci->func` and `ci->u.l.trap`, and the Lua state and heap of
  `luaLayout` (`LuaStateAt`, `DlHeap.HeapAt`, `ErrorJmpAt`).

**Relocation.** Registers are decoded relative to `ci->func` as the complement
holds it (`w.func`, `base = func + 16`), not to a fixed address. `OP_VARARGPREP`
moves `ci->func` inside the main activation (`luaT_adjustvarargs`), and
`CALL print` can reallocate the Lua stack (`luaD_precall` → `checkstackGCp`,
`correctstack` rewrites `ci->func`); after either, `luaV_execute` reloads
`base` from `ci->func` (`updatebase`) and the relation holds again with a new
`func` and the moved slots. The pilot arms (`MOVE`, `LOADI`, `JMP`) keep `w`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (MState Config)

/-- **The relation's strings.** `ptr` is the intern map: the one `TString`
of each short content (`internshrstr`), which a short-string register points
to. `own` is the set of string objects a register or constant may point to;
`Complement.own` places each in an in-use allocator chunk apart from the
window (`StrOwned`). At the entry it is the string constants
(`Lua.Vm.KStrAt`); an arm that creates a string (`CONCAT`, `CALL`) must add
it. -/
structure Strs where
  ptr : List UInt8 → Nat
  own : Nat → List UInt8 → Prop

/-- **A register's value from its slot's tag byte `t` and payload `x`.**
The `TValueRepr` of `Lua/Vm/Repr.lean` in the form the arms read it (`lbu`
of the tag, `ld` of the payload); a string's bytes live in the complement
memory `mo`. Tight enough that `luaV_equalobj` (which compares `ttypetag`,
`tt & 63`, then the payload) decides `δ .eq`:

* nil is exactly `LUA_VNIL` (0): every instruction that makes a register nil
  writes `setnilvalue` (`sb zero`; `luaV_finishget` for an absent key), so
  the empty and absent-key variants never reach a register;
* a string's tag is `strTag s` (the variant follows the length, as
  `luaS_newlstr` chooses it), so equal contents have equal tags;
* a short string's pointer is the intern map's `ι.ptr s` (`internshrstr`: one
  `TString` per short content), so pointer equality (`eqshrstr`) is content
  equality; distinct contents have distinct pointers because `TStringRepr` is
  functional (`TStringRepr.inj`);
* a float's payload is the double: the value is its model and its sign bit
  (`Value.flt`), so a NaN payload is free but its sign is not;
* a string's object is one the relation owns (`Strs.own`): `Complement.own`
  puts it in an in-use allocator chunk apart from the window (`StrOwned`).
  Copying a register copies its `ValRepr`, so ownership travels with the
  value and no arm restates it. -/
inductive ValRepr (mo : Mem) (ι : Strs) : BitVec 8 → BitVec 64 → Value → Prop where
  | nil {x} : ValRepr mo ι (BitVec.ofNat 8 vNil) x .nil
  | false_ {x} : ValRepr mo ι (BitVec.ofNat 8 vFalse) x (.bool false)
  | true_ {x} : ValRepr mo ι (BitVec.ofNat 8 vTrue) x (.bool true)
  | int {i} : ValRepr mo ι (BitVec.ofNat 8 vNumInt) i (.int i)
  /-- a float (`LUA_VNUMFLT`): the payload is the double; the value is its
  model (`Float.Model.ofBits`, which canonicalises NaN payloads) and its sign
  bit -/
  | flt {x} : ValRepr mo ι (BitVec.ofNat 8 vNumFlt) x
      (.flt (Float.Model.ofBits (UInt64.ofBitVec x)) x.msb)
  | str {x s} : TStringRepr mo x.toNat s → (s.length ≤ maxShortLen → x.toNat = ι.ptr s) →
      ι.own x.toNat s → ValRepr mo ι (BitVec.ofNat 8 (strTag s)) x (.str s)
  | print {x} : x = BitVec.ofNat 64 symLuaBPrint →
      ValRepr mo ι (BitVec.ofNat 8 vLcf) x (.builtin .print)

/-- `luaV_execute`'s own C frame (`addi sp,sp,-176` in its prologue). -/
def execFrame : Nat := 176

/-- The pointers of the relation. -/
structure RelPtrs where
  /-- `lua_State *L` (s0) -/
  L : Nat
  /-- `CallInfo *ci` (s7) -/
  ci : Nat
  /-- `ci->func` as the complement holds it; `base = func + 16` -/
  func : Nat
  /-- the `Proto`, its `code` array and its constant array `k` -/
  pa : Nat
  code : Nat
  k : Nat
  /-- `sp` inside `luaV_execute` -/
  sp : Nat
  /-- the memory outside the window -/
  mo : Mem
  /-- the strings (`Strs`): the intern map, which a short-string register
  points to, and the owned string objects (`ValRepr.str`) -/
  ι : Strs
  /-- the runtime's pointers and heap shape (`RuntimeMem`): the allocator
  chunks that own the strings (`StrOwned`) -/
  rt : RtPtrs

namespace RelPtrs

/-- `base = ci->func + 1` (s9). -/
def base (w : RelPtrs) : Nat := w.func + stackValueSize

/-- The stack slot of register `j`. -/
def slot (w : RelPtrs) (j : Nat) : Nat := w.base + stackValueSize * j

end RelPtrs

/-- The register slots `[base, base + 16·maxstacksize)`. -/
def Slots (p : Proto) (w : RelPtrs) (a : Nat) : Prop :=
  w.base ≤ a ∧ a < w.base + stackValueSize * p.maxstacksize

/-- **Scratch**: the memory an arm may write outside the register slots and
the C frame, with no invariant at the fetch head:

* `ci->u.l.savedpc`, which `savepc`/`savestate` (`Protect`, `OP_MOD`,
  `OP_IDIV`, `OP_EQ`, …: `sd s3,32(s7)`) write back; the head keeps the pc in
  s11 (`Pins.pc`);
* `L->top`, which `savestate` sets to `ci->top` (`ld a4,8(s7); sd a4,16(s0)`)
  and `CALL print` leaves at `ra` (`moveresults`); no non-IT instruction reads
  it at its head (`lvm.c` `vmfetch`'s assert), and the one IT head of F1,
  `OP_VARARGPREP` at pc 0, reads the entry value (`RuntimeReadyAt.top`);
* the callee frames below `sp` (`luaV_equalobj`'s `sd ra,40(sp)`, `luaV_mod` →
  `__moddi3`, …): `[spEntry - cStackBudget, sp)`, which `cstack_room` puts
  above the heap `[_end, __heap_end)`, so apart from every object the relation
  reads.

The complement `mo` stays the entry memory; the machine's bytes here are
free. -/
def Scratch (w : RelPtrs) (a : Nat) : Prop :=
  (w.ci + ciSavedpcOff ≤ a ∧ a < w.ci + ciSavedpcOff + 8) ∨
  (w.L + stateTopOff ≤ a ∧ a < w.L + stateTopOff + 8) ∨
  (RuntimeData.spEntry - cStackBudget ≤ a ∧ a < w.sp)

/-- **The window**: the register slots, `luaV_execute`'s C frame
`[sp, sp + 176)` and the scratch words (`Scratch`). Outside it the memory is
the complement's (`Core.frame`). -/
def Win (p : Proto) (w : RelPtrs) (a : Nat) : Prop :=
  Slots p w a ∨ (w.sp ≤ a ∧ a < w.sp + execFrame) ∨ Scratch w a

/-- **A heap range the relation reads through its complement** (lane F1-7):
`[lo, lo + n)` lies above `tohost`, below the callee frames, and outside the
window, so the machine's bytes there are the complement's (`Core.frame`).
`_ENV`'s objects (`Complement.env`, `EnvMem`). -/
structure HeapRead (p : Proto) (w : RelPtrs) (lo n : Nat) : Prop where
  above : tohostAddr + 16 ≤ lo
  below : lo + n ≤ RuntimeData.spEntry - cStackBudget
  out : ∀ a, lo ≤ a → a < lo + n → ¬ Win p w a

/-- **The chunk `c` owns the string object at `ts`** holding `s`: `c` is an
in-use chunk of the allocator's walk (`HeapAt`'s `chunks`, `w.rt`), its user
range `[addr + 16, addr + size + 8)` (an in-use chunk also owns the next
chunk's `prev_size` word) holds the whole object (the header from `ts`, the
contents at `+24` and the terminator), and no byte of that range is in the
window. Keyed to the chunk, not to the window: a freed string's bytes are
the allocator's (dlmalloc's `fd`/`bk` overwrite its tag and length), and an
in-use chunk is apart from every other chunk however the window moves. -/
structure ChunkOwns (p : Proto) (w : RelPtrs) (c : DlHeap.Chunk) (ts : Nat) (s : List UInt8) :
    Prop where
  walk : c ∈ w.rt.chunks
  inuse : c.inuse = true
  lo : c.addr + 16 ≤ ts
  hi : ts + tstringContentsOff + s.length + 1 ≤ c.addr + c.size + 8
  out : ∀ a, c.addr + 16 ≤ a → a < c.addr + c.size + 8 → ¬ Win p w a

/-- **An owned string object**: some chunk owns it (`ChunkOwns`). -/
def StrOwned (p : Proto) (w : RelPtrs) (ts : Nat) (s : List UInt8) : Prop :=
  ∃ c, ChunkOwns p w c ts s

/-- An owned string object lies outside the window, header to terminator. -/
theorem StrOwned.out {p : Proto} {w : RelPtrs} {ts : Nat} {s : List UInt8}
    (h : StrOwned p w ts s) : ∀ a, ts ≤ a → a < ts + tstringContentsOff + s.length + 1 →
      ¬ Win p w a := by
  obtain ⟨c, hc⟩ := h
  intro a h1 h2
  exact hc.out a (by have := hc.lo; omega) (by have := hc.hi; omega)

/-- **The `CallInfo` after the Lua one** (`ci->next`, lane F1-12): the C
`CallInfo` a `CALL` of a C function uses (`next_ci`: reused, or allocated by
`luaE_extendCI` at the first one), in the arena below the C stack, 8-aligned,
its `previous` the Lua `CallInfo` (`luaD_poscall` restores `L->ci` from it). -/
structure CiNext (m : Mem) (ci nci : Nat) : Prop where
  lo : symEnd ≤ nci
  hi : nci + ciSize ≤ RuntimeData.spEntry - cStackBudget
  al : nci % 8 = 0
  previous : rd64 m (nci + ciPreviousOff) = some ci

/-- **The Lua state the relation keeps** (lane F1-12): `LuaStateAt` but its
parts a `CALL` changes. `ci->next` is NULL before the first `CALL` of a C
function (`luaE_extendCI` links a new `CallInfo` there, never freed while the
collector is stopped) and a `CiNext` block after it; `g->strt` and
`g->strcache` change with the strings a `print` interns, so they are not the
relation's (the `CALL` arm's own facts). -/
structure LuaStateRel (m : Mem) (L ci : Nat) (w : RtPtrs) : Prop where
  hookmask : rd32 m (L + stateHookmaskOff) = some 0
  trap : rd32 m (ci + ciTrapOff) = some 0
  errfunc : rd64 m (L + stateErrfuncOff) = some 0
  nCcalls : rd32 m (L + stateNCcallsOff) = some RuntimeData.nCcallsEntry
  openupval : rd64 m (L + stateOpenupvalOff) = some 0
  tbclist : rd64 m (L + stateTbclistOff) = some w.stack
  stack : rd64 m (L + stateStackOff) = some w.stack
  stack_last : rd64 m (L + stateStackLastOff) = some w.stackLast
  func : rd64 m (ci + ciFuncOff) = some w.func
  stack_le : w.stack ≤ w.func
  ci_top : rd64 m (ci + ciTopOff) = some w.ciTop
  ci_top_le : w.ciTop ≤ w.stackLast
  callstatus : rd16 m (ci + ciCallstatusOff) = some cistFresh
  nresults : rd16 m (ci + ciNresultsOff) = some 0
  previous : rd64 m (ci + ciPreviousOff) = some (L + stateBaseCiOff)
  next : rd64 m (ci + ciNextOff) = some 0 ∨ ∃ nci, rd64 m (ci + ciNextOff) = some nci ∧ CiNext m ci nci
  g : rd64 m (L + stateGOff) = some w.g
  mt_nil : rd64 m (w.g + gMtOff + 8 * luaTnil) = some 0
  mt_boolean : rd64 m (w.g + gMtOff + 8 * luaTboolean) = some 0
  mt_number : rd64 m (w.g + gMtOff + 8 * luaTnumber) = some 0
  /-- `L->ci` is the Lua `CallInfo` (`VmEntryData.ci_eq`): `luaD_precall`'s
  C path reads it (`next_ci`), `luaD_poscall` restores it -/
  lci : rd64 m (L + stateCiOff) = some ci

/-- The relation's Lua state from the boot contract's (`ci->next` NULL) and
`L->ci = ci`. -/
theorem _root_.Lua.Vm.LuaStateAt.rel {m : Mem} {L ci : Nat} {w : RtPtrs} (h : LuaStateAt m L ci w)
    (hci : rd64 m (L + stateCiOff) = some ci) : LuaStateRel m L ci w :=
  ⟨h.hookmask, h.trap, h.errfunc, h.nCcalls, h.openupval, h.tbclist, h.stack, h.stack_last, h.func,
    h.stack_le, h.ci_top, h.ci_top_le, h.callstatus, h.nresults, h.previous, .inl h.next, h.g, h.mt_nil,
    h.mt_boolean, h.mt_number, hci⟩

/-- The parts of `luaRuntimeReady` that live in memory and that the F1 arms
keep: the Lua state (with `ci->func = func`; `LuaStateRel`, the parts a
`CALL` keeps), the heap and the error handler. (`StdioBoot`/`MemfsBoot`
describe the state before the first `print` and belong to the `CALL` arm.) -/
structure RuntimeMem (m : Mem) (L ci func : Nat) (rt : RtPtrs) : Prop where
  func : rt.func = func
  lua : LuaStateRel m L ci rt
  heap : DlHeap.HeapAt m rt.top rt.brkv rt.chunks (fun i => rt.bins.getD i [])
  error_jmp : ErrorJmpAt m L

/-- The caller frames lie in `[spEntry, __stack_top)`. -/
theorem callerFrames_above : ∀ s ∈ RuntimeData.callerFrames,
    RuntimeData.spEntry ≤ s.1 ∧ s.1 + s.2.length ≤ 0x88000000 := by
  decide +kernel

/-- Byte segments survive a memory change that keeps their bytes. -/
theorem _root_.Lua.Vm.SegsAt.congr {m m' : Mem} {segs : List (Nat × List UInt8)}
    (h : SegsAt m segs) (hm : ∀ s ∈ segs, ∀ i, i < s.2.length → m'[s.1 + i]? = m[s.1 + i]?) :
    SegsAt m' segs := fun s hs i hi => (hm s hs i hi).trans (h s hs i hi)

/-- **The caller frames survive** a memory change that keeps `[spEntry, __stack_top)`. -/
theorem callers_congr {m m' : Mem} (h : SegsAt m RuntimeData.callerFrames)
    (hm : ∀ a, RuntimeData.spEntry ≤ a → a < 0x88000000 → m'[a]? = m[a]?) :
    SegsAt m' RuntimeData.callerFrames :=
  h.congr fun s hs i hi => have := callerFrames_above s hs; hm _ (by omega) (by omega)

/-- The caller frames' copies of `L` lie in `[spEntry, __stack_top)`. -/
theorem callerLSlots_above : ∀ a ∈ RuntimeData.callerLSlots,
    RuntimeData.spEntry ≤ a ∧ a + 8 ≤ 0x88000000 := by
  decide

/-- **The registers at `exit`'s entry** (`_start`'s `j exit` after `main`
returns 0): `a0 = 0`, `sp = __stack_top`, `ra` after `_start`'s `jal main`,
`gp`, and some callee-saved values. -/
abbrev exitRow (q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64) : List Pin :=
  [⟨Register.x10, 0#64⟩, ⟨Register.x1, 0x80000038#64⟩, ⟨Register.x2, 0x88000000#64⟩,
   ⟨Register.x3, BitVec.ofNat 64 symGlobalPointer⟩, ⟨Register.x8, q8⟩, ⟨Register.x9, q9⟩,
   ⟨Register.x18, q18⟩, ⟨Register.x19, q19⟩, ⟨Register.x20, q20⟩, ⟨Register.x21, q21⟩,
   ⟨Register.x22, q22⟩, ⟨Register.x23, q23⟩, ⟨Register.x24, q24⟩, ⟨Register.x25, q25⟩,
   ⟨Register.x26, q26⟩, ⟨Register.x27, q27⟩]

/-- **What `exit` may find changed from the complement**: the C stack, the
`lua_State` and the `CallInfo` (the return chain's stores, `Scratch`), and the
register slots. -/
def ExitFree (p : Proto) (w : RelPtrs) (a : Nat) : Prop :=
  (RuntimeData.spEntry - cStackBudget ≤ a ∧ a < 0x88000000) ∨ (w.L ≤ a ∧ a < w.L + stateSize) ∨
    (w.ci ≤ a ∧ a < w.ci + ciSize) ∨ Slots p w a

/-- **`exit(0)` from the complement halts with code 0 and prints nothing**:
from `exit`'s entry (`exitRow`) with any memory that reads (totally) as
`w.mo` off `ExitFree`, the machine halts with the console it has. This is the
end of every `RETURN*` (`FinalSim`): the return chain reaches `exit(0)` with
such a memory. At the entry it holds by `exit_run` (`__atexit = NULL`, no
`__stdio_exit_handler`); an arm that changes `w.mo` (`CALL print`: after a
`print`, newlib's `stdio_exit_handler` closes the standard streams) must show
it of its complement. -/
def ExitOk (p : Proto) (w : RelPtrs) : Prop :=
  ∀ (M : Mem) (o : Array String) (c : Config) (q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27 : BitVec 64),
    (∀ a, ¬ ExitFree p w a → bytesT1 M a = bytesT1 w.mo a) →
    SegSt (BitVec.ofNat 64 symCExit) (exitRow q8 q9 q18 q19 q20 q21 q22 q23 q24 q25 q26 q27)
      (fun σ => Arms.TextLoaded σ.mem ∧ σ.mem = M ∧ σ.sailOutput = o ∧ RegsOk σ) c →
    Vsa.Machine.Halts c (Vsa.Machine.output c.σ) 0

/-! ## The `CALL` invariant (lane F1-13)

What `OP_CALL print` needs of the complement beyond the arms' facts, kept by
every other arm because it is a fact of `w` alone (no arm but `CALL` changes
`w.mo`): `stdout`'s phase with the heap (the room for the first `print`'s
allocations at boot), the objects a `print` leaves alone frozen on a footprint
in chunks in use apart from what it writes (`CallDirty`), the reserved
literals interned, and where the `lua_State`, `g`, the `CallInfo`s and the Lua
stack lie. -/

/-- The heap indices of the runtime witness (`HeapAt`'s). -/
def _root_.Lua.Vm.RtPtrs.hix (rt : RtPtrs) : Kit.HeapIx :=
  ⟨rt.top, rt.brkv, rt.chunks, fun i => rt.bins.getD i []⟩

/-- **What a `CALL print` writes inside the heap's chunks in use**: `L->top`,
`L->ci`, the Lua `CallInfo`, the Lua stack above `ci->func`, `g`'s first words
(the GC debt, the string table's header) and its string cache (`EntryDirty` at
the relation's pointers). -/
def CallDirty (w : RelPtrs) (a : Nat) : Prop :=
  (w.L + stateTopOff ≤ a ∧ a < w.L + stateTopOff + 8) ∨ (w.L + stateCiOff ≤ a ∧ a < w.L + stateCiOff + 8) ∨
  (w.ci ≤ a ∧ a < w.ci + ciSize) ∨ (w.func ≤ a ∧ a < w.rt.stackLast) ∨ (w.rt.g + 16 ≤ a ∧ a < w.rt.g + 64) ∨
  (w.rt.g + gStrcacheOff ≤ a ∧ a < w.rt.g + gEnd) ∨ (w.L + stateNciOff ≤ a ∧ a < w.L + stateNciOff + 2)

/-- **What the literals' facts stay apart from**: `L->top`, `L->ci`, the Lua
`CallInfo` and the Lua stack above `ci->func` (`LitDirty`). -/
def CallLitDirty (w : RelPtrs) (a : Nat) : Prop :=
  (w.L + stateTopOff ≤ a ∧ a < w.L + stateTopOff + 8) ∨ (w.L + stateCiOff ≤ a ∧ a < w.L + stateCiOff + 8) ∨
  (w.ci ≤ a ∧ a < w.ci + ciSize) ∨ (w.func ≤ a ∧ a < w.rt.stackLast) ∨
  (w.L + stateNciOff ≤ a ∧ a < w.L + stateNciOff + 2) ∨
  (w.rt.g + gGCdebtOff ≤ a ∧ a < w.rt.g + gGCdebtOff + 8) ∨
  (w.rt.g + gTotalbytesOff ≤ a ∧ a < w.rt.g + gTotalbytesOff + 8) ∨
  (w.rt.g + gStrcacheOff ≤ a ∧ a < w.rt.g + gEnd)

/-- (lane F1-15) **The string cache's candidates survive** a change off the
cache's words. -/
theorem _root_.Lua.Vm.LitCache.congr {m m' : Mem} {g : Nat} {ls : LitPtrs} (h : LitCache m g ls)
    (hk : ∀ a, g + gStrcacheOff ≤ a → a < g + gEnd → bytesT1 m' a = bytesT1 m a) : LitCache m' g ls := by
  intro i hi
  have hgi : g + gStrcacheOff + 8 * i + 8 ≤ g + gEnd := by
    simp only [gEnd, gStrcacheOff, strcacheN, strcacheM] at hi ⊢; omega
  rw [bytesT8_congrT (m := m') (m' := m) fun j hj => hk _ (by omega) (by omega)]
  exact h i hi

/-- **The words of the `lua_State` and `g` a `print` keeps** (`LuaStateRel`'s
`L` and `g` words, and `L->errorJmp`). -/
structure LuaStatic (M : Mem) (L : Nat) (rt : RtPtrs) : Prop where
  hookmask : rd32 M (L + stateHookmaskOff) = some 0
  errfunc : rd64 M (L + stateErrfuncOff) = some 0
  nCcalls : rd32 M (L + stateNCcallsOff) = some RuntimeData.nCcallsEntry
  openupval : rd64 M (L + stateOpenupvalOff) = some 0
  tbclist : rd64 M (L + stateTbclistOff) = some rt.stack
  stack : rd64 M (L + stateStackOff) = some rt.stack
  stack_last : rd64 M (L + stateStackLastOff) = some rt.stackLast
  g : rd64 M (L + stateGOff) = some rt.g
  mt_nil : rd64 M (rt.g + gMtOff + 8 * luaTnil) = some 0
  mt_boolean : rd64 M (rt.g + gMtOff + 8 * luaTboolean) = some 0
  mt_number : rd64 M (rt.g + gMtOff + 8 * luaTnumber) = some 0
  errjmp : rd64 M (L + stateErrorJmpOff) = some RuntimeData.ljAddr
  /-- (lane F1-14) `g->frealloc`, `luaM_malloc_`'s allocator -/
  frealloc : rd64 M rt.g = some symLAlloc
  /-- (lane F1-15) the collector stopped (`luaC_step`'s `gcrunning` test:
  `luaE_setdebt(g, -2000)` only) -/
  gcstp : rd8 M (rt.g + gGcstpOff) = some gcstpUsr

/-- **The objects a `CALL print` leaves alone**, in a memory `M`: `.rodata`,
the prototype and its code pointer, the owned strings, `_ENV`'s chain to
`print`, the `lua_State`'s and `g`'s static words. -/
structure StatFacts (p : Proto) (w : RelPtrs) (M : Mem) : Prop where
  rodata : RodataLoaded M
  proto : ProtoRepr M w.pa p
  proto_code : rd64 M (w.pa + protoCodeOff) = some w.code
  strs : ∀ ts s, w.ι.own ts s → TStringRepr M ts s
  env : ∀ ts, w.ι.own ts printKey → EnvMem M w.rt.cl ts (HeapRead p w)
  lua : LuaStatic M w.L w.rt

/-- **The objects a `CALL print` writes are apart** at the relation's
pointers: `g` up to its string cache, the literals' objects, the `lua_State`,
the `CallInfo` and the Lua stack above `ci->func`. -/
structure CallObjs (w : RelPtrs) (ls : LitPtrs) : Prop where
  g_L : Apart w.rt.g gEnd w.L stateSize
  g_ci : Apart w.rt.g gEnd w.ci ciSize
  g_stack : Apart w.rt.g gEnd w.func (w.rt.stackLast - w.func)
  ci_stack : Apart w.ci ciSize w.func (w.rt.stackLast - w.func)
  lit_L : ∀ ts ∈ ls.strs, Apart ts 30 w.L stateSize
  lit_g : ∀ ts ∈ ls.strs, Apart ts 30 w.rt.g gEnd
  lit_ci : ∀ ts ∈ ls.strs, Apart ts 30 w.ci ciSize
  lit_stack : ∀ ts ∈ ls.strs, Apart ts 30 w.func (w.rt.stackLast - w.func)
  /-- (lane F1-15) the `lua_State` apart from the Lua stack -/
  L_stack : Apart w.L stateSize w.func (w.rt.stackLast - w.func)

/-- **The C `CallInfo` `nci` after the Lua one**: in a chunk in use, apart
from both footprints and from the objects a `CALL` writes. -/
structure NciApart (w : RelPtrs) (ph : Kit.StdoutPh) (F FL : Nat → Prop) (ls : LitPtrs) (nci : Nat) : Prop where
  kept : ∀ a, nci ≤ a → a < nci + ciSize → Kit.Kept w.rt.hix ph a
  foot : ∀ a, nci ≤ a → a < nci + ciSize → ¬ F a ∧ ¬ FL a
  L : Apart nci ciSize w.L stateSize
  g : Apart nci ciSize w.rt.g gEnd
  ci : Apart nci ciSize w.ci ciSize
  stack : Apart nci ciSize w.func (w.rt.stackLast - w.func)
  lits : ∀ ts ∈ ls.strs, Apart nci ciSize ts 30

/-- **The `CALL` invariant** at `stdout`'s phase `ph`, the footprints `F` (the
objects a `print` leaves alone) and `FL` (the interned literals), and the
literals `ls`. -/
structure CallInvAt (p : Proto) (w : RelPtrs) (ph : Kit.StdoutPh) (F FL : Nat → Prop) (ls : LitPtrs) :
    Prop where
  /-- every RAM byte of the complement is present -/
  dense : ∀ a, 0x80000000 ≤ a → a < 0x88000000 → (w.mo[a]?).isSome
  /-- `stdout` in phase `ph` with the heap, nothing pending -/
  io : Kit.StdoutIn w.mo w.rt.hix ph
  pend : ph.pend = []
  cells : Kit.PrintCells w.mo
  /-- before the first `print`, room for its allocations -/
  room : ((∀ buf pend, ph ≠ .up buf pend) ∨ rd64 w.mo (w.ci + ciNextOff) = some 0) →
    w.rt.brkv + firstRoom ≤ DlHeap.heapEnd
  /-- no `atexit` handler -/
  atexit : Vsa.Sim.bytesT8 w.mo symAtexit = 0#64
  /-- the objects a `print` leaves alone, frozen on `F` -/
  stat : Kit.Frozen F (fun M => StatFacts p w (Vsa.Densify.fillZeroMem M)) w.mo
  stat_in : ∀ a, F a → Kit.Kept w.rt.hix ph a ∨ (0x80000000 ≤ a ∧ a < symTohost)
  stat_apart : ∀ a, F a → ¬ CallDirty w a
  /-- the register frame lies below `L->stack_last` -/
  fits : w.func + stackValueSize * (1 + p.maxstacksize) ≤ w.rt.stackLast
  /-- (lane F1-14) room for `LUA_MINSTACK` slots above the frame: `OP_CALL
  print` does not grow the stack -/
  growFree : w.func + stackValueSize * (1 + p.maxstacksize) + 320 < w.rt.stackLast
  /-- (lane F1-14) `g` 8-aligned (`luaE_extendCI`'s `g->GCdebt` store) -/
  g_al : w.rt.g % 8 = 0
  /-- the constant array is frozen (its slots in `F`) -/
  kslots : ∀ j, j < tvalueSize * p.k.length → F (w.k + j)
  /-- the reserved literals interned, frozen on `FL` -/
  lits : Kit.Frozen FL (fun M => LitsHold M w.rt.g w.rt.stackLast ls) w.mo
  lits_in : ∀ a, FL a → Kit.Kept w.rt.hix ph a
  lits_apart : ∀ a, FL a → ¬ CallLitDirty w a
  lit_strs : ∀ ts ∈ ls.strs, ∀ a, ts ≤ a → a < ts + 30 → Kit.Kept w.rt.hix ph a
  marks : ∀ ts ∈ ls.strs, ¬ F (ts + gcMarkedOff)
  /-- (lane F1-15) nor in `FL` -/
  lit_marks : ∀ ts ∈ ls.strs, ¬ FL (ts + gcMarkedOff)
  /-- (lane F1-15) the string cache holds candidates -/
  cache : LitCache w.mo w.rt.g ls
  /-- the `lua_State`, `g` up to its string cache, the `CallInfo` and the Lua
  stack above `ci->func` in chunks in use -/
  L_in : ∀ a, w.L ≤ a → a < w.L + stateSize → Kit.Kept w.rt.hix ph a
  g_in : ∀ a, w.rt.g ≤ a → a < w.rt.g + gEnd → Kit.Kept w.rt.hix ph a
  ci_in : ∀ a, w.ci ≤ a → a < w.ci + ciSize → Kit.Kept w.rt.hix ph a
  stack_in : ∀ a, w.func ≤ a → a < w.rt.stackLast → Kit.Kept w.rt.hix ph a
  /-- the C `CallInfo` after the Lua one, once there is one: in a chunk in
  use, apart from both footprints -/
  nci : ∀ nci, rd64 w.mo (w.ci + ciNextOff) = some nci → nci ≠ 0 → NciApart w ph F FL ls nci
  /-- the objects a `CALL` writes are apart (`ObjsApart` at the relation's pointers) -/
  objs : CallObjs w ls

-- discipline: allow(R7-conj-tower-def) one existential over the invariant's
-- witnesses; its body is the named-field structure `CallInvAt`
/-- **The `CALL` invariant** (`CallInvAt` for some phase, footprints and
literals). -/
def CallInv (p : Proto) (w : RelPtrs) : Prop := ∃ ph F FL ls, CallInvAt p w ph F FL ls

/-- **The complement**: what the relation knows about `w.mo`. -/
structure Complement (p : Proto) (w : RelPtrs) : Prop where
  text : Arms.TextLoaded w.mo
  rodata : RodataLoaded w.mo
  /-- `VmEntryData.proto`/`proto_code`: the prototype is loaded -/
  proto : ProtoRepr w.mo w.pa p
  proto_code : rd64 w.mo (w.pa + protoCodeOff) = some w.code
  /-- `proto`'s code words, as `lw` reads them (the total-read form) -/
  code_word : ∀ i ins, p.fetch i = some ins → bytesT4 w.mo (w.code + 4 * i) = ins
  /-- `ci->func`, as `updatebase` reads it -/
  func_word : bytesT8 w.mo (w.ci + ciFuncOff) = BitVec.ofNat 64 w.func
  /-- `ci->u.l.trap = 0` (no hooks), as `updatetrap` reads it -/
  trap_word : bytesT4 w.mo (w.ci + ciTrapOff) = 0
  runtime : RuntimeMem w.mo w.L w.ci w.func w.rt
  /-- the constants (`kval`), as the `K` arms read `k[i]` -/
  kconst : ∀ i v, kval p i = some v →
    ValRepr w.mo w.ι (slotTag w.mo (w.k + stackValueSize * i)) (slotVal w.mo (w.k + stackValueSize * i)) v
  /-- every string object a register or constant may point to is owned -/
  own : ∀ ts s, w.ι.own ts s → StrOwned p w ts s
  /-- the caller frames above the entry `sp`, as the boot left them
  (`CStackAt.callers`): the return chain after `luaV_execute` returns
  (`ccall`, `luaD_rawrunprotected`, `luaD_pcall`, `lua_pcallk`, `main`) reloads
  its saved registers and locals, and `lj.status`, from them -/
  callers : SegsAt w.mo RuntimeData.callerFrames
  /-- the caller frames' copies of `L` (`RuntimeReadyAt.callerL`): the return
  chain's stores to `L->nCcalls`, `L->errorJmp`, `L->errfunc` go through them -/
  callerL : ∀ a ∈ RuntimeData.callerLSlots, bytesT8 w.mo a = BitVec.ofNat 64 w.L
  /-- `exit(0)` from this complement halts with code 0 (`ExitOk`) -/
  exit : ExitOk p w
  /-- **`_ENV.print`** (lane F1-7): for the string object of every owned
  `"print"`, `OP_GETTABUP`'s reads through the closure `w.rt.cl` (`8(sp)`,
  `Core.clptr`) and `luaH_getshortstr`'s walk find `print` (`EnvMem`), the
  objects outside the window (`HeapRead`) -/
  env : ∀ ts, w.ι.own ts printKey → EnvMem w.mo w.rt.cl ts (HeapRead p w)
  /-- **(lane F1-13) the `CALL` invariant** (`CallInv`): established at the
  entry and after `OP_VARARGPREP` from the boot contract, kept by every arm
  that keeps `w`, and by `CALL print` (`PrintCall_Statement`) -/
  call : CallInv p w

/-- **Where things are**: the address ranges the arms' side conditions need,
and the window's separation from the code array and the `CallInfo`. -/
structure Ranges (p : Proto) (w : RelPtrs) : Prop where
  sp_eq : w.sp + execFrame = RuntimeData.spEntry
  base_lo : tohostAddr + 16 ≤ w.base
  base_hi : w.base + stackValueSize * p.maxstacksize ≤ 0x100000000
  base_al : w.base % 8 = 0
  code_lo : tohostAddr + 16 ≤ w.code
  code_hi : w.code + 4 * p.code.length ≤ 0x100000000
  ci_lo : tohostAddr + 16 ≤ w.ci
  ci_hi : w.ci + ciSize ≤ 0x100000000
  L_lo : tohostAddr + 16 ≤ w.L
  code_out : ∀ a, w.code ≤ a → a < w.code + 4 * p.code.length → ¬ Win p w a
  /-- the `CallInfo` but its `savedpc` word (which is `Scratch`) -/
  ci_out : ∀ a, w.ci ≤ a → a < w.ci + ciSize →
    (a < w.ci + ciSavedpcOff ∨ w.ci + ciSavedpcOff + 8 ≤ a) → ¬ Win p w a
  k_lo : tohostAddr + 16 ≤ w.k
  k_hi : w.k + stackValueSize * p.k.length ≤ 0x100000000
  k_al : w.k % 8 = 0
  k_out : ∀ a, w.k ≤ a → a < w.k + stackValueSize * p.k.length → ¬ Win p w a
  /-- the register slots lie below the C frame -/
  frame_sep : w.base + stackValueSize * p.maxstacksize ≤ w.sp
  /-- the constant array lies apart from the register slots -/
  k_sep : w.k + stackValueSize * p.k.length ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ w.k
  /-- the `CallInfo` and the `lua_State` (whose `savedpc`, `top` words are
  `Scratch`) lie apart from the register slots, and below the C stack -/
  ci_sep : w.ci + ciSize ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ w.ci
  L_sep : w.L + stateSize ≤ w.base ∨ w.base + stackValueSize * p.maxstacksize ≤ w.L
  ci_top : w.ci + ciSize ≤ RuntimeData.spEntry - cStackBudget
  L_top : w.L + stateSize ≤ RuntimeData.spEntry - cStackBudget
  slots_top : w.base + stackValueSize * p.maxstacksize ≤ RuntimeData.spEntry - cStackBudget
  L_al : w.L % 8 = 0
  ci_al : w.ci % 8 = 0
  L_sep_ci : w.L + stateSize ≤ w.ci ∨ w.ci + ciSize ≤ w.L
  /-- the constant array lies below the C stack (`VmRegionsAt.k_hi` and
  `cstack_room`): `luaV_equalobj`'s frame below `sp` misses `K[B]` (`OP_EQK`) -/
  k_top : w.k + stackValueSize * p.k.length ≤ RuntimeData.spEntry - cStackBudget

/-- **The fetch-head registers** for pointers `w` and bytecode pc `pc`. -/
structure Pins (σ : MState) (w : RelPtrs) (pc : Nat) : Prop where
  sp : σ.regs.get? Register.x2 = some (BitVec.ofNat 64 w.sp)
  gp : σ.regs.get? Register.x3 = some (BitVec.ofNat 64 symGlobalPointer)
  L : σ.regs.get? Register.x8 = some (BitVec.ofNat 64 w.L)
  opMax : σ.regs.get? Register.x9 = some (BitVec.ofNat 64 (Arms.jtEntries - 1))
  intTag : σ.regs.get? Register.x18 = some (BitVec.ofNat 64 vNumInt)
  trap : σ.regs.get? Register.x21 = some (0#64)
  ci : σ.regs.get? Register.x23 = some (BitVec.ofNat 64 w.ci)
  jt : σ.regs.get? Register.x24 = some (BitVec.ofNat 64 Arms.jtBase)
  base : σ.regs.get? Register.x25 = some (BitVec.ofNat 64 w.base)
  pc : σ.regs.get? Register.x27 = some (BitVec.ofNat 64 (w.code + 4 * pc))

/-- The slot of a saved `s`-register in `luaV_execute`'s frame: `sd s1,152(sp)`,
`sd s2,144(sp)` … `sd s11,72(sp)`. -/
def savedOff (r : Nat) : Nat := if r = 9 then 152 else 144 - 8 * (r - 18)

/-- **`luaV_execute`'s saved words** at `72…175(sp)`: the prologue's `sd ra,168(sp)`
(the return into `ccall`), `sd s0,160(sp)` (`L`) and `sd s1,152(sp)` …
`sd s11,72(sp)` (the callers' values, `RuntimeData.calleeSavedEntry`). Only the
prologue writes these words; the epilogue of `OP_RETURN*` (`CIST_FRESH`)
reloads them for the return chain (`ccall`, `luaD_rawrunprotected`,
`luaD_pcall`, `lua_pcallk`, `main`). -/
structure SavedAt (m : Mem) (w : RelPtrs) : Prop where
  ra : bytesT8 m (w.sp + 168) = BitVec.ofNat 64 RuntimeData.retCcall
  s0 : bytesT8 m (w.sp + 160) = BitVec.ofNat 64 w.L
  s : ∀ rv ∈ RuntimeData.calleeSavedEntry, bytesT8 m (w.sp + savedOff rv.1) = BitVec.ofNat 64 rv.2

/-- The saved `s`-register slots lie in `[72, 152]`. -/
theorem savedOff_mem : ∀ rv ∈ RuntimeData.calleeSavedEntry,
    72 ≤ savedOff rv.1 ∧ savedOff rv.1 + 8 ≤ 160 := by
  decide

/-- **The saved words are a region fact**: a memory equal on `[sp + 72, sp + 176)`
keeps them. -/
theorem SavedAt.congr {m m' : Mem} {w : RelPtrs} (h : SavedAt m w)
    (hm : ∀ x, w.sp + 72 ≤ x → x < w.sp + execFrame → m'[x]? = m[x]?) : SavedAt m' w where
  ra := (bytesT8_congr fun i hi => hm _ (by omega) (by simp only [execFrame]; omega)).trans h.ra
  s0 := (bytesT8_congr fun i hi => hm _ (by omega) (by simp only [execFrame]; omega)).trans h.s0
  s rv hrv := by
    have := savedOff_mem rv hrv
    exact (bytesT8_congr fun i hi => hm _ (by omega) (by simp only [execFrame]; omega)).trans
      (h.s rv hrv)

/-- Everything but the machine pc: shared by the head (`VmRelAt`) and the arm
entry after dispatch (`ArmAt`). -/
structure Core (p : Proto) (c : Config) (s : State) (w : RelPtrs) : Prop where
  good : GoodState c.σ
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  pins : Pins c.σ w s.pc
  out : Vsa.Machine.output c.σ = s.out
  /-- every GPR present, the HTIF mailbox idle -/
  ok : RegsOk c.σ
  /-- `.text` is present: the segments' fetches (`SegSt`'s `TextLoaded`) demand it -/
  text : Arms.TextLoaded c.σ.mem
  /-- outside the window, every TOTAL read (`bytesT1`, the model's `getD 0`) is the
  complement's: presence is not demanded, the densification gives it -/
  frame : ∀ a, ¬ Win p w a → bytesT1 c.σ.mem a = bytesT1 w.mo a
  /-- `0(sp)` holds `k` (the prologue's `sd`; the `K` arms' `ld a4,0(sp)`) -/
  kptr : bytesT8 c.σ.mem w.sp = BitVec.ofNat 64 w.k
  /-- `8(sp)` holds the closure (the prologue's `sd a5,8(sp)`; `OP_GETTABUP`'s
  and `OP_VARARGPREP`'s `ld a4,8(sp)`): no F1 arm writes `[8(sp), 16(sp))`
  (`CFrame` starts at `16(sp)`), so every close keeps it (lane F1-7) -/
  clptr : bytesT8 c.σ.mem (w.sp + 8) = BitVec.ofNat 64 w.rt.cl
  stack : ∀ j v, j < p.maxstacksize → s.regs j = some v →
    ValRepr w.mo w.ι (slotTag c.σ.mem (w.slot j)) (slotVal c.σ.mem (w.slot j)) v
  comp : Complement p w
  ranges : Ranges p w
  /-- `luaV_execute`'s saved `ra`, `s0 … s11` (`SavedAt`): no arm writes
  `72…175(sp)`, so every close keeps them (`Core.saved_of`) -/
  saved : SavedAt c.σ.mem w

/-- **The payload of an arm's segments** (`gen_lua_arms.py`, `sim` segments):
`.text` present, the memory `m`, the console `o`, `RegsOk`. -/
abbrev ArmPay (m : Mem) (o : Array String) : MState → Prop :=
  fun σ => Arms.TextLoaded σ.mem ∧ σ.mem = m ∧ σ.sailOutput = o ∧ RegsOk σ

section
variable {pcv : BitVec 64} {L : List Pin} {m : Mem} {o : Array String} {c : Config}

/-- The payload's fields (its one destructuring point). -/
theorem _root_.Vsa.Sim.SegSt.armText (h : SegSt pcv L (ArmPay m o) c) : Arms.TextLoaded c.σ.mem := h.extra.1
theorem _root_.Vsa.Sim.SegSt.armMem (h : SegSt pcv L (ArmPay m o) c) : c.σ.mem = m := h.extra.2.1
theorem _root_.Vsa.Sim.SegSt.armOut (h : SegSt pcv L (ArmPay m o) c) : c.σ.sailOutput = o := h.extra.2.2.1
theorem _root_.Vsa.Sim.SegSt.armOk (h : SegSt pcv L (ArmPay m o) c) : RegsOk c.σ := h.extra.2.2.2

end

/-- **The relation at the fetch head**, for pointers `w`. -/
structure VmRelAt (p : Proto) (c : Config) (s : State) (w : RelPtrs) : Prop where
  core : Core p c s w
  pcAt : c.σ.regs.get? Register.PC = some Arms.headPc

/-- **`VmRel p c s`**: `c` is at `luaV_execute`'s fetch head about to run
instruction `s.pc` of `p`, representing `s`. -/
def VmRel (p : Proto) (c : Config) (s : State) : Prop := ∃ w, VmRelAt p c s w

/-- **Open (A1): the entry lemma.** From `luaV_execute`'s entry, the prologue
runs to the fetch head in the relation with the initial state. -/
def vmRel_entry_Statement : Prop :=
  ∀ p c, Supported p → VmLoaded luaLayout p c →
    ∃ c', Vsa.Machine.Steps c c' ∧ VmRel p c' State.init

/-- **Open (A1): the `Final` side of the fold (`term_sim`).** At the fetch
head in the relation with a final state (the pc at `RETURN`, `RETURN0` or
`RETURN1`), the machine halts with exit code 0 and console `s.out`. The run is
`OP_RETURN*` → `luaD_poscall` → `luaV_execute`'s return (`CIST_FRESH`) →
`ccall` → `lua_pcallk` → the harness's `main` → `exit(0)` through HTIF: it
never comes back to the fetch head, so it is not a `sim_<OP>`; it is the
`Final` clause of the `VmSim` fold, with the return chain's callee contracts. -/
def vmRel_final_Statement : Prop :=
  ∀ p c s, Supported p → VmRel p c s → Final p s → Vsa.Machine.Halts c s.out 0

/-- **The statement of an arm's simulation lemma** (`sim_ADD`'s shape): from
the fetch head in the relation, at an instruction of opcode `o`, every
bytecode step is matched by a non-empty machine run back to the fetch head,
in the relation with the successor. -/
def SimArm (o : OpCode) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State}, VmRel p c s →
    ∀ {ins : Word}, p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      ∃ c' n, 0 < n ∧ Vsa.Machine.StepsN n c c' ∧ VmRel p c' s'

/-- **An arm's simulation on the states where `Q` holds** (`Q` over the
program, the bytecode state and the instruction): one family of an arm's
paths. The arms proved before floats were in `δ` hold off their float paths,
which are the premises `FloatArms` (`Lua/Vm/Sim/Fold.lean`). -/
def SimArmOn (o : OpCode) (Q : Proto → State → Word → Prop) : Prop :=
  ∀ {p : Proto}, Supported p → ∀ {c : Config} {s s' : State}, VmRel p c s →
    ∀ {ins : Word}, p.fetch s.pc = some ins → ins.op? = some o → Step binaryHost p s s' →
      Q p s ins → ∃ c' n, 0 < n ∧ Vsa.Machine.StepsN n c c' ∧ VmRel p c' s'

/-- The states off a path family `Q`. -/
abbrev Off (Q : Proto → State → Word → Prop) : Proto → State → Word → Prop :=
  fun p s ins => ¬ Q p s ins

/-- **An arm from its two path families**: off `Q`, and on `Q`. -/
theorem SimArm.split {o : OpCode} {Q : Proto → State → Word → Prop}
    (h₁ : SimArmOn o fun p s ins => ¬ Q p s ins) (h₂ : SimArmOn o Q) : SimArm o :=
  fun {p} hS {_ s _} hR {ins} hf hop hstep =>
    (Classical.em (Q p s ins)).elim (h₂ hS hR hf hop hstep) (h₁ hS hR hf hop hstep)

/-- **Open (A1, round-3 bake-off target): `OP_MOD`.** The arm at `0x8001dc58`
is `savestate` then `op_arith(luaV_mod)`:

* `ld a4,8(s7); sd s3,32(s7); sd a4,16(s0)` write `ci->u.l.savedpc` and
  `L->top := ci->top`: both words are `Scratch`, so `Core.frame` does not
  constrain them;
* the tag tests `lbu a3,8(a5)` / `beq a3,s2` (and `lbu a4,8(s10)` at
  `0x8001e428`) take the integer path exactly when both operands are integers
  (`ValRepr.int_of_tag`), which is `δ`'s only defined case in F1 (no floats:
  `ValRepr.ne_float` discharges the `li 19` tests, and a non-number jumps to
  `0x8001c1e4`, the metamethod path, where `δ` is `none` for F1's values, so
  there is no `Step`);
* the integer path at `0x8001f7e0` is `luaV_mod` inlined: `n + 1 ≤ 1`
  (`bgeu`) splits off `n = 0` (`0x8001fde0` → `luaG_opinterror`, the error
  that `imod`'s `none` leaves without a `Step`) and `n = -1` (result 0,
  `0x8001fd34`); otherwise `jal __moddi3` (0x8002f7b0) and the floor
  correction (`xor`, `bltz` → `0x8001fb74`). `__moddi3` (which
  returns through `t0` with `__udivdi3`'s remainder) leaves the callee-saved
  registers the `Pins` hold (s0, s1, s2, s5, s7 … s11) unchanged and writes
  memory at most below `sp`, which is `Scratch` (`[spEntry - cStackBudget,
  sp)`, above the heap by `cstack_room`);
* `sd a5,0(s6); sb 3,8(s6)` store `R[A]` in the window (`Core.write`), and
  `addi s11,s11,8` skips the following `OP_MMBIN`, which is `kernel`'s `next`.

So the post-state differs from the pre-state only in `R[A]` and in `Scratch`,
and `VmRel` (whose `Core.frame` exempts `Scratch`) holds of it. -/
def sim_MOD_Statement : Prop := SimArm .MOD

/-- **Open (A1): `OP_MODK`**, `OP_MOD` with `K[C]` (`Core.kconst`). -/
def sim_MODK_Statement : Prop := SimArm .MODK

/-- **Open (A1): `OP_IDIV`**, as `OP_MOD` with `luaV_idiv` (`__divdi3`). -/
def sim_IDIV_Statement : Prop := SimArm .IDIV

/-- **Open (A1): `OP_IDIVK`**, `OP_IDIV` with `K[C]`. -/
def sim_IDIVK_Statement : Prop := SimArm .IDIVK

/-- **Open (A1, round-3 bake-off target): `OP_EQ`.** The arm at `0x8001c690`
is `Protect(cond = luaV_equalobj(L, s2v(ra), rb))` then `docondjump`:

* `ld a5,8(s7); sd s3,32(s7); sd a5,16(s0)` (`savestate`) write the two
  `Scratch` words;
* `jal luaV_equalobj` (`0x8001b780`) writes only its own frame below `sp`
  (`sd ra,40(sp)`, …), which is `Scratch`, and restores the callee-saved
  registers of `Pins`;
* `luaV_equalobj` returns `δ .eq` on represented values: it compares
  `ttypetag` (`tt & 63`), and `ValRepr` makes the tag a function of the value
  (nil exactly `LUA_VNIL`, a string's tag `strTag s`), so different kinds or
  different string variants are unequal on both sides; then per variant:
  integers by payload, booleans by tag, `print` by its one pointer, long
  strings by length and `memcmp` (`luaS_eqlngstr`, over the `TStringRepr`
  bytes), and short strings by pointer (`eqshrstr`), which is content
  equality because short-string registers hold `ι.ptr s` (`ValRepr.str`) and a
  pointer holds one content (`TStringRepr.inj`). It never reaches
  `luaT_callTMres` on F1 values (`__eq` is only tried for tables and full
  userdata);
* `lw t6,40(s7)` (`updatetrap`) reads `ci->u.l.trap`, outside `Scratch`
  (`Ranges.ci_out`); the `bne a5,a0` against the `k` bit either skips the
  following `OP_JMP` (`addi s11,s11,8`) or takes it (`0x8001e9cc`,
  `donextjump` from `s3`), `docondjump`'s two exits.

The only memory changes are `Scratch`, so the post-state is in `VmRel` with
the same pointers and register file. -/
def sim_EQ_Statement : Prop := SimArm .EQ

/-- **Open (A1): `OP_EQK`**, `luaV_rawequalobj(R[A], K[B])` (no `savestate`:
only `luaV_equalobj`'s frame below `sp` is written); `K[B]`'s short strings
share `ι` with the registers (`Complement.kconst`, from `KInterned`). -/
def sim_EQK_Statement : Prop := SimArm .EQK

/-- **After dispatch**: at the arm of `ins`'s opcode, with s3 = `pc + 1` and
s4 = the instruction (sign-extended by `lw`). -/
structure ArmAt (p : Proto) (c : Config) (s : State) (w : RelPtrs) (ins : Word) : Prop where
  core : Core p c s w
  pcAt : c.σ.regs.get? Register.PC = some (armTarget ins.opNum)
  s3 : c.σ.regs.get? Register.x19 = some (BitVec.ofNat 64 (w.code + 4 * (s.pc + 1)))
  s4 : c.σ.regs.get? Register.x20 = some (sign_extend (m := 64) ins)

/-! ## Reading the machine through the relation -/

section
variable {p : Proto} {c : Config} {s : State} {w : RelPtrs}

/-- The scratch words miss the register slots and lie below the C frame. -/
theorem Ranges.scratch_out (hr : Ranges p w) (a : Nat) (h : Scratch w a) :
    ¬ Slots p w a ∧ a < w.sp := by
  have := hr.ci_sep; have := hr.L_sep; have := hr.ci_top; have := hr.L_top; have := hr.sp_eq
  have := hr.slots_top
  simp only [Scratch, Slots, RelPtrs.base, ciSavedpcOff, stateTopOff, ciSize, stateSize,
    stackValueSize, execFrame, cStackBudget, RuntimeData.spEntry] at *
  omega

theorem Win.above (hr : Ranges p w) {a : Nat} (h : Win p w a) : tohostAddr + 16 ≤ a := by
  have := hr.sp_eq
  have := hr.base_lo
  have := hr.ci_lo
  have := hr.L_lo
  simp only [Win, Slots, Scratch, execFrame, RuntimeData.spEntry, cStackBudget, tohostAddr] at *
  omega

theorem Win.of_slots {a : Nat} (h : ¬ Win p w a) : ¬ Slots p w a := fun hs => h (.inl hs)

/-- The machine's `.rodata`, read totally, is the image's. -/
theorem Core.rodata (hc : Core p c s w) : RodataRead c.σ.mem := fun o ho => by
  have := rodata_below_tohost
  refine (hc.frame _ fun hw => ?_).trans ?_
  · have := Win.above hc.ranges hw; omega
  · simp only [bytesT1, hc.comp.rodata o ho, Option.getD_some]

/-- The instruction at `pc`, as `lw s4,0(s11)` reads it. -/
theorem Core.fetch (hc : Core p c s w) {pc : Nat} {ins : Word} (hf : p.fetch pc = some ins) :
    bytesT4 c.σ.mem (w.code + 4 * pc) = ins := by
  have hlt := fetch_lt hf
  refine (bytesT4_congrT fun i hi => ?_).trans (hc.comp.code_word pc ins hf)
  exact hc.frame _ (hc.ranges.code_out _ (by omega) (by omega))

/-- The instruction at `pc`, read from any memory exact outside the register slots. -/
theorem Core.fetch_of (hc : Core p c s w) {m : Mem} (h : ∀ y, ¬ Slots p w y → m[y]? = c.σ.mem[y]?)
    {pc : Nat} {ins : Word} (hf : p.fetch pc = some ins) : bytesT4 m (w.code + 4 * pc) = ins := by
  have hlt := fetch_lt hf
  refine (bytesT4_congr fun i hi => ?_).trans (hc.fetch hf)
  exact h _ (Win.of_slots (hc.ranges.code_out _ (by omega) (by omega)))

/-- A byte store into the register slots is exact outside them. -/
theorem insert_frame {m : Mem} {x : Nat} {b : BitVec 8} (hx : Slots p w x) :
    ∀ y, ¬ Slots p w y → (m.insert x b)[y]? = m[y]? := fun y hy => by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp only [beq_iff_eq]; rintro rfl; exact hy hx)]

/-- `ci->u.l.trap`, as `updatetrap` reads it. -/
theorem Core.trap (hc : Core p c s w) : bytesT4 c.σ.mem (w.ci + ciTrapOff) = 0 := by
  refine (bytesT4_congrT fun i hi => ?_).trans hc.comp.trap_word
  exact hc.frame _ (hc.ranges.ci_out _ (by omega) (by simp only [ciTrapOff, ciSize]; omega)
    (by simp only [ciTrapOff, ciSavedpcOff]; omega))

theorem kval_lt {p : Proto} {i : Nat} {v : Value} (h : kval p i = some v) : i < p.k.length := by
  simp only [kval, Proto.const, Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, -⟩ := h
  exact (List.getElem?_eq_some_iff.1 hc).1

/-- The constant `k[i]`, as a `K` arm reads it (`ld a4,0(sp)`, then the slot). -/
theorem Core.kconst (hc : Core p c s w) {i : Nat} {v : Value} (hk : kval p i = some v) :
    ValRepr w.mo w.ι (slotTag c.σ.mem (w.k + stackValueSize * i))
      (slotVal c.σ.mem (w.k + stackValueSize * i)) v := by
  have hi := kval_lt hk
  obtain ⟨ht, hv⟩ := slot_congrT (m := c.σ.mem) (m' := w.mo) (a := w.k + stackValueSize * i)
    fun j hj => hc.frame _ (hc.ranges.k_out _ (by omega) (by simp only [stackValueSize] at *; omega))
  rw [ht, hv]
  exact hc.comp.kconst i v hk

/-- A represented string's object is owned (`Complement.own`). -/
theorem ValRepr.owned (hc : Complement p w) {t : BitVec 8} {x : BitVec 64} {str : List UInt8}
    (h : ValRepr w.mo w.ι t x (.str str)) : StrOwned p w x.toNat str := by
  cases h with
  | str _ _ ho => exact hc.own _ _ ho

/-- **A string register's object is owned**: it lies in an in-use allocator
chunk apart from the window, so the machine's bytes there are the
complement's (`Core.frame`). -/
theorem Core.reg_owned (hc : Core p c s w) {j : Nat} {str : List UInt8} (hj : j < p.maxstacksize)
    (hv : s.regs j = some (.str str)) : StrOwned p w (slotVal c.σ.mem (w.slot j)).toNat str :=
  (hc.stack j _ hj hv).owned hc.comp

/-- **A string constant's object is owned.** -/
theorem Core.k_owned (hc : Core p c s w) {i : Nat} {str : List UInt8} (hk : kval p i = some (.str str)) :
    StrOwned p w (slotVal c.σ.mem (w.k + stackValueSize * i)).toNat str :=
  (hc.kconst hk).owned hc.comp

/-- **An owned string's bytes are the complement's**: every byte of the
object, header to terminator, reads (totally) as `w.mo`'s. -/
theorem Core.str_frame (hc : Core p c s w) {ts : Nat} {str : List UInt8} (ho : StrOwned p w ts str)
    {a : Nat} (h1 : ts ≤ a) (h2 : a < ts + tstringContentsOff + str.length + 1) :
    bytesT1 c.σ.mem a = bytesT1 w.mo a :=
  hc.frame a (ho.out a h1 h2)

/-! ## Re-establishing the relation after an arm -/

/-- `.text` survives any memory change that is exact outside the register slots. -/
theorem Core.text_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    Arms.TextLoaded m :=
  Vsa.Sim.Code.FixedBytesLoaded.transport hc.text fun a _ h2 => h a fun hw => by
    have := Win.above hc.ranges (.inl hw); have := Arms.text_below_tohost; omega

/-- The frame survives any memory change that is exact outside the register slots. -/
theorem Core.frame_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    ∀ x, ¬ Win p w x → bytesT1 m x = bytesT1 w.mo x := fun x hx => by
  simp only [bytesT1, h x (Win.of_slots hx)]; exact hc.frame x hx

/-- `0(sp)` survives any memory change that is exact outside the register slots. -/
theorem Core.kptr_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    bytesT8 m w.sp = BitVec.ofNat 64 w.k :=
  (bytesT8_congr fun i _ => h _ fun hs => by
    have := hc.ranges.frame_sep; simp only [Slots] at hs; omega).trans hc.kptr

/-- `8(sp)` survives any memory change that is exact outside the register slots. -/
theorem Core.clptr_of (hc : Core p c s w) {m : Mem} (h : ∀ x, ¬ Slots p w x → m[x]? = c.σ.mem[x]?) :
    bytesT8 m (w.sp + 8) = BitVec.ofNat 64 w.rt.cl :=
  (bytesT8_congr fun i _ => h _ fun hs => by
    have := hc.ranges.frame_sep; simp only [Slots] at hs; omega).trans hc.clptr

/-- `8(sp)` survives any memory change that is exact outside the register slots
and `Scratch`. -/
theorem Core.clptr_of' (hc : Core p c s w) {m : Mem}
    (h : ∀ x, ¬ Slots p w x → ¬ Scratch w x → m[x]? = c.σ.mem[x]?) :
    bytesT8 m (w.sp + 8) = BitVec.ofNat 64 w.rt.cl :=
  (bytesT8_congr fun i _ => h _ (fun hs => by
    have := hc.ranges.frame_sep; simp only [Slots] at hs; omega)
    (fun hs => by have := (hc.ranges.scratch_out _ hs).2; omega)).trans hc.clptr

/-- **The saved words survive every close**: a memory that is exact outside the
register slots and `Scratch` (the C frame is neither) keeps them. -/
theorem Core.saved_of (hc : Core p c s w) {m : Mem}
    (h : ∀ x, ¬ Slots p w x → ¬ Scratch w x → m[x]? = c.σ.mem[x]?) : SavedAt m w :=
  hc.saved.congr fun x h1 _ => h x
    (fun hs => by have := hc.ranges.frame_sep; simp only [Slots] at hs; omega)
    (fun hs => by have := (hc.ranges.scratch_out _ hs).2; omega)

theorem output_congr {σ σ' : MState} (h : σ'.sailOutput = σ.sailOutput) :
    Vsa.Machine.output σ' = Vsa.Machine.output σ := by
  simp only [Vsa.Machine.output, h]

/-- **An arm that writes `R[a]`**: the machine stored the slot of `a` (and
nothing else), with a tag and payload that represent `v`. -/
theorem Core.write (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' a : Nat} {v : Value}
    {tag : BitVec 8} {val : BitVec 64} (ha : a < p.maxstacksize) (hpins : Pins c'.σ w pc')
    (hst : SlotStore c.σ.mem c'.σ.mem (w.slot a) tag val)
    (hv : ValRepr w.mo w.ι tag val v) :
    Core p c' ⟨pc', fun j => if j = a then some v else s.regs j, s.out⟩ w := by
  have hwin : ∀ x, ¬ (x < w.slot a ∨ w.slot a + 9 ≤ x) → Slots p w x := fun x hx => by
    simp only [RelPtrs.slot, Slots, stackValueSize] at hx ⊢
    constructor <;> omega
  have hfr : ∀ x, ¬ Slots p w x → c'.σ.mem[x]? = c.σ.mem[x]? := fun x hx =>
    hst.frame x (Classical.byContradiction fun h => hx (hwin x h))
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hc.text_of hfr, hc.frame_of hfr, hc.kptr_of hfr, hc.clptr_of hfr,
    fun j v' hj hv' => ?_, hc.comp,
    hc.ranges, hc.saved_of fun x hx _ => hfr x hx⟩
  · simp only at hv'
    by_cases hja : j = a
    · subst hja
      simp only [if_true, Option.some.injEq] at hv'
      subst hv'
      simp only [slotTag, slotVal, tvalueTagOff, tvalueValOff, Nat.add_zero, hst.val, hst.tag]
      exact hv
    · simp only [hja, if_false] at hv'
      obtain ⟨ht, hv2⟩ := slot_congr (m := c'.σ.mem) (m' := c.σ.mem) (a := w.slot j) fun i hi =>
        hst.frame _ (by
          simp only [RelPtrs.slot, stackValueSize]
          rcases Nat.lt_or_gt_of_ne hja with h | h
          · left; omega
          · right; omega)
      rw [ht, hv2]
      exact hc.stack j v' hj hv'

/-- **An arm that writes no register** and no memory (a jump). -/
theorem Core.jump (hc : Core p c s w) {c' : Config} {pcv : BitVec 64} {L : List Pin}
    {m : Mem} (hseg : SegSt pcv L (ArmPay m c.σ.sailOutput) c') {pc' : Nat}
    (hpins : Pins c'.σ w pc') (hmem : c'.σ.mem = c.σ.mem) :
    Core p c' ⟨pc', s.regs, s.out⟩ w := by
  refine ⟨hseg.good, hseg.minstret, hseg.tick, hpins, (output_congr hseg.armOut).trans hc.out,
    hseg.armOk, hmem ▸ hc.text, hmem ▸ hc.frame, hmem ▸ hc.kptr, hmem ▸ hc.clptr,
    fun j v hj hv => ?_, hc.comp,
    hc.ranges, hmem ▸ hc.saved⟩
  rw [hmem]
  exact hc.stack j v hj hv

end

end Lua.Vm.Sim

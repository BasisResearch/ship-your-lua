import Lua.Vm.Loaded
import Lua.Vm.DlHeap
import Lua.Vm.Boot.View
import Lua.Vm.RuntimeData
import Vsa.Densify.Transport

/-!
# `luaRuntimeReady`: the runtime at `luaV_execute`'s entry (PHASES A0.6)

The concrete `VmLayout.runtimeReady`, the analogue of ship-your-interpreter's
`InterpRunReadyFacts` (`Vsa/Sim/LayoutInstance.lean`). `VmLoaded` already has
the machine (`MachineAt`) and the VM's own data (`VmEntryData`); this adds
what `luaV_execute` and its F1 callees read outside those:

* `CStackAt`: the C stack and registers of the call `ccall` makes;
* `ErrorJmpAt`: the `lua_longjmp` record `luaD_rawrunprotected` set up;
* `StdioBoot`: newlib's stdio before its lazy `__sinit`;
* `MemfsBoot`: htif.c's in-image file system before its lazy `fs_init`;
* `DlHeap.HeapAt`: the dlmalloc heap `[_end, __heap_end)` in canonical shape;
* `LuaStateAt`: the `lua_State`/`CallInfo`/`global_State` invariants F1 reads
  beyond `VmEntryData` (hooks, error function, the stack bounds, the call's
  `callstatus`/`nresults`, the upvalue and to-be-closed lists, the string
  table and string cache, the basic types' metatables);
* `VmRegionsAt`: where the objects `luaV_execute` addresses lie (the heap, and
  apart from the Lua stack), for A1's `VmRel`;
* `KInterned`, `KOwned`: the string constants are interned, and each lies in
  an in-use allocator chunk apart from the Lua stack, `L` and `ci`;
* `HarnessAt`: the platform loop's tick counter and the empty console.

Every field says which callee reads it. Boot-invariant values (the entry `sp`,
the return addresses, the `jmp_buf`, the caller frames' bytes) are
`Lua/Vm/RuntimeData.lean`, generated from the boot traces by
`scripts/gen_lua_boot_witness.py`, which fails unless every traced program
agrees on them. Everything program-dependent is in the witness `RtPtrs`.

Two properties are stated as facts about the fixed image, not the
configuration: `retCcall_after_call` (the entry `ra` follows `ccall`'s
`jal luaV_execute`) and `setjmpRet_after_call` (the `jmp_buf`'s `ra` follows
`luaD_rawrunprotected`'s `jal setjmp`).
-/

namespace Lua.Vm

open Layout
open Vsa.Machine (MState Config)
open Vsa.Sim (gprGet)

/-- `s0`, `s1`, `s2 … s11`: the registers `luaV_execute`'s prologue saves
(`sd s0,160(sp)` … `sd s11,72(sp)`) and its epilogue restores for `ccall`. -/
def calleeSavedRegs : List Nat := [8, 9, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]

/-- The C stack `luaV_execute` and its F1 callees may use below `sp`: its own
176-byte frame, `luaD_precall` → `luaB_print` → `luaL_tolstring` →
`lua_pushfstring` → `snprintf`'s `_svfprintf_r`, and `fwrite` →
`__sfvwrite_r` → `_write`, plus the allocator. A bound, to be justified by A1's
frame census; `cstack_room` shows the real stack has it many times over. -/
def cStackBudget : Nat := 0x10000

/-- **The C stack and registers** at the entry of `luaV_execute(L, ci)`,
called by `ccall` (inlined into `luaD_callnoyield`, called from `f_call`,
under `luaD_rawrunprotected`, `luaD_pcall`, `lua_pcallk`, `main`, `_start`). -/
structure CStackAt (σ : MState) : Prop where
  /-- `luaV_execute`'s prologue `addi sp,sp,-176` and every callee frame below
  it; the entry `sp` is the same for every chunk (`RuntimeData.spEntry`). -/
  sp : gprGet σ 2 = some (BitVec.ofNat 64 RuntimeData.spEntry)
  /-- The return into `ccall` after `jal luaV_execute` (`retCcall_after_call`),
  where `OP_RETURN` of a `CIST_FRESH` call returns. -/
  ra : gprGet σ 1 = some (BitVec.ofNat 64 RuntimeData.retCcall)
  /-- `gp` as crt0 set it (`__global_pointer$`): newlib and Lua address their
  small globals `gp`-relative. -/
  gp : gprGet σ 3 = some (BitVec.ofNat 64 symGlobalPointer)
  /-- Saved by `luaV_execute`'s prologue (`sd s0 … s11`), so they must be
  readable; their values are the callers', restored at the return. -/
  callee_saved : ∀ r ∈ calleeSavedRegs, (gprGet σ r).isSome = true
  /-- `s0 = L` (`ccall`'s `mv s0,a0`): `ccall` reloads `L->nCcalls` through it
  after `luaV_execute` returns. -/
  s0 : gprGet σ 8 = gprGet σ 10
  /-- `s1`, `s2 … s11` are the callers' values (`RuntimeData.calleeSavedEntry`),
  which the return chain reads after `luaV_execute`'s epilogue restores them
  (`luaD_pcall`'s `s1` = the old `errfunc`, …). -/
  saved : ∀ rv ∈ RuntimeData.calleeSavedEntry, gprGet σ rv.1 = some (BitVec.ofNat 64 rv.2)
  /-- The caller frames above `sp`, byte for byte as the boot left them: the
  return path after `luaV_execute` returns (`ccall`'s `ld ra,24(sp)`, `f_call`,
  `luaD_rawrunprotected`, `luaD_pcall`, `lua_pcallk`, `main`, `_start`'s
  `tail exit`) reloads its saved registers and locals from them, and the
  `lua_longjmp` record `L->errorJmp` points to lives among them. -/
  callers : SegsAt σ.mem RuntimeData.callerFrames
  /-- Every RAM byte is present. True of the zero fill by construction
  (`Vsa.Densify.fillZeroMem_ram`); the state the theorems are stated at is the
  fill (`vm_refinement_Statement`), and loads read absent bytes as 0 anyway. -/
  dense : ∀ a, Vsa.Densify.ramBase ≤ a → a < Vsa.Densify.ramBase + Vsa.Densify.ramSize →
    (σ.mem[a]?).isSome = true

/-- **`L->errorJmp`**: the `lua_longjmp` of the outermost protected call. Read
by `luaD_throw` on every error path F1 reaches (`luaG_opinterror`,
`luaG_forerror`, `luaG_runerror` → `luaG_errormsg` → `luaD_throw` →
`longjmp(L->errorJmp->b, 1)`), which reloads `ra`, `s0 … s11` and `sp` from
the `jmp_buf` (newlib's riscv `setjmp` slots, `RuntimeData.jb*`). -/
structure ErrorJmpAt (m : Mem) (L : Nat) : Prop where
  ptr : rd64 m (L + stateErrorJmpOff) = some RuntimeData.ljAddr
  /-- The outermost handler: `luaD_throw` needs no further chain. -/
  previous : rd64 m (RuntimeData.ljAddr + ljPreviousOff) = some 0
  /-- `longjmp` returns into `luaD_rawrunprotected` after its `jal setjmp`
  (`setjmpRet_after_call`), which then returns the error status. -/
  ret : rd64 m (RuntimeData.ljAddr + ljBOff + 8 * RuntimeData.jbRa) = some RuntimeData.setjmpRet
  /-- `luaD_rawrunprotected`'s own `sp`. -/
  sp : rd64 m (RuntimeData.ljAddr + ljBOff + 8 * RuntimeData.jbSp) = some RuntimeData.rawrunSp
  saved : ∀ i, i < 12 → (rd64 m (RuntimeData.ljAddr + ljBOff + 8 * (RuntimeData.jbS0 + i))).isSome = true

/-- **newlib's stdio before `__sinit`.** Nothing is printed before the chunk
runs, so the first `print` → `lua_writestring` = `fwrite(…, stdout)` →
`_fwrite_r` runs `CHECK_INIT` → `__sinit` (because `__stdio_exit_handler` is
still NULL), whose `std()` initialises the three `FILE`s in `__sf`; then
`__sfvwrite_r` → `__swsetup_r` → `__smakebuf_r` allocates the buffer. -/
structure StdioBoot (m : Mem) : Prop where
  exit_handler : rd64 m symStdioExitHandler = some 0
  /-- `_REENT` for every `_r` function. -/
  impure_ptr : rd64 m symImpurePtr = some symImpureData
  /-- `stdin`/`stdout`/`stderr` are `_REENT->_stdin …`: the `FILE`s of `__sf`. -/
  stdin : rd64 m (symImpureData + reentStdinOff) = some symSf
  stdout : rd64 m (symImpureData + reentStdoutOff) = some (symSf + fileSize)
  stderr : rd64 m (symImpureData + reentStderrOff) = some (symSf + 2 * fileSize)
  /-- `__sglue`: `__sfp`'s list of `FILE` arrays, only `__sf`. -/
  glue_next : rd64 m (symSglue + glueNextOff) = some 0
  glue_niobs : rd32 m (symSglue + glueNiobsOff) = some 3
  glue_iobs : rd64 m (symSglue + glueIobsOff) = some symSf
  /-- The three `FILE`s are still `.bss` zeros: `std()` writes most fields and
  relies on the others (`_ub`, `_lb`, `_nbuf`, `_offset`, `_mbstate`) being 0. -/
  files : ZeroAt m symSf symSfSize
  /-- No `atexit` handler: `exit` → `__call_exitprocs` finds `__atexit = NULL`
  (the `OP_RETURN*` chain's end, `FinalSim`). -/
  atexit : rd64 m symAtexit = some 0

/-- **htif.c's file system before `fs_init`.** `_write(1, …)` (from `__swrite`),
and `_fstat(1)`/`_isatty(1)` (from `__smakebuf_r` at the first write) call
`getfd` → `fs_init`, which sets `fs_ready` and the kinds of descriptors 0-2
and relies on the rest of both tables being zero (free descriptors, unused
files). -/
structure MemfsBoot (m : Mem) : Prop where
  ready : rd32 m symFsReady = some 0
  fds : ZeroAt m symFds symFdsSize
  files : ZeroAt m symFiles symFilesSize

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

/-- **The Lua-side invariants beyond `VmEntryData`.** -/
structure LuaStateAt (m : Mem) (L ci : Nat) (w : RtPtrs) : Prop where
  /-- `luaV_execute` loads `trap = L->hookmask` first (`lw t6,192(s0)`); the
  C-call path of `luaD_precall` and `luaD_poscall` test it too. No hooks. -/
  hookmask : rd32 m (L + stateHookmaskOff) = some 0
  /-- `vmfetch` re-reads `ci->u.l.trap` after every call (`updatetrap`). -/
  trap : rd32 m (ci + ciTrapOff) = some 0
  /-- `luaG_errormsg` calls a handler iff `L->errfunc ≠ 0` (`lua_pcall(L,0,0,0)`). -/
  errfunc : rd64 m (L + stateErrfuncOff) = some 0
  /-- `ccall` subtracts `0x10001` after `luaV_execute` returns
  (`lw a4,176(s0)`), and `luaE_checkcstack` bounds it. -/
  nCcalls : rd32 m (L + stateNCcallsOff) = some RuntimeData.nCcallsEntry
  /-- `OP_RETURN` with `k` (the vararg main chunk) runs `luaF_close`, which
  walks `L->openupval` and `L->tbclist`: nothing open, nothing to close. -/
  openupval : rd64 m (L + stateOpenupvalOff) = some 0
  tbclist : rd64 m (L + stateTbclistOff) = some w.stack
  /-- The stack: `luaD_checkstack`/`luaD_growstack` (from `OP_VARARGPREP`'s
  `luaT_adjustvarargs` and `luaD_precall`'s `checkstackGCp`) compare
  `L->stack_last - L->top` and reallocate from `L->stack`. -/
  stack : rd64 m (L + stateStackOff) = some w.stack
  stack_last : rd64 m (L + stateStackLastOff) = some w.stackLast
  func : rd64 m (ci + ciFuncOff) = some w.func
  stack_le : w.stack ≤ w.func
  /-- `ci->top`: `OP_RETURN` raises `L->top` to it; `luaD_precall`'s C call
  sets the new frame's top from `L->top`. -/
  ci_top : rd64 m (ci + ciTopOff) = some w.ciTop
  ci_top_le : w.ciTop ≤ w.stackLast
  /-- `CIST_FRESH` (set by `ccall`, `sh a5,62(a0)`): `OP_RETURN*` returns from
  `luaV_execute` to its C caller instead of continuing the caller's frame. -/
  callstatus : rd16 m (ci + ciCallstatusOff) = some cistFresh
  /-- `luaD_poscall` → `moveresults` keeps `ci->nresults` results (0). -/
  nresults : rd16 m (ci + ciNresultsOff) = some 0
  /-- `luaD_poscall` sets `L->ci = ci->previous`: `lua_pcallk`'s `base_ci`. -/
  previous : rd64 m (ci + ciPreviousOff) = some (L + stateBaseCiOff)
  /-- `next_ci` (`luaD_precall` for `print`) reuses `ci->next` or allocates
  one (`luaE_extendCI`) when it is NULL. -/
  next : rd64 m (ci + ciNextOff) = some 0
  g : rd64 m (L + stateGOff) = some w.g
  /-- `luaL_tolstring` → `luaL_callmeta` → `lua_getmetatable` reads
  `G(L)->mt[type]`: no `__tostring` for nil, booleans and numbers. -/
  mt_nil : rd64 m (w.g + gMtOff + 8 * luaTnil) = some 0
  mt_boolean : rd64 m (w.g + gMtOff + 8 * luaTboolean) = some 0
  mt_number : rd64 m (w.g + gMtOff + 8 * luaTnumber) = some 0
  strt : StrtAt m w
  strcache : StrCacheAt m w

/-- **Where the VM's objects lie.** The `lua_State`, the `CallInfo`, the Lua
stack `[L->stack, L->stack_last)`, the main closure, its `Proto` and the
proto's `code` array are `l_alloc` blocks of the dlmalloc heap
`[_end, __heap_end)`, below the C stack (`cstack_room`); the `CallInfo` and
the code array are apart from the Lua stack. Read by A1's entry lemma
`Lua.Vm.Sim.vmRel_entry` (`Lua/Vm/Sim/Entry.lean`): the prologue's loads
(`lw t6,192(s0)`, `ld t1,0(s7)`, `ld s11,32(s7)`, `ld a5,0(t1)`,
`ld a5,24(a5)`, `ld a5,56(a5)`) need their addresses in RAM and off
`tohost`, and `VmRel`'s `Ranges` bound the register window, the code array
and the `CallInfo` and separate them (`code_out`, `ci_out`). -/
structure VmRegionsAt (m : Mem) (L ci : Nat) (w : RtPtrs) : Prop where
  L_lo : symEnd ≤ L
  L_hi : L + stateSize ≤ symHeapEnd
  ci_lo : symEnd ≤ ci
  ci_hi : ci + ciSize ≤ symHeapEnd
  stack_lo : symEnd ≤ w.stack
  stack_hi : w.stackLast ≤ symHeapEnd
  /-- `TValue`s are 8-aligned: the arms' `ld`/`sd` of a slot's payload. -/
  func_al : w.func % 8 = 0
  ci_sep : ci + ciSize ≤ w.stack ∨ w.stackLast ≤ ci
  cl : rd64 m (w.func + tvalueValOff) = some w.cl
  cl_lo : symEnd ≤ w.cl
  /-- the closure's header, up to its upvalue array -/
  cl_hi : w.cl + lclosureUpvalsOff ≤ symHeapEnd
  proto : rd64 m (w.cl + lclosureProtoOff) = some w.proto
  proto_lo : symEnd ≤ w.proto
  /-- the `Proto` up to its `code` field -/
  proto_hi : w.proto + protoCodeOff + 8 ≤ symHeapEnd
  code : rd64 m (w.proto + protoCodeOff) = some w.code
  sizecode : rd32 m (w.proto + protoSizecodeOff) = some w.sizecode
  code_lo : symEnd ≤ w.code
  code_hi : w.code + 4 * w.sizecode ≤ symHeapEnd
  code_sep : w.code + 4 * w.sizecode ≤ w.stack ∨ w.stackLast ≤ w.code
  /-- the constant array (`k`, read by the `K` arms through `0(sp)`) -/
  kArr : rd64 m (w.proto + protoKOff) = some w.k
  sizek : rd32 m (w.proto + protoSizekOff) = some w.sizek
  k_lo : symEnd ≤ w.k
  k_hi : w.k + tvalueSize * w.sizek ≤ symHeapEnd
  k_al : w.k % 8 = 0
  k_sep : w.k + tvalueSize * w.sizek ≤ w.stack ∨ w.stackLast ≤ w.k
  /-- The `lua_State`, the `CallInfo`, the code array and the constant array
  are distinct `l_alloc` blocks: the words the F1 arms write outside the
  register slots (`ci->u.l.savedpc`, `L->top`; `Lua.Vm.Sim.Scratch`) miss the
  code, the constants and the `CallInfo`'s other fields. -/
  L_sep_ci : L + stateSize ≤ ci ∨ ci + ciSize ≤ L
  code_sep_L : w.code + 4 * w.sizecode ≤ L ∨ L + stateSize ≤ w.code
  code_sep_ci : w.code + 4 * w.sizecode ≤ ci ∨ ci + ciSize ≤ w.code
  k_sep_L : w.k + tvalueSize * w.sizek ≤ L ∨ L + stateSize ≤ w.k
  k_sep_ci : w.k + tvalueSize * w.sizek ≤ ci ∨ ci + ciSize ≤ w.k
  /-- The `lua_State` is apart from the Lua stack: `savestate`'s `L->top`
  store (`Scratch`) misses every register slot. -/
  L_sep_stack : L + stateSize ≤ w.stack ∨ w.stackLast ≤ L
  /-- `L` and `ci` are 8-aligned (`l_alloc` blocks): `savestate`'s `sd` to
  `ci->u.l.savedpc` and `L->top` -/
  L_al : L % 8 = 0
  ci_al : ci % 8 = 0

/-- **The platform loop and the console.** Every segment state carries the
tick bound (`Vsa.Sim.SegSt.tick`): the loop's counter runs below
`plat_insns_per_tick = 2` in every configuration reached from 0 (checked by
the generator). Nothing is printed before the chunk runs: `VmRel`'s
`Core.out` at `State.init` (`Lua.Vm.Sim.vmRel_entry`); the generator checks
that no boot store touches `tohost`. -/
structure HarnessAt (c : Config) : Prop where
  tick : c.tick < 2
  console : Vsa.Machine.output c.σ = ""

/-- **The short-string constants are interned.** `lundump`'s `loadStringN`
creates every short constant with `luaS_newlstr` → `internshrstr`, which
returns the one `TString` of the string table with those bytes: two short
constants with equal contents are the same pointer. `luaV_equalobj` compares
short strings by pointer (`eqshrstr`), so A1's `ValRepr` needs content
equality to be pointer equality (its intern map `RelPtrs.ι`), established at
the entry from this. -/
def KInterned (m : Mem) (k sizek : Nat) : Prop :=
  ∀ i j x y (s : List UInt8), i < sizek → j < sizek →
    tagAt m (k + tvalueSize * i) = some vShrStr → tagAt m (k + tvalueSize * j) = some vShrStr →
    rd64 m (k + tvalueSize * i + tvalueValOff) = some x →
    rd64 m (k + tvalueSize * j + tvalueValOff) = some y →
    s.length ≤ maxShortLen → TStringRepr m x s → TStringRepr m y s → x = y

/-- **`k[i]` is the string `s`, at `ts`**: the constant's tag (`strTag s`),
its pointer, and the `TString` there. -/
structure KStrAt (m : Mem) (k sizek i ts : Nat) (s : List UInt8) : Prop where
  lt : i < sizek
  tag : tagAt m (k + tvalueSize * i) = some (strTag s)
  ptr : rd64 m (k + tvalueSize * i + tvalueValOff) = some ts
  str : TStringRepr m ts s

/-- **The chunk `c` owns the `TString` at `ts` with `n` content bytes**: an
in-use chunk of the allocator's walk whose user range
`[addr + 16, addr + size + 8)` holds the object (header, contents at `+24`,
terminator) and lies in the heap, apart from the Lua stack
`[stack, stack_last)`, the `lua_State` and the `CallInfo`. These are the
facts A1's `Lua.Vm.Sim.ChunkOwns` needs for the window (register slots,
`savedpc`, `L->top`, the C stack above the heap). -/
structure StrChunkAt (L ci : Nat) (w : RtPtrs) (c : DlHeap.Chunk) (ts n : Nat) : Prop where
  walk : c ∈ w.chunks
  inuse : c.inuse = true
  lo : c.addr + 16 ≤ ts
  hi : ts + tstringContentsOff + n + 1 ≤ c.addr + c.size + 8
  heap : c.addr + c.size + 8 ≤ symHeapEnd
  stack_sep : c.addr + c.size + 8 ≤ w.stack ∨ w.stackLast ≤ c.addr + 16
  L_sep : c.addr + c.size + 8 ≤ L ∨ L + stateSize ≤ c.addr + 16
  ci_sep : c.addr + c.size + 8 ≤ ci ∨ ci + ciSize ≤ c.addr + 16

/-- **The string constants are owned by the allocator.** `luaS_newlstr` →
`luaC_newobj` → `l_alloc` → `realloc` gives every `TString` its own block,
which stays in use while the prototype reaches it. A1's `VmRel` reads string
bytes through its complement memory only outside the window, so it needs
every constant's object in an in-use chunk apart from the window
(`Lua.Vm.Sim.Complement.own`); dlmalloc's free path overwrites a freed
string's header, so the fact is keyed to the in-use chunks. -/
def KOwned (m : Mem) (L ci : Nat) (w : RtPtrs) : Prop :=
  ∀ i ts s, KStrAt m w.k w.sizek i ts s → ∃ c, StrChunkAt L ci w c ts s.length

/-- The witness after `OP_VARARGPREP` at the entry: `ci->func` and `ci->top` one
slot up (`luaT_adjustvarargs` with no arguments). -/
def RtPtrs.vmoved (w : RtPtrs) : RtPtrs :=
  { w with func := w.func + stackValueSize, ciTop := w.ciTop + stackValueSize }

/-- The memory after `OP_VARARGPREP` at the entry (`varargMemV`), for the
witness `w`. -/
abbrev varargMem (m : Mem) (ci : Nat) (w : RtPtrs) : Mem := varargMemV m ci w.func w.cl w.ciTop

/-- **The memory structures A1's relation keeps**, at a memory `m`: the heap,
the Lua state, the error handler, the regions and the string constants. -/
structure RtPostAt (m : Mem) (L ci : Nat) (w : RtPtrs) : Prop where
  heap : DlHeap.HeapAt m w.top w.brkv w.chunks (fun i => w.bins.getD i [])
  lua : LuaStateAt m L ci w
  error_jmp : ErrorJmpAt m L
  regions : VmRegionsAt m L ci w
  interned : KInterned m w.k w.sizek
  kowned : KOwned m L ci w

/-- **The runtime at `luaV_execute`'s entry**, for the witness `w`. -/
structure RuntimeReadyAt (c : Config) (L ci : Nat) (w : RtPtrs) : Prop where
  harness : HarnessAt c
  cstack : CStackAt c.σ
  error_jmp : ErrorJmpAt c.σ.mem L
  stdio : StdioBoot c.σ.mem
  memfs : MemfsBoot c.σ.mem
  /-- Read by every allocation (`l_alloc` → `realloc`, see `Lua/Vm/DlHeap.lean`). -/
  heap : DlHeap.HeapAt c.σ.mem w.top w.brkv w.chunks (fun i => w.bins.getD i [])
  lua : LuaStateAt c.σ.mem L ci w
  /-- `L->top = func + 1`: no arguments. Read at the entry only: `OP_VARARGPREP`
  (pc 0) → `luaT_adjustvarargs` counts `L->top - func - 1` actual arguments.
  Not an invariant of the fetch head: `Protect`/`savestate` (`OP_MOD`,
  `OP_IDIV`, `OP_EQ`, …) set `L->top = ci->top`, `CALL print` with `C = 1`
  leaves `L->top = ra` (`moveresults`), and no non-IT instruction reads it at
  its head (`lvm.c` `vmfetch`'s assert); A1's `VmRel` leaves the word free
  (`Lua.Vm.Sim.Scratch`). -/
  top : rd64 c.σ.mem (L + stateTopOff) = some (w.func + stackValueSize)
  regions : VmRegionsAt c.σ.mem L ci w
  interned : KInterned c.σ.mem w.k w.sizek
  kowned : KOwned c.σ.mem L ci w
  /-- **After `OP_VARARGPREP`** (pc 0 of every main chunk): the same structures
  hold at the memory `luaT_adjustvarargs` leaves (`varargMem`), for the moved
  `ci->func` and `ci->top` (`RtPtrs.vmoved`). The CallInfo and the Lua stack are
  `l_alloc` blocks of their own, so the stores miss every other object; the
  boot witness checks it at the stored bytes (`postView`). -/
  vararg : RtPostAt (varargMem c.σ.mem ci w) L ci w.vmoved
  /-- The caller frames' copies of `L` (`RuntimeData.callerLSlots`: `ccall`'s
  saved `s0`, `luaD_rawrunprotected`'s local): the return chain after
  `luaV_execute` (`FinalSim`) stores `L->nCcalls`, `L->errorJmp` and
  `L->errfunc` through them. -/
  callerL : ∀ a ∈ RuntimeData.callerLSlots, rd64 c.σ.mem a = some L

/-- **`luaRuntimeReady`**: some choice of the program-dependent pointers and
heap shape makes the runtime ready. -/
def luaRuntimeReady (c : Config) (L ci : Nat) : Prop := ∃ w, RuntimeReadyAt c L ci w

/-- **The Lua ELF's layout** (PHASES A0.6). -/
def luaLayout : VmLayout := ⟨luaRuntimeReady⟩

/-! ## Facts about the fixed image the fields rely on -/

/-- The little-endian word of `.text` at `a`. -/
def textWord (a : Nat) : Nat :=
  (List.range 4).foldr (fun i acc => (Image.textByte (a - Image.textBase + i)).toNat + 256 * acc) 0

/-- The target of the `jal ra, …` at `a`, if that is what the word is. -/
def jalTarget (a : Nat) : Option Nat :=
  let w := textWord a
  if w % 128 = 0x6f ∧ (w >>> 7) % 32 = 1 then
    let imm := ((w >>> 31) % 2) * 2 ^ 20 + ((w >>> 12) % 256) * 2 ^ 12 +
      ((w >>> 20) % 2) * 2 ^ 11 + ((w >>> 21) % 1024) * 2
    some ((a + imm + 2 ^ 64 - (if imm ≥ 2 ^ 20 then 2 ^ 21 else 0)) % 2 ^ 64)
  else none

/-- The entry `ra` is the return address of `ccall`'s `jal luaV_execute`. -/
theorem retCcall_after_call : jalTarget (RuntimeData.retCcall - 4) = some symLuaVExecute := by
  decide +kernel

/-- The `jmp_buf`'s `ra` is the return address of `luaD_rawrunprotected`'s
`jal setjmp`. -/
theorem setjmpRet_after_call : jalTarget (RuntimeData.setjmpRet - 4) = some symSetjmp := by
  decide +kernel

/-- The stack below the entry `sp` has room for `cStackBudget`. -/
theorem cstack_room : symHeapEnd + cStackBudget ≤ RuntimeData.spEntry := by decide

end Lua.Vm

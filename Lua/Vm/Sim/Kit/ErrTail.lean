import Lua.Vm.Sim.Fold
import Lua.Vm.Sim.Kit.Throw
import Lua.Vm.Sim.Kit.AtErr
import Lua.Vm.Sim.Kit.RetChain
import Lua.Vm.Sim.Kit.HeapKeep

/-!
# The shared tail of every Lua error (lane F1-16)

Every error site of F1 formats its message (`luaO_pushvfstring`,
`luaG_addinfo`: string objects on the heap, the Lua stack, the C stack) and
then calls `luaG_errormsg(L)` with the message on top of the Lua stack
(`luaG_runerror`; `luaG_typeerror` → `luaG_runerror`; `lua_error` for
`lstrlib.c`'s `luaL_error`). The seam is `luaG_errormsg`'s entry:

* `ErrMsgIn X c`: the machine there, relative to the arm context `X` (whose
  `Core` holds at `X.c`): the memory off what the formatting may write
  (`HeadW`) is `X.c`'s, `L->errfunc`/`L->errorJmp` as the boot left them, a
  well-formed heap keeping `X`'s chunks in use, and the message: a string
  value just below `L->top` (`ErrMsgMem`);
* the head of a site, from its exit's entry (`ErrIn`) to the seam: for
  `luaG_runerror`, `RunerrorHead_Statement f msg`;
* the tail, from the seam to `StuckOut`: `ErrorTail_Statement`, proved
  (`errorTail_of_unwind`) from the throw `throw_land` (`Kit/Throw.lean`:
  `luaG_errormsg` → `luaD_throw` → `longjmp` → `luaD_rawrunprotected`
  returns `2` into `luaD_pcall`) and `Unwind_Statement`: `luaD_pcall`'s error
  branch (`luaD_closeprotected`, `luaD_seterrorobj`, `luaD_shrinkstack`,
  `luaE_shrinkCI`), `lua_pcallk`, `main`'s `fprintf(stderr, "lua: %s\n", …)`
  (newlib `vfprintf` on the unbuffered `stderr`), `return 2`, `exit(2)`
  (the stdio handler's `_fclose_r` of the three streams), `_exit(2)`.

`throwFrom_of` composes a head and the tail into `ThrowFrom f msg`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim

open Lua.Vm.Sim.At Lua.Bytecode Lua.Vm.Layout
open Vsa.Machine (Config)

/-- **The throw obligation at the error exit `f` with the message `msg`**:
from the exit's entry as an arm's error path reaches it (`ErrIn`: the call's
pins, the arm's entry memory but `savestate`'s words and the C frame's
spills), for an arm context whose relation facts hold (`Core`) at a
reachable state, the machine diverges or halts with a nonzero code. `f` does
not return; its summary is the error path `luaG_errormsg` → `luaD_throw` →
`longjmp` → `luaD_rawrunprotected` returns → `lua_pcallk` returns
`LUA_ERRRUN` → `main` returns 2 → `exit(2)`.

(Lane F1-16: the earlier form keyed the obligation by the entry pc alone,
`Steps c c' → ErrAt f c' → StuckOut c'` from a related `c`: nothing about
the registers or the memory at `c'` was given, so no summary of `f` could
discharge it locally.) -/
def ThrowFrom (f msg : Nat) : Prop :=
  ∀ (X : At.Cx) c, Supported X.p → Reach X.p X.s → Core X.p X.c X.s X.w → ErrIn X f msg c → StuckOut c

/-- The messages the F1 arms call `luaG_runerror` with (`luaV_idiv`,
`luaV_mod`, `forprep`; `Lua/Vm/LayoutErr.lean`). -/
def runerrMsgs : List Nat := [msgIdiv0, msgMod0, msgForZero]

/-- **`luaG_runerror`'s throw obligation**, for each of its messages. -/
def RunerrorThrow : Prop := ∀ msg ∈ runerrMsgs, ThrowFrom symLuaGRunerror msg

end Lua.Vm.Sim

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.At Lua.Vm.Sim.Ret Lua.Bytecode Lua.Vm.Layout Lua.Vm.DlHeap
open Vsa.Machine (MState Config Steps)

/-- The chunk of `g`'s string table (`g->strt.hash`), in use in the arm
entry's heap: interning writes a bucket, `luaS_resize` reallocates it. -/
def StrtChunk (X : At.Cx) (a : Nat) : Prop :=
  ∃ c ∈ X.w.rt.hix.chunks, c.inuse = true ∧
    BitVec.ofNat 64 (c.addr + 16) = bytesT8 X.c.σ.mem (X.w.rt.g + gStrtHashOff) ∧
    c.addr + 16 ≤ a ∧ a < c.addr + c.size + 8

/-- **What a Lua error's message formatting may write**, relative to the
arm context `X`, all below the entry `sp` (never the caller frames): the C
stack below `luaV_execute`'s frame, the arm's error path's own words
(`ErrW`), the allocator's words and the arena off `X`'s chunks in use
(`MallocW`: the new string objects), `g` up to its string cache (the GC
debt, `allgc`, the string table's header), the string table's chunk, the
Lua stack above `ci->func` (with `EXTRA_STACK`: the pushed messages),
`L->top`. -/
def HeadW (X : At.Cx) (a : Nat) : Prop :=
  a < RuntimeData.spEntry ∧
    ((RuntimeData.spEntry - cStackBudget ≤ a ∧ a < X.w.sp) ∨ ErrW X.w a ∨
      MallocW X.w.rt.hix.chunks a ∨ (X.w.rt.g ≤ a ∧ a < X.w.rt.g + gEnd) ∨ StrtChunk X a ∨
      (X.w.func ≤ a ∧ a < X.w.rt.stackLast + 5 * tvalueSize) ∨
      (X.w.L + stateTopOff ≤ a ∧ a < X.w.L + stateTopOff + 8))

/-- **The memory at the seam** (`luaG_errormsg`'s entry), relative to the
arm context `X`. -/
structure ErrMsgMem (X : At.Cx) (M : Mem) : Prop where
  /-- off what the formatting may write, the arm entry's memory -/
  keep : ∀ a, ¬ HeadW X a → bytesT1 M a = bytesT1 X.c.σ.mem a
  /-- `L->errfunc = 0` (`main`'s `lua_pcall(L, 0, 0, 0)`) -/
  errfunc : bytesT8 M (X.w.L + stateErrfuncOff) = 0#64
  /-- `L->errorJmp`: `luaD_rawrunprotected`'s `lua_longjmp` -/
  errjmp : bytesT8 M (X.w.L + stateErrorJmpOff) = BitVec.ofNat 64 RuntimeData.ljAddr
  /-- the heap, well formed, `X`'s chunks in use (but the string table's) in use -/
  heap : ∃ H : HeapIx, HeapAt (Vsa.Densify.fillZeroMem M) H.top H.brk H.chunks H.bins ∧
    ∀ a, InUse X.w.rt.hix.chunks a → ¬ StrtChunk X a → InUse H.chunks a
  /-- the message: a string just below `L->top`, in the Lua stack -/
  msg : ∃ t s, bytesT8 M (X.w.L + stateTopOff) = BitVec.ofNat 64 (t + tvalueSize) ∧
    X.w.func < t ∧ t + tvalueSize ≤ X.w.rt.stackLast + 5 * tvalueSize ∧
    TValueRepr (Vsa.Densify.fillZeroMem M) t (.str s)

/-- **The machine at `luaG_errormsg(L)`'s entry with the message pushed**:
the call's pins (`L`, any `ra`, an `sp` in the C stack below `luaV_execute`'s
frame with room, the caller's `s0 … s11`), the memory `ErrMsgMem`. -/
structure ErrMsgInM (X : At.Cx) (sp : Nat) (r : BitVec 64) (f : AbiFrame) (M : Mem) (c : Config) :
    Prop where
  seg : SegSt (BitVec.ofNat 64 symLuaGErrormsg) (callPre [⟨Register.x10, BitVec.ofNat 64 X.w.L⟩] sp r f)
    (ArmPay M X.c.σ.sailOutput) c
  sp_lo : RuntimeData.spEntry - cStackBudget + 64 ≤ sp
  sp_hi : sp ≤ X.w.sp
  sp_al : sp % 16 = 0
  mem : ErrMsgMem X M

-- discipline: allow(R7-conj-tower-def) one existential over the seam's
-- witnesses; the body is the named-field structure `ErrMsgInM`
/-- **`ErrMsgInM` for some `sp`, `ra`, frame and memory.** -/
def ErrMsgIn (X : At.Cx) (c : Config) : Prop := ∃ sp r f M, ErrMsgInM X sp r f M c

/-- **Open: a site's head for `luaG_runerror`**: from its entry as the arm's
error path reaches it (`ErrIn`, the message `msg`) to `luaG_errormsg` with
the formatted message pushed (`ErrMsgIn`): `luaC_checkGC` (`luaC_step` with
the collector stopped: `luaE_setdebt`), `luaO_pushvfstring` (`strchr`,
`addstr2buff`, `luaS_newlstr` → `internshrstr`, `luaC_newobj` → `l_alloc` →
`_malloc_r`, `MallocR_Statement`), `luaG_getfuncline` (no line info: `-1`),
`luaG_addinfo` → `luaO_pushfstring("%s:%d: %s")` (`snprintf("%lld")`:
`_svfprintf_r`, `IntegerToStr_Statement`'s routine), the second string. -/
def RunerrorHead_Statement (f msg : Nat) : Prop :=
  ∀ (X : At.Cx) c, Supported X.p → Reach X.p X.s → Core X.p X.c X.s X.w → ErrIn X f msg c →
    ∃ c', Steps c c' ∧ ErrMsgIn X c'

/-- **The shared tail**: from the seam, the machine diverges or halts with a
nonzero code. -/
def ErrorTail_Statement : Prop :=
  ∀ (X : At.Cx) c, Supported X.p → Reach X.p X.s → Core X.p X.c X.s X.w → ErrMsgIn X c → StuckOut c

/-- **Open: the unwind after the throw**: back in `luaD_pcall` with the status
`2` (`throw_land`'s post: `throwRow`, `ThrowPost`), from a seam memory `M`:
`luaD_pcall`'s error branch (`luaD_rawrunprotected(closepaux)` → `luaF_close`,
nothing open: `L->openupval = NULL`, `L->tbclist` below the level;
`luaD_seterrorobj` moves the message to the old top; `luaD_shrinkstack`:
`luaD_reallocstack` when the stack is more than three times what is in use,
`luaE_shrinkCI` frees every other free `CallInfo`, `FreeR_Statement`),
`lua_pcallk` returns `2`, `main`'s `lua_tolstring(L, -1)` and
`fprintf(stderr, "lua: %s\n", msg)` (newlib `_vfprintf_r`; `__sinit` first if
no `print` ran; `stderr` unbuffered: `__sprint_r` → `__sfvwrite_r` →
`__swrite` → `_write(2)`, the console), `return 2`, `_start`'s `exit(2)`
(`__call_exitprocs`, the stdio handler `_fwalk_sglue(_fclose_r)` over the
three streams, `stdout`'s buffer freed if a `print` set it up), `_exit(2)`'s
`tohost` store. -/
def Unwind_Statement : Prop :=
  ∀ (X : At.Cx) (sp : Nat) (M M' : Mem) c, Supported X.p → Reach X.p X.s → Core X.p X.c X.s X.w →
    ErrMsgMem X M → sp ≤ X.w.sp → ThrowPost X.w.L sp M M' →
    SegSt 0x8000b4c0#64 (throwRow M) (ArmPay M' X.c.σ.sailOutput) c → StuckOut c

/-- The caller frames' words the throw reads, as the boot left them. -/
theorem throw_callers {p : Proto} {c : Config} {s : State} {w : RelPtrs} (hc : Core p c s w) :
    bytesT8 c.σ.mem 0x87fffe68 = BitVec.ofNat 64 RuntimeData.setjmpRet ∧
    bytesT8 c.σ.mem 0x87fffed0 = BitVec.ofNat 64 RuntimeData.rawrunSp ∧
    bytesT8 c.σ.mem 0x87fffe40 = BitVec.ofNat 64 w.L ∧
    bytesT8 c.σ.mem 0x87fffe60 = 0#64 ∧
    bytesT8 c.σ.mem 0x87ffff48 = 0x8000b4c0#64 := by
  have hf := hc.comp.callers
  have hT := chainMem hc (RAgree.refl w c.σ.mem)
  have e8 : ∀ a x, framesRd a 8 = some x → RuntimeData.spEntry ≤ a → a + 8 ≤ 0x88000000 →
      bytesT8 c.σ.mem a = BitVec.ofNat 64 x := fun a x hx h1 h2 => by
    rw [hc.callers8 (RAgree.refl w c.σ.mem) h1 h2]; exact bytesT8_of_rd64 (framesRd_rdLE hf hx)
  exact ⟨e8 _ _ (by decide +kernel) (by decide) (by decide),
    e8 _ _ (by decide +kernel) (by decide) (by decide), hT.rawrun_L,
    e8 _ _ (by decide +kernel) (by decide) (by decide), hT.rawrun_ra⟩

/-- **The throw's words at the seam**: `L`'s from `ErrMsgMem`, the caller
frames' from the arm entry's (`HeadW` lies below the entry `sp`). -/
theorem throwMem_of {X : At.Cx} {M : Mem} (hc : Core X.p X.c X.s X.w) (h : ErrMsgMem X M) :
    ThrowMem X.w.L M := by
  obtain ⟨j1, j2, j3, j4, j5⟩ := throw_callers hc
  have hi : ∀ a, RuntimeData.spEntry ≤ a → bytesT8 M a = bytesT8 X.c.σ.mem a := fun a ha =>
    bytesT8_congrT fun i _ => h.keep _ fun hw => absurd hw.1 (by omega)
  exact ⟨h.errfunc, h.errjmp, (hi _ (by decide)).trans j1, (hi _ (by decide)).trans j2,
    (hi _ (by decide)).trans j3, (hi _ (by decide)).trans j4, (hi _ (by decide)).trans j5⟩

/-- **The tail from the unwind**: the throw (`throw_land`), then the unwind. -/
theorem errorTail_of_unwind (hU : Unwind_Statement) : ErrorTail_Statement := by
  rintro X c hS hs hc ⟨sp, r, f, M, h⟩
  have hr := hc.ranges
  have hL := hr.L_lo; have hLt := hr.L_top; have hLa := hr.L_al; have hsp := hr.sp_eq
  have hlo := h.sp_lo; have hhi := h.sp_hi
  simp only [RuntimeData.spEntry, cStackBudget, execFrame, stateSize] at hLt hsp hlo ⊢
  obtain ⟨c', hst, M', hseg, hpost⟩ := throw_land X.w.L sp r f M X.c.σ.sailOutput (throwMem_of hc h.mem)
    hL hLa (by omega) (by simp only [RuntimeData.spEntry]; omega) h.sp_al c h.seg
  exact StuckOut.of_steps hst (hU X sp M M' c' hS hs hc h.mem h.sp_hi hpost hseg)

/-- **A site's throw obligation from its head and the tail.** -/
theorem throwFrom_of {f msg : Nat} (hH : RunerrorHead_Statement f msg) (hT : ErrorTail_Statement) :
    ThrowFrom f msg := by
  intro X c hS hs hc hE
  obtain ⟨c', hst, hM⟩ := hH X c hS hs hc hE
  exact StuckOut.of_steps hst (hT X c' hS hs hc hM)

end Lua.Vm.Sim.Kit

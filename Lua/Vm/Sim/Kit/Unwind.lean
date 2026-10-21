import Lua.Vm.Sim.Kit.ErrTail
import Lua.Vm.Sim.Kit.ExitErr
import Lua.Vm.Arms.Segs.Hmain
import Lua.Vm.Arms.Segs.Hstart

/-!
# The unwind after a Lua error, cut at `main`'s `fprintf` (lane F1-26)

`Unwind_Statement` (`Kit/ErrTail.lean`) runs from `luaD_pcall`'s return of
`luaD_rawrunprotected` with the status 2 (`throw_land`'s post) to a halt with
a nonzero code. The ELF executes (checked on the Lean emulator's trace of
`c/tests/stuck/e_idiv0.lua`, 1,153 distinct instructions after
`luaG_errormsg`):

1. `luaD_pcall`'s error branch: `L->ci = old_ci`, `luaD_closeprotected` →
   `luaD_rawrunprotected(closepaux)` (`setjmp`, `luaF_close` with nothing
   open), `luaD_seterrorobj` (the message to the old top), `luaD_shrinkstack`
   (`luaD_reallocstack` → `_realloc_r` when the stack is more than three times
   its use; `luaE_shrinkCI` → `_free_r` of `print`'s `CallInfo`);
   `lua_pcallk` returns 2; `main`'s `lua_tolstring(L, -1, NULL)`;
2. `fprintf(stderr, "lua: %s\n", msg)`: `_vfprintf_r` (`__sinit` if no
   `print` ran; `__swsetup_r` → `__smakebuf_r` on the unbuffered `stderr`;
   three `__sprint_r` → `__sfvwrite_r`'s unbuffered path → `__swrite` →
   `_write(2)`; no `__sbprintf`: `stderr`'s `_flags` carry `__SRW`);
3. `main` returns 2, `_start`'s `tail exit`, `exit(2)`: `stdio_exit_handler`
   closes the three streams, `_exit(2)`'s `tohost` store.

The seams: `ErrPrintAt` (`fprintf`'s entry, its pre `FprintfPre`) and
`ErrExitAt` (`fprintf`'s return into `main`, `ErrExitIn`). Step 3 is proved
(`errExit_stuck`, over `exit_run_err`); steps 1 and 2 are the named
statements `PcallErr_Statement` and `FprintfErr_Statement`, and
`unwind_of : UnwindRest → Unwind_Statement`.

`StuckOut` asks a halt with a nonzero code (or divergence) and nothing of the
console: `stderr`'s bytes go to the console `stdout` shares, and no
statement here restates them.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Sim.Ret Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify Lua.Bytecode
open Vsa.Machine (MState Config Steps)

/-- `main.c`'s format `"lua: %s\n"` in `.rodata`. -/
abbrev fmtLuaS : Nat := 0x8004ecd8

/-- `fprintf`'s entry in `main`'s error branch (`0x80001884`). -/
abbrev symFprintf : Nat := 0x80033164

/-- **A NUL-terminated string** of `n` bytes at `p`, in the heap. -/
structure StrZ (M : Mem) (p n : Nat) : Prop where
  bytes : ∀ i, i < n → bytesT1 M (p + i) ≠ 0#8
  nul : bytesT1 M (p + n) = 0#8
  lo : heapStart ≤ p
  hi : p + n < heapEnd

/-- **`stderr` once `__sinit` ran** (a `print`'s): as `std()` left it, its
tail still the `.bss` zeros. -/
structure ErrStd (M : Mem) : Prop where
  std : FileStd M stderrFile 0x20012#32
  tail : ∀ a, stderrFile + 88 ≤ a → a < stderrFile + 176 → bytesT1 M a = 0#8

/-- **What `fprintf(stderr, "lua: %s\n", msg)` reads in `main`'s error
branch**: `main`'s saved `ra` (its return after the call), no `atexit`
handler, `stdout` in the phase `ph` of the `CALL` invariant with nothing
pending (`StdoutIn`: before the first write `StdioBoot`/`MemfsBoot`),
`stderr` as `std()` left it once `__sinit` ran, `_REENT->_stderr`, the
locale's words, `.rodata` (the format), the message, the heap. -/
structure FprintfPre (M : Mem) (H : HeapIx) (ph : StdoutPh) (sptr n : Nat) : Prop where
  main_ra : bytesT8 M 0x87fffff8 = 0x80000038#64
  atexit : bytesT8 M symAtexit = 0#64
  io : StdoutIn M H ph
  pend : ph.pend = []
  err : ph ≠ .boot → ErrStd M
  stderr_ptr : bytesT8 M (symImpureData + reentStderrOff) = BitVec.ofNat 64 stderrFile
  locale : LocaleWords (fillZeroMem M)
  rodata : RodataLoaded (fillZeroMem M)
  msg : StrZ M sptr n
  heap : HeapAt (fillZeroMem M) H.top H.brk H.chunks H.bins

/-- **At `fprintf`'s entry** in `main`'s error branch: `a0 = stderr`, `a1`
the format, `a2` the message's bytes, `ra` back into `main`, `main`'s `sp`,
`s0 = stderr`, `s1 = L`. -/
def ErrPrintAt (c : Config) : Prop :=
  ∃ (M : Mem) (o : Array String) (H : HeapIx) (ph : StdoutPh) (sptr n : Nat) (f : AbiFrame),
    SegSt (BitVec.ofNat 64 symFprintf) (callPre [⟨Register.x10, BitVec.ofNat 64 stderrFile⟩,
      ⟨Register.x11, BitVec.ofNat 64 fmtLuaS⟩, ⟨Register.x12, BitVec.ofNat 64 sptr⟩] 0x87ffffe0
      0x80001888#64 f) (ArmPay M o) c ∧ FprintfPre M H ph sptr n

/-- **What `main`'s return and `exit(2)` read after the `fprintf`**. -/
structure ErrExitIn (M : Mem) (H : HeapIx) (ph : StdoutPh) : Prop where
  main_ra : bytesT8 M 0x87fffff8 = 0x80000038#64
  exit : ErrExitMem M H ph

/-- **Back in `main` after the `fprintf`** (`0x80001888`), its frame. -/
def ErrExitAt (c : Config) : Prop :=
  ∃ (M : Mem) (o : Array String) (H : HeapIx) (ph : StdoutPh) (f : AbiFrame),
    voidRet 0x80001888#64 0x87ffffe0 f M o c ∧ ErrExitIn M H ph

set_option hygiene false in
local macro_rules | `(tactic| kit_norm $h) => `(tactic|
  simp (disch := kit_disch) only [add_imm, Ret.sl_negX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
    Nat.add_zero, Vsa.Sim.sext_zero, BitVec.add_zero, BitVec.ofNat_add_ofNat, Nat.reduceSub,
    Nat.reduceAdd, symGlobalPointer, sext64_id, hra] at $h:ident)

set_option hygiene false in
local macro_rules
  | `(tactic| kit_guard_ext) => `(tactic| first
      | decide
      | (rw [Ret.rtgt _ (by decide)]; decide)
      | (simp (disch := kit_disch) only [add_imm, BitVec.toNat_ofNat, Nat.mod_eq_of_lt,
          Nat.reduceAdd, symGlobalPointer, sext64_id, hra, Vsa.Sim.sext_zero, BitVec.add_zero]
         first | decide | (rw [Ret.rtgt _ (by decide)]; decide)))

/-- **After the `fprintf`, the machine halts with code 2**: `main` returns
2, `_start`'s `tail exit`, `exit(2)` (`exit_run_err`). -/
theorem errExit_stuck {c : Config} (h : ErrExitAt c) : StuckOut c := by
  obtain ⟨M, o, H, ph, f, h, hE⟩ := h
  have acc := Steps.refl c
  have hra := hE.main_ra
  simp only [voidRet, AbiFrame.pins] at h
  kit_run h acc
  have h := h.at (Ret.rtgt _ (by decide))
  kit_run h acc until [0x8002f85c]
  have hm := h.armMem
  obtain ⟨out, hh⟩ := exit_run_err (M := M) (H := H) (ph := ph) (h.repin (by pins_of h)) hE.exit
  exact .inr ⟨out, 2, Lua.Vm.Sim.Halts.of_steps acc hh, by decide⟩

/-- **Open: `luaD_pcall`'s error branch to `main`'s `fprintf`**, from
`throw_land`'s post: `luaD_closeprotected`, `luaD_seterrorobj`,
`luaD_shrinkstack` (with `luaE_shrinkCI`), `lua_pcallk`'s return,
`lua_tolstring(L, -1, NULL)`. -/
def PcallErr_Statement : Prop :=
  ∀ (X : At.Cx) (sp : Nat) (M M' : Mem) c, Supported X.p → Reach X.p X.s → Core X.p X.c X.s X.w →
    ErrMsgMem X M → sp ≤ X.w.sp → ThrowPost X.w.L sp M M' →
    SegSt 0x8000b4c0#64 (throwRow M) (ArmPay M' X.c.σ.sailOutput) c → ∃ c', Steps c c' ∧ ErrPrintAt c'

/-- **Open: `fprintf(stderr, "lua: %s\n", msg)`** from `main`'s call to its
return, leaving what `exit(2)` reads (`ErrExitIn`). -/
def FprintfErr_Statement : Prop :=
  ∀ c, ErrPrintAt c → ∃ c', Steps c c' ∧ ErrExitAt c'

/-- **What is left of the unwind** (lane F1-26). -/
structure UnwindRest : Prop where
  pcall : PcallErr_Statement
  fprintf : FprintfErr_Statement

/-- **The unwind from its two open steps**, `exit(2)` proved. -/
theorem unwind_of (h : UnwindRest) : Unwind_Statement := by
  intro X sp M M' c hS hs hc hM hsp hT hseg
  obtain ⟨c1, s1, h1⟩ := h.pcall X sp M M' c hS hs hc hM hsp hT hseg
  obtain ⟨c2, s2, h2⟩ := h.fprintf c1 h1
  exact StuckOut.of_steps (s1.trans s2) (errExit_stuck h2)

end Lua.Vm.Sim.Kit

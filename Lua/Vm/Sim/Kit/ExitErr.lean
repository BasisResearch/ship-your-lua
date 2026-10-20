import Lua.Vm.Sim.Kit.ExitUp
import Lua.Vm.AtF.FcloseErrW
import Lua.Vm.AtF.FcloseOut9
import Lua.Vm.AtF.FcloseOutF

/-!
# `exit(2)` after a Lua error (lane F1-26)

After `main`'s `fprintf(stderr, "lua: %s\n", msg)` newlib's stdio is set up
(`__sinit` ran, by a `print` or by the `fprintf`), `stderr` has been written
(unbuffered: `_p = _bf._base = _nbuf`, `_flags` `__SORD | __SWR | __SRW |
__SNBF`) and `stdout` is in one of three states: as `std()` left it (no
`print` ran), as an empty first write left it (`_flags` `0x2009`), or set up
and flushed. `exit(2)` closes the three streams through `stdio_exit_handler`
(lane F1-14's walk, `Lua/Vm/AtF/ExitHandlerE*.lean`) and halts with code 2.

* the write streams with nothing pending, closed: `fclose_errW`,
  `fclose_out9`, `fclose_outF` (`__sflush_r`'s write path, the `_close` hook;
  `Lua/Vm/AtF/{FcloseErrW,FcloseOut9,FcloseOutF}.lean`);
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- `stderr`'s one-byte buffer `_nbuf` (`__smakebuf_r` on an unbuffered stream). -/
abbrev errNbuf : Nat := stderrFile + 0x77

/-- **A write stream `exit` closes with nothing pending**: `_flags` `fl`
(`__SWR`, no `__SMBF`), `_file` `fd`, `_bf._base` `base` (`_p` too when
`base ≠ 0`: nothing buffered), the cookie, `_close = __sclose`, no `ungetc`
or line buffer, `_flags2 = 0`. -/
structure WQuiet (m : Mem) (fp : Nat) (fl fd : BitVec 16) (base : Nat) : Prop where
  flags : bytesT2 m (fp + 16) = fl
  file : bytesT2 m (fp + 18) = fd
  base : bytesT8 m (fp + 24) = BitVec.ofNat 64 base
  cookie : bytesT8 m (fp + 48) = BitVec.ofNat 64 fp
  close : bytesT8 m (fp + 80) = BitVec.ofNat 64 symSclose
  ub : bytesT8 m (fp + 88) = 0#64
  lb : bytesT8 m (fp + 120) = 0#64
  flags2 : bytesT4 m (fp + 176) = 0#32

theorem WQuiet.congrT {m m' : Mem} {fp : Nat} {fl fd : BitVec 16} {base : Nat} (h : WQuiet m fp fl fd base)
    (hk : ∀ a, fp + 16 ≤ a → a < fp + fileSize → bytesT1 m' a = bytesT1 m a) : WQuiet m' fp fl fd base := by
  have : fileSize = 184 := rfl
  exact ⟨(bT2_congrT fun i _ => (hk _ (by omega) (by omega)).symm).symm.trans h.flags,
    (bT2_congrT fun i _ => (hk _ (by omega) (by omega)).symm).symm.trans h.file,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.base,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.cookie,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.close,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ub,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.lb,
    (bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.flags2⟩

/-- **What `_fclose_r` of a write stream with nothing pending writes**: the
stream's `_p`, `_r`, `_w`, `_flags`, its descriptor's `kind`, `errno`, its
stack. -/
def WCloseW (sp fp fd a : Nat) : Prop :=
  Rng fp 20 a ∨ Rng (symFds + 24 * fd) 4 a ∨ Rng errnoAddr 4 a ∨ Below sp 128 a

set_option hygiene false in
/-- The one-root `_fclose_r` run of a write stream: its at-lemmas, then the keep. -/
macro "wclose_run" ns:ident ok:ident r0:ident : tactic => `(tactic| (
  intro c h
  let X := abiCx sp r f m o
  have hX : $ok X := ⟨hlo, hhi, hal, hra⟩
  simp only [callPre, List.cons_append, List.nil_append] at h
  have h : SegSt 0x80032580#64 ($r0 X) (ArmPay X.m X.o) c := h.repin (by pins_of h)
  have acc := Steps.refl c
  fat_run $ns h acc
  fcx_unfold at h
  refine ⟨_, acc, _, h.repin (by pins_of h), fun a ha => ?_⟩
  fs_nums
  simp only [WCloseW, Rng, Below, not_or, not_and, Nat.not_lt] at ha
  simp only [stdoutFile, stderrFile, symSf, fileSize] at ha
  simp only [show X.n 0 = sp from rfl, show X.m = m from rfl]
  exact AtF.bT1_congr (by fs_off)))

/-- The guards every `_fclose_r` at `exit` reads: `__cleanup` set, `fs_ready` set. -/
structure ExitGuards (m : Mem) : Prop where
  init : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64
  ready : bytesT4 m symFsReady ≠ 0#32

/-- **`_fclose_r(_REENT, stderr)` after the error**: `0` returned, `WCloseW` written. -/
theorem fclose_errW (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stderrFile 0x201a#16 2#16 errNbuf) (hp : bytesT8 m stderrFile = BitVec.ofNat 64 errNbuf)
    (hk : bytesT4 m (symFds + 24 * 2) = 3#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stderrFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stderrFile 2 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hp; have hc4 := hq.close
  have hc5 := hq.cookie; have hc6 := hq.file; have hc7 := hk; have hc8 := hq.ub; have hc9 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stderrFile, errNbuf, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hc9 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseErrW Lua.Vm.AtF.FcloseErrW.Ok Lua.Vm.AtF.FcloseErrW.r0

/-- **`_fclose_r(_REENT, stdout)` on `stdout` as `std()` left it**. -/
theorem fclose_out9 (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stdoutFile 0x9#16 1#16 0) (hk : bytesT4 m (symFds + 24 * 1) = 2#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stdoutFile 1 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hq.close
  have hc4 := hq.cookie; have hc5 := hq.file; have hc6 := hk; have hc7 := hq.ub; have hc8 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stdoutFile, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseOut9 Lua.Vm.AtF.FcloseOut9.Ok Lua.Vm.AtF.FcloseOut9.r0

/-- **`_fclose_r(_REENT, stdout)` on `stdout` after an empty first write**. -/
theorem fclose_outF (sp : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hra : r.toNat % 4 = 0) (hlo : 0x87800000 + 8192 ≤ sp) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0)
    (hq : WQuiet m stdoutFile 0x2009#16 1#16 0) (hk : bytesT4 m (symFds + 24 * 1) = 2#32) (hG : ExitGuards m) :
    Triple (SegSt 0x80032580#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
        ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] sp r f) (ArmPay m o))
      (fun c => ∃ m', wrRet r sp 0 f m' o c ∧ ∀ a, ¬ WCloseW sp stdoutFile 1 a → bytesT1 m' a = bytesT1 m a) := by
  have hc0 := hq.flags2; have hc1 := hq.flags; have hc2 := hq.base; have hc3 := hq.close
  have hc4 := hq.cookie; have hc5 := hq.file; have hc6 := hk; have hc7 := hq.ub; have hc8 := hq.lb
  have hg_2 := beq0_false hG.init
  have hg_5 := sext_ne0 hG.ready
  simp only [stdoutFile, symSf, fileSize, symFds, symSclose, symImpureData, reentCleanupOff,
    symFsReady, Nat.reduceAdd, Nat.reduceMul] at hc0 hc1 hc2 hc3 hc4 hc5 hc6 hc7 hc8 hg_2 hg_5
  wclose_run Lua.Vm.AtF.FcloseOutF Lua.Vm.AtF.FcloseOutF.Ok Lua.Vm.AtF.FcloseOutF.r0

end Lua.Vm.Sim.Kit

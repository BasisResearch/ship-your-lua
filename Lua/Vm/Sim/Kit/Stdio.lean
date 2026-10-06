import Lua.Vm.Sim.Kit.CallSpec
import Lua.Vm.Sim.Kit.AtFn

/-!
# `stdout`'s state across a callee's own stores (lane F1-8)

The stdio callees on the callee-context route (`Kit/AtFn.lean`) store only
into their stack frames, above `stdout` and its buffer. `StdoutAt` and
`StdioUp` read below the buffer's end, so they survive any memory that agrees
with the old one there (`StdoutAt.below`, `StdioUp.below`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout

/-- The numbers of `stdout`'s layout, for `omega`. -/
macro "stdio_nums" : tactic => `(tactic| (
  have : stdoutFile = 0x8005e668 := rfl
  have : fileSize = 184 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFsReady = 0x8005d3c0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl
  have : fileFlags2Off = 176 := rfl
  have : fileBufPOff = 0 := rfl
  have : fileWOff = 12 := rfl
  have : fileFlagsOff = 16 := rfl
  have : fileFileOff = 18 := rfl
  have : fileBfBaseOff = 24 := rfl
  have : fileBfSizeOff = 32 := rfl
  have : fileLbfsizeOff = 40 := rfl
  have : fileCookieOff = 48 := rfl
  have : fileWriteOff = 64 := rfl))

/-- **`stdout` across stores above its buffer.** -/
theorem StdoutAt.below {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} (hs : StdoutAt m buf pend)
    (h : ∀ a, a < buf + 1024 → m'[a]? = m[a]?) : StdoutAt m' buf pend := by
  have hb := hs.buf_lo; have hr := hs.room
  stdio_nums
  refine ⟨(bT8_congr fun i _ => h _ (by omega)).trans hs.p, (bT4_congr fun i _ => h _ (by omega)).trans hs.w,
    (bT2_congr fun i _ => h _ (by omega)).trans hs.flags, (bT2_congr fun i _ => h _ (by omega)).trans hs.file,
    (bT8_congr fun i _ => h _ (by omega)).trans hs.base, (bT4_congr fun i _ => h _ (by omega)).trans hs.size,
    (bT4_congr fun i _ => h _ (by omega)).trans hs.lbf, (bT8_congr fun i _ => h _ (by omega)).trans hs.cookie,
    (bT8_congr fun i _ => h _ (by omega)).trans hs.write, ?_, hs.room, hs.buf_lo, hs.buf_hi, ?_, ?_⟩
  · rw [bytesAt_congr (m := m) fun i hi => bT1_congr (h _ (by omega))]; exact hs.bytes
  · rw [bT4_congr fun i _ => h _ (by omega)]; exact hs.ready
  · rw [bT4_congr fun i _ => h _ (by omega)]; exact hs.stdout

/-- **newlib's set-up words across stores above `stdout`.** -/
theorem StdioUp.below {m m' : Mem} (hu : StdioUp m) (h : ∀ a, a < stdoutFile + fileSize → m'[a]? = m[a]?) :
    StdioUp m' := by
  stdio_nums
  refine ⟨(bT8_congr fun i _ => h _ (by omega)).trans hu.impure, ?_,
    (bT4_congr fun i _ => h _ (by omega)).trans hu.flags2⟩
  rw [bT8_congr fun i _ => h _ (by omega)]; exact hu.init

/-- Reads from byte-wise agreement (`bytesT1`, as the summaries' keep facts state it). -/
theorem bT2_congrT {m m' : Mem} {x : Nat} (h : ∀ i, i < 2 → bytesT1 m (x + i) = bytesT1 m' (x + i)) :
    bytesT2 m x = bytesT2 m' x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega)
  simp only [bytesT1, Nat.add_zero] at h0 h1
  simp only [bytesT2, h0, h1]

theorem bT4_congrT {m m' : Mem} {x : Nat} (h : ∀ i, i < 4 → bytesT1 m (x + i) = bytesT1 m' (x + i)) :
    bytesT4 m x = bytesT4 m' x := by
  have h0 := h 0 (by omega); have h1 := h 1 (by omega); have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  simp only [bytesT1, Nat.add_zero] at h0 h1 h2 h3
  simp only [bytesT4, h0, h1, h2, h3]

/-- The facts `fflush`/`fwrite`'s at-lemmas read off `StdioUp`, at the
generator's literal addresses. -/
theorem StdioUp.impure' {m : Mem} (hu : StdioUp m) : bytesT8 m 0x8005d398 = 0x8005d1b8#64 := hu.impure
theorem StdioUp.flags2' {m : Mem} (hu : StdioUp m) : bytesT4 m 0x8005e718 = 0x0#32 := hu.flags2
theorem StdioUp.init' {m : Mem} (hu : StdioUp m) : (bytesT8 m 0x8005d200 == 0x0#64) = false := by
  have h : bytesT8 m 0x8005d200 ≠ 0#64 := hu.init
  simpa only [beq_eq_false_iff_ne] using h
theorem StdoutAt.flags' {m : Mem} {buf : Nat} {pend : List (BitVec 8)} (hs : StdoutAt m buf pend) :
    bytesT2 m 0x8005e678 = 0x2889#16 := hs.flags

end Lua.Vm.Sim.Kit

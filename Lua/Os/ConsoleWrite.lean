import Lua.Os.Htif
import Lua.Vm.Sim.Kit.Write

/-!
# The proved console machine runs against the OS specification

This bridge consumes `Kit.write_console_sum`, whose generated segments and HTIF
seam supply the actual Sail execution. It establishes a full console write
for every buffer under that summary's frame and descriptor preconditions.
It does not discharge `HtifPrint_Statement`: a persistent OS representation,
its frame, stdin and console fstat remain separate obligations.
-/

namespace Lua.Os

open Vsa.Machine Lua.Vm Lua.Vm.Layout Lua.Vm.Sim Lua.Vm.Sim.Kit
open Vsa.Sim LeanRV64DExecutable Sail TCB.Os

/-- A complete write is one of the spec's allowed stdout/stderr writes. -/
theorem osStep_write_full (st : OsState) (fd : Nat) (stream : Stream) (bs : List UInt8)
    (hfd : lookupFd st fd = some (.stream stream))
    (hstream : stream = .stdout ∨ stream = .stderr)
    (hlive : st.proc.exited = none) :
    OsStep st (.write fd bs bs.length) (.num bs.length)
      { st with streams := st.streams.doWrite stream bs } := by
  rcases hstream with rfl | rfl <;>
    simp only [OsStep, next, hlive, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      outs, osWrite, hfd]
  all_goals
    apply List.mem_filterMap.mpr
    refine ⟨_, List.mem_map.mpr ⟨bs.length, by simp [Streams.writeLengths], rfl⟩, ?_⟩
    simp [Ret.matches]

/-- Present bytes read by the ABI decoder are the total bytes read by the
machine summary. Presence is required by `HtifCallAt`, not by `write_sum`. -/
theorem bytesAt_of_BytesAt {m : Mem} {buf : Nat} {bs : List UInt8}
    (h : BytesAt m buf bs) : bytesAt m buf bs.length = bs.map UInt8.toBitVec := by
  apply List.ext_getElem
  · simp [bytesAt]
  · intro i hi hj
    simp only [bytesAt, List.getElem_map, List.getElem_range]
    simp only [bytesT1, h i (by simpa using hj), Option.getD_some]
    simp only [UInt8.toNat, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- A full machine-call result, including the exact memory/ABI summary
needed to preserve a future OS representation across the call. -/
structure ConsoleWriteResult (fd : Nat) (stream : Stream) (c : Config) (st : OsState) (sp buf : Nat)
    (bs : List UInt8) (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (c' : Config) : Prop where
  run : Steps c c'
  call : HtifCallAt c (.write fd bs bs.length)
  returns : ReturnsTo c c'
  result : HtifRetAt (.write fd bs bs.length) c c' (.num bs.length)
  spec : OsStep st (.write fd bs bs.length) (.num bs.length)
    { st with streams := st.streams.doWrite stream bs }
  console : ConsoleAt c' { st with streams := st.streams.doWrite stream bs }
  frame : wrRet r sp bs.length f (wrMem m sp r) (pushes o (bytesAt m buf bs.length)) c'

/-- The existing stdout result API, now an instance of the shared console result. -/
abbrev StdoutWriteResult := ConsoleWriteResult 1 .stdout

/-- The fd=2 boundary result. It does not assert the `fprintf` caller is proved. -/
abbrev StderrWriteResult := ConsoleWriteResult 2 .stderr

/-- `_write(fd, buf, bs.length)` refines a complete OS console write, with
actual machine steps. The entry is the summary's real machine predicate,
not an existential relation allowed to hold only at `_start`. -/
theorem console_write_refines (fd : Nat) (stream : Stream) (st : OsState) (sp buf : Nat) (bs : List UInt8)
    (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : WrConsoleCtx m fd sp buf bs.length r) (hra : r.toNat < 2 ^ 63)
    (hbs : BytesAt m buf bs) (hfd : lookupFd st fd = some (.stream stream))
    (hstream : stream = .stdout ∨ stream = .stderr)
    (hlive : st.proc.exited = none) (c : Config)
    (h : SegSt 0x80000ae8#64 (wrConsolePre fd sp buf bs.length r f) (ArmPay m o) c)
    (hc : ConsoleAt c st) :
    ∃ c', ConsoleWriteResult fd stream c st sp buf bs r f m o c' := by
  obtain ⟨c', hs, h'⟩ := write_console_sum fd sp buf bs.length r f m o hx c h
  obtain ⟨ha0, ha1, ha2, har, has, _, _⟩ := h.pins
  obtain ⟨hret, hrs, _, _⟩ := h'.pins
  have hfd_bound : fd ≤ 2 := by rcases hx.fd_console with e | e <;> omega
  have hsp := hx.sp_hi
  have hbuf := hx.buf_hi
  refine ⟨c', ?_⟩
  refine {
    run := hs
    call := ?_
    returns := ?_
    result := ?_
    spec := osStep_write_full st fd stream bs hfd hstream hlive
    console := ?_
    frame := h' }
  · apply HtifCallAt.write (buf := buf)
    · exact h.pcAt
    · exact ⟨by omega, ha0⟩
    · exact ⟨by omega, ha1⟩
    · exact ⟨by omega, ha2⟩
    · rw [h.armMem]; exact hbs
    · rfl
  · exact .mk r.toNat ⟨hra, by simpa [gprGet] using har⟩ (by simpa [PcAt] using h'.pcAt)
      (by change _ = _; exact hrs.trans has.symm)
  · exact .num rfl ⟨by omega, hret⟩
  · unfold ConsoleAt at hc ⊢
    change (String.join c'.σ.sailOutput.toList).toList = _
    rw [h'.armOut, output_pushes, String.toList_append]
    have hold : (String.join o.toList).toList =
        st.streams.console.map (fun b => Char.ofNat b.toNat) := by
      simpa only [output, h.armOut] using hc
    rw [hold, bytesAt_of_BytesAt hbs]
    rcases hstream with rfl | rfl <;> simp [Streams.doWrite, charsOf, List.map_map]

/-- `_write(1, buf, bs.length)` refines a full stdout write. Its API and
preconditions are unchanged. -/
theorem stdout_write_refines (st : OsState) (sp buf : Nat) (bs : List UInt8)
    (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : WrCtx m sp buf bs.length r) (hra : r.toNat < 2 ^ 63)
    (hbs : BytesAt m buf bs) (hfd : lookupFd st 1 = some (.stream .stdout))
    (hlive : st.proc.exited = none) (c : Config)
    (h : SegSt 0x80000ae8#64 (wrPre sp buf bs.length r f) (ArmPay m o) c)
    (hc : ConsoleAt c st) :
    ∃ c', StdoutWriteResult c st sp buf bs r f m o c' :=
  console_write_refines 1 .stdout st sp buf bs r f m o hx.console hra hbs hfd (.inl rfl) hlive c h hc

/-- `_write(2, buf, bs.length)` refines a full stderr write, with the real
finite Sail run, exact console append and memory/ABI frame, even for no bytes.
`FprintfErr` and the persistent `HtifPrint` representation remain obligations. -/
theorem stderr_write_refines (st : OsState) (sp buf : Nat) (bs : List UInt8)
    (r : BitVec 64) (f : AbiFrame) (m : Mem) (o : Array String)
    (hx : WrConsoleCtx m 2 sp buf bs.length r) (hra : r.toNat < 2 ^ 63)
    (hbs : BytesAt m buf bs) (hfd : lookupFd st 2 = some (.stream .stderr))
    (hlive : st.proc.exited = none) (c : Config)
    (h : SegSt 0x80000ae8#64 (wrConsolePre 2 sp buf bs.length r f) (ArmPay m o) c)
    (hc : ConsoleAt c st) :
    ∃ c', StderrWriteResult c st sp buf bs r f m o c' :=
  console_write_refines 2 .stderr st sp buf bs r f m o hx hra hbs hfd (.inr rfl) hlive c h hc

end Lua.Os

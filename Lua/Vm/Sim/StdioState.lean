import Lua.Vm.Runtime
import Lua.Vm.Sim.Mem

/-!
# `stdout`'s state between `print`s and the bytes a `print` keeps

The predicates the `CALL` invariant (`Lua.Vm.Sim.CallInv`, `Rel.lean`) states
about the complement, below the relation (lanes F1-6..12 defined them in
`Kit/`; lane F1-13 moved them here unchanged): `stdout`'s phases
(`StdoutPh`, `StdoutIn`: boot, after an empty write, set up), the words
`luaB_print` reads (`PrintCells`), the bytes a `print`'s Lua side keeps
(`Kept`), and the facts **frozen on a footprint** (`Frozen`): a predicate of
every memory that agrees with this one there, which a change off the
footprint keeps (`Frozen.trans`), the one region lemma the arms need.
-/

open Vsa Vsa.Sim

namespace Lua.Vm.Sim.Kit

open Lua.Vm Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify

/-- newlib's `stdout`, the second of the three standard `FILE`s (`__sf`). -/
def stdoutFile : Nat := symSf + fileSize

/-- `__sinit`'s cleanup hook (`_REENT->__cleanup`) and the exit handler
(`__stdio_exit_handler`), `cleanup_stdio` and `stdio_exit_handler`. -/
abbrev symCleanupStdio : Nat := 0x80032b0c
abbrev symStdioExitHandlerFn : Nat := 0x80032af8

/-- The `n` bytes from `lo`. -/
def Rng (lo n a : Nat) : Prop := lo ≤ a ∧ a < lo + n

/-- The bytes `[buf, buf + n)` of `m`, in order. -/
def bytesAt (m : Mem) (buf n : Nat) : List (BitVec 8) := (List.range n).map fun i => bytesT1 m (buf + i)

/-- `stdin`, `stderr`: the first and third `FILE` of `__sf`. -/
abbrev stdinFile : Nat := symSf
abbrev stderrFile : Nat := symSf + 2 * fileSize

/-- newlib's `__sclose` (every standard stream's `_close` hook). -/
abbrev symSclose : Nat := 0x80035004

/-- **`stdout`'s words past its hooks that `exit` reads** (lane F1-14), as
`std()` and the `.bss` left them: `_close = __sclose`, no `ungetc` buffer
(`_ub`), no line buffer (`_lb`). No `print` writes them. -/
structure StdoutTail (m : Mem) : Prop where
  close : bytesT8 m (stdoutFile + 80) = BitVec.ofNat 64 symSclose
  ub : bytesT8 m (stdoutFile + 88) = 0#64
  lb : bytesT8 m (stdoutFile + 120) = 0#64

/-- **htif.c's standard descriptors after `fs_init`** (lane F1-14):
`fds[0]` the console's input, `fds[2]` its error output (`fds[1]` is
`StdoutAtW.stdout`); `exit`'s `_close(0)`/`_close(2)` read them. -/
structure FdsStd (m : Mem) : Prop where
  fd0 : bytesT4 m symFds = 1#32
  fd2 : bytesT4 m (symFds + 48) = 3#32

/-- **newlib's stdio set up** (after the first `fwrite`): the words the
`fwrite`/`fflush` entries test, and (lane F1-14) `stdout`'s tail and the
standard descriptors, which `exit`'s `_fclose_r` reads. -/
structure StdioUp (m : Mem) : Prop where
  /-- `_REENT` -/
  impure : bytesT8 m symImpurePtr = BitVec.ofNat 64 symImpureData
  /-- `CHECK_INIT` (`ld a5, 72(ptr)`): `__sinit` ran -/
  init : bytesT8 m (symImpureData + reentCleanupOff) ≠ 0#64
  /-- `_flags2`: the stream is locked through the no-op `__retarget_lock_*` -/
  flags2 : bytesT4 m (stdoutFile + fileFlags2Off) = 0#32
  tail : StdoutTail m
  fds : FdsStd m

/-- **newlib's `stdout`, set up and line-buffered**, its buffer at `buf`
holding `pend` (up to a full buffer), its write count `_w` the word `wv`
(`StdoutAt`: `-|pend|`; `__sfvwrite_r`'s fill path advances `_p` alone
before the flush, which resets `_w` without reading it). -/
structure StdoutAtW (m : Mem) (buf : Nat) (pend : List (BitVec 8)) (wv : BitVec 32) : Prop where
  p : bytesT8 m (stdoutFile + fileBufPOff) = BitVec.ofNat 64 (buf + pend.length)
  w : bytesT4 m (stdoutFile + fileWOff) = wv
  flags : bytesT2 m (stdoutFile + fileFlagsOff) = 0x2889#16
  file : bytesT2 m (stdoutFile + fileFileOff) = 1#16
  base : bytesT8 m (stdoutFile + fileBfBaseOff) = BitVec.ofNat 64 buf
  size : bytesT4 m (stdoutFile + fileBfSizeOff) = 1024#32
  lbf : bytesT4 m (stdoutFile + fileLbfsizeOff) = 0#32 - 1024#32
  cookie : bytesT8 m (stdoutFile + fileCookieOff) = BitVec.ofNat 64 stdoutFile
  write : bytesT8 m (stdoutFile + fileWriteOff) = BitVec.ofNat 64 symSwrite
  bytes : bytesAt m buf pend.length = pend
  room : pend.length ≤ 1024
  /-- the buffer is heap memory: above the C runtime's globals, apart from `stdout` -/
  buf_lo : stdoutFile + fileSize ≤ buf
  buf_hi : buf + 1024 ≤ 2 ^ 32
  /-- htif.c's descriptor table: `fs_init` ran, `fds[1]` is the console -/
  ready : bytesT4 m symFsReady ≠ 0#32
  stdout : bytesT4 m (symFds + 24) = 2#32

/-- **`stdout` between calls**: `_w = -|pend|`. -/
abbrev StdoutAt (m : Mem) (buf : Nat) (pend : List (BitVec 8)) : Prop :=
  StdoutAtW m buf pend (0#32 - BitVec.ofNat 32 pend.length)

/-- **`stdout` as `std()` and `_fwrite_r`'s `ORIENT` leave it** (`__sinit`
ran; `_flags` `__SORD | __SWR | __SLBF`, file 1, no buffer), htif.c's tables
before `fs_init`. -/
structure StdoutFresh (m : Mem) : Prop where
  impure : bytesT8 m symImpurePtr = BitVec.ofNat 64 symImpureData
  cleanup : bytesT8 m (symImpureData + reentCleanupOff) = BitVec.ofNat 64 symCleanupStdio
  flags : bytesT2 m (stdoutFile + 16) = 0x2009#16
  file : bytesT2 m (stdoutFile + 18) = 1#16
  pad : bytesT4 m (stdoutFile + 20) = 0#32
  base : bytesT8 m (stdoutFile + 24) = 0#64
  cookie : bytesT8 m (stdoutFile + 48) = BitVec.ofNat 64 stdoutFile
  write : bytesT8 m (stdoutFile + 64) = BitVec.ofNat 64 symSwrite
  flags2 : bytesT4 m (stdoutFile + 176) = 0#32
  fs : bytesT4 m symFsReady = 0#32
  tail : StdoutTail m

/-- **A standard stream `exit` closes quietly** (lane F1-14): read-only or
unbuffered as `std()` left it (`_flags` `fl`, `_file` `fd`; no `__SWR`, no
`__SMBF`), nothing read ahead (`_r`, `_ur`), no `ungetc` or line buffer,
`_close = __sclose` on the cookie `fp`, `_flags2 = 0`: `_fclose_r` flushes
nothing and frees nothing. -/
structure StdQuiet (m : Mem) (fp : Nat) (fl fd : BitVec 16) : Prop where
  r : bytesT4 m (fp + 8) = 0#32
  flags : bytesT2 m (fp + 16) = fl
  file : bytesT2 m (fp + 18) = fd
  cookie : bytesT8 m (fp + 48) = BitVec.ofNat 64 fp
  close : bytesT8 m (fp + 80) = BitVec.ofNat 64 symSclose
  ub : bytesT8 m (fp + 88) = 0#64
  ur : bytesT4 m (fp + 112) = 0#32
  lb : bytesT8 m (fp + 120) = 0#64
  flags2 : bytesT4 m (fp + 176) = 0#32

/-- **What `exit` reads of stdio besides `stdout`** once `__sinit` ran (lane
F1-14): the exit handler `stdio_exit_handler`, `__sglue` (only `__sf`'s three
streams), `stdin` and `stderr` quiet. `print` writes none of it after
`__sinit` (`RestFoot`). -/
structure StdioRest (m : Mem) : Prop where
  handler : bytesT8 m symStdioExitHandler = BitVec.ofNat 64 symStdioExitHandlerFn
  glue_next : bytesT8 m symSglue = 0#64
  glue_niobs : bytesT4 m (symSglue + 8) = 3#32
  glue_iobs : bytesT8 m (symSglue + 16) = BitVec.ofNat 64 symSf
  stdin : StdQuiet m stdinFile 0x4#16 0#16
  stderr : StdQuiet m stderrFile 0x12#16 2#16

/-- The bytes `StdioRest` reads: the handler, `__sglue`, `stdin`, `stderr`. -/
def RestFoot (a : Nat) : Prop :=
  (symStdioExitHandler ≤ a ∧ a < symStdioExitHandler + 8) ∨ (symSglue ≤ a ∧ a < symSglue + 24) ∨
  (stdinFile ≤ a ∧ a < stdinFile + fileSize) ∨ (stderrFile ≤ a ∧ a < stderrFile + fileSize)

/-- **The phases of `stdout` between `print`'s writes.** -/
inductive StdoutPh where
  /-- before the first write (`StdioBoot`) -/
  | boot
  /-- after an empty first write: `__sinit` ran, no buffer (`StdoutFresh`) -/
  | fresh
  /-- set up, `pend` pending in the buffer `buf` (`StdoutAt`, `StdioUp`) -/
  | up (buf : Nat) (pend : List (BitVec 8))

/-- The bytes pending in `stdout`'s buffer. -/
def StdoutPh.pend : StdoutPh → List (BitVec 8)
  | .up _ p => p
  | _ => []

/-- The buffer's bytes, once there is one. -/
def StdoutPh.Buf : StdoutPh → Nat → Prop
  | .up buf _, a => Rng buf 1024 a
  | _, _ => False

/-- The heap's indices (`HeapAt`'s). -/
structure HeapIx where
  top : Nat
  brk : Nat
  chunks : List Chunk
  bins : Nat → List Nat

/-- `buf` is the payload of a chunk in use, in the arena. -/
structure BufOwned (H : HeapIx) (buf : Nat) : Prop where
  block : ∃ sz, (⟨buf - 16, sz, true⟩ : Chunk) ∈ H.chunks ∧ 1024 + 8 ≤ sz
  lo : heapStart + 16 ≤ buf
  hi : buf + 1024 ≤ heapEnd

/-- **`stdout` in phase `ph`** over `m`, with the heap `H`: before the
buffer, room for it (`_malloc_r`'s `_sbrk`); after, the buffer owned. -/
inductive StdoutIn (m : Mem) (H : HeapIx) : StdoutPh → Prop where
  | boot : StdioBoot (fillZeroMem m) → MemfsBoot (fillZeroMem m) → H.brk + 1024 + 16384 ≤ heapEnd →
      StdoutIn m H .boot
  | fresh : StdoutFresh m → H.brk + 1024 + 16384 ≤ heapEnd → StdioRest m → StdoutIn m H .fresh
  | up {buf : Nat} {pend : List (BitVec 8)} : StdoutAt m buf pend → StdioUp m → BufOwned H buf →
      StdioRest m → StdoutIn m H (.up buf pend)

/-- The words `luaB_print` reads itself (`_impure_ptr`, `_REENT->_stdout`) and
its two literals (`"\t"`, `"\n"` in `.rodata`). -/
structure PrintCells (m : Mem) : Prop where
  impure : bytesT8 m 0x8005d398 = 0x8005d1b8#64
  stdout : bytesT8 m 0x8005d1c8 = 0x8005e668#64
  tab : bytesAt m 0x8004ff40 1 = [0x09#8]
  nl : bytesAt m 0x8004fb48 1 = [0x0a#8]

/-- **A byte a `print`'s Lua side keeps**: in a chunk in use of the heap, in
the arena, apart from `stdout`'s buffer. -/
structure Kept (H : HeapIx) (ph : StdoutPh) (a : Nat) : Prop where
  inuse : InUse H.chunks a
  lo : heapStart ≤ a
  hi : a < heapEnd
  nbuf : ¬ ph.Buf a

/-! ## Facts frozen on a footprint -/

/-- **`P` is frozen on `F` at `m`**: it holds of every memory that agrees with
`m` on `F` (total reads). -/
def Frozen (F : Nat → Prop) (P : Mem → Prop) (m : Mem) : Prop :=
  ∀ M : Mem, (∀ a, F a → bytesT1 M a = bytesT1 m a) → P M

/-- **The region lemma**: a change off the footprint keeps frozen facts. -/
theorem Frozen.trans {F : Nat → Prop} {P : Mem → Prop} {m m' : Mem} (h : Frozen F P m)
    (hk : ∀ a, F a → bytesT1 m' a = bytesT1 m a) : Frozen F P m' :=
  fun M hM => h M fun a ha => (hM a ha).trans (hk a ha)

/-- Frozen facts hold of the memory itself. -/
theorem Frozen.self {F : Nat → Prop} {P : Mem → Prop} {m : Mem} (h : Frozen F P m) : P m :=
  h m fun _ _ => rfl

/-- Frozen facts give their consequences. -/
theorem Frozen.conseq {F : Nat → Prop} {P Q : Mem → Prop} {m : Mem} (h : Frozen F P m)
    (hPQ : ∀ M, P M → Q M) : Frozen F Q m :=
  fun M hM => hPQ M (h M hM)

/-! ## What `exit` reads, across byte agreement (lane F1-14) -/

private theorem b2T {m m' : Mem} {a : Nat} (h : ∀ i, i < 2 → bytesT1 m' (a + i) = bytesT1 m (a + i)) :
    bytesT2 m' a = bytesT2 m a := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide)
  simp only [bytesT1, Nat.add_zero] at h0 h1
  simp only [bytesT2, h0, h1]

theorem StdQuiet.congrT {m m' : Mem} {fp : Nat} {fl fd : BitVec 16} (h : StdQuiet m fp fl fd)
    (hk : ∀ a, fp ≤ a → a < fp + fileSize → bytesT1 m' a = bytesT1 m a) : StdQuiet m' fp fl fd := by
  have : fileSize = 184 := rfl
  exact ⟨(bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.r,
    (b2T fun i _ => hk _ (by omega) (by omega)).trans h.flags,
    (b2T fun i _ => hk _ (by omega) (by omega)).trans h.file,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.cookie,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.close,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ub,
    (bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ur,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.lb,
    (bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.flags2⟩

/-- **Where `RestFoot` lies**: in the stdio globals, apart from `stdout`,
`errno` and htif.c's tables. -/
theorem RestFoot.range {a : Nat} (h : RestFoot a) :
    0x8005cee0 ≤ a ∧ a < 0x8005e7d8 ∧ (a < 0x8005e668 ∨ 0x8005e720 ≤ a) ∧
      (a < 0x8005d3c0 ∨ 0x8005d3e0 ≤ a ∧ a < 0x8005d3e8 ∨ 0x8005e5b0 ≤ a) := by
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : fileSize = 184 := rfl
  simp only [RestFoot, stdinFile, stderrFile] at h
  omega

/-- **`exit`'s other stdio words across a change off `RestFoot`.** -/
theorem StdioRest.congrT {m m' : Mem} (h : StdioRest m) (hk : ∀ a, RestFoot a → bytesT1 m' a = bytesT1 m a) :
    StdioRest m' := by
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symSglue = 0x8005cee0 := rfl
  exact ⟨(bytesT8_congrT fun i _ => hk _ (.inl ⟨by omega, by omega⟩)).trans h.handler,
    (bytesT8_congrT fun i _ => hk _ (.inr (.inl ⟨by omega, by omega⟩))).trans h.glue_next,
    (bytesT4_congrT fun i _ => hk _ (.inr (.inl ⟨by omega, by omega⟩))).trans h.glue_niobs,
    (bytesT8_congrT fun i _ => hk _ (.inr (.inl ⟨by omega, by omega⟩))).trans h.glue_iobs,
    h.stdin.congrT fun a h1 h2 => hk a (.inr (.inr (.inl ⟨h1, h2⟩))),
    h.stderr.congrT fun a h1 h2 => hk a (.inr (.inr (.inr ⟨h1, h2⟩)))⟩

theorem StdoutTail.congrT {m m' : Mem} (h : StdoutTail m)
    (hk : ∀ a, stdoutFile + 80 ≤ a → a < stdoutFile + 128 → bytesT1 m' a = bytesT1 m a) : StdoutTail m' :=
  ⟨(bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.close,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.ub,
    (bytesT8_congrT fun i _ => hk _ (by omega) (by omega)).trans h.lb⟩

theorem FdsStd.congrT {m m' : Mem} (h : FdsStd m)
    (hk : ∀ a, symFds ≤ a → a < symFds + 52 → bytesT1 m' a = bytesT1 m a) : FdsStd m' :=
  ⟨(bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.fd0,
    (bytesT4_congrT fun i _ => hk _ (by omega) (by omega)).trans h.fd2⟩

end Lua.Vm.Sim.Kit

namespace Lua.Vm.Sim

open Lua.Vm.Layout

/-- A little-endian read depends only on its bytes. -/
theorem rdLE_congr {m m' : Mem} {a n : Nat} (h : ∀ i, i < n → m'[a + i]? = m[a + i]?) :
    rdLE m' a n = rdLE m a n := by
  unfold rdLE
  have : ∀ l : List Nat, (∀ i ∈ l, i < n) →
      l.foldr (fun i acc => do let b ← m'[a + i]?; let r ← acc; pure (b.toNat + 256 * r)) (some 0) =
        l.foldr (fun i acc => do let b ← m[a + i]?; let r ← acc; pure (b.toNat + 256 * r)) (some 0) := by
    intro l hl
    induction l with
    | nil => rfl
    | cons x t ih =>
      simp only [List.foldr_cons]
      rw [h x (hl x (List.mem_cons_self ..)), ih fun i hi => hl i (List.mem_cons_of_mem _ hi)]
  exact this _ fun i hi => List.mem_range.mp hi

namespace Kit

/-- The stdio globals: `__sglue`, `_impure_data`, htif.c's tables, the
handlers, `__sf`. -/
def StdioGlob (a : Nat) : Prop := 0x8005cee0 ≤ a ∧ a < 0x8005e7d8

/-- (lane F1-14) **The allocator's words among the stdio globals**
(`__malloc_sbrk_base`, `brk.0`, `__malloc_max_total_mem`,
`__malloc_max_sbrked_mem`, `__malloc_top_pad`, `errno`,
`__malloc_current_mallinfo`; lane F1-A0-M: `_REENT->_errno` and
`__malloc_trim_threshold`, in the ported proof's footprint): `_malloc_r` writes
them, no stdio state reads them. -/
def AllocWords (a : Nat) : Prop :=
  (0x8005d1b8 ≤ a ∧ a < 0x8005d1bc) ∨ (0x8005d388 ≤ a ∧ a < 0x8005d398) ∨ (0x8005d3b8 ≤ a ∧ a < 0x8005d3c0) ∨ (0x8005d3c8 ≤ a ∧ a < 0x8005d3e0) ∨
    (0x8005d408 ≤ a ∧ a < 0x8005d40c) ∨ (0x8005e560 ≤ a ∧ a < 0x8005e5b0)

/-- **What the stdio state reads** among the stdio globals: all but the
allocator's words, so it is kept across a `_malloc_r`. -/
def StdioFoot (a : Nat) : Prop := StdioGlob a ∧ ¬ AllocWords a

/-- A stdio word off the allocator's words, for `omega`. -/
macro "aw_off" : tactic => `(tactic| (simp only [AllocWords]; omega))

theorem _root_.Lua.Vm.StdioBoot.congrF {m m' : Mem} (h : StdioBoot m) (hk : ∀ a, StdioFoot a → m'[a]? = m[a]?) :
    StdioBoot m' := by
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symImpurePtr = 0x8005d398 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : symSglue = 0x8005cee0 := rfl
  have : symSf = 0x8005e5b0 := rfl
  have : symSfSize = 552 := rfl
  have : symAtexit = 0x8005d450 := rfl
  have : reentCleanupOff = 72 := rfl
  have : reentStdinOff = 8 := rfl
  have : reentStdoutOff = 16 := rfl
  have : reentStderrOff = 24 := rfl
  have : glueNextOff = 0 := rfl
  have : glueNiobsOff = 8 := rfl
  have : glueIobsOff = 16 := rfl
  have r : ∀ {a n : Nat}, StdioGlob a → StdioGlob (a + n - 1) → 0 < n → (∀ i, i < n → ¬ AllocWords (a + i)) →
      rdLE m' a n = rdLE m a n :=
    fun {a n} h1 h2 _ h3 => rdLE_congr fun i hi => hk _ ⟨⟨by have := h1.1; omega, by have := h2.2; omega⟩, h3 i hi⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun i hi => ?_, ?_, ?_⟩
  all_goals first
    | (simp only [rd64, rd32]; rw [r ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ (by omega) fun i hi => by aw_off])
    | skip
  · exact h.exit_handler
  · exact h.impure_ptr
  · exact h.stdin
  · exact h.stdout
  · exact h.stderr
  · exact h.glue_next
  · exact h.glue_niobs
  · exact h.glue_iobs
  · exact (hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩).trans (h.files i hi)
  · exact h.atexit
  · exact h.cleanup

theorem _root_.Lua.Vm.StdioBoot.congr {m m' : Mem} (h : StdioBoot m) (hk : ∀ a, StdioGlob a → m'[a]? = m[a]?) :
    StdioBoot m' := h.congrF fun a ha => hk a ha.1

theorem _root_.Lua.Vm.MemfsBoot.congrF {m m' : Mem} (h : MemfsBoot m) (hk : ∀ a, StdioFoot a → m'[a]? = m[a]?) :
    MemfsBoot m' := by
  have : symFsReady = 0x8005d3c0 := rfl
  have : symFds = 0x8005d460 := rfl
  have : symFdsSize = 768 := rfl
  have : symFiles = 0x8005d760 := rfl
  have : symFilesSize = 3584 := rfl
  refine ⟨?_, fun i hi => (hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩).trans (h.fds i hi),
    fun i hi => (hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩).trans (h.files i hi)⟩
  simp only [rd32]
  rw [rdLE_congr fun i hi => hk _ ⟨⟨by omega, by omega⟩, by aw_off⟩]
  exact h.ready

theorem _root_.Lua.Vm.MemfsBoot.congr {m m' : Mem} (h : MemfsBoot m) (hk : ∀ a, StdioGlob a → m'[a]? = m[a]?) :
    MemfsBoot m' := h.congrF fun a ha => hk a ha.1

end Kit

end Lua.Vm.Sim

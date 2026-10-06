import Lua.Vm.Sim.Kit.Fwrite
import Lua.Vm.Sim.Kit.Memchr
import Lua.Vm.AtF.Sfvwrite

/-!
# `__sfvwrite_r`'s line-buffered loop (lane F1-9)

`SfvwriteLbf_Statement` over the generated at-lemmas
(`Lua/Vm/AtF/Sfvwrite.lean`, `gen_lua_at.py --fn __sfvwrite_r`). The
generator's roots: the entry, the loop head `0x80033dac` (`a0` = "newline
known"), the step body `0x80033db0` (the newline distance known), the step
size `0x80033dbc` (`s = min(len, nldist)`) and the nine call returns
(`memchr` ×2 return values, `memmove` for a copy and for a fill,
`__swrite`, `_fflush_r` after a fill and after a newline). Every root shares
one atom layout: `X.n 0 … 4` = `sp`, uio, iov, `n`, `src`; `X.n 20 … 25` =
`s2`, `s3`, `s6`, `s7` (bytes left), `s8` (newline distance), `s9` (cursor);
`X.b 0 … 12` = `ra` and the caller's `s0`–`s11`.

The loop is `seg_loop` over the head on `2·len + [buffer full]` (a fill of
a full buffer consumes nothing but empties it). The invariant (`SfvSt`):
`stdout` set up holding `pend`, the console gained `out` with
`out ++ pend = pend₀ ++ (the bytes consumed)`, the saved frame, and the
caller's bytes kept (`SfvKeep`). Each call return is one splice: the
callee's summary (`memchr_nl`, `memmove_sum`, `swrite_sum`,
`fflush_r_stdout`) carries the invariant (`sfv_flush`, `sfv_move`,
`sfv_swrite`, `sfv_mc`), and the root's context is the next root's with the
re-bound registers.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-! ## The run's data and invariant -/

/-- The fixed data of a `__sfvwrite_r` run: its frame `sp`, `stdout`'s
buffer, the uio and its iov, the `n` bytes at `src`, the pending bytes on
entry, `ra`, the caller's frame, the entry memory and console. -/
structure SfvG where
  sp : Nat
  buf : Nat
  U : Nat
  I : Nat
  src : Nat
  n : Nat
  pend0 : List (BitVec 8)
  r : BitVec 64
  f : AbiFrame
  m : Mem
  o : Array String

/-- The hypotheses of `SfvwriteLbf_Statement` on the run's data. -/
structure SfvG.Ok (G : SfvG) : Prop where
  ra : G.r.toNat % 4 = 0
  sp_hi : G.sp ≤ 2 ^ 32
  sp_al : G.sp % 16 = 0
  buf_lo : stdoutFile + fileSize ≤ G.buf
  buf_sp : G.buf + 3584 ≤ G.sp
  i_ge : G.sp ≤ G.I
  i_u : G.I + 16 ≤ G.U
  u_hi : G.U + 24 ≤ G.sp + 2048
  u_top : G.U + 24 ≤ 2 ^ 32
  u_al : G.U % 8 = 0
  i_al : G.I % 8 = 0
  src_lo : errnoAddr + 4 ≤ G.src
  src_hi : G.src + G.n + 3072 ≤ G.sp
  src_buf : G.src + G.n ≤ G.buf ∨ G.buf + 1024 ≤ G.src
  src_file : G.src + G.n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ G.src

/-- The numbers of the run, for `omega`. -/
macro "sfv_nums " hG:term : tactic => `(tactic| (
  stdio_nums
  have : errnoAddr = 0x8005d408 := rfl
  have := ($hG).ra; have := ($hG).sp_hi; have := ($hG).sp_al; have := ($hG).buf_lo; have := ($hG).buf_sp
  have := ($hG).i_ge; have := ($hG).i_u; have := ($hG).u_hi; have := ($hG).u_top; have := ($hG).u_al; have := ($hG).i_al
  have := ($hG).src_lo; have := ($hG).src_hi; have := ($hG).src_buf; have := ($hG).src_file))

/-- A root's context on the run: the atoms the generator fixed. -/
structure SfvAt (G : SfvG) (X : FCx) : Prop where
  sp : X.n 0 = G.sp
  U : X.n 1 = G.U
  I : X.n 2 = G.I
  n : X.n 3 = G.n
  src : X.n 4 = G.src
  r : X.b 0 = G.r
  s0 : X.b 1 = G.f.s0
  s1 : X.b 2 = G.f.s1
  s2 : X.b 3 = G.f.s2
  s3 : X.b 4 = G.f.s3
  s4 : X.b 5 = G.f.s4
  s5 : X.b 6 = G.f.s5
  s6 : X.b 7 = G.f.s6
  s7 : X.b 8 = G.f.s7
  s8 : X.b 9 = G.f.s8
  s9 : X.b 10 = G.f.s9
  s10 : X.b 11 = G.f.s10
  s11 : X.b 12 = G.f.s11

/-- `__sfvwrite_r`'s saved registers in its frame `[sp - 88, sp)`. -/
structure SfvFrame (G : SfvG) (M : Mem) : Prop where
  ra : bytesT8 M (G.sp - 8) = G.r
  s0 : bytesT8 M (G.sp - 16) = G.f.s0
  s1 : bytesT8 M (G.sp - 24) = G.f.s1
  s2 : bytesT8 M (G.sp - 32) = G.f.s2
  s3 : bytesT8 M (G.sp - 40) = G.f.s3
  s4 : bytesT8 M (G.sp - 48) = G.f.s4
  s5 : bytesT8 M (G.sp - 56) = G.f.s5
  s6 : bytesT8 M (G.sp - 64) = G.f.s6
  s7 : bytesT8 M (G.sp - 72) = G.f.s7
  s8 : bytesT8 M (G.sp - 80) = G.f.s8
  s9 : bytesT8 M (G.sp - 88) = G.f.s9

/-- **The loop's invariant** on a memory `M` and console `o`: `stdout`
holding `pend` (its `_w` the word `wv`), the console gained `out` with
`out ++ pend = pend₀ ++ (the q bytes consumed)`, the frame, the caller's
bytes. -/
structure SfvSt (G : SfvG) (M : Mem) (o : Array String) (pend : List (BitVec 8)) (wv : BitVec 32)
    (q : Nat) : Prop where
  stdout : StdoutAtW M G.buf pend wv
  up : StdioUp M
  out : ∃ out, o = pushes G.o out ∧ out ++ pend = G.pend0 ++ bytesAt G.m G.src q
  frame : SfvFrame G M
  keep : SfvKeep G.m M G.sp G.buf G.U
  q_le : q ≤ G.n

/-- The run's result: `0` returned, the console gained `out`, the buffer
holds `pend'`. -/
def SfvPost (G : SfvG) (c : Config) : Prop :=
  ∃ m' out pend', wrRet G.r G.sp 0 G.f m' (pushes G.o out) c ∧ StdoutAt m' G.buf pend' ∧ StdioUp m' ∧
    out ++ pend' = G.pend0 ++ bytesAt G.m G.src G.n ∧ SfvKeep G.m m' G.sp G.buf G.U

/-! ## Values the rows compute -/

theorem ofNat64_toNat (v : BitVec 64) : BitVec.ofNat 64 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq; simp

theorem sub_ofNat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show a - b < 2 ^ 64 by omega)]
  omega

/-- `subw`: a 32-bit difference that fits. -/
theorem subw_nat {a b : Nat} (hb : b ≤ a) (ha : a < 2 ^ 32) (hd : a - b < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 a) 31 0 -
      Sail.BitVec.extractLsb (BitVec.ofNat 64 b) 31 0) = BitVec.ofNat 64 (a - b) := by
  have e : a = b + (a - b) := by omega
  conv => lhs; rw [e]
  exact subw_len (by omega) hd

/-- `addiw rd, rs, 1`. -/
theorem addiw1 {a : Nat} (h : a + 1 < 2 ^ 31) :
    sign_extend (m := 64) (Sail.BitVec.extractLsb (BitVec.ofNat 64 a + sign_extend (m := 64) (0x001#12)) 31 0) =
      BitVec.ofNat 64 (a + 1) := by
  rw [show (0x001#12 : BitVec 12) = BitVec.ofNat 12 1 from rfl, add_imm a 1 (by decide)]
  have := subw_nat (a := a + 1) (b := 0) (by omega) (by omega) (by omega)
  rw [show Sail.BitVec.extractLsb (BitVec.ofNat 64 0) 31 0 = 0#32 by decide, BitVec.sub_zero] at this
  simpa using this

/-- `slt`/`blt` on two values that fit. -/
theorem slt_nat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    zopz0zI_s (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  have ea : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  have eb : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  unfold zopz0zI_s
  rw [ea, eb]; simp

/-- `blez`: `0 ≥ a`. -/
theorem sge0_nat {a : Nat} (ha : a < 2 ^ 63) :
    zopz0zKzJ_s (0x0#64) (BitVec.ofNat 64 a) = decide (a = 0) := by
  have ea : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_lt (by simp; omega)]; simp; omega
  unfold zopz0zKzJ_s
  rw [ea]; simp

/-- `fp->_w + fp->_bf._size`: the room left in the buffer. -/
abbrev sfvW (M : Mem) : BitVec 64 :=
  sign_extend (m := 64) ((Sail.BitVec.extractLsb (sign_extend (m := 64) (bytesT4 (M)
    ((0x8005e668#64) + sign_extend (m := 64) (0x00c#12)).toNat : BitVec (8 * 4))) 31 0) +
    (Sail.BitVec.extractLsb (sign_extend (m := 64) (bytesT4 (M)
    ((0x8005e668#64) + sign_extend (m := 64) (0x020#12)).toNat : BitVec (8 * 4))) 31 0))

theorem sfvW_eq {M : Mem} {buf : Nat} {pend : List (BitVec 8)} (hs : StdoutAt M buf pend) :
    sfvW M = BitVec.ofNat 64 (1024 - pend.length) := by
  have hw := hs.w; have hz := hs.size; have hr := hs.room
  rw [show stdoutFile + fileWOff = ((0x8005e668#64) + sign_extend (m := 64) (0x00c#12)).toNat from rfl] at hw
  rw [show stdoutFile + fileBfSizeOff = ((0x8005e668#64) + sign_extend (m := 64) (0x020#12)).toNat from rfl] at hz
  simp only [sfvW, hw, hz]
  generalize pend.length = l at hr
  have e : (0#32 - BitVec.ofNat 32 l) + 1024#32 = BitVec.ofNat 32 (1024 - l) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
    omega
  rw [extract_sext, extract_sext, e]
  apply BitVec.eq_of_toNat_eq
  have hl : (BitVec.ofNat 32 (1024 - l)).toNat = 1024 - l := by simp; omega
  have hm : (BitVec.ofNat 32 (1024 - l)).msb = false := by rw [BitVec.msb_eq_decide, hl]; simp; omega
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend, hm, BitVec.toNat_ofNat]
  simp; omega

/-- `uio_resid -= w`, tested against `0`. -/
theorem g_resid {M : Mem} {U len w : Nat} (h : bytesT8 M (U + 16) = BitVec.ofNat 64 len) (hU : U + 16 < 2 ^ 64)
    (hw : w ≤ len) (hl : len < 2 ^ 64) :
    ((sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 U) + sign_extend (m := 64) (0x010#12)).toNat :
      BitVec (8 * 8))) - BitVec.ofNat 64 w == 0#64) = decide (len = w) := by
  rw [show (0x010#12 : BitVec 12) = BitVec.ofNat 12 16 from rfl, add_imm U 16 (by decide), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hU, h, sext64_id, sub_ofNat hw hl, show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl,
    fbeq (by omega) (by decide)]
  simp; omega

/-- The stored `uio_resid`. -/
theorem v_resid {M : Mem} {U len w : Nat} (h : bytesT8 M (U + 16) = BitVec.ofNat 64 len) (hU : U + 16 < 2 ^ 64)
    (hw : w ≤ len) (hl : len < 2 ^ 64) :
    (sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 U) + sign_extend (m := 64) (0x010#12)).toNat :
      BitVec (8 * 8))) - BitVec.ofNat 64 w = BitVec.ofNat 64 (len - w) := by
  rw [show (0x010#12 : BitVec 12) = BitVec.ofNat 12 16 from rfl, add_imm U 16 (by decide), BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hU, h, sext64_id, sub_ofNat hw hl]

/-! ## Memory facts across the run's stores and calls -/

theorem SfvKeep.trans {m M M' : Mem} {sp buf U : Nat} (h1 : SfvKeep m M sp buf U) (h2 : SfvKeep M M' sp buf U) :
    SfvKeep m M' sp buf U :=
  ⟨fun a ha hu => (h2.keep_hi a ha hu).trans (h1.keep_hi a ha hu),
   fun a ha h3 h4 h5 => (h2.keep_lo a ha h3 h4 h5).trans (h1.keep_lo a ha h3 h4 h5)⟩

/-- A callee one frame below (`sp - 96`) keeps what the run keeps. -/
theorem SfvKeep.of_std {M M' : Mem} {sp buf U : Nat} (h : StdoutKeep M M' (sp - 96) buf) (hsp : 96 ≤ sp) :
    SfvKeep M M' sp buf U :=
  ⟨fun a ha _ => h.keep_hi a (by omega), fun a ha h3 h4 h5 => h.keep_lo a (by omega) h3 h4 h5⟩

/-- Stores the run keeps out of: its frame, `stdout`, the buffer, `errno`, `uio_resid`. -/
theorem SfvKeep.of_agree {M M' : Mem} {sp buf U : Nat}
    (h : ∀ a, ((sp ≤ a ∧ (a < U + 16 ∨ U + 24 ≤ a)) ∨ (a + 3072 ≤ sp ∧ (a < stdoutFile ∨ stdoutFile + fileSize ≤ a) ∧
      (a < buf ∨ buf + 1024 ≤ a) ∧ (a < errnoAddr ∨ errnoAddr + 4 ≤ a))) → bytesT1 M' a = bytesT1 M a) :
    SfvKeep M M' sp buf U :=
  ⟨fun a ha hu => h a (.inl ⟨ha, hu⟩), fun a ha h3 h4 h5 => h a (.inr ⟨ha, h3, h4, h5⟩)⟩

/-- The frame across stores outside it. -/
theorem SfvFrame.congr {G : SfvG} {M M' : Mem} (h : SfvFrame G M) (h88 : 88 ≤ G.sp)
    (hM : ∀ a, G.sp - 88 ≤ a → a < G.sp → bytesT1 M' a = bytesT1 M a) : SfvFrame G M' := by
  have e : ∀ k, 1 ≤ k → k ≤ 11 → bytesT8 M' (G.sp - 8 * k) = bytesT8 M (G.sp - 8 * k) :=
    fun k h1 h2 => bytesT8_congrT fun i _ => hM _ (by omega) (by omega)
  exact ⟨(e 1 (by omega) (by omega)).trans h.ra, (e 2 (by omega) (by omega)).trans h.s0,
    (e 3 (by omega) (by omega)).trans h.s1, (e 4 (by omega) (by omega)).trans h.s2,
    (e 5 (by omega) (by omega)).trans h.s3, (e 6 (by omega) (by omega)).trans h.s4,
    (e 7 (by omega) (by omega)).trans h.s5, (e 8 (by omega) (by omega)).trans h.s6,
    (e 9 (by omega) (by omega)).trans h.s7, (e 10 (by omega) (by omega)).trans h.s8,
    (e 11 (by omega) (by omega)).trans h.s9⟩

/-- `stdout` across stores that leave its words but `_flags` alone, `_flags`
rewritten with its value (`__swrite`'s `&= ~__SOFF`), and `errno`. -/
theorem StdoutAtW.congr' {m m' : Mem} {buf : Nat} {pend : List (BitVec 8)} {wv : BitVec 32}
    (hs : StdoutAtW m buf pend wv)
    (h : ∀ a, a < buf + 1024 → (a < stdoutFile + 16 ∨ stdoutFile + 18 ≤ a) → (a < errnoAddr ∨ errnoAddr + 4 ≤ a) →
      m'[a]? = m[a]?)
    (hf : bytesT2 m' (stdoutFile + fileFlagsOff) = 0x2889#16) : StdoutAtW m' buf pend wv := by
  have hb := hs.buf_lo; have hr := hs.room
  stdio_nums
  have : errnoAddr = 0x8005d408 := rfl
  refine ⟨(bT8_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.p,
    (bT4_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.w, hf,
    (bT2_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.file,
    (bT8_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.base,
    (bT4_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.size,
    (bT4_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.lbf,
    (bT8_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.cookie,
    (bT8_congr fun i _ => h _ (by omega) (by omega) (by omega)).trans hs.write, ?_, hs.room, hs.buf_lo,
    hs.buf_hi, ?_, ?_⟩
  · rw [bytesAt_congr (m := m) fun i hi => bT1_congr (h _ (by omega) (by omega) (by omega))]; exact hs.bytes
  · rw [bT4_congr fun i _ => h _ (by omega) (by omega) (by omega)]; exact hs.ready
  · rw [bT4_congr fun i _ => h _ (by omega) (by omega) (by omega)]; exact hs.stdout

theorem bytesAt_add (m : Mem) (a k : Nat) : ∀ j, bytesAt m a (k + j) = bytesAt m a k ++ bytesAt m (a + k) j
  | 0 => by simp [bytesAt]
  | j + 1 => by
    rw [← Nat.add_assoc, bytesAt_succ, bytesAt_add m a k j, bytesAt_succ, List.append_assoc, Nat.add_assoc]

/-- The bytes still to consume are the caller's. -/
theorem SfvSt.src_bytes {G : SfvG} (hG : G.Ok) {M : Mem} {o : Array String} {pend : List (BitVec 8)}
    {wv : BitVec 32} {q : Nat} (st : SfvSt G M o pend wv q) {i k : Nat} (hik : i + k ≤ G.n) :
    bytesAt M (G.src + i) k = bytesAt G.m (G.src + i) k := by
  sfv_nums hG
  exact bytesAt_congr fun j hj => st.keep.keep_lo _ (by omega) (by omega) (by omega) (by omega)

/-- `SfvSt` with `stdout`'s `_w` as between calls. -/
abbrev SfvStA (G : SfvG) (M : Mem) (o : Array String) (pend : List (BitVec 8)) (q : Nat) : Prop :=
  SfvSt G M o pend (0#32 - BitVec.ofNat 32 pend.length) q

/-! ## The calls -/

/-- **`_fflush_r(_REENT, stdout)`** from the run's frame: the pending bytes
on the console, the buffer empty, the invariant kept. -/
theorem sfv_flush {G : SfvG} (hG : G.Ok) {M : Mem} {o : Array String} {pend : List (BitVec 8)} {wv : BitVec 32}
    {q : Nat} {ret : BitVec 64} {f : AbiFrame} {c : Config} (st : SfvSt G M o pend wv q) (hret : ret.toNat % 4 = 0)
    (h : SegSt 0x80032954#64 (callPre [⟨Register.x10, BitVec.ofNat 64 symImpureData⟩,
      ⟨Register.x11, BitVec.ofNat 64 stdoutFile⟩] (G.sp - 96) ret f) (ArmPay M o) c) :
    ∃ c' M', Steps c c' ∧ wrRet ret (G.sp - 96) 0 f M' (pushes o pend) c' ∧ SfvStA G M' (pushes o pend) [] q ∧
      ∀ a, G.sp - 96 ≤ a → bytesT1 M' a = bytesT1 M a := by
  sfv_nums hG
  obtain ⟨c', s, M', hr, hs', hu', hk⟩ := fflush_r_stdout (G.sp - 96) G.buf pend ret f M o
    ⟨hret, by omega, by omega, by omega⟩ st.stdout st.up c h
  have kh : ∀ a, G.sp - 96 ≤ a → bytesT1 M' a = bytesT1 M a := hk.keep_hi
  obtain ⟨out, ho, hout⟩ := st.out
  refine ⟨c', M', s, hr, ⟨hs', hu', ⟨out ++ pend, by rw [ho, pushes_append], by rw [List.append_nil, hout]⟩,
    st.frame.congr (by omega) fun a h1 _ => kh a (by omega), st.keep.trans (SfvKeep.of_std hk (by omega)), st.q_le⟩, kh⟩

/-! ## The loop head and the run's end -/

/-- **The loop head** (`0x80033dac`) on a root context `X`: `stdout` holding
`pend`, `X.n 23` bytes left from the cursor `X.n 25`, `a0 = X.b 14` the
"newline distance `X.n 24` known" flag. -/
structure SfvHead (G : SfvG) (X : FCx) (pend : List (BitVec 8)) : Prop where
  cx : SfvAt G X
  st : SfvStA G X.m X.o pend (X.n 25 - G.src)
  res : bytesT8 X.m (G.U + 16) = BitVec.ofNat 64 (X.n 23)
  cur : X.n 25 + X.n 23 = G.src + G.n
  lo : G.src ≤ X.n 25
  len : 1 ≤ X.n 23
  nl : X.b 14 = 0#64 ∨ (X.b 14 = 1#64 ∧ 1 ≤ X.n 24 ∧ X.n 24 < 2 ^ 31)

/-- The loop's measure: two per byte left, one for a full buffer (a fill of a
full buffer consumes nothing but empties it). -/
def sfvMu (a : FCx × List (BitVec 8)) : Nat := 2 * a.1.n 23 + (if a.2.length = 1024 then 1 else 0)

/-- The loop's state at its head. -/
def SfvLoop (G : SfvG) (a : FCx × List (BitVec 8)) (c : Config) : Prop :=
  SfvHead G a.1 a.2 ∧ SegSt 0x80033dac#64 (Lua.Vm.AtF.Sfvwrite.r16 a.1) (ArmPay a.1.m a.1.o) c

/-- One step's outcome: the head again, lower, or the run's end. -/
def SfvNext (G : SfvG) (μ0 : Nat) (c : Config) : Prop :=
  (∃ a, sfvMu a < μ0 ∧ SfvLoop G a c) ∨ SfvPost G c

/-- A root's context from another's: some atoms re-bound (`ns`, `bs`: index,
value), the memory and console of the new root. -/
def _root_.Lua.Vm.Sim.AtF.FCx.set (X : FCx) (ns : List (Nat × Nat)) (bs : List (Nat × BitVec 64)) (M : Mem)
    (o : Array String) : FCx :=
  ⟨fun i => (ns.lookup i).getD (X.n i), fun i => (bs.lookup i).getD (X.b i), M, o⟩

/-- A re-bound context's atoms evaluated (for `omega`). -/
macro "sfv_set" : tactic => `(tactic| simp only [Lua.Vm.Sim.AtF.FCx.set, List.lookup, Nat.reduceBEq,
  Option.getD_some, Option.getD_none])

/-- `SfvAt` of a re-bound context (concrete lists that leave the run's atoms:
each field by definitional unfolding). -/
macro "sfv_at% " hX:term : term => `(⟨($hX).sp, ($hX).U, ($hX).I, ($hX).n, ($hX).src, ($hX).r, ($hX).s0, ($hX).s1,
  ($hX).s2, ($hX).s3, ($hX).s4, ($hX).s5, ($hX).s6, ($hX).s7, ($hX).s8, ($hX).s9, ($hX).s10, ($hX).s11⟩)

/-- A root's context facts (the generated `Ok_*`) from the run's. -/
macro "sfv_ok " hX:term : tactic => `(tactic| (
  constructor <;> simp only [($hX).sp, ($hX).U, ($hX).I, ($hX).r] <;> first | omega | assumption))

/-- **The run's end** (`0x80033c00` → `ret`): `uio_resid` stored as `0`. -/
theorem sfv_ret {G : SfvG} (hG : G.Ok) {X : FCx} (hX : SfvAt G X) {M : Mem} {pend : List (BitVec 8)} {w : Nat}
    {c : Config} (st : SfvStA G M X.o pend G.n) (res : bytesT8 M (G.U + 16) = BitVec.ofNat 64 w) (hw : w ≤ G.n)
    (h : SegSt (X.b 0) (Lua.Vm.AtF.Sfvwrite.r2 X) (ArmPay (writeMap8 M (X.n 1 + 16) (sdData_val
      ((sign_extend (m := 64) (bytesT8 M ((BitVec.ofNat 64 (X.n 1)) + sign_extend (m := 64) (0x010#12)).toNat :
        BitVec (8 * 8))) - BitVec.ofNat 64 w))) X.o) c) :
    SfvPost G c := by
  sfv_nums hG
  have hb := st.stdout.buf_lo
  rw [hX.U, v_resid res (by omega) (Nat.le_refl _) (by omega), Nat.sub_self] at h
  simp only [Lua.Vm.AtF.Sfvwrite.r2, hX.sp, hX.r, hX.s0, hX.s1, hX.s2, hX.s3, hX.s4, hX.s5, hX.s6, hX.s7, hX.s8,
    hX.s9, hX.s10, hX.s11] at h
  obtain ⟨out, ho, hout⟩ := st.out
  have kM : ∀ a, (a < G.U + 16 ∨ G.U + 16 + 8 ≤ a) →
      bytesT1 (writeMap8 M (G.U + 16) (sdData_val (BitVec.ofNat 64 0))) a = bytesT1 M a := fun a ha =>
    bytesT1_writeMap8_out _ _ _ ha
  refine ⟨_, out, pend, ?_, st.stdout.below fun a ha => getElem?_writeMap8_out _ _ _ _ (by omega),
    st.up.below fun a ha => getElem?_writeMap8_out _ _ _ _ (by omega), hout,
    st.keep.trans (SfvKeep.of_agree fun a ha => kM a (by omega))⟩
  rw [← ho]
  exact h.repin (by pins_of h)

/-- The saved frame in the form the return path's at-lemmas read it (over a
root's context `X`). -/
structure SfvFrameX (X : FCx) : Prop where
  ra : bytesT8 X.m (X.n 0 - 8) = X.b 0
  s0 : bytesT8 X.m (X.n 0 - 16) = X.b 1
  s1 : bytesT8 X.m (X.n 0 - 24) = X.b 2
  s2 : bytesT8 X.m (X.n 0 - 32) = X.b 3
  s3 : bytesT8 X.m (X.n 0 - 40) = X.b 4
  s4 : bytesT8 X.m (X.n 0 - 48) = X.b 5
  s5 : bytesT8 X.m (X.n 0 - 56) = X.b 6
  s6 : bytesT8 X.m (X.n 0 - 64) = X.b 7
  s7 : bytesT8 X.m (X.n 0 - 72) = X.b 8
  s8 : bytesT8 X.m (X.n 0 - 80) = X.b 9
  s9 : bytesT8 X.m (X.n 0 - 88) = X.b 10

theorem SfvFrame.toX {G : SfvG} {X : FCx} (hX : SfvAt G X) (h : SfvFrame G X.m) : SfvFrameX X :=
  ⟨by rw [hX.sp, hX.r]; exact h.ra, by rw [hX.sp, hX.s0]; exact h.s0, by rw [hX.sp, hX.s1]; exact h.s1,
    by rw [hX.sp, hX.s2]; exact h.s2, by rw [hX.sp, hX.s3]; exact h.s3, by rw [hX.sp, hX.s4]; exact h.s4,
    by rw [hX.sp, hX.s5]; exact h.s5, by rw [hX.sp, hX.s6]; exact h.s6, by rw [hX.sp, hX.s7]; exact h.s7,
    by rw [hX.sp, hX.s8]; exact h.s8, by rw [hX.sp, hX.s9]; exact h.s9⟩

theorem SfvSt.cast {G : SfvG} {M : Mem} {o : Array String} {pend : List (BitVec 8)} {wv : BitVec 32} {q q' : Nat}
    (st : SfvSt G M o pend wv q) (e : q = q') : SfvSt G M o pend wv q' := e ▸ st

/-- A root's atoms for `omega`. -/
macro "sfv_cx " hX:term : tactic => `(tactic| (
  have := ($hX).sp; have := ($hX).U; have := ($hX).I; have := ($hX).n; have := ($hX).src))

/-- The invariant across the store of `uio_resid` (above the frame). -/
theorem SfvSt.resid {G : SfvG} (hG : G.Ok) {M : Mem} {o : Array String} {pend : List (BitVec 8)} {wv : BitVec 32}
    {q a : Nat} (st : SfvSt G M o pend wv q) (ha : a = G.U + 16) (d : BitVec (8 * 8)) :
    SfvSt G (writeMap8 M a d) o pend wv q := by
  sfv_nums hG
  have hb := st.stdout.buf_lo
  subst ha
  exact ⟨st.stdout.below fun x hx => getElem?_writeMap8_out _ _ _ _ (by omega),
    st.up.below fun x hx => getElem?_writeMap8_out _ _ _ _ (by omega), st.out,
    st.frame.congr (by omega) fun x h1 h2 => bytesT1_writeMap8_out _ _ _ (by omega),
    st.keep.trans (SfvKeep.of_agree fun x hx => bytesT1_writeMap8_out _ _ _ (by omega)), st.q_le⟩

/-- **Back at the head** (`Y` the head's context). -/
theorem sfv_head {G : SfvG} {Y : FCx} {pend : List (BitVec 8)} {μ0 : Nat} {c : Config} (hY : SfvAt G Y)
    (st : SfvStA G Y.m Y.o pend (Y.n 25 - G.src)) (res : bytesT8 Y.m (G.U + 16) = BitVec.ofNat 64 (Y.n 23))
    (cur : Y.n 25 + Y.n 23 = G.src + G.n) (lo : G.src ≤ Y.n 25) (hlen : 1 ≤ Y.n 23)
    (nl : Y.b 14 = 0#64 ∨ (Y.b 14 = 1#64 ∧ 1 ≤ Y.n 24 ∧ Y.n 24 < 2 ^ 31))
    (hμ : 2 * Y.n 23 + (if pend.length = 1024 then 1 else 0) < μ0)
    (h : SegSt 0x80033dac#64 (Lua.Vm.AtF.Sfvwrite.r16 Y) (ArmPay Y.m Y.o) c) :
    SfvNext G μ0 c :=
  .inl ⟨(Y, pend), hμ, ⟨⟨hY, st, res, cur, lo, hlen, nl⟩, h⟩⟩

/-! ## The step's tail and the newline distance -/

/-- **The step's tail** (`0x80033e0c`, the root `T`): `w = X.n 20` bytes
consumed from the cursor `X.n 25`, `uio_resid -= w`; the run's end, or the
head. -/
theorem sfv_tail {G : SfvG} (hG : G.Ok) {X : FCx} (hX : SfvAt G X) {pend : List (BitVec 8)} {μ0 : Nat}
    (st : SfvStA G X.m X.o pend (X.n 20 + X.n 25 - G.src))
    (res : bytesT8 X.m (G.U + 16) = BitVec.ofNat 64 (X.n 23))
    (cur : X.n 25 + X.n 23 = G.src + G.n) (lo : G.src ≤ X.n 25) (hw : X.n 20 ≤ X.n 23)
    (nl : X.b 14 = 0#64 ∨ (X.b 14 = 1#64 ∧ 1 ≤ X.n 24 ∧ X.n 24 < 2 ^ 31))
    (hμ : 2 * (X.n 23 - X.n 20) + (if pend.length = 1024 then 1 else 0) < μ0) :
    Triple (SegSt 0x80033e0c#64 (Lua.Vm.AtF.Sfvwrite.r40 X) (ArmPay X.m X.o)) (SfvNext G μ0) := by
  intro c h
  sfv_nums hG
  sfv_cx hX
  have hX' : Lua.Vm.AtF.Sfvwrite.Ok_T X := by sfv_ok hX
  obtain ⟨hc13, hc14, hc9, hc10, hc11, hc15, hc16, hc12, hc6, hc7, hc8⟩ := st.frame.toX hX
  have acc := Steps.refl c
  have hres : bytesT8 X.m (X.n 1 + 16) = BitVec.ofNat 64 (X.n 23) := by rw [hX.U]; exact res
  have hg := g_resid hres (by omega) hw (by omega)
  by_cases e : X.n 23 = X.n 20
  · rw [decide_eq_true e] at hg
    fat_run Lua.Vm.AtF.Sfvwrite h acc
    rw [e] at res
    exact ⟨_, acc, .inr (sfv_ret hG hX (st.cast (by omega)) res (by omega) h)⟩
  · rw [decide_eq_false e] at hg
    have hg3 : ((BitVec.ofNat 64 (X.n 23) - BitVec.ofNat 64 (X.n 20)) != 0x0#64) = true := by
      rw [sub_ofNat hw (by omega), show (0x0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, fbne (by omega) (by decide)]
      simp; omega
    fat_run Lua.Vm.AtF.Sfvwrite h acc until [0x80033dac]
    simp only [Lua.Vm.AtF.Sfvwrite.r44, sub_ofNat hw (by omega : X.n 23 < 2 ^ 64)] at h
    have hY : SfvAt G (X.set [(23, X.n 23 - X.n 20), (25, X.n 20 + X.n 25)] [(15, BitVec.ofNat 64 (X.n 20))]
        (Lua.Vm.AtF.Sfvwrite.m5 X) X.o) := sfv_at% hX
    refine ⟨_, acc, sfv_head hY (st.resid hG (a := X.n 1 + 16) (by omega) _) ?_ (by sfv_set; omega)
      (by sfv_set; omega) (by sfv_set; omega) nl (by sfv_set; simpa using hμ) (h.repin (by pins_of h))⟩
    show bytesT8 (Lua.Vm.AtF.Sfvwrite.m5 X) (G.U + 16) = BitVec.ofNat 64 (X.n 23 - X.n 20)
    rw [fw8_same (by omega), v_resid hres (by omega) hw (by omega)]

end Lua.Vm.Sim.Kit

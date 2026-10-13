import Lua.Vm.Sim.Kit.StdoutEmpty
import Lua.Vm.Sim.Kit.HeapFill

/-!
# `print`'s writes from any state of `stdout` (lane F1-11)

`luaB_print` writes each argument's string, a `"\t"` between them and a
`"\n"`, each by `fwrite(s, 1, n, stdout)` (`lua_writestring`), then
`fflush(stdout)`. Between two writes `stdout` is in one of three phases
(`StdoutPh`): the boot state, *fresh* (an empty first write, `print("")`,
ran `__sinit` and `ORIENT` but not the set-up), or set up holding the
pending bytes `pend` in the heap buffer `buf`. `StdoutIn` states each phase
with the heap it needs; `fwrite_print` is one write from any phase, every
case proved (from `MallocR_Statement` where the buffer is allocated):

| from | `n` | proof |
|---|---|---|
| boot | `0` | `fwrite_boot0` |
| boot | `≥ 1` | `stdoutSetup_of_malloc` |
| fresh | `0` | `fwrite_fresh0` |
| fresh | `≥ 1` | `stdoutSetup_fresh` |
| up | any | `fwrite_stdout` |

The heap is stated of the zero fill (`HeapAt (fillZeroMem m)`), and what a
write keeps is a total-read region fact (`PrintKeep`): off `PrintW` every
byte reads as before. The heap after a write is `HeapAt.ofStdioKeep`/
`SetupPost.heapAfter` (lane F1-11's presence-level keeps).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout Lua.Vm.DlHeap Vsa.Densify
open Vsa.Machine (Config Steps)

/-- **What a write may change**: htif.c's and the allocator's globals, the
arena off the chunks in use, `__sinit`'s words, `stdout`, `errno`, the new
buffer, the callees' stack below `sp`. -/
def PrintW (sp : Nat) (H : HeapIx) (ph' : StdoutPh) (a : Nat) : Prop :=
  FsGlobal a ∨ MallocW H.chunks a ∨ SinitW a ∨ Rng stdoutFile fileSize a ∨ ph'.Buf a ∨ Below sp 4096 a

/-- **What a write leaves**: the phase `ph'` with heap `H'`, the console's
bytes `out` (`out ++ pend' = pend ++ the n bytes`), the chunks in use kept,
the bytes off `PrintW` kept. -/
structure PrintPost (m m' : Mem) (sp src n : Nat) (ph : StdoutPh) (H : HeapIx) (ph' : StdoutPh) (H' : HeapIx)
    (out : List (BitVec 8)) : Prop where
  phase : StdoutIn m' H' ph'
  heap : HeapAt (fillZeroMem m') H'.top H'.brk H'.chunks H'.bins
  out : out ++ ph'.pend = ph.pend ++ bytesAt m src n
  kept : ∀ c ∈ H.chunks, c.inuse = true → c ∈ H'.chunks
  /-- a new buffer is a fresh block of the arena -/
  buf_new : ∀ a, ph'.Buf a → ph.Buf a ∨ (heapStart ≤ a ∧ a < heapEnd ∧ ¬ InUse H.chunks a)
  /-- a write of at least one byte leaves `stdout` set up -/
  up_of : 1 ≤ n → ∃ buf pend, ph' = .up buf pend
  keep : ∀ a, ¬ PrintW sp H ph' a → bytesT1 m' a = bytesT1 m a

/-- The numbers the regions are stated over, for `omega`. -/
macro "pw_nums" : tactic => `(tactic| (
  fs_nums
  stdio_nums
  have : symSf = 0x8005e5b0 := rfl
  have : symStdioExitHandler = 0x8005d3e0 := rfl
  have : symImpureData = 0x8005d1b8 := rfl
  have : reentCleanupOff = 72 := rfl))

/-- **A write that set `stdout` up** (`SetupPost`, from boot or fresh). -/
theorem SetupPost.print {m M m' : Mem} {sp src n buf brk : Nat} {chunks : List Chunk} {top' brk' : Nat}
    {chunks' : List Chunk} {bins' : Nat → List Nat} {out pend' : List (BitVec 8)} {H : HeapIx} {ph : StdoutPh}
    (P : SetupPost m M m' sp src n buf brk chunks top' brk' chunks' bins' out pend')
    (hph : ph.pend = []) (hc : H.chunks = chunks) (hsp : heapEnd + 8192 ≤ sp)
    (hkept : ∀ c ∈ chunks, c.inuse = true → c ∈ chunks') :
    PrintPost m m' sp src n ph H (.up buf pend') ⟨top', brk', chunks', bins'⟩ out := by
  subst hc
  have hb2 := P.grant.heap.brk_le
  refine ⟨.up P.stdout P.up ⟨P.grant.block, P.grant.lo, Nat.le_trans P.grant.hi hb2⟩ P.rest, P.heapAfter hsp,
    by rw [hph, List.nil_append]; exact P.out, hkept, fun a ha => by
      have ha' : buf ≤ a ∧ a < buf + 1024 := ha
      exact .inr ⟨Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans P.grant.lo ha'.1),
        Nat.lt_of_lt_of_le ha'.2 (Nat.le_trans P.grant.hi hb2), P.grant.fresh a ha'.1 ha'.2⟩,
    fun _ => ⟨_, _, rfl⟩, fun a ha => ?_⟩
  simp only [PrintW, StdoutPh.Buf, not_or] at ha
  obtain ⟨hg, hw, hs, hst, hb, hbl⟩ := ha
  have hk : bytesT1 M a = bytesT1 m a := bT1_congr (P.agree a fun h => by
    rcases h with h | h | h | h
    · exact hg h
    · exact hw h
    · exact hs h
    · exact hbl (by simp only [Below] at h ⊢; omega))
  refine Eq.trans ?_ hk
  simp only [Below, Rng, not_and, Nat.not_lt] at hbl hb hst
  pw_nums
  by_cases h1 : sp - 112 ≤ a
  · exact P.keep.keep_hi a h1 (by omega)
  · exact P.keep.keep_lo a (by omega) (by omega) (by omega) (by
      simp only [FsGlobal, not_or, not_and] at hg; omega)

/-- **One write of `print`** (`fwrite(src, 1, n, stdout)`) from any phase. -/
theorem fwrite_print (hM : MallocR_Statement) (sp src n : Nat) (r : BitVec 64) (f : AbiFrame) (m : Mem)
    (o : Array String) (ph : StdoutPh) (H : HeapIx)
    (hin : StdoutIn m H ph) (hheap : HeapAt (fillZeroMem m) H.top H.brk H.chunks H.bins)
    (hra : r.toNat % 4 = 0) (hhi : sp ≤ 2 ^ 32) (hal : sp % 16 = 0) (hlo : heapEnd + 8192 ≤ sp)
    (hsl : SrcLo src n) (hsh : src + n + 4096 ≤ sp)
    (hsrc : ∀ a, src ≤ a → a < src + n → ¬ FsGlobal a ∧ ¬ MallocW H.chunks a ∧ ¬ SinitW a)
    (hsf : src + n ≤ stdoutFile ∨ stdoutFile + fileSize ≤ src)
    (hsb : ∀ buf pend, ph = .up buf pend → src + n ≤ buf ∨ buf + 1024 ≤ src) :
    Triple (SegSt 0x800342e4#64 (fwPre src n sp r f) (ArmPay m o))
      (fun c => ∃ m' out ph' H', wrRet r sp n f m' (pushes o out) c ∧ PrintPost m m' sp src n ph H ph' H' out) := by
  have q : heapEnd + 4096 ≤ sp ∧ 0x8005e7d8 + 64 + 112 ≤ sp ∧ 0x8005e720 + 96 + 112 ≤ sp := by
    obtain ⟨E, hE⟩ : ∃ E, heapEnd = E := ⟨_, rfl⟩
    have : E = 0x87800000 := hE ▸ rfl
    rw [hE] at hlo ⊢; omega
  intro c h
  cases hin with
  | boot hB hMf hroom =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨c', s', M, hret, hF, hag, hR⟩ := fwrite_boot0 sp src r f m o hra q.2.1 hhi hal hB hMf c h
      refine ⟨c', s', M, [], .fresh, H, hret, ⟨.fresh hF hroom hR, ?_, rfl, fun c hc _ => hc, fun _ h => h.elim, fun h => absurd h (by omega), ?_⟩⟩
      · exact hheap.congr fun a ha => fill_congr (hag a fun hr => by
          pw_nums
          have e9 : symMallocMallinfo = 0x8005e560 := rfl
          have e4 : symMallocAv = 0x8005c6d0 := rfl
          have e2 : heapStart = 0x8006ecd0 := rfl
          have e3 : heapEnd = 0x87800000 := rfl
          have e5 : symMallocSbrkBase = 0x8005d388 := rfl
          have e6 : symBrk = 0x8005d3b8 := rfl
          have e7 : symMallocTopPad = 0x8005d3d8 := rfl
          have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
          simp only [HeapReads, SinitW, Below, Rng] at ha hr; omega)
      · intro a ha
        exact bT1_congr (hag a fun hr => ha (by
          rcases hr with hr | hr
          · exact .inr (.inr (.inl hr))
          · simp only [Below] at hr; exact .inr (.inr (.inr (.inr (.inr ⟨hr.1, by omega⟩))))))
    · obtain ⟨c', s', M, m', out, pend', buf, top', brk', chunks', bins', hret, P⟩ :=
        stdoutSetup_of_malloc hM sp src n H.top H.brk H.chunks H.bins r f m o hB hMf hheap hra hhi hal hlo
          hroom hn hsl hsh hsf hsrc c h
      exact ⟨c', s', m', out, _, _, hret, P.print rfl rfl hlo P.grant.kept⟩
  | fresh hF hroom hR =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · obtain ⟨c', s', M, hret, hF', hag⟩ := fwrite_fresh0 sp src r f m o hra q.2.2 hhi hal hF c h
      have hR' : StdioRest M := hR.congrT fun a ha => hag.t1 (by
        have := ha.range; simp only [Below]; omega)
      refine ⟨c', s', M, [], .fresh, H, hret, ⟨.fresh hF' hroom hR', ?_, rfl, fun c hc _ => hc, fun _ h => h.elim, fun h => absurd h (by omega), ?_⟩⟩
      · exact hheap.congr fun a ha => fill_congr (hag a fun hr => by
          have e2 : heapStart = 0x8006ecd0 := rfl
          have e3 : heapEnd = 0x87800000 := rfl
          have e4 : symMallocAv = 0x8005c6d0 := rfl
          have e9 : symMallocMallinfo = 0x8005e560 := rfl
          have e5 : symMallocSbrkBase = 0x8005d388 := rfl
          have e6 : symBrk = 0x8005d3b8 := rfl
          have e7 : symMallocTopPad = 0x8005d3d8 := rfl
          have e8 : symMallocMaxSbrked = 0x8005d3d0 := rfl
          simp only [HeapReads, Below] at ha hr; omega)
      · intro a ha
        exact bT1_congr (hag a fun hr => ha (by
          simp only [Below] at hr; exact .inr (.inr (.inr (.inr (.inr ⟨hr.1, by omega⟩))))))
    · obtain ⟨c', s', M, m', out, pend', buf, top', brk', chunks', bins', hret, P⟩ :=
        stdoutSetup_fresh hM sp src n H.top H.brk H.chunks H.bins r f m o hF hR hheap hra hhi hal hlo hroom hn hsl
          hsh hsf (fun a h1 h2 => ⟨(hsrc a h1 h2).1, (hsrc a h1 h2).2.1⟩) c h
      exact ⟨c', s', m', out, _, _, hret, P.print rfl rfl hlo P.grant.kept⟩
  | @up buf pend hs hu hb hR =>
    have hsb := hsb buf pend rfl
    have hbh := hb.hi
    have hx : StdioCtx sp buf r := ⟨hra, by omega, hhi, hal⟩
    obtain ⟨c', s', m', out, pend', hret, hs', hu', hout, hk⟩ :=
      fwrite_stdout sp buf src n pend r f m o hx hs hu (by omega) hsl hsh hsb hsf c h
    have hd : heapEnd + 32 + 4096 ≤ sp := by
      obtain ⟨E, hE⟩ : ∃ E, heapEnd = E := ⟨_, rfl⟩
      rw [hE] at hlo ⊢; omega
    refine ⟨c', s', m', out, .up buf pend', H, hret, ⟨.up hs' hu' hb (hR.congrT fun a ha => by
        have := ha.range; have := hb.lo
        have : heapStart = 0x8006ecd0 := rfl; have : errnoAddr = 0x8005d408 := rfl
        stdio_nums
        exact hk.keep_lo a (by omega) (by omega) (by omega) (by omega)), ?_, hout, fun c hc _ => hc, fun _ h => .inl h, fun _ => ⟨_, _, rfl⟩, ?_⟩⟩
    · exact hheap.ofStdioKeep hb.block hb.lo hd fun a h1 h2 h3 h4 =>
        (hk.keep_lo a h1 h2 h3 h4).trans (bytesT1_fill m a).symm
    · intro a ha
      simp only [PrintW, StdoutPh.Buf, not_or] at ha
      obtain ⟨hg, _, _, hst, hbuf, hbl⟩ := ha
      simp only [Below, Rng, not_and, Nat.not_lt] at hbl hbuf hst
      by_cases h1 : sp ≤ a
      · exact hk.keep_hi a h1
      · pw_nums
        exact hk.keep_lo a (by omega) (by omega) (by omega) (by
          simp only [FsGlobal, not_or, not_and] at hg; omega)

end Lua.Vm.Sim.Kit

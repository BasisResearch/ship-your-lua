import Lua.Vm.Sim.Kit.Strlen
import Lua.Vm.Sim.Kit.Memmove
import Lua.Vm.Sim.Kit.DecDigits
import Lua.Vm.Sim.Kit.HeapKeep
import Lua.Vm.AtF.SnprintfLld

/-!
# `lua_integer2str`: `snprintf(buf, 44, "%lld", i)` (lane F1-FMT)

`IntegerToStr_Statement` over the at-lemmas of `Lua/Vm/AtF/SnprintfLld`
(`gen_lua_at.py --fn snprintf/lld`): `_svfprintf_r` specialised to the
format's bytes. Its roots: the entry, the return from `strlen(".")`
(`strlen_sumU`), the `'d'` conversion `0x80043824`, the digit loop's head
`0x80043b38` (`seg_loop` over the quotient), the loop's exit `0x80043b88`,
and the returns from `memmove` (`memmove_sum`) inside `__ssputs_r`. Every
root's context is `SnG.X`: the run's fixed atoms and a root's own (`SnV`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-- The fixed data of a run: `snprintf`'s `sp`, the buffer, the format, `i`,
`ra`, the caller's frame, the variadic spill `a4`-`a7`, the console. -/
structure SnG where
  sp : Nat
  buf : Nat
  fmt : Nat
  i : BitVec 64
  r : BitVec 64
  f : AbiFrame
  a4 : BitVec 64
  a5 : BitVec 64
  a6 : BitVec 64
  a7 : BitVec 64
  o : Array String

/-- A root's own atoms: the digit cursor `c`, the count `k`, the first digit
`c5`; the quotient `q` and the dead registers' words. -/
structure SnV where
  c : Nat := 0
  k : Nat := 0
  c5 : Nat := 0
  q : BitVec 64 := 0
  b19 : BitVec 64 := 0
  b20 : BitVec 64 := 0
  b21 : BitVec 64 := 0
  b22 : BitVec 64 := 0
  b23 : BitVec 64 := 0
  b24 : BitVec 64 := 0

/-- **A root's context** (the generator's atom layout, `SNP_*`). -/
abbrev SnG.X (G : SnG) (V : SnV) (m : Mem) : FCx :=
  FCx.mk' [G.sp, G.buf, G.fmt, V.c, V.k, V.c5]
    [G.r, G.f.s0, G.f.s1, G.f.s2, G.f.s3, G.f.s4, G.f.s5, G.f.s6, G.f.s7, G.f.s8, G.f.s9, G.f.s10,
     G.f.s11, G.i, G.a4, G.a5, G.a6, G.a7, V.q, V.b19, V.b20, V.b21, V.b22, V.b23, V.b24] m G.o

/-- A signed test of small counts, literals and their negations (a guard
`fat_run` closes). -/
macro "fmt_scmp2" : tactic => `(tactic| (
  simp (disch := omega) only [zopz0zI_s, zopz0zKzJ_s, fmt_toInt_ofNat, fmt_toInt_neg, toInt_m1, toInt_z]
  (try simp only [decide_eq_true_eq, decide_eq_false_iff_not, ge_iff_le, Bool.not_eq_true]) <;>
  omega))

macro_rules
  | `(tactic| fat_hyp) => `(tactic| (fmt_scmp2; done))

/-- A root context's facts as hypotheses (`omega` reads them; `hX` stays for
the at-lemmas). -/
macro "fmt_facts " hX:ident : tactic => `(tactic| (have hX' := $hX; cases hX'))

/-! ## The runs of the roots

One lemma per root path: the generated at-lemmas chained by `fat_run`, the
root memory's facts and the path's guards (on `i`, the quotient, the sign
byte) as hypotheses. -/

theorem run_E (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok X)
    (hc0 : bytesT8 X.m 0x8005d398 = 0x8005d1b8#64)
    (hc1 : bytesT8 X.m 0x8005d0f0 = 0x8004fb10#64)
    (hc2 : bytesT8 X.m 0x8004fb10 = 0x2e#64)
    (hc3 : bytesT1 X.m 0x8004fb10 = 0x2e#8)
    (hc4 : bytesT1 X.m 0x8004fb11 = 0x0#8)
    : Triple (SegSt 0x80034de0#64 (Lua.Vm.AtF.SnprintfLld.r0 X) (ArmPay X.m X.o))
      (SegSt (0x80042ec0#64) (Lua.Vm.AtF.SnprintfLld.r1 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m12 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80042ec0]
  exact ⟨_, acc, h⟩

theorem run_F (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_F X)
    (hc5 : bytesT2 X.m (X.n 0 - 248) = 0x208#16)
    (hc6 : bytesT8 X.m 0x8005d0d8 = 0x8003cd58#64)
    (hc7 : bytesT1 X.m 0x8005d150 = 0x1#8)
    (hc8 : bytesT1 X.m (X.n 2) = 0x25#8)
    (hc9 : bytesT1 X.m (X.n 2 + 1) = 0x6c#8)
    (hc10 : bytesT4 X.m 0x800555f4 = 0xfffee88c#32)
    (hc11 : bytesT1 X.m (X.n 2 + 2) = 0x6c#8)
    (hc12 : bytesT1 X.m (X.n 2 + 3) = 0x64#8)
    (hc13 : bytesT4 X.m 0x800555d4 = 0xfffee360#32)
    : Triple (SegSt 0x80042ec0#64 (Lua.Vm.AtF.SnprintfLld.r16 X) (ArmPay X.m X.o))
      (SegSt (0x80043824#64) (Lua.Vm.AtF.SnprintfLld.r18 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m15 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80043824]
  exact ⟨_, acc, h⟩

theorem run_Dn1 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc14 : bytesT8 X.m (X.n 0 - 840) = BitVec.ofNat 64 (X.n 0 - 40))
    (hc15 : bytesT8 X.m (X.n 0 - 40) = X.b 13)
    (hg_5 : zopz0zKzJ_s (X.b 13) (0x0#64) = false)
    (hg_2 : zopz0zI_u (0x9#64) (((0#64) - (X.b 13))) = false)
    (hc18 : bytesT8 X.m (X.n 0 - 624) = 0x0#64)
    (hc19 : bytesT4 X.m (X.n 0 - 632) = 0x0#32)
    (hc20 : bytesT8 X.m (X.n 0 - 848) = 0x0#64)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc22 : bytesT8 X.m (X.n 0 - 640) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r89 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m45 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Dnm (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc14 : bytesT8 X.m (X.n 0 - 840) = BitVec.ofNat 64 (X.n 0 - 40))
    (hc15 : bytesT8 X.m (X.n 0 - 40) = X.b 13)
    (hg_5 : zopz0zKzJ_s (X.b 13) (0x0#64) = false)
    (hg_2 : zopz0zI_u (0x9#64) (((0#64) - (X.b 13))) = true)
    (hc16 : bytesT8 X.m (X.n 0 - 760) = 0x0#64)
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 X) (ArmPay X.m X.o))
      (SegSt (0x80043b38#64) (Lua.Vm.AtF.SnprintfLld.r86 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m35 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80043b38]
  exact ⟨_, acc, h⟩

theorem run_Dp1 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc14 : bytesT8 X.m (X.n 0 - 840) = BitVec.ofNat 64 (X.n 0 - 40))
    (hc15 : bytesT8 X.m (X.n 0 - 40) = X.b 13)
    (hg_5 : zopz0zKzJ_s (X.b 13) (0x0#64) = true)
    (hg_2 : zopz0zI_u (0x9#64) (X.b 13) = false)
    (hc17 : bytesT1 X.m (X.n 0 - 697) = 0x0#8)
    (hc18 : bytesT8 X.m (X.n 0 - 624) = 0x0#64)
    (hc19 : bytesT4 X.m (X.n 0 - 632) = 0x0#32)
    (hc20 : bytesT8 X.m (X.n 0 - 848) = 0x0#64)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc22 : bytesT8 X.m (X.n 0 - 640) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r39 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m27 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Dpm (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc14 : bytesT8 X.m (X.n 0 - 840) = BitVec.ofNat 64 (X.n 0 - 40))
    (hc15 : bytesT8 X.m (X.n 0 - 40) = X.b 13)
    (hg_5 : zopz0zKzJ_s (X.b 13) (0x0#64) = true)
    (hg_2 : zopz0zI_u (0x9#64) (X.b 13) = true)
    (hc16 : bytesT8 X.m (X.n 0 - 760) = 0x0#64)
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 X) (ArmPay X.m X.o))
      (SegSt (0x80043b38#64) (Lua.Vm.AtF.SnprintfLld.r36 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m18 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80043b38]
  exact ⟨_, acc, h⟩

theorem run_Qp1 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc26 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc28 : bytesT8 X.m (X.n 0 - 624) = 0x1#64)
    (hc29 : bytesT8 X.m (X.n 0 - 880) = 0x8005d1b8#64)
    (hc30 : bytesT8 X.m (X.n 0 - 896) = 0x10#64)
    (hc31 : bytesT8 X.m (X.n 0 - 904) = 0x25#64)
    (hc32 : bytesT8 X.m (X.n 0 - 912) = 0xfffffffffffffffe#64)
    (hc33 : bytesT8 X.m (X.n 0 - 920) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc34 : bytesT8 X.m (X.n 0 - 872) = 0x80043ea4#64)
    (hc35 : bytesT8 X.m (X.n 0 - 888) = 0x8005cff0#64)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc37 : bytesT8 X.m (X.n 0 - 864) = BitVec.ofNat 64 (X.n 2 + 4))
    (hc6 : bytesT8 X.m 0x8005d0d8 = 0x8003cd58#64)
    (hc7 : bytesT1 X.m 0x8005d150 = 0x1#8)
    (hc38 : bytesT1 X.m (X.n 2 + 4) = 0x0#8)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc5 : bytesT2 X.m (X.n 0 - 248) = 0x208#16)
    (hc39 : bytesT8 X.m (X.n 0 - 304) = X.b 3)
    (hc40 : bytesT8 X.m (X.n 0 - 312) = X.b 4)
    (hc41 : bytesT8 X.m (X.n 0 - 320) = X.b 5)
    (hc42 : bytesT8 X.m (X.n 0 - 328) = X.b 6)
    (hc43 : bytesT8 X.m (X.n 0 - 344) = X.b 8)
    (hc44 : bytesT8 X.m (X.n 0 - 352) = X.b 9)
    (hc45 : bytesT8 X.m (X.n 0 - 360) = X.b 10)
    (hc46 : bytesT8 X.m (X.n 0 - 368) = X.b 11)
    (hc47 : bytesT8 X.m (X.n 0 - 376) = X.b 12)
    (hc48 : bytesT8 X.m (X.n 0 - 280) = 0x80034e58#64)
    (hc49 : bytesT8 X.m (X.n 0 - 288) = 0x2c#64)
    (hc50 : bytesT8 X.m (X.n 0 - 848) = 0x1#64)
    (hc51 : bytesT8 X.m (X.n 0 - 296) = 0x8005d1b8#64)
    (hc52 : bytesT8 X.m (X.n 0 - 336) = X.b 7)
    (hc53 : bytesT8 X.m (X.n 0 - 64) = X.b 1)
    (hc54 : bytesT8 X.m (X.n 0 - 56) = X.b 0)
    (hc55 : bytesT8 X.m (X.n 0 - 72) = X.b 2)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r40 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.SnprintfLld.r42 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m33 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc
  exact ⟨_, acc, h⟩

theorem run_Qn1 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc26 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc56 : bytesT8 X.m (X.n 0 - 624) = 0x2#64)
    (hc57 : bytesT4 X.m (X.n 0 - 632) = 0x1#32)
    (hc58 : bytesT8 X.m (X.n 0 - 488) = 0x1#64)
    (hc59 : bytesT8 X.m (X.n 0 - 496) = BitVec.ofNat 64 (X.n 0 - 517))
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r90 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r92 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m48 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  -- the root's row is the second `memmove` return's too: its first at-lemma named
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.SnprintfLld.at_8004e4e8_8004e518_2 X hX hc23 hc24 hc25 hc26 hc27)
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Qn2 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_D X)
    (hc60 : bytesT4 X.m (X.n 0 - 252) = 0x2a#32)
    (hc61 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1 + 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc62 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 496))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc28 : bytesT8 X.m (X.n 0 - 624) = 0x1#64)
    (hc29 : bytesT8 X.m (X.n 0 - 880) = 0x8005d1b8#64)
    (hc30 : bytesT8 X.m (X.n 0 - 896) = 0x10#64)
    (hc31 : bytesT8 X.m (X.n 0 - 904) = 0x25#64)
    (hc32 : bytesT8 X.m (X.n 0 - 912) = 0xfffffffffffffffe#64)
    (hc33 : bytesT8 X.m (X.n 0 - 920) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc34 : bytesT8 X.m (X.n 0 - 872) = 0x80043ea4#64)
    (hc35 : bytesT8 X.m (X.n 0 - 888) = 0x8005cff0#64)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc37 : bytesT8 X.m (X.n 0 - 864) = BitVec.ofNat 64 (X.n 2 + 4))
    (hc6 : bytesT8 X.m 0x8005d0d8 = 0x8003cd58#64)
    (hc7 : bytesT1 X.m 0x8005d150 = 0x1#8)
    (hc38 : bytesT1 X.m (X.n 2 + 4) = 0x0#8)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc5 : bytesT2 X.m (X.n 0 - 248) = 0x208#16)
    (hc39 : bytesT8 X.m (X.n 0 - 304) = X.b 3)
    (hc40 : bytesT8 X.m (X.n 0 - 312) = X.b 4)
    (hc41 : bytesT8 X.m (X.n 0 - 320) = X.b 5)
    (hc42 : bytesT8 X.m (X.n 0 - 328) = X.b 6)
    (hc43 : bytesT8 X.m (X.n 0 - 344) = X.b 8)
    (hc44 : bytesT8 X.m (X.n 0 - 352) = X.b 9)
    (hc45 : bytesT8 X.m (X.n 0 - 360) = X.b 10)
    (hc46 : bytesT8 X.m (X.n 0 - 368) = X.b 11)
    (hc47 : bytesT8 X.m (X.n 0 - 376) = X.b 12)
    (hc48 : bytesT8 X.m (X.n 0 - 280) = 0x80034e58#64)
    (hc49 : bytesT8 X.m (X.n 0 - 288) = 0x2c#64)
    (hc63 : bytesT8 X.m (X.n 0 - 848) = 0x2#64)
    (hc51 : bytesT8 X.m (X.n 0 - 296) = 0x8005d1b8#64)
    (hc52 : bytesT8 X.m (X.n 0 - 336) = X.b 7)
    (hc53 : bytesT8 X.m (X.n 0 - 64) = X.b 1)
    (hc54 : bytesT8 X.m (X.n 0 - 56) = X.b 0)
    (hc55 : bytesT8 X.m (X.n 0 - 72) = X.b 2)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r90 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.SnprintfLld.r94 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m54 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  obtain ⟨_, acc, h⟩ := Vsa.Sim.SegSt.run acc h (Vsa.Sim.SegSt.pins h)
    (Lua.Vm.AtF.SnprintfLld.at_8004e4e8_8004e518_1 X hX hc60 hc61 hc25 hc62 hc27)
  fat_run Lua.Vm.AtF.SnprintfLld h acc
  exact ⟨_, acc, h⟩

theorem run_Lc (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_L X)
    (hg_5 : zopz0zKzJ_u (0x9#64) (X.b 18) = false)
    : Triple (SegSt 0x80043b38#64 (Lua.Vm.AtF.SnprintfLld.r133 X) (ArmPay X.m X.o))
      (SegSt (0x80043b38#64) (Lua.Vm.AtF.SnprintfLld.r134 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m55 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80043b38]
  exact ⟨_, acc, h⟩

theorem run_Lx (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_L X)
    (hg_5 : zopz0zKzJ_u (0x9#64) (X.b 18) = true)
    (hc64 : bytesT8 X.m (X.n 0 - 752) = BitVec.ofNat 64 (X.n 0 - 516))
    (hc65 : bytesT8 X.m (X.n 0 - 808) = 0xffffffffffffffff#64)
    (hc66 : bytesT8 X.m (X.n 0 - 824) = 0x20#64)
    : Triple (SegSt 0x80043b38#64 (Lua.Vm.AtF.SnprintfLld.r133 X) (ArmPay X.m X.o))
      (SegSt (0x80043b88#64) (Lua.Vm.AtF.SnprintfLld.r135 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m56 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x80043b88]
  exact ⟨_, acc, h⟩

theorem run_Pn (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_P X)
    (hsg : bytesT1 X.m (X.n 0 - 697) = 0x2d#8)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc67 : bytesT8 X.m (X.n 0 - 816) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc68 : bytesT8 X.m (X.n 0 - 744) = 0x8005d1b8#64)
    (hc18 : bytesT8 X.m (X.n 0 - 624) = 0x0#64)
    (hc19 : bytesT4 X.m (X.n 0 - 632) = 0x0#32)
    (hc20 : bytesT8 X.m (X.n 0 - 848) = 0x0#64)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc22 : bytesT8 X.m (X.n 0 - 640) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    : Triple (SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r141 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r186 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m78 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Pp (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_P X)
    (hsg : bytesT1 X.m (X.n 0 - 697) = 0x0#8)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc67 : bytesT8 X.m (X.n 0 - 816) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc68 : bytesT8 X.m (X.n 0 - 744) = 0x8005d1b8#64)
    (hc18 : bytesT8 X.m (X.n 0 - 624) = 0x0#64)
    (hc19 : bytesT4 X.m (X.n 0 - 632) = 0x0#32)
    (hc20 : bytesT8 X.m (X.n 0 - 848) = 0x0#64)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc22 : bytesT8 X.m (X.n 0 - 640) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    : Triple (SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r141 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r143 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m65 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Rp (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_P X)
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc26 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc69 : bytesT8 X.m (X.n 0 - 624) = BitVec.ofNat 64 (X.n 4))
    (hc29 : bytesT8 X.m (X.n 0 - 880) = 0x8005d1b8#64)
    (hc30 : bytesT8 X.m (X.n 0 - 896) = 0x10#64)
    (hc31 : bytesT8 X.m (X.n 0 - 904) = 0x25#64)
    (hc70 : bytesT8 X.m (X.n 0 - 912) = (BitVec.ofNat 64 (0) - BitVec.ofNat 64 (X.n 4 + 1)))
    (hc33 : bytesT8 X.m (X.n 0 - 920) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc34 : bytesT8 X.m (X.n 0 - 872) = 0x80043ea4#64)
    (hc35 : bytesT8 X.m (X.n 0 - 888) = 0x8005cff0#64)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc37 : bytesT8 X.m (X.n 0 - 864) = BitVec.ofNat 64 (X.n 2 + 4))
    (hc6 : bytesT8 X.m 0x8005d0d8 = 0x8003cd58#64)
    (hc7 : bytesT1 X.m 0x8005d150 = 0x1#8)
    (hc38 : bytesT1 X.m (X.n 2 + 4) = 0x0#8)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc5 : bytesT2 X.m (X.n 0 - 248) = 0x208#16)
    (hc39 : bytesT8 X.m (X.n 0 - 304) = X.b 3)
    (hc40 : bytesT8 X.m (X.n 0 - 312) = X.b 4)
    (hc41 : bytesT8 X.m (X.n 0 - 320) = X.b 5)
    (hc42 : bytesT8 X.m (X.n 0 - 328) = X.b 6)
    (hc43 : bytesT8 X.m (X.n 0 - 344) = X.b 8)
    (hc44 : bytesT8 X.m (X.n 0 - 352) = X.b 9)
    (hc45 : bytesT8 X.m (X.n 0 - 360) = X.b 10)
    (hc46 : bytesT8 X.m (X.n 0 - 368) = X.b 11)
    (hc47 : bytesT8 X.m (X.n 0 - 376) = X.b 12)
    (hc48 : bytesT8 X.m (X.n 0 - 280) = 0x80034e58#64)
    (hc49 : bytesT8 X.m (X.n 0 - 288) = 0x2c#64)
    (hc71 : bytesT8 X.m (X.n 0 - 848) = BitVec.ofNat 64 (X.n 4))
    (hc51 : bytesT8 X.m (X.n 0 - 296) = 0x8005d1b8#64)
    (hc52 : bytesT8 X.m (X.n 0 - 336) = X.b 7)
    (hc53 : bytesT8 X.m (X.n 0 - 64) = X.b 1)
    (hc54 : bytesT8 X.m (X.n 0 - 56) = X.b 0)
    (hc55 : bytesT8 X.m (X.n 0 - 72) = X.b 2)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r144 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.SnprintfLld.r146 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m71 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc
  exact ⟨_, acc, h⟩

theorem run_Rn1 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_P X)
    (hc23 : bytesT4 X.m (X.n 0 - 252) = 0x2b#32)
    (hc24 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc26 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc72 : bytesT8 X.m (X.n 0 - 624) = BitVec.ofNat 64 (X.n 4 + 1))
    (hc57 : bytesT4 X.m (X.n 0 - 632) = 0x1#32)
    (hc73 : bytesT8 X.m (X.n 0 - 488) = BitVec.ofNat 64 (X.n 4))
    (hc74 : bytesT8 X.m (X.n 0 - 496) = BitVec.ofNat 64 (X.n 5))
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r187 X) (ArmPay X.m X.o))
      (SegSt (0x8003b444#64) (Lua.Vm.AtF.SnprintfLld.r189 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m81 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc until [0x8003b444]
  exact ⟨_, acc, h⟩

theorem run_Rn2 (X : FCx) (hX : Lua.Vm.AtF.SnprintfLld.Ok_P X)
    (hc60 : bytesT4 X.m (X.n 0 - 252) = 0x2a#32)
    (hc61 : bytesT8 X.m (X.n 0 - 264) = BitVec.ofNat 64 (X.n 1 + 1))
    (hc25 : bytesT8 X.m (X.n 0 - 936) = 0x8004975c#64)
    (hc62 : bytesT8 X.m (X.n 0 - 944) = BitVec.ofNat 64 (X.n 0 - 496))
    (hc27 : bytesT8 X.m (X.n 0 - 952) = BitVec.ofNat 64 (X.n 0 - 640))
    (hc69 : bytesT8 X.m (X.n 0 - 624) = BitVec.ofNat 64 (X.n 4))
    (hc29 : bytesT8 X.m (X.n 0 - 880) = 0x8005d1b8#64)
    (hc30 : bytesT8 X.m (X.n 0 - 896) = 0x10#64)
    (hc31 : bytesT8 X.m (X.n 0 - 904) = 0x25#64)
    (hc70 : bytesT8 X.m (X.n 0 - 912) = (BitVec.ofNat 64 (0) - BitVec.ofNat 64 (X.n 4 + 1)))
    (hc33 : bytesT8 X.m (X.n 0 - 920) = BitVec.ofNat 64 (X.n 0 - 512))
    (hc34 : bytesT8 X.m (X.n 0 - 872) = 0x80043ea4#64)
    (hc35 : bytesT8 X.m (X.n 0 - 888) = 0x8005cff0#64)
    (hc36 : bytesT8 X.m (X.n 0 - 832) = 0x0#64)
    (hc37 : bytesT8 X.m (X.n 0 - 864) = BitVec.ofNat 64 (X.n 2 + 4))
    (hc6 : bytesT8 X.m 0x8005d0d8 = 0x8003cd58#64)
    (hc7 : bytesT1 X.m 0x8005d150 = 0x1#8)
    (hc38 : bytesT1 X.m (X.n 2 + 4) = 0x0#8)
    (hc21 : bytesT8 X.m (X.n 0 - 856) = BitVec.ofNat 64 (X.n 0 - 264))
    (hc5 : bytesT2 X.m (X.n 0 - 248) = 0x208#16)
    (hc39 : bytesT8 X.m (X.n 0 - 304) = X.b 3)
    (hc40 : bytesT8 X.m (X.n 0 - 312) = X.b 4)
    (hc41 : bytesT8 X.m (X.n 0 - 320) = X.b 5)
    (hc42 : bytesT8 X.m (X.n 0 - 328) = X.b 6)
    (hc43 : bytesT8 X.m (X.n 0 - 344) = X.b 8)
    (hc44 : bytesT8 X.m (X.n 0 - 352) = X.b 9)
    (hc45 : bytesT8 X.m (X.n 0 - 360) = X.b 10)
    (hc46 : bytesT8 X.m (X.n 0 - 368) = X.b 11)
    (hc47 : bytesT8 X.m (X.n 0 - 376) = X.b 12)
    (hc48 : bytesT8 X.m (X.n 0 - 280) = 0x80034e58#64)
    (hc49 : bytesT8 X.m (X.n 0 - 288) = 0x2c#64)
    (hc75 : bytesT8 X.m (X.n 0 - 848) = BitVec.ofNat 64 (X.n 4 + 1))
    (hc51 : bytesT8 X.m (X.n 0 - 296) = 0x8005d1b8#64)
    (hc52 : bytesT8 X.m (X.n 0 - 336) = X.b 7)
    (hc53 : bytesT8 X.m (X.n 0 - 64) = X.b 1)
    (hc54 : bytesT8 X.m (X.n 0 - 56) = X.b 0)
    (hc55 : bytesT8 X.m (X.n 0 - 72) = X.b 2)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r190 X) (ArmPay X.m X.o))
      (SegSt (X.b 0) (Lua.Vm.AtF.SnprintfLld.r192 X) (ArmPay (Lua.Vm.AtF.SnprintfLld.m87 X) X.o)) := by
  intro c h
  have acc := Steps.refl c
  fmt_facts hX
  fat_run Lua.Vm.AtF.SnprintfLld h acc
  exact ⟨_, acc, h⟩


end Lua.Vm.Sim.Kit

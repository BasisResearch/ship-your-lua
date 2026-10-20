import Lua.Vm.Sim.Kit.IntFmtSum

/-!
# `%lld`'s digit loop and the multi-digit paths (lane F1-FMT)

The `'d'` conversion of an `|i| > 9` hands the loop head `0x80043b38` the
magnitude (`run_Dpm`, `run_Dnm`); the loop (`seg_loop` over the quotient,
`run_Lc` per digit, `run_Lx` at the last) writes the digits last to first
below `sp - 516` (`decBytes_ge`, `decBytes_lt`) and hands the exit
`0x80043b88` the count `k` and the first digit's address `c5`. The exit's
paths (`run_Pp`, `run_Pn`) copy the sign and the digits into the buffer
(`memmove_sum`) and return (`run_Rp`, `run_Rn1`, `run_Rn2`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim Vsa.Logic

namespace Lua.Vm.Sim.Kit

open Lua.Vm.Sim Lua.Vm.Sim.AtF Lua.Vm.Layout
open Vsa.Machine (Config Steps)

/-! ## Digits -/

theorem udivT10 (q : BitVec 64) : (udivT q 0xa#64).toNat = q.toNat / 10 := by
  rw [udivT_ne (by decide), BitVec.toNat_udiv]; rfl

theorem umod10 (q : BitVec 64) : (q % 0xa#64).toNat = q.toNat % 10 := by
  rw [BitVec.toNat_umod]; rfl

/-- A digit's store read back as the first byte of the bytes from it. -/
theorem bytesAt_ins_cons (m : Mem) (a n : Nat) (d : BitVec 8) :
    bytesAt (m.insert a d) a (n + 1) = d :: bytesAt m (a + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  rw [Lua.Vm.Sim.AtF.fw1_same rfl]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [Lua.Vm.Sim.AtF.fw1_ins (by omega), Nat.add_assoc, Nat.add_comm 1 i]

/-- `zopz0zKzJ_u 9 q` (`bgeu`, `9 ≥ q`). -/
theorem le9_iff (q : BitVec 64) : zopz0zKzJ_u (0x9#64) q = true ↔ q.toNat ≤ 9 := by
  have e : BitVec.toNatInt (0x9#64 : BitVec 64) = 9 := by decide
  unfold zopz0zKzJ_u
  rw [e, decide_eq_true_iff]
  simp only [BitVec.toNatInt, Int.ofNat_eq_coe, ge_iff_le]
  omega

/-! ## The loop -/

/-- The loop's state: the root's atoms and memory. -/
structure SnL where
  V : SnV
  M : Mem

/-- What the loop has written: the digits from the cursor up to `sp - 516`. -/
abbrev snDig (G : SnG) (c : Nat) : Nat → Prop := fun x => c ≤ x ∧ x < G.sp - 516

/-- What the loop's exit reads of the memory the conversion left. -/
structure FacL (G : SnG) (M : Mem) : Prop where
  s752 : bytesT8 M (G.sp - 752) = BitVec.ofNat 64 (G.sp - 516)
  s808 : bytesT8 M (G.sp - 808) = 0xffffffffffffffff#64
  s824 : bytesT8 M (G.sp - 824) = 0x20#64

/-- **The loop invariant**: the digits of `q` still to come fit below the
cursor, the digits written are the rest of `q0`'s, the memory is the
conversion's off them. -/
structure SnLI (G : SnG) (M0 : Mem) (q0 : Nat) (a : SnL) : Prop where
  c_lo : G.sp - 536 + (decBytes a.V.q.toNat).length ≤ a.V.c
  c_hi : a.V.c ≤ G.sp - 516
  ag : Agree (snDig G a.V.c) M0 a.M
  dig : decBytes a.V.q.toNat ++ bytesAt a.M a.V.c (G.sp - 516 - a.V.c) = decBytes q0

/-- The digit region and the slot `sp - 760` the exit clears. -/
def snLoopW (sp a : Nat) : Prop := (sp - 536 ≤ a ∧ a < sp - 516) ∨ (sp - 760 ≤ a ∧ a < sp - 752)

/-- **What the loop leaves**: `k` digits from `c5` up to `sp - 516`, `q0`'s. -/
structure SnLO (G : SnG) (M0 : Mem) (q0 : Nat) (V : SnV) (M : Mem) : Prop where
  k_lo : 1 ≤ V.k
  k_hi : V.k ≤ 20
  k_c : V.c5 + V.k = G.sp - 516
  ag : Agree (snLoopW G.sp) M0 M
  dig : bytesAt M V.c5 V.k = decBytes q0

theorem sext88 (x : BitVec (8 * 8)) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- The count `k` the exit computes (`subw` of the cursor from the end). -/
theorem lx_k (X : FCx) (h752 : bytesT8 X.m (X.n 0 - 752) = BitVec.ofNat 64 (X.n 0 - 516))
    (hc : X.n 0 - 536 + 1 ≤ X.n 3) (hc' : X.n 3 ≤ X.n 0 - 516) (hsp : 0x8005e720 + 8192 ≤ X.n 0)
    (hsp2 : X.n 0 ≤ 2 ^ 32) :
    (sign_extend (m := 64) ((Sail.BitVec.extractLsb (sign_extend (m := 64) (bytesT8 ((Lua.Vm.AtF.SnprintfLld.m55 X))
      ((BitVec.ofNat 64 (X.n 0 - 864)) + sign_extend (m := 64) (0x070#12)).toNat : BitVec (8 * 8))) 31 0) -
      (Sail.BitVec.extractLsb (BitVec.ofNat 64 (X.n 3 - 1)) 31 0))) =
    BitVec.ofNat 64 (X.n 0 - 516 - (X.n 3 - 1)) := by
  have e1 : ((BitVec.ofNat 64 (X.n 0 - 864)) + sign_extend (m := 64) (0x070#12)).toNat = X.n 0 - 752 := by
    fmt_nat
  rw [e1]
  simp only [Lua.Vm.AtF.SnprintfLld.m55]
  rw [Lua.Vm.Sim.AtF.fw8_ins (by omega), h752]
  rw [sext88]
  fmt_w32

/-- The atoms after a digit (`run_Lc`'s row as the head's). -/
def SnV.next (V : SnV) : SnV :=
  { V with
    c := V.c - 1
    q := udivT V.q 0xa#64
    b19 := V.q
    b20 := sign_extend (m := 64) (Sail.BitVec.extractLsb (V.b20 + sign_extend (m := 64) (0x001#12)) 31 0)
    b21 := BitVec.ofNat 64 (V.c - 1) }

/-- The atoms at the exit (`run_Lx`'s row as the exit's). -/
def SnV.exit (V : SnV) (sp : Nat) : SnV :=
  { k := sp - 516 - (V.c - 1)
    c5 := V.c - 1
    b22 := udivT V.q 0xa#64
    b23 := sign_extend (m := 64) (Sail.BitVec.extractLsb (V.b20 + sign_extend (m := 64) (0x001#12)) 31 0) }

/-- The head's facts on the cursor (apart from the invariant's other atoms:
`omega` on the subtracted literals alone). -/
theorem okl_c {sp c l : Nat} (h0 : 0 < l) (h1 : sp - 536 + l ≤ c) (h2 : c ≤ sp - 516) (h3 : 8192 ≤ sp) :
    sp - 864 + 328 ≤ c ∧ c ≤ sp - 864 + 348 ∧ sp - 536 + 1 ≤ c := by omega

/-- The loop head's state. -/
abbrev SnLS (G : SnG) (M0 : Mem) (q0 : Nat) (a : SnL) (c : Config) : Prop :=
  SegSt 0x80043b38#64 (Lua.Vm.AtF.SnprintfLld.r134 (G.X a.V a.M)) (ArmPay (G.X a.V a.M).m (G.X a.V a.M).o) c ∧
    SnLI G M0 q0 a

/-- The loop's exit state. -/
abbrev SnLX (G : SnG) (M0 : Mem) (q0 : Nat) (c : Config) : Prop :=
  ∃ V M, SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r142 (G.X V M)) (ArmPay (G.X V M).m (G.X V M).o) c ∧
    SnLO G M0 q0 V M

/-- **One pass of the digit loop** (`run_Lc`: a digit and the quotient by
ten; `run_Lx`: the last digit, the count). -/
theorem snp_loop_body (G : SnG) (m : Mem) (hin : G.In m) (M0 : Mem) (FL : FacL G M0) (q0 : Nat) (a : SnL) :
    Triple (SnLS G M0 q0 a) (fun c => (∃ a', a'.V.q.toNat < a.V.q.toNat ∧ SnLS G M0 q0 a' c) ∨ SnLX G M0 q0 c) := by
  intro c ⟨h, I⟩
  have := hin.sp_lo; have := hin.sp_hi; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  obtain ⟨c_lo, c_hi, ag, dig⟩ := I
  have hl0 : 0 < (decBytes a.V.q.toNat).length := List.length_pos_iff.2 (decBytes_ne_nil _)
  obtain ⟨k1, k2, k3⟩ := okl_c hl0 c_lo c_hi (by omega)
  have hOk : Lua.Vm.AtF.SnprintfLld.Ok_L (G.X a.V a.M) :=
    ⟨hin.sp_lo, hin.sp_hi, hin.sp_al, hin.ra, Nat.le_trans (by decide) hin.b_lo, hin.b_ap, hin.b_hi, hin.f_lo,
      hin.f_hi, k1, k2⟩
  clear k1 k2
  cases hq : zopz0zKzJ_u (0x9#64) (a.V.q)
  · -- `q > 9`: a digit, then the quotient
    have hq9 : 9 < a.V.q.toNat := by
      refine Nat.lt_of_not_le fun hc => ?_
      have h' := (le9_iff a.V.q).2 hc
      rw [hq] at h'
      exact Bool.false_ne_true h'
    obtain ⟨c1, s1, h1⟩ := run_Lc (G.X a.V a.M) hOk (by sn_u1; exact hq) c h
    have hge := decBytes_ge (n := a.V.q.toNat) (by omega)
    have hlen : (decBytes a.V.q.toNat).length = (decBytes (a.V.q.toNat / 10)).length + 1 := by
      rw [hge]; simp
    refine ⟨c1, s1, .inl ⟨⟨a.V.next, Lua.Vm.AtF.SnprintfLld.m55 (G.X a.V a.M)⟩, ?_, ?_, ?_⟩⟩
    · simp only [SnV.next, udivT10]; omega
    · sn_unfold at h1 ⊢; simp only [SnV.next]; exact h1.repin (by pins_of h1)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [SnV.next, udivT10]
        omega
      · simp only [SnV.next]; omega
      · simp only [SnV.next, Lua.Vm.AtF.SnprintfLld.m55, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
        exact (ag.mono fun x hx => by simp only [snDig] at hx ⊢; omega).st1 (by simp only [snDig]; omega)
      · simp only [SnV.next, udivT10, Lua.Vm.AtF.SnprintfLld.m55, SnG.X, FCx.mk', List.getD_cons_zero,
          List.getD_cons_succ]
        rw [show G.sp - 516 - (a.V.c - 1) = (G.sp - 516 - a.V.c) + 1 by omega, bytesAt_ins_cons,
          show a.V.c - 1 + 1 = a.V.c by omega, digit_byte _ (by rw [umod10]; omega), umod10]
        rw [← dig, hge, List.append_assoc, List.singleton_append]
  · -- `q ≤ 9`: the last digit
    have hq9 : a.V.q.toNat ≤ 9 := (le9_iff a.V.q).1 hq
    have r752 : bytesT8 a.M (G.sp - 752) = BitVec.ofNat 64 (G.sp - 516) :=
      (ag.b8 fun j _ => by simp only [snDig]; omega).trans FL.s752
    have r808 : bytesT8 a.M (G.sp - 808) = 0xffffffffffffffff#64 :=
      (ag.b8 fun j _ => by simp only [snDig]; omega).trans FL.s808
    have r824 : bytesT8 a.M (G.sp - 824) = 0x20#64 :=
      (ag.b8 fun j _ => by simp only [snDig]; omega).trans FL.s824
    obtain ⟨c1, s1, h1⟩ := run_Lx (G.X a.V a.M) hOk (by sn_u1; exact hq) (by sn_u1; exact r752)
      (by sn_u1; exact r808) (by sn_u1; exact r824) c h
    have hlt := decBytes_lt (n := a.V.q.toNat) (by omega)
    have hl1 : (decBytes a.V.q.toNat).length = 1 := by rw [hlt]; rfl
    simp only [Lua.Vm.AtF.SnprintfLld.r136] at h1
    rw [lx_k (G.X a.V a.M) (by sn_u1; exact r752) (by sn_u1; omega) (by sn_u1; omega) (by sn_u1; omega)
      (by sn_u1; omega)] at h1
    refine ⟨c1, s1, .inr ⟨a.V.exit G.sp, Lua.Vm.AtF.SnprintfLld.m56 (G.X a.V a.M), ?_, ?_⟩⟩
    · sn_unfold at h1 ⊢; simp only [SnV.exit]; exact h1.repin (by pins_of h1)
    · refine ⟨by simp only [SnV.exit]; omega, by simp only [SnV.exit]; omega, by simp only [SnV.exit]; omega, ?_, ?_⟩
      · simp only [Lua.Vm.AtF.SnprintfLld.m56, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
        refine Agree.st8 ((ag.mono fun x hx => by simp only [snDig, snLoopW] at hx ⊢; omega).st1
          (by simp only [snLoopW]; omega)) fun j hj => by simp only [snLoopW]; omega
      · simp only [SnV.exit, Lua.Vm.AtF.SnprintfLld.m56, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
        rw [bytesAt_congr (m := (a.M).insert (a.V.c - 1) _) fun j hj =>
          Lua.Vm.Sim.AtF.fw1_wm8 (by omega)]
        rw [show G.sp - 516 - (a.V.c - 1) = (G.sp - 516 - a.V.c) + 1 by omega, bytesAt_ins_cons,
          show a.V.c - 1 + 1 = a.V.c by omega, digit_byte _ (by rw [umod10]; omega), umod10,
          Nat.mod_eq_of_lt (by omega : a.V.q.toNat < 10)]
        rw [← dig, hlt, List.singleton_append]

/-- **The digit loop** from its head with `q0` to come (`seg_loop`). -/
theorem snp_loop (G : SnG) (m : Mem) (hin : G.In m) (M0 : Mem) (FL : FacL G M0) (q0 : Nat) (a : SnL) :
    Triple (SnLS G M0 q0 a) (SnLX G M0 q0) :=
  seg_loop (S := SnLS G M0 q0) (fun a => a.V.q.toNat) (snp_loop_body G m hin M0 FL q0) a

/-! ## Into the loop -/

/-- The loop head's atoms the conversion hands over (`run_Dpm`'s,
`run_Dnm`'s row). -/
def SnV.head (c : Nat) (q : BitVec 64) : SnV :=
  { c := c
    q := q
    b19 := BitVec.ofNat 64 c
    b20 := 0x0#64
    b21 := 0x5a#64 }

theorem bytesAt_zero (m : Mem) (a : Nat) : bytesAt m a 0 = [] := rfl

/-- The loop's start: nothing written, the digits of `q` all to come. -/
theorem snLI_head (G : SnG) (M : Mem) (q : BitVec 64) (hs : 8192 ≤ G.sp) :
    SnLI G M q.toNat ⟨SnV.head (G.sp - 516) q, M⟩ := by
  have hl := decBytes_length_64 q.isLt
  refine ⟨?_, ?_, Agree.refl _ _, ?_⟩
  · show G.sp - 536 + (decBytes q.toNat).length ≤ G.sp - 516
    omega
  · exact Nat.le_refl _
  · show decBytes q.toNat ++ bytesAt M (G.sp - 516) (G.sp - 516 - (G.sp - 516)) = decBytes q.toNat
    rw [Nat.sub_self, bytesAt_zero, List.append_nil]

/-- A stack slot `[sp - k, sp - k + n)` off the loop's writes (decided on
the literals). -/
theorem snLoopW_off {sp k n : Nat} (hs : 4096 ≤ sp) (hk : k ≤ 4096)
    (h : (k ≤ 516 ∨ 536 + n ≤ k) ∧ (k ≤ 752 ∨ 760 + n ≤ k)) : ∀ j, j < n → ¬ snLoopW sp (sp - k + j) := by
  intro j hj hw
  unfold snLoopW at hw
  omega

/-- What the loop's exit reads of the memory the conversion left (and the
`memmove` root after it). -/
structure FacP (G : SnG) (s : BitVec 8) (M : Mem) : Prop where
  sgn : bytesT1 M (G.sp - 697) = s
  s832 : bytesT8 M (G.sp - 832) = 0x0#64
  s816 : bytesT8 M (G.sp - 816) = BitVec.ofNat 64 (G.sp - 512)
  s744 : bytesT8 M (G.sp - 744) = 0x8005d1b8#64
  resid : bytesT8 M (G.sp - 624) = 0x0#64
  cnt : bytesT4 M (G.sp - 632) = 0x0#32
  ret : bytesT8 M (G.sp - 848) = 0x0#64
  fp : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)
  iov : bytesT8 M (G.sp - 640) = BitVec.ofNat 64 (G.sp - 512)
  w : bytesT4 M (G.sp - 252) = 0x2b#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf
  s864 : bytesT8 M (G.sp - 864) = BitVec.ofNat 64 (G.fmt + 4)

theorem FacP.congr {G : SnG} {s : BitVec 8} {M M' : Mem} (F : FacP G s M) (ha : Agree (snLoopW G.sp) M M')
    (hs : 4096 ≤ G.sp) : FacP G s M' where
  sgn := (ha.t1 (by simpa using snLoopW_off (n := 1) hs (by decide) (by decide) 0 (by decide))).trans F.sgn
  s832 := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.s832
  s816 := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.s816
  s744 := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.s744
  resid := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.resid
  cnt := (ha.b4 (snLoopW_off hs (by decide) (by decide))).trans F.cnt
  ret := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.ret
  fp := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.fp
  iov := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.iov
  w := (ha.b4 (snLoopW_off hs (by decide) (by decide))).trans F.w
  p := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.p
  s864 := (ha.b8 (snLoopW_off hs (by decide) (by decide))).trans F.s864

theorem facL18 (G : SnG) (MD : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp) :
    FacL G (Lua.Vm.AtF.SnprintfLld.m18 (G.X {} MD)) := by
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_rd2

theorem facL35 (G : SnG) (MD : Mem) (hs : 0x8005e720 + 8192 ≤ G.sp) :
    FacL G (Lua.Vm.AtF.SnprintfLld.m35 (G.X {} MD)) := by
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_rd2

theorem facP18 (G : SnG) (MD : Mem) (F : FacD G MD) (hs : 0x8005e720 + 8192 ≤ G.sp) :
    FacP G 0x0#8 (Lua.Vm.AtF.SnprintfLld.m18 (G.X {} MD)) := by
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_rd2

theorem facP35 (G : SnG) (MD : Mem) (F : FacD G MD) (hs : 0x8005e720 + 8192 ≤ G.sp) :
    FacP G 0x2d#8 (Lua.Vm.AtF.SnprintfLld.m35 (G.X {} MD)) := by
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_rd2

/-- **A non-negative `i > 9`, to the loop head** (`run_Dpm`). -/
theorem snp_pm_toL (G : SnG) (m : Mem) (hin : G.In m)
    (hp : zopz0zKzJ_s G.i (0x0#64) = true) (hs : zopz0zI_u (0x9#64) G.i = true)
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m)) (ArmPay (G.XD m).m (G.XD m).o))
      (SnLS G (Lua.Vm.AtF.SnprintfLld.m18 (G.XD m)) G.i.toNat
      ⟨SnV.head (G.sp - 516) G.i, Lua.Vm.AtF.SnprintfLld.m18 (G.XD m)⟩) := by
  intro c h
  have hs8 : 8192 ≤ G.sp := by have := hin.sp_lo; omega
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := facD G m hin
  obtain ⟨c1, s1, h1⟩ := run_Dpm (G.XD m) ⟨hin.sp_lo, hin.sp_hi, hin.sp_al, hin.ra,
      Nat.le_trans (by decide) hin.b_lo, hin.b_ap, hin.b_hi, hin.f_lo, hin.f_hi⟩
    (by sn_u1; exact fap) (by sn_u1; exact fi) (by sn_u1; exact hp) (by sn_u1; exact hs)
    (by sn_u1; exact f760) c h
  refine ⟨c1, s1, ?_, snLI_head G _ G.i hs8⟩
  sn_unfold at h1 ⊢; simp only [SnV.head]; exact h1.repin (by pins_of h1)

/-- **A negative `i < -9`, to the loop head** (`run_Dnm`: the sign stored,
the magnitude `0 - i`). -/
theorem snp_nm_toL (G : SnG) (m : Mem) (hin : G.In m)
    (hp : zopz0zKzJ_s G.i (0x0#64) = false) (hs : zopz0zI_u (0x9#64) (0#64 - G.i) = true)
    : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m)) (ArmPay (G.XD m).m (G.XD m).o))
      (SnLS G (Lua.Vm.AtF.SnprintfLld.m35 (G.XD m)) (0#64 - G.i).toNat
      ⟨SnV.head (G.sp - 516) (0#64 - G.i), Lua.Vm.AtF.SnprintfLld.m35 (G.XD m)⟩) := by
  intro c h
  have hs8 : 8192 ≤ G.sp := by have := hin.sp_lo; omega
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := facD G m hin
  obtain ⟨c1, s1, h1⟩ := run_Dnm (G.XD m) ⟨hin.sp_lo, hin.sp_hi, hin.sp_al, hin.ra,
      Nat.le_trans (by decide) hin.b_lo, hin.b_ap, hin.b_hi, hin.f_lo, hin.f_hi⟩
    (by sn_u1; exact fap) (by sn_u1; exact fi) (by sn_u1; exact hp) (by sn_u1; exact hs)
    (by sn_u1; exact f760) c h
  refine ⟨c1, s1, ?_, snLI_head G _ (0#64 - G.i) hs8⟩
  sn_unfold at h1 ⊢; simp only [SnV.head]; exact h1.repin (by pins_of h1)

/-! ## From the loop's exit: the copies and the return -/

theorem snb_length (m : Mem) (a k : Nat) : (bytesAt m a k).length = k := by simp [bytesAt]

theorem snb_shift {m m' : Mem} {a b k : Nat} (h : ∀ i, i < k → bytesT1 m' (a + i) = bytesT1 m (b + i)) :
    bytesAt m' a k = bytesAt m b k := by
  unfold bytesAt
  exact List.map_congr_left fun i hi => h i (List.mem_range.1 hi)

theorem sub864 {sp : Nat} (h : 864 ≤ sp) : sp - 864 + 348 = sp - 516 := by omega

/-- The exit's context facts from the loop's. -/
theorem okP_of {G : SnG} {m : Mem} (hin : G.In m) {V : SnV} {M : Mem} {M0 : Mem} {q0 : Nat}
    (O : SnLO G M0 q0 V M) (M' : Mem) : Lua.Vm.AtF.SnprintfLld.Ok_P (G.X V M') :=
  ⟨hin.sp_lo, hin.sp_hi, hin.sp_al, hin.ra, Nat.le_trans (by decide) hin.b_lo, hin.b_ap, hin.b_hi, hin.f_lo,
    hin.f_hi, O.k_lo, O.k_hi, O.k_c.trans (sub864 (Nat.le_trans (by decide) hin.sp_lo)).symm⟩

/-- The digits' copy: apart from the buffer, in RAM. -/
theorem mmspan_dig {sp buf c5 k : Nat} (h1 : 0x8005e720 + 8192 ≤ sp) (h2 : sp ≤ 2 ^ 32)
    (hb : buf + 44 + 4096 ≤ sp ∨ sp ≤ buf) (hb2 : buf + 44 ≤ 2 ^ 32) (hbl : 0x8005e720 ≤ buf) (hk : k ≤ 20)
    (hc : c5 + k = sp - 516) : MmSpan buf c5 k :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The sign's copy. -/
theorem mmspan_sgn {sp buf : Nat} (h1 : 0x8005e720 + 8192 ≤ sp) (h2 : sp ≤ 2 ^ 32)
    (hb : buf + 44 + 4096 ≤ sp ∨ sp ≤ buf) (hb2 : buf + 44 ≤ 2 ^ 32) (hbl : 0x8005e720 ≤ buf) :
    MmSpan buf (sp - 697) 1 :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- The digits' copy after the sign. -/
theorem mmspan_dig1 {sp buf c5 k : Nat} (h1 : 0x8005e720 + 8192 ≤ sp) (h2 : sp ≤ 2 ^ 32)
    (hb : buf + 44 + 4096 ≤ sp ∨ sp ≤ buf) (hb2 : buf + 44 ≤ 2 ^ 32) (hbl : 0x8005e720 ≤ buf) (hk : k ≤ 20)
    (hc : c5 + k = sp - 516) : MmSpan (buf + 1) c5 k :=
  ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem snLoopW_snWd {sp buf : Nat} (hs : 1000 ≤ sp) : ∀ a, snLoopW sp a → snWdN sp buf a := by
  intro a ha
  unfold snLoopW at ha
  unfold snWdN
  omega

theorem agree_18X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m18 X) := by fmt_agree3
theorem agree_35X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m35 X) := by fmt_agree3
theorem agree_65X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m65 X) := by fmt_agree3
theorem agree_71X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) (hk : X.n 4 ≤ 20) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m71 X) := by fmt_agree3
theorem agree_78X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m78 X) := by fmt_agree3
theorem agree_81X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m81 X) := by fmt_agree3
theorem agree_87X (X : FCx) (h : 0x8005e720 + 8192 ≤ X.n 0) (hk : X.n 4 ≤ 20) :
    Agree (snWdN (X.n 0) (X.n 1)) X.m (Lua.Vm.AtF.SnprintfLld.m87 X) := by fmt_agree3

/-- **A non-negative `i > 9`, from the loop's exit to `memmove` of its
digits** (`run_Pp`). -/
theorem snp_pm_mv (G : SnG) (m : Mem) (hin : G.In m) {M0 : Mem} {q0 : Nat} (V : SnV) (M : Mem)
    (O : SnLO G M0 q0 V M) (F : FacP G 0x0#8 M) (c : Config)
    (h : SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r142 (G.X V M)) (ArmPay (G.X V M).m (G.X V M).o) c) :
    ∃ c2 M2, Steps c c2 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r145 (G.X V M2)) (ArmPay (G.X V M2).m (G.X V M2).o) c2 ∧
      MoveOut (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) M2 G.buf V.c5 V.k := by
  obtain ⟨c1, s1, h1⟩ := run_Pp (G.X V M) (okP_of hin O _) (by sn_u1; exact F.sgn) (by sn_u1; exact F.s832)
    (by sn_u1; exact F.s816) (by sn_u1; exact F.s744) (by sn_u1; exact F.resid) (by sn_u1; exact F.cnt)
    (by sn_u1; exact F.ret) (by sn_u1; exact F.fp) (by sn_u1; exact F.iov) (by sn_u1; exact F.w)
    (by sn_u1; exact F.p) c h
  obtain ⟨c2, s2, M2, hr, hmv⟩ := memmove_sum (G.sp - 992) G.buf V.c5 V.k 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) G.o
    ⟨mmspan_dig hin.sp_lo hin.sp_hi hin.b_ap hin.b_hi hin.b_lo O.k_hi O.k_c,
      Nat.le_trans (Nat.sub_le _ _) hin.sp_hi, by rfl⟩ c1
    (h1.repin (by
      simp only [Lua.Vm.AtF.SnprintfLld.r144, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h1
      pins_of h1))
  refine ⟨c2, M2, s1.trans s2, ?_, hmv⟩
  dsimp only [mmRet] at hr
  refine hr.repin ?_
  simp only [Lua.Vm.AtF.SnprintfLld.r145, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr

/-- What the root after the digits' `memmove` reads (`k` digits copied). -/
structure FacRa (G : SnG) (k : Nat) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x2b#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 512)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = BitVec.ofNat 64 k
  e880 : bytesT8 M (G.sp - 880) = 0x8005d1b8#64
  e896 : bytesT8 M (G.sp - 896) = 0x10#64
  e904 : bytesT8 M (G.sp - 904) = 0x25#64

structure FacRb (G : SnG) (k : Nat) (M : Mem) : Prop where
  e912 : bytesT8 M (G.sp - 912) = (BitVec.ofNat 64 (0) - BitVec.ofNat 64 (k + 1))
  e920 : bytesT8 M (G.sp - 920) = BitVec.ofNat 64 (G.sp - 512)
  e872 : bytesT8 M (G.sp - 872) = 0x80043ea4#64
  e888 : bytesT8 M (G.sp - 888) = 0x8005cff0#64
  e832 : bytesT8 M (G.sp - 832) = 0x0#64
  e864 : bytesT8 M (G.sp - 864) = BitVec.ofNat 64 (G.fmt + 4)
  e848 : bytesT8 M (G.sp - 848) = BitVec.ofNat 64 k
  e856 : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)

theorem facRa (G : SnG) (V : SnV) (M : Mem) (F : FacP G 0x0#8 M) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hk : V.k ≤ 20) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) M2 G.buf V.c5 V.k) : FacRa G V.k M2 := by
  obtain ⟨-, f832, f816, f744, fres, fcnt, fret, ffp, fiov, fw, fp, f864⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem facRb (G : SnG) (V : SnV) (M : Mem) (F : FacP G 0x0#8 M) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hk : V.k ≤ 20) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) M2 G.buf V.c5 V.k) : FacRb G V.k M2 := by
  obtain ⟨-, f832, f816, f744, fres, fcnt, fret, ffp, fiov, fw, fp, f864⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- `intBytes` of a non-negative `i`. -/
theorem intBytes_pos {i : BitVec 64} (hp : zopz0zKzJ_s i (0x0#64) = true) : intBytes i = decBytes i.toNat := by
  have hi : 0 ≤ i.toInt := by
    simp only [zopz0zKzJ_s, decide_eq_true_eq] at hp; simpa using hp
  rw [intBytes_eq, magOf, if_neg (by omega), if_neg (by omega), List.nil_append]

/-- **A non-negative `i > 9`, from the digits' `memmove` to the return**
(`run_Rp`). -/
theorem snp_pm_ret (G : SnG) (m : Mem) (hin : G.In m) (hp : zopz0zKzJ_s G.i (0x0#64) = true)
    (V : SnV) (M M2 : Mem) (O : SnLO G (Lua.Vm.AtF.SnprintfLld.m18 (G.XD m)) G.i.toNat V M)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) M2 G.buf V.c5 V.k)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r145 (G.X V M2)) (ArmPay (G.X V M2).m (G.X V M2).o))
      (SnPost G m) := by
  intro c2 hQ
  have := hin.sp_lo; have := hin.sp_hi; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have hk := O.k_hi; have hkc := O.k_c; have hk1 := O.k_lo
  have FP : FacP G 0x0#8 M := (facP18 G (G.MD m) (facD G m hin) hin.sp_lo).congr O.ag (by omega)
  have ag1 : Agree (snWd G) (G.MD m) M2 :=
    (((agree_18X (G.XD m) hin.sp_lo).tr (O.ag.mono (snLoopW_snWd (by omega)))).tr
      (agree_65X (G.X V M) hin.sp_lo)).tr (agree_move (G := G) hmv (by omega) (by omega))
  obtain ⟨⟨v2, v3, v4, v5, v7, v8, v9, v10, v11⟩, ⟨vfp, vfl, v6, vra, vs0, vs1, cs1, cra, cs0⟩⟩ :=
    (snSave_D G m hin).congr ag1 (by omega) (by omega)
  have agk : Agree (snWk G) m M2 :=
    ((agree_E G m hin).tr (agree_F G m hin)).tr (snWd_snWk ag1 (by omega))
  have st := stat_of hin agk
  obtain ⟨-, -, -, -, f4⟩ := fmt_of hin agk
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := facRa G V M FP hin.sp_lo hin.b_ap hk M2 hmv
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := facRb G V M FP hin.sp_lo hin.b_ap hk M2 hmv
  obtain ⟨c3, s3, h3⟩ := run_Rp (G.X V M2) (okP_of hin O _)
    (by sn_u1; exact a1) (by sn_u1; exact a2) (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5)
    (by sn_u1; exact a6) (by sn_u1; exact a7) (by sn_u1; exact a8) (by sn_u1; exact a9) (by sn_u1; exact b1)
    (by sn_u1; exact b2) (by sn_u1; exact b3) (by sn_u1; exact b4) (by sn_u1; exact b5) (by sn_u1; exact b6)
    (by sn_u1; exact st.mbtowc) (by sn_u1; exact st.mbmax) (by sn_u1; exact f4) (by sn_u1; exact vfp)
    (by sn_u1; exact vfl) (by sn_u1; exact v2) (by sn_u1; exact v3) (by sn_u1; exact v4) (by sn_u1; exact v5)
    (by sn_u1; exact v7) (by sn_u1; exact v8) (by sn_u1; exact v9) (by sn_u1; exact v10) (by sn_u1; exact v11)
    (by sn_u1; exact vra) (by sn_u1; exact vs0) (by sn_u1; exact b7) (by sn_u1; exact vs1) (by sn_u1; exact v6)
    (by sn_u1; exact cs0) (by sn_u1; exact cra) (by sn_u1; exact cs1) c2 hQ
  have hib := intBytes_pos hp
  have hl : (intBytes G.i).length = V.k := by rw [hib, ← O.dig, snb_length]
  have ag2 : Agree (snWd G) M2 _ := agree_71X (G.X V M2) hin.sp_lo hk
  refine ⟨c3, s3, Lua.Vm.AtF.SnprintfLld.m71 (G.X V M2), ?_, ?_, ?_⟩
  · rw [hl]
    dsimp only [wrRet]
    refine h3.repin ?_
    simp only [Lua.Vm.AtF.SnprintfLld.r147, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] at h3
    pins_of h3
  · rw [hl, hib, ← O.dig, bytesAt_succ]
    have k0 : bytesAt (Lua.Vm.AtF.SnprintfLld.m71 (G.X V M2)) G.buf V.k = bytesAt M2 G.buf V.k := by
      refine bytesAt_congr fun j hj => ?_
      simp only [Lua.Vm.AtF.SnprintfLld.m71, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins]
    have k1 : bytesAt (Lua.Vm.AtF.SnprintfLld.m65 (G.X V M)) V.c5 V.k = bytesAt M V.c5 V.k := by
      refine bytesAt_congr fun j hj => ?_
      simp only [Lua.Vm.AtF.SnprintfLld.m65, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
    have k2 : bytesT1 (Lua.Vm.AtF.SnprintfLld.m71 (G.X V M2)) (G.buf + V.k) = 0#8 := by
      simp only [Lua.Vm.AtF.SnprintfLld.m71, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      rw [Lua.Vm.Sim.AtF.fw1_same rfl]; decide
    rw [k0, snb_shift hmv.moved, k1, k2]
  · intro a h1 h2
    exact (agk.tr (snWd_snWk ag2 (by omega))).t1 (by simp only [snWk, snWkN]; omega)

/-! ## A negative `i < -9` from the loop's exit: the sign's copy, the digits', the return -/

theorem bytesAt_cons (m : Mem) (a n : Nat) : bytesAt m a (n + 1) = bytesT1 m a :: bytesAt m (a + 1) n := by
  simp only [bytesAt, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  congr 1
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp, Nat.succ_eq_add_one]
    rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- `intBytes` of a negative `i`. -/
theorem intBytes_neg {i : BitVec 64} (hp : zopz0zKzJ_s i (0x0#64) = false) :
    intBytes i = 45#8 :: decBytes (0#64 - i).toNat := by
  have hi : i.toInt < 0 := by
    simp only [zopz0zKzJ_s, decide_eq_false_iff_not] at hp
    have : ¬ (0 ≤ i.toInt) := by simpa using hp
    omega
  rw [intBytes_eq, magOf, if_pos hi, if_pos hi]
  rfl

/-- **A negative `i < -9`, from the loop's exit to `memmove` of its sign**
(`run_Pn`). -/
theorem snp_nm_mv (G : SnG) (m : Mem) (hin : G.In m) {M0 : Mem} {q0 : Nat} (V : SnV) (M : Mem)
    (O : SnLO G M0 q0 V M) (F : FacP G 0x2d#8 M) (c : Config)
    (h : SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r142 (G.X V M)) (ArmPay (G.X V M).m (G.X V M).o) c) :
    ∃ c2 M2, Steps c c2 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r188 (G.X V M2)) (ArmPay (G.X V M2).m (G.X V M2).o) c2 ∧
      MoveOut (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) M2 G.buf (G.sp - 697) 1 := by
  obtain ⟨c1, s1, h1⟩ := run_Pn (G.X V M) (okP_of hin O _) (by sn_u1; exact F.sgn) (by sn_u1; exact F.s832)
    (by sn_u1; exact F.s816) (by sn_u1; exact F.s744) (by sn_u1; exact F.resid) (by sn_u1; exact F.cnt)
    (by sn_u1; exact F.ret) (by sn_u1; exact F.fp) (by sn_u1; exact F.iov) (by sn_u1; exact F.w)
    (by sn_u1; exact F.p) c h
  obtain ⟨c2, s2, M2, hr, hmv⟩ := memmove_sum (G.sp - 992) G.buf (G.sp - 697) 1 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) G.o
    ⟨mmspan_sgn hin.sp_lo hin.sp_hi hin.b_ap hin.b_hi hin.b_lo,
      Nat.le_trans (Nat.sub_le _ _) hin.sp_hi, by rfl⟩ c1
    (h1.repin (by
      simp only [Lua.Vm.AtF.SnprintfLld.r187, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h1
      pins_of h1))
  refine ⟨c2, M2, s1.trans s2, ?_, hmv⟩
  dsimp only [mmRet] at hr
  refine hr.repin ?_
  simp only [Lua.Vm.AtF.SnprintfLld.r188, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr

/-- What the root after the sign's `memmove` reads. -/
structure FacN1a (G : SnG) (V : SnV) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x2b#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 G.buf
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 512)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = BitVec.ofNat 64 (V.k + 1)
  e632 : bytesT4 M (G.sp - 632) = 0x1#32
  e488 : bytesT8 M (G.sp - 488) = BitVec.ofNat 64 V.k
  e496 : bytesT8 M (G.sp - 496) = BitVec.ofNat 64 V.c5

/-- What the root after the digits' `memmove` reads that the sign's root
does not write. -/
structure FacN1b (G : SnG) (V : SnV) (M : Mem) : Prop where
  e880 : bytesT8 M (G.sp - 880) = 0x8005d1b8#64
  e896 : bytesT8 M (G.sp - 896) = 0x10#64
  e904 : bytesT8 M (G.sp - 904) = 0x25#64
  e912 : bytesT8 M (G.sp - 912) = (BitVec.ofNat 64 (0) - BitVec.ofNat 64 (V.k + 1))
  e920 : bytesT8 M (G.sp - 920) = BitVec.ofNat 64 (G.sp - 512)
  e872 : bytesT8 M (G.sp - 872) = 0x80043ea4#64
  e888 : bytesT8 M (G.sp - 888) = 0x8005cff0#64
  e832 : bytesT8 M (G.sp - 832) = 0x0#64
  e864 : bytesT8 M (G.sp - 864) = BitVec.ofNat 64 (G.fmt + 4)
  e848 : bytesT8 M (G.sp - 848) = BitVec.ofNat 64 (V.k + 1)
  e856 : bytesT8 M (G.sp - 856) = BitVec.ofNat 64 (G.sp - 264)

theorem facN1a (G : SnG) (V : SnV) (M : Mem) (F : FacP G 0x2d#8 M) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) M2 G.buf (G.sp - 697) 1) : FacN1a G V M2 := by
  obtain ⟨-, f832, f816, f744, fres, fcnt, fret, ffp, fiov, fw, fp, f864⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem facN1b (G : SnG) (V : SnV) (M : Mem) (F : FacP G 0x2d#8 M) (hs : 0x8005e720 + 8192 ≤ G.sp)
    (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (M2 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) M2 G.buf (G.sp - 697) 1) : FacN1b G V M2 := by
  obtain ⟨-, f832, f816, f744, fres, fcnt, fret, ffp, fiov, fw, fp, f864⟩ := F
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- **A negative `i < -9`, from the sign's `memmove` to the digits'**
(`run_Rn1`). -/
theorem snp_nm_mv2 (G : SnG) (m : Mem) (hin : G.In m) {M0 : Mem} {q0 : Nat} (V : SnV) (M M2 : Mem)
    (O : SnLO G M0 q0 V M) (F : FacP G 0x2d#8 M)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) M2 G.buf (G.sp - 697) 1) (c2 : Config)
    (hQ : SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r188 (G.X V M2)) (ArmPay (G.X V M2).m (G.X V M2).o) c2) :
    ∃ c3 M3, Steps c2 c3 ∧
      SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r191 (G.X V M3)) (ArmPay (G.X V M3).m (G.X V M3).o) c3 ∧
      MoveOut (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) M3 (G.buf + 1) V.c5 V.k := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := facN1a G V M F hin.sp_lo hin.b_ap M2 hmv
  obtain ⟨c3, s3, h3⟩ := run_Rn1 (G.X V M2) (okP_of hin O _) (by sn_u1; exact a1) (by sn_u1; exact a2)
    (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5) (by sn_u1; exact a6) (by sn_u1; exact a7)
    (by sn_u1; exact a8) (by sn_u1; exact a9) c2 hQ
  obtain ⟨c4, s4, M3, hr, hmv2⟩ := memmove_sum (G.sp - 992) (G.buf + 1) V.c5 V.k 0x8004e4e8#64
    (AbiFrame.mk _ _ _ _ _ _ _ _ _ _ _ _) (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) G.o
    ⟨mmspan_dig1 hin.sp_lo hin.sp_hi hin.b_ap hin.b_hi hin.b_lo O.k_hi O.k_c,
      Nat.le_trans (Nat.sub_le _ _) hin.sp_hi, by rfl⟩ c3
    (h3.repin (by
      simp only [Lua.Vm.AtF.SnprintfLld.r190, SnG.X, FCx.mk', List.getD_cons_zero,
        List.getD_cons_succ] at h3
      pins_of h3))
  refine ⟨c4, M3, s3.trans s4, ?_, hmv2⟩
  dsimp only [mmRet] at hr
  refine hr.repin ?_
  simp only [Lua.Vm.AtF.SnprintfLld.r191, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
  pins_of hr

/-- What the root after the digits' `memmove` reads (the negative path). -/
structure FacN2a (G : SnG) (V : SnV) (M : Mem) : Prop where
  w : bytesT4 M (G.sp - 252) = 0x2a#32
  p : bytesT8 M (G.sp - 264) = BitVec.ofNat 64 (G.buf + 1)
  e936 : bytesT8 M (G.sp - 936) = 0x8004975c#64
  e944 : bytesT8 M (G.sp - 944) = BitVec.ofNat 64 (G.sp - 496)
  e952 : bytesT8 M (G.sp - 952) = BitVec.ofNat 64 (G.sp - 640)
  e624 : bytesT8 M (G.sp - 624) = BitVec.ofNat 64 V.k
  e880 : bytesT8 M (G.sp - 880) = 0x8005d1b8#64
  e896 : bytesT8 M (G.sp - 896) = 0x10#64
  e904 : bytesT8 M (G.sp - 904) = 0x25#64

theorem facN2a (G : SnG) (V : SnV) (M2 : Mem) (F : FacN1a G V M2) (F' : FacN1b G V M2)
    (hs : 0x8005e720 + 8192 ≤ G.sp) (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hk : V.k ≤ 20) (M3 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) M3 (G.buf + 1) V.c5 V.k) : FacN2a G V M3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := F
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := F'
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

theorem facN2b (G : SnG) (V : SnV) (M2 : Mem) (F : FacN1a G V M2) (F' : FacN1b G V M2)
    (hs : 0x8005e720 + 8192 ≤ G.sp) (hb : G.buf + 44 + 4096 ≤ G.sp ∨ G.sp ≤ G.buf) (hk : V.k ≤ 20) (M3 : Mem)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) M3 (G.buf + 1) V.c5 V.k) : FacN1b G V M3 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := F
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := F'
  have hS : 4096 ≤ G.sp := by omega
  constructor <;> sn_mv2

/-- **A negative `i < -9`, from the digits' `memmove` to the return**
(`run_Rn2`). -/
theorem snp_nm_ret (G : SnG) (m : Mem) (hin : G.In m) (hp : zopz0zKzJ_s G.i (0x0#64) = false)
    (V : SnV) (M M2 M3 : Mem) (O : SnLO G (Lua.Vm.AtF.SnprintfLld.m35 (G.XD m)) (0#64 - G.i).toNat V M)
    (hmv : MoveOut (Lua.Vm.AtF.SnprintfLld.m78 (G.X V M)) M2 G.buf (G.sp - 697) 1)
    (hmv2 : MoveOut (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) M3 (G.buf + 1) V.c5 V.k)
    : Triple (SegSt 0x8004e4e8#64 (Lua.Vm.AtF.SnprintfLld.r191 (G.X V M3)) (ArmPay (G.X V M3).m (G.X V M3).o))
      (SnPost G m) := by
  intro c3 hQ
  have := hin.sp_lo; have := hin.sp_hi; have := hin.b_lo
  have := hin.b_ap; have := hin.b_hi; have := hin.f_lo; have := hin.f_hi
  have hk := O.k_hi; have hkc := O.k_c; have hk1 := O.k_lo
  have FP : FacP G 0x2d#8 M := (facP35 G (G.MD m) (facD G m hin) hin.sp_lo).congr O.ag (by omega)
  have F1 := facN1a G V M FP hin.sp_lo hin.b_ap M2 hmv
  have F1' := facN1b G V M FP hin.sp_lo hin.b_ap M2 hmv
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := facN2a G V M2 F1 F1' hin.sp_lo hin.b_ap hk M3 hmv2
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := facN2b G V M2 F1 F1' hin.sp_lo hin.b_ap hk M3 hmv2
  have ag1 : Agree (snWd G) (G.MD m) M3 :=
    (((((agree_35X (G.XD m) hin.sp_lo).tr (O.ag.mono (snLoopW_snWd (by omega)))).tr
      (agree_78X (G.X V M) hin.sp_lo)).tr (agree_move (G := G) hmv (by omega) (by omega))).tr
      (agree_81X (G.X V M2) hin.sp_lo)).tr (agree_move (G := G) hmv2 (by omega) (by omega))
  obtain ⟨⟨v2, v3, v4, v5, v7, v8, v9, v10, v11⟩, ⟨vfp, vfl, v6, vra, vs0, vs1, cs1, cra, cs0⟩⟩ :=
    (snSave_D G m hin).congr ag1 (by omega) (by omega)
  have agk : Agree (snWk G) m M3 :=
    ((agree_E G m hin).tr (agree_F G m hin)).tr (snWd_snWk ag1 (by omega))
  have st := stat_of hin agk
  obtain ⟨-, -, -, -, f4⟩ := fmt_of hin agk
  obtain ⟨c4, s4, h4⟩ := run_Rn2 (G.X V M3) (okP_of hin O _)
    (by sn_u1; exact a1) (by sn_u1; exact a2) (by sn_u1; exact a3) (by sn_u1; exact a4) (by sn_u1; exact a5)
    (by sn_u1; exact a6) (by sn_u1; exact a7) (by sn_u1; exact a8) (by sn_u1; exact a9) (by sn_u1; exact b4)
    (by sn_u1; exact b5) (by sn_u1; exact b6) (by sn_u1; exact b7) (by sn_u1; exact b8) (by sn_u1; exact b9)
    (by sn_u1; exact st.mbtowc) (by sn_u1; exact st.mbmax) (by sn_u1; exact f4) (by sn_u1; exact vfp)
    (by sn_u1; exact vfl) (by sn_u1; exact v2) (by sn_u1; exact v3) (by sn_u1; exact v4) (by sn_u1; exact v5)
    (by sn_u1; exact v7) (by sn_u1; exact v8) (by sn_u1; exact v9) (by sn_u1; exact v10) (by sn_u1; exact v11)
    (by sn_u1; exact vra) (by sn_u1; exact vs0) (by sn_u1; exact b10) (by sn_u1; exact vs1) (by sn_u1; exact v6)
    (by sn_u1; exact cs0) (by sn_u1; exact cra) (by sn_u1; exact cs1) c3 hQ
  have hib := intBytes_neg hp
  have hl : (intBytes G.i).length = V.k + 1 := by rw [hib, List.length_cons, ← O.dig, snb_length]
  have ag2 : Agree (snWd G) M3 _ := agree_87X (G.X V M3) hin.sp_lo hk
  refine ⟨c4, s4, Lua.Vm.AtF.SnprintfLld.m87 (G.X V M3), ?_, ?_, ?_⟩
  · rw [hl]
    dsimp only [wrRet]
    refine h4.repin ?_
    simp only [Lua.Vm.AtF.SnprintfLld.r193, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ] at h4
    pins_of h4
  · rw [hl, hib, ← O.dig, bytesAt_succ, bytesAt_cons]
    have hS : 4096 ≤ G.sp := by omega
    have k0 : bytesT1 (Lua.Vm.AtF.SnprintfLld.m87 (G.X V M3)) G.buf = 45#8 := by
      simp only [Lua.Vm.AtF.SnprintfLld.m87, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins]
      rw [hmv2.rd1 (by omega)]
      simp only [Lua.Vm.AtF.SnprintfLld.m81, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
      have e := hmv.moved 0 (by omega)
      simp only [Nat.add_zero] at e
      rw [e]
      simp only [Lua.Vm.AtF.SnprintfLld.m78, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := first | assumption | decide | rfl) only [fwS1_wm8, fwS1_wm4, fwS1_wm2, fwS1_ins]
      exact FP.sgn
    have k1 : bytesAt (Lua.Vm.AtF.SnprintfLld.m87 (G.X V M3)) (G.buf + 1) V.k = bytesAt M3 (G.buf + 1) V.k := by
      refine bytesAt_congr fun j hj => ?_
      simp only [Lua.Vm.AtF.SnprintfLld.m87, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4, Lua.Vm.Sim.AtF.fw1_ins]
    have k2 : bytesAt (Lua.Vm.AtF.SnprintfLld.m81 (G.X V M2)) V.c5 V.k = bytesAt M V.c5 V.k := by
      refine bytesAt_congr fun j hj => ?_
      simp only [Lua.Vm.AtF.SnprintfLld.m81, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
      rw [hmv.rd1 (by omega)]
      simp only [Lua.Vm.AtF.SnprintfLld.m78, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      simp (disch := omega) only [Lua.Vm.Sim.AtF.fw1_wm8, Lua.Vm.Sim.AtF.fw1_wm4]
    have k3 : bytesT1 (Lua.Vm.AtF.SnprintfLld.m87 (G.X V M3)) (G.buf + (V.k + 1)) = 0#8 := by
      simp only [Lua.Vm.AtF.SnprintfLld.m87, SnG.X, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
      rw [Lua.Vm.Sim.AtF.fw1_same (by omega)]; decide
    rw [k0, k1, snb_shift hmv2.moved, k2, k3]
  · intro a h1 h2
    exact (agk.tr (snWd_snWk ag2 (by omega))).t1 (by simp only [snWk, snWkN]; omega)

/-! ## `IntegerToStr_Statement` -/

/-- **`snprintf(buf, 44, "%lld", i)`** (lane F1-FMT): the entry to the
`'d'` conversion (`snp_toD`), then by the sign and `|i| ≤ 9`: one digit
(`snp_p1_*`, `snp_n1_*`) or the digit loop (`snp_loop`) and the copies
(`snp_pm_*`, `snp_nm_*`). -/
theorem integerToStr_proved : IntegerToStr_Statement := by
  intro sp buf fmt i r f m o hin c h
  simp only [callPre, List.cons_append, List.nil_append] at h
  obtain ⟨a4, ha4⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 14 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x14, a4⟩ :: _) h ⟨ha4, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a5, ha5⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 15 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x15, a5⟩ :: _) h ⟨ha5, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a6, ha6⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 16 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x16, a6⟩ :: _) h ⟨ha6, Vsa.Sim.SegSt.pins h⟩
  obtain ⟨a7, ha7⟩ := Option.isSome_iff_exists.mp
    (Lua.Vm.RegsOk.gpr (Vsa.Sim.SegSt.armOk h) 17 (by decide) (by decide))
  have h := Vsa.Sim.SegSt.repin (L' := ⟨Register.x17, a7⟩ :: _) h ⟨ha7, Vsa.Sim.SegSt.pins h⟩
  let G : SnG := ⟨sp, buf, fmt, i, r, f, a4, a5, a6, a7, o⟩
  have hin' : G.In m := hin
  have h0 : SegSt 0x80034de0#64 (Lua.Vm.AtF.SnprintfLld.r0 (G.X0 m)) (ArmPay (G.X0 m).m (G.X0 m).o) c := by
    refine h.repin ?_
    simp only [Lua.Vm.AtF.SnprintfLld.r0, SnG.X0, SnG.X, G, FCx.mk', List.getD_cons_zero, List.getD_cons_succ]
    pins_of h
  obtain ⟨c1, s1, h1⟩ := snp_toD G m hin' c h0
  suffices hpost : Triple (SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m))
      (ArmPay (G.XD m).m (G.XD m).o)) (SnPost G m) by
    obtain ⟨c', s', hp'⟩ := hpost c1 h1
    exact ⟨c', s1.trans s', hp'⟩
  clear h1 s1
  intro c1 h1
  have hs8 : 0x8005e720 + 8192 ≤ G.sp := hin'.sp_lo
  cases hp : zopz0zKzJ_s G.i (0x0#64)
  · cases hs : zopz0zI_u (0x9#64) (0#64 - G.i)
    · obtain ⟨c2, M1, s2, h2, hmv⟩ := snp_n1_mv G m hin' hp hs c1 h1
      obtain ⟨c3, M2, s3, h3, hmv2⟩ := snp_n1_mv2 G m hin' M1 hmv c2 h2
      obtain ⟨c4, s4, h4⟩ := snp_n1_ret G m hin' hp hs M1 M2 hmv hmv2 c3 h3
      exact ⟨c4, s2.trans (s3.trans s4), h4⟩
    · obtain ⟨c2, s2, h2⟩ := snp_nm_toL G m hin' hp hs c1 h1
      obtain ⟨c3, s3, V, M, h3, O⟩ := snp_loop G m hin' _ (facL35 G (G.MD m) hs8) _ _ c2 h2
      have FP : FacP G 0x2d#8 M := (facP35 G (G.MD m) (facD G m hin') hs8).congr O.ag (by omega)
      obtain ⟨c4, M2, s4, h4, hmv⟩ := snp_nm_mv G m hin' V M O FP c3 h3
      obtain ⟨c5, M3, s5, h5, hmv2⟩ := snp_nm_mv2 G m hin' V M M2 O FP hmv c4 h4
      obtain ⟨c6, s6, h6⟩ := snp_nm_ret G m hin' hp V M M2 M3 O hmv hmv2 c5 h5
      exact ⟨c6, s2.trans (s3.trans (s4.trans (s5.trans s6))), h6⟩
  · cases hs : zopz0zI_u (0x9#64) G.i
    · obtain ⟨c2, M1, s2, h2, hmv⟩ := snp_p1_mv G m hin' hp hs c1 h1
      obtain ⟨c3, s3, h3⟩ := snp_p1_ret G m hin' hp hs M1 hmv c2 h2
      exact ⟨c3, s2.trans s3, h3⟩
    · obtain ⟨c2, s2, h2⟩ := snp_pm_toL G m hin' hp hs c1 h1
      obtain ⟨c3, s3, V, M, h3, O⟩ := snp_loop G m hin' _ (facL18 G (G.MD m) hs8) _ _ c2 h2
      have FP : FacP G 0x0#8 M := (facP18 G (G.MD m) (facD G m hin') hs8).congr O.ag (by omega)
      obtain ⟨c4, M2, s4, h4, hmv⟩ := snp_pm_mv G m hin' V M O FP c3 h3
      obtain ⟨c5, s5, h5⟩ := snp_pm_ret G m hin' hp V M M2 O hmv c4 h4
      exact ⟨c5, s2.trans (s3.trans (s4.trans s5)), h5⟩

end Lua.Vm.Sim.Kit

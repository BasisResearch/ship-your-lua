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
  SegSt 0x80043b38#64 (Lua.Vm.AtF.SnprintfLld.r133 (G.X a.V a.M)) (ArmPay (G.X a.V a.M).m (G.X a.V a.M).o) c ∧
    SnLI G M0 q0 a

/-- The loop's exit state. -/
abbrev SnLX (G : SnG) (M0 : Mem) (q0 : Nat) (c : Config) : Prop :=
  ∃ V M, SegSt 0x80043b88#64 (Lua.Vm.AtF.SnprintfLld.r141 (G.X V M)) (ArmPay (G.X V M).m (G.X V M).o) c ∧
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
    simp only [Lua.Vm.AtF.SnprintfLld.r135] at h1
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
    (hp : zopz0zKzJ_s G.i (0x0#64) = true) (hs : zopz0zI_u (0x9#64) G.i = true) (c : Config)
    (h : SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m)) (ArmPay (G.XD m).m (G.XD m).o) c) :
    ∃ c1, Steps c c1 ∧ SnLS G (Lua.Vm.AtF.SnprintfLld.m18 (G.XD m)) G.i.toNat
      ⟨SnV.head (G.sp - 516) G.i, Lua.Vm.AtF.SnprintfLld.m18 (G.XD m)⟩ c1 := by
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
    (hp : zopz0zKzJ_s G.i (0x0#64) = false) (hs : zopz0zI_u (0x9#64) (0#64 - G.i) = true) (c : Config)
    (h : SegSt 0x80043824#64 (Lua.Vm.AtF.SnprintfLld.r34 (G.XD m)) (ArmPay (G.XD m).m (G.XD m).o) c) :
    ∃ c1, Steps c c1 ∧ SnLS G (Lua.Vm.AtF.SnprintfLld.m35 (G.XD m)) (0#64 - G.i).toNat
      ⟨SnV.head (G.sp - 516) (0#64 - G.i), Lua.Vm.AtF.SnprintfLld.m35 (G.XD m)⟩ c1 := by
  have hs8 : 8192 ≤ G.sp := by have := hin.sp_lo; omega
  obtain ⟨fap, fi, f760, fsgn, fres, fcnt, fret, ffp, fiov, fw, fp⟩ := facD G m hin
  obtain ⟨c1, s1, h1⟩ := run_Dnm (G.XD m) ⟨hin.sp_lo, hin.sp_hi, hin.sp_al, hin.ra,
      Nat.le_trans (by decide) hin.b_lo, hin.b_ap, hin.b_hi, hin.f_lo, hin.f_hi⟩
    (by sn_u1; exact fap) (by sn_u1; exact fi) (by sn_u1; exact hp) (by sn_u1; exact hs)
    (by sn_u1; exact f760) c h
  refine ⟨c1, s1, ?_, snLI_head G _ (0#64 - G.i) hs8⟩
  sn_unfold at h1 ⊢; simp only [SnV.head]; exact h1.repin (by pins_of h1)

end Lua.Vm.Sim.Kit

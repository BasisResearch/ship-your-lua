import Lua.Vm.Sim.Mem

/-!
# `_ENV.print` as the machine reads it (lane F1-7)

`OP_GETTABUP A 0 C` with `K[C] = "print"` reads, through the closure `cl`
that `luaV_execute` keeps at `8(sp)`: `cl->upvals[0]` (`uv`), `uv->v` (the
`TValue` of `_ENV`), its tag (`LUA_VTABLE`) and table `t`, then calls
`luaH_getshortstr(t, key)`, which reads `t->lsizenode`, `t->node`, the key's
hash and walks the chain from the main position (`Lua.Vm.shrWalk`).

* `Env.uv`, `Env.tv`, `Env.tab`, `Env.lsz`, `Env.node`, `Env.find`,
  `Env.pnode`: those values as total reads (`getD 0`) of a memory, so the
  arm's rows can name them as functions of the relation's complement;
* `EnvMem m cl ts R`: the facts the arm and `luaH_getshortstr` need, with the
  objects' byte ranges in a region predicate `R` (at the entry `HeapApart`,
  in the relation `HeapRead`: outside the window);
* `EnvMem.congr`: it survives a memory change off the objects
  (`OP_VARARGPREP`'s stores); `EnvGetAt.envMem`: it follows from the boot
  witness's `EnvGetAt` (`rdLE` reads).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Sim

namespace Lua.Vm.Sim

open Lua.Vm.Layout

/-- `rdLE` byte by byte, from the lowest address. -/
theorem rdLE_succ (m : Mem) (a n : Nat) :
    rdLE m a (n + 1) = (do
      let b ← m[a]?
      let r ← rdLE m (a + 1) n
      pure (b.toNat + 256 * r)) := by
  simp only [rdLE, List.range_succ_eq_map, List.foldr_cons, List.foldr_map, Nat.add_zero]
  congr 1
  funext b
  congr 1
  congr 1
  funext i acc
  rw [Nat.add_assoc, Nat.add_comm 1 i]

/-- **A little-endian read is the total read**, and fits its width. -/
theorem rdLE_spec : ∀ (n : Nat) (m : Mem) (a x : Nat), rdLE m a n = some x →
    x < 2 ^ (8 * n) ∧ bytesT m a n = BitVec.ofNat (8 * n) x
  | 0, m, a, x, h => by
    simp [rdLE] at h
    subst h
    exact ⟨by decide, rfl⟩
  | n + 1, m, a, x, h => by
    rw [rdLE_succ] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨b, hb, r, hr, rfl⟩ := h
    obtain ⟨hlt, hbt⟩ := rdLE_spec n m (a + 1) r hr
    have hb8 := b.isLt
    have hbound : b.toNat + 256 * r < 2 ^ (8 * (n + 1)) := by
      rw [show 8 * (n + 1) = 8 * n + 8 by omega, Nat.pow_add]
      have : (r + 1) * 2 ^ 8 ≤ 2 ^ (8 * n) * 2 ^ 8 := Nat.mul_le_mul_right _ hlt
      simp only [Nat.add_mul, Nat.one_mul] at this
      omega
    refine ⟨hbound, ?_⟩
    simp only [bytesT, hbt, hb, Option.getD_some]
    apply BitVec.eq_of_toNat_eq
    show (BitVec.ofNat (8 * n) r ++ b).toNat = _
    rw [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt,
      ← Nat.shiftLeft_add_eq_or_of_lt hb8, Nat.shiftLeft_eq, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hbound]
    omega

/-- The machine's total reader (`getD 0` bytes, the model's `readByte`), in
`shrWalk`'s form. -/
def totR (m : Mem) (a n : Nat) : Option Nat := some (bytesT m a n).toNat

/-- A little-endian read that succeeds is the total read. -/
theorem totR_of_rdLE {m : Mem} {a n x : Nat} (h : rdLE m a n = some x) : totR m a n = some x := by
  obtain ⟨hlt, hb⟩ := rdLE_spec n m a x h
  simp only [totR, hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem bytesT_one_eq (m : Mem) (a : Nat) : bytesT m a 1 = bytesT1 m a := by
  apply BitVec.eq_of_toNat_eq
  simp only [bytesT, bytesT1, BitVec.toNat_cast, BitVec.append_eq, BitVec.toNat_append]
  simp

/-- A total read depends only on the total reads of its bytes. -/
theorem bytesT_congrT {m m' : Mem} :
    ∀ {a n : Nat}, (∀ i, i < n → bytesT1 m (a + i) = bytesT1 m' (a + i)) → bytesT m a n = bytesT m' a n
  | _, 0, _ => rfl
  | a, n + 1, h => by
    have h0 : (m[a]?).getD 0 = (m'[a]?).getD 0 := by
      have := h 0 (by omega); simpa only [bytesT1, Nat.add_zero] using this
    have hr : bytesT m (a + 1) n = bytesT m' (a + 1) n := bytesT_congrT fun i hi => by
      have := h (i + 1) (by omega)
      rw [show a + (i + 1) = a + 1 + i by omega] at this
      exact this
    simp only [bytesT, hr, h0]

theorem bytesT1_of_rd8' {m : Mem} {a t : Nat} (h : rd8 m a = some t) :
    bytesT1 m a = BitVec.ofNat 8 t := by
  rw [← bytesT_one_eq, (rdLE_spec 1 m a t h).2]

theorem bytesT8_of_rd64' {m : Mem} {a x : Nat} (h : rd64 m a = some x) :
    bytesT8 m a = BitVec.ofNat 64 x := by
  rw [← bytesT_eight_eq]; exact (rdLE_spec 8 m a x h).2

theorem bytesT4_of_rd32' {m : Mem} {a x : Nat} (h : rd32 m a = some x) :
    bytesT4 m a = BitVec.ofNat 32 x := by
  rw [← bytesT_four_eq]; exact (rdLE_spec 4 m a x h).2

theorem toNat_of_rdLE {m : Mem} {a n x : Nat} (h : rdLE m a n = some x) :
    (bytesT m a n).toNat = x := by
  obtain ⟨hlt, hb⟩ := rdLE_spec n m a x h
  rw [hb, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

/-! ## The values -/

namespace Env

/-- `cl->upvals[0]` -/
def uv (m : Mem) (cl : Nat) : Nat := (bytesT8 m (cl + lclosureUpvalsOff)).toNat
/-- `uv->v`: `_ENV`'s `TValue` -/
def tv (m : Mem) (cl : Nat) : Nat := (bytesT8 m (uv m cl + upvalVOff)).toNat
/-- `_ENV`'s table -/
def tab (m : Mem) (cl : Nat) : Nat := (bytesT8 m (tv m cl + tvalueValOff)).toNat
/-- `t->lsizenode` -/
def lsz (m : Mem) (cl : Nat) : Nat := (bytesT1 m (tab m cl + tableLsizenodeOff)).toNat
/-- `t->node` -/
def node (m : Mem) (cl : Nat) : Nat := (bytesT8 m (tab m cl + tableNodeOff)).toNat
/-- the node array's bytes -/
def size (m : Mem) (cl : Nat) : Nat := nodeSize * 2 ^ lsz m cl
/-- the key's hash -/
def hash (m : Mem) (ts : Nat) : Nat := (bytesT4 m (ts + tstringHashOff)).toNat
/-- the key's main position -/
def mpos (m : Mem) (cl ts : Nat) : Nat := node m cl + nodeSize * (hash m ts % 2 ^ lsz m cl)
/-- `luaH_getshortstr(t, ts)`'s walk -/
def find (m : Mem) (cl ts : Nat) : Option Nat :=
  shrWalk (totR m) ts (node m cl) (node m cl + size m cl) (2 ^ lsz m cl) (mpos m cl ts)
/-- the node it finds -/
def pnode (m : Mem) (cl ts : Nat) : Nat := (find m cl ts).getD 0

end Env

/-- **`_ENV.print` in the memory `m`**, through the closure `cl`, for the key
pointer `ts`: the objects' byte ranges in the region `R`, `_ENV`'s tag, a
`lsizenode` below 31 (the mask is a positive 32-bit value), the walk's success
and the found node's value `print`. -/
structure EnvMem (m : Mem) (cl ts : Nat) (R : Nat → Nat → Prop) : Prop where
  cl_at : R (cl + lclosureUpvalsOff) 8
  uv_at : R (Env.uv m cl + upvalVOff) 8
  tv_at : R (Env.tv m cl) 16
  tab_at : R (Env.tab m cl) 32
  nodes_at : R (Env.node m cl) (Env.size m cl)
  key_at : R ts 16
  tag : bytesT1 m (Env.tv m cl + tvalueTagOff) = BitVec.ofNat 8 vTable
  lsz_lt : Env.lsz m cl < 31
  found : Env.find m cl ts = some (Env.pnode m cl ts)
  ptag : bytesT1 m (Env.pnode m cl ts + tvalueTagOff) = BitVec.ofNat 8 vLcf
  pval : bytesT8 m (Env.pnode m cl ts + tvalueValOff) = BitVec.ofNat 64 symLuaBPrint

namespace EnvMem
variable {m : Mem} {cl ts : Nat} {R : Nat → Nat → Prop}

/-- A larger region. -/
theorem mono (h : EnvMem m cl ts R) {R' : Nat → Nat → Prop} (hR : ∀ lo n, R lo n → R' lo n) :
    EnvMem m cl ts R' :=
  { h with
    cl_at := hR _ _ h.cl_at, uv_at := hR _ _ h.uv_at, tv_at := hR _ _ h.tv_at,
    tab_at := hR _ _ h.tab_at, nodes_at := hR _ _ h.nodes_at, key_at := hR _ _ h.key_at }

/-- The found node lies in the node array. -/
theorem pnode_mem (h : EnvMem m cl ts R) :
    Env.node m cl ≤ Env.pnode m cl ts ∧ Env.pnode m cl ts + nodeSize ≤ Env.node m cl + Env.size m cl :=
  shrWalk_mem h.found

/-- **The facts survive a memory that agrees on the objects.** -/
theorem congr (h : EnvMem m cl ts R) {m' : Mem}
    (hag : ∀ lo n, R lo n → ∀ a, lo ≤ a → a < lo + n → bytesT1 m' a = bytesT1 m a) :
    EnvMem m' cl ts R := by
  have r8 : ∀ {lo n a}, R lo n → lo ≤ a → a + 8 ≤ lo + n → bytesT8 m' a = bytesT8 m a :=
    fun hR h1 h2 => bytesT8_congrT fun i hi => hag _ _ hR _ (by omega) (by omega)
  have r1 : ∀ {lo n a}, R lo n → lo ≤ a → a < lo + n → bytesT1 m' a = bytesT1 m a :=
    fun hR h1 h2 => hag _ _ hR _ h1 h2
  have euv : Env.uv m' cl = Env.uv m cl := by
    simp only [Env.uv]; rw [r8 h.cl_at (Nat.le_refl _) (Nat.le_refl _)]
  have etv : Env.tv m' cl = Env.tv m cl := by
    simp only [Env.tv]; rw [euv, r8 h.uv_at (Nat.le_refl _) (Nat.le_refl _)]
  have etab : Env.tab m' cl = Env.tab m cl := by
    simp only [Env.tab]; rw [etv, r8 h.tv_at (by simp only [tvalueValOff]; omega)
      (by simp only [tvalueValOff]; omega)]
  have elsz : Env.lsz m' cl = Env.lsz m cl := by
    simp only [Env.lsz]; rw [etab, r1 h.tab_at (by simp only [tableLsizenodeOff]; omega)
      (by simp only [tableLsizenodeOff]; omega)]
  have enode : Env.node m' cl = Env.node m cl := by
    simp only [Env.node]; rw [etab, r8 h.tab_at (by simp only [tableNodeOff]; omega)
      (by simp only [tableNodeOff]; omega)]
  have ehash : Env.hash m' ts = Env.hash m ts := by
    simp only [Env.hash]
    rw [bytesT4_congrT fun i hi => hag _ _ h.key_at _ (by omega)
      (by simp only [tstringHashOff]; omega)]
  have esize : Env.size m' cl = Env.size m cl := by simp only [Env.size, elsz]
  have efind : Env.find m' cl ts = Env.find m cl ts := by
    simp only [Env.find, Env.mpos, enode, esize, elsz, ehash]
    exact shrWalk_congr fun a n h1 h2 => by
      simp only [totR]
      rw [bytesT_congrT fun i hi => hag _ _ h.nodes_at _ (by omega) (by omega)]
  have epn : Env.pnode m' cl ts = Env.pnode m cl ts := by simp only [Env.pnode, efind]
  have hpm := h.pnode_mem
  refine ⟨?_, ?_, ?_, ?_, ?_, h.key_at, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.cl_at
  · rw [euv]; exact h.uv_at
  · rw [etv]; exact h.tv_at
  · rw [etab]; exact h.tab_at
  · rw [enode, esize]; exact h.nodes_at
  · rw [etv, r1 h.tv_at (by simp only [tvalueTagOff]; omega) (by simp only [tvalueTagOff]; omega)]
    exact h.tag
  · rw [elsz]; exact h.lsz_lt
  · rw [efind, epn]; exact h.found
  · rw [epn, r1 h.nodes_at (by simp only [tvalueTagOff]; omega)
      (by simp only [tvalueTagOff, nodeSize] at hpm ⊢; omega)]
    exact h.ptag
  · rw [epn, r8 h.nodes_at (by simp only [tvalueValOff]; omega)
      (by simp only [tvalueValOff, nodeSize] at hpm ⊢; omega)]
    exact h.pval

end EnvMem

/-- **The boot witness's `EnvGetAt` is `EnvMem`** with the objects `HeapApart`. -/
theorem _root_.Lua.Vm.EnvGetAt.envMem {m : Mem} {L ci : Nat} {e : EntryPtrs} {ts : Nat}
    {s : EnvSlot} (h : EnvGetAt m L ci e ts s) :
    EnvMem m e.cl ts (HeapApart L ci e.func e.stackLast) := by
  have euv : Env.uv m e.cl = e.uv := by
    simp only [Env.uv]; rw [← bytesT_eight_eq]; exact toNat_of_rdLE h.upval
  have etv : Env.tv m e.cl = e.envv := by
    simp only [Env.tv, euv]; rw [← bytesT_eight_eq]; exact toNat_of_rdLE h.uv_v
  have etab : Env.tab m e.cl = e.env := by
    simp only [Env.tab, etv]; rw [← bytesT_eight_eq]; exact toNat_of_rdLE h.env_val
  have elsz : Env.lsz m e.cl = s.lsz := by
    simp only [Env.lsz, etab]; rw [← bytesT_one_eq]; exact toNat_of_rdLE h.lsz
  have enode : Env.node m e.cl = s.node := by
    simp only [Env.node, etab]; rw [← bytesT_eight_eq]; exact toNat_of_rdLE h.node
  have ehash : Env.hash m ts = s.hash := by
    simp only [Env.hash]; rw [← bytesT_four_eq]; exact toNat_of_rdLE h.hash
  have efind : Env.find m e.cl ts = some s.r := by
    simp only [Env.find, Env.mpos, Env.size, elsz, enode, ehash]
    exact shrWalk_mono (fun _ _ _ hx => totR_of_rdLE hx) h.walk
  have epn : Env.pnode m e.cl ts = s.r := by simp only [Env.pnode, efind, Option.getD_some]
  refine ⟨h.cl_at, ?_, ?_, ?_, ?_, h.key_at, ?_, ?_, ?_, ?_, ?_⟩
  · rw [euv]; exact h.uv_at
  · rw [etv]; exact h.tv_at
  · rw [etab]; exact h.tab_at
  · simp only [Env.size, enode, elsz]; exact h.nodes_at
  · rw [etv]; exact bytesT1_of_rd8' h.env_tag
  · rw [elsz]; exact h.lsz_lt
  · rw [efind, epn]
  · rw [epn]; exact bytesT1_of_rd8' h.tag
  · rw [epn]; exact bytesT8_of_rd64' h.val

end Lua.Vm.Sim

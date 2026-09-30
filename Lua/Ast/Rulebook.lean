/-!
# Rulebooks: a big-step relation as the graph of one program per call

A **rulebook** gives, for every judgment instance `c : C` (a "call"), one
non-recursive program `rb c : Prog C R (R c)` that may *call* other
judgment instances and branch on their answers with ordinary Lean
`if`/`match`. The program is the construct's rules: its premises are its
calls, its side conditions are its branches, and "no rule applies" is
`fail`.

* **The relation** `Sem rb c r` is the least relation resolving the calls:
  `Runs rb p a` follows the program `p`, answering each `call c' k` by some
  `r'` with `Sem rb c' r'`.
* **The interpreter** `solve rb fuel c` answers each call by recursion on
  `fuel`.
* **One generic theorem**, `sem_iff_solve : Sem rb c r ↔ ∃ fuel, solve rb
  fuel c = some r`, proved once for every rulebook. Soundness and
  completeness of the interpreter are its two directions, and determinism
  (`Sem.det`) follows because `solve` is a function monotone in its fuel.

This is the Bove–Capretta graph of a reified recursion (free "call" monad);
`abstractions/ROUND-1.md` §3 candidate C4.
-/

namespace Lua.Rulebook

/-- A program over the call effect: return, call a judgment instance and
continue with its answer, or fail (no rule). -/
inductive Prog (C : Type) (R : C → Type) (α : Type) : Type where
  | ret (a : α)
  | call (c : C) (k : R c → Prog C R α)
  | fail

variable {C : Type} {R : C → Type}

namespace Prog

def bind {α β : Type} : Prog C R α → (α → Prog C R β) → Prog C R β
  | .ret a, f => f a
  | .call c k, f => .call c fun r => (k r).bind f
  | .fail, _ => .fail

instance : Monad (Prog C R) where
  pure := .ret
  bind := Prog.bind

/-- Call a judgment instance for its answer. -/
abbrev ask (c : C) : Prog C R (R c) := .call c .ret

/-- A partial primitive: `none` is "no rule". -/
def lift {α : Type} : Option α → Prog C R α
  | some a => .ret a
  | none => .fail

/-- Run a program, answering calls with `h`. -/
def handle {α : Type} (h : (c : C) → Option (R c)) : Prog C R α → Option α
  | .ret a => some a
  | .call c k => match h c with
    | some r => (k r).handle h
    | none => none
  | .fail => none

end Prog

/-- One program per call. -/
abbrev Rulebook (C : Type) (R : C → Type) := (c : C) → Prog C R (R c)

variable (rb : Rulebook C R)

/-- `Runs rb p a`: the program `p` can return `a` when every call is
answered by the relation. -/
inductive Runs : {α : Type} → Prog C R α → α → Prop where
  | ret {α : Type} {a : α} : Runs (.ret a) a
  | call {α : Type} {c : C} {k : R c → Prog C R α} {r : R c} {a : α} :
      Runs (rb c) r → Runs (k r) a → Runs (.call c k) a

/-- **The relation of a rulebook**: the least one resolving the calls. -/
def Sem (c : C) (r : R c) : Prop := Runs rb (rb c) r

/-- **The interpreter of a rulebook**, with `fuel` bounding the call depth. -/
def solve : Nat → (c : C) → Option (R c)
  | 0, _ => none
  | n + 1, c => (rb c).handle (solve n)

variable {rb}

/-! ## The generic theorems -/

namespace Prog

theorem handle_mono {h h' : (c : C) → Option (R c)}
    (hh : ∀ c r, h c = some r → h' c = some r) {α : Type} {p : Prog C R α} {a : α}
    (e : p.handle h = some a) : p.handle h' = some a := by
  induction p with
  | ret => exact e
  | fail => exact e
  | call c k ih =>
    simp only [handle] at e ⊢
    split at e
    · rename_i r hr; rw [hh c r hr]; exact ih r e
    · cases e

theorem handle_sound {h : (c : C) → Option (R c)} (hh : ∀ c r, h c = some r → Sem rb c r)
    {α : Type} {p : Prog C R α} {a : α} (e : p.handle h = some a) : Runs rb p a := by
  induction p with
  | ret => cases e; exact .ret
  | fail => cases e
  | call c k ih =>
    simp only [handle] at e
    split at e
    · rename_i r hr; exact .call (hh c r hr) (ih r e)
    · cases e

end Prog

theorem solve_succ {n : Nat} {c : C} {r : R c} (h : solve rb n c = some r) :
    solve rb (n + 1) c = some r := by
  induction n generalizing c r with
  | zero => cases h
  | succ n ih => exact Prog.handle_mono (fun _ _ => ih) h

theorem solve_mono {n m : Nat} (hnm : n ≤ m) {c : C} {r : R c} (h : solve rb n c = some r) :
    solve rb m c = some r := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact solve_succ ih

theorem solve_sound : ∀ {n : Nat} {c : C} {r : R c}, solve rb n c = some r → Sem rb c r
  | 0, _, _, h => by cases h
  | _ + 1, _, _, h => Prog.handle_sound (fun _ _ => solve_sound) h

theorem Runs.complete {α : Type} {p : Prog C R α} {a : α} (h : Runs rb p a) :
    ∃ n, p.handle (solve rb n) = some a := by
  induction h with
  | ret => exact ⟨0, rfl⟩
  | @call _ c k r a _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁⟩ := ih₁
    obtain ⟨n₂, h₂⟩ := ih₂
    have e₁ : solve rb (max n₁ n₂ + 1) c = some r :=
      solve_mono (Nat.succ_le_succ (Nat.le_max_left _ _)) (n := n₁ + 1) h₁
    refine ⟨max n₁ n₂ + 1, ?_⟩
    simp only [Prog.handle, e₁]
    exact Prog.handle_mono (fun _ _ => solve_mono (Nat.le_succ_of_le (Nat.le_max_right _ _))) h₂

/-- **The graph law**: a rulebook's relation is the graph of its
interpreter. -/
theorem sem_iff_solve {c : C} {r : R c} : Sem rb c r ↔ ∃ n, solve rb n c = some r :=
  ⟨fun h => let ⟨n, e⟩ := Runs.complete h; ⟨n + 1, e⟩, fun ⟨_, e⟩ => solve_sound e⟩

/-- **Determinism of every rulebook's relation.** -/
theorem Sem.det {c : C} {r r' : R c} (h : Sem rb c r) (h' : Sem rb c r') : r = r' := by
  obtain ⟨n, e⟩ := sem_iff_solve.1 h
  obtain ⟨n', e'⟩ := sem_iff_solve.1 h'
  have := (solve_mono (Nat.le_max_left n n') e).symm.trans (solve_mono (Nat.le_max_right n n') e')
  exact Option.some.inj this

/-! ## Reading rules back (for derived rule lemmas) -/

@[simp] theorem runs_ret {α : Type} {a b : α} : Runs rb (.ret a : Prog C R α) b ↔ a = b :=
  ⟨fun h => by cases h; rfl, fun h => h ▸ .ret⟩

@[simp] theorem runs_fail {α : Type} {b : α} : ¬ Runs rb (.fail : Prog C R α) b := nofun

@[simp] theorem runs_call {α : Type} {c : C} {k : R c → Prog C R α} {a : α} :
    Runs rb (.call c k) a ↔ ∃ r, Sem rb c r ∧ Runs rb (k r) a :=
  ⟨fun h => by cases h; exact ⟨_, ‹_›, ‹_›⟩, fun ⟨_, h₁, h₂⟩ => .call h₁ h₂⟩

@[simp] theorem runs_bind {α β : Type} {p : Prog C R α} {f : α → Prog C R β} {b : β} :
    Runs rb (p >>= f) b ↔ ∃ a, Runs rb p a ∧ Runs rb (f a) b := by
  show Runs rb (p.bind f) b ↔ _
  induction p with
  | ret a => simp [Prog.bind]
  | fail => simp [Prog.bind]
  | call c k ih => simp only [Prog.bind, runs_call, ih]; exact
      ⟨fun ⟨r, hr, a, h₁, h₂⟩ => ⟨a, ⟨r, hr, h₁⟩, h₂⟩, fun ⟨a, ⟨r, hr, h₁⟩, h₂⟩ => ⟨r, hr, a, h₁, h₂⟩⟩

@[simp] theorem runs_pure {α : Type} {a b : α} : Runs rb (pure a : Prog C R α) b ↔ a = b :=
  runs_ret

@[simp] theorem runs_lift {α : Type} {o : Option α} {b : α} :
    Runs rb (Prog.lift o : Prog C R α) b ↔ o = some b := by
  cases o <;> simp [Prog.lift]

@[simp] theorem runs_ask {c : C} {r : R c} : Runs rb (Prog.ask c) r ↔ Sem rb c r := by
  simp

end Lua.Rulebook

/-!
# Clock (TRUSTED: part of the OS interface)

A clock is only constrained to be monotone: a reading returns any value at
least the previous one (`gettimeofday`/`times`/`clock_gettime` on Linux
with `CLOCK_MONOTONIC`; the wall clock can in fact go backwards, so a
program that reads `CLOCK_REALTIME` is outside this spec). The bare-metal
build's clock (`c/src/htif.c`: `_gettimeofday` and `_times` return 0) is
the instance `Clock.frozen`, which meets the spec (`frozen_ok`).
-/

namespace TCB.Os

structure Clock where
  /-- the last value read, in microseconds -/
  now : Nat
  deriving DecidableEq, Repr

namespace Clock

def init : Clock := ⟨0⟩

/-- The spec: a reading `t` is allowed iff `t ≥ now`, and becomes `now`. -/
def Allowed (c : Clock) (t : Nat) : Prop := c.now ≤ t

instance (c : Clock) (t : Nat) : Decidable (c.Allowed t) := inferInstanceAs (Decidable (_ ≤ _))

def read (_c : Clock) (t : Nat) : Clock := ⟨t⟩

/-- The bare-metal clock: every reading is 0. -/
def frozen : Nat := 0

/-- The bare-metal clock meets the spec from the initial clock, forever. -/
theorem frozen_ok : ∀ n : Nat, (Nat.repeat (fun c => read c frozen) n init).Allowed frozen := by
  intro n
  induction n with
  | zero => exact Nat.le_refl _
  | succ n _ => exact Nat.le_refl _

end Clock
end TCB.Os

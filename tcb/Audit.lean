import TCB

/-! Axiom audit of the proved lemmas of the TCB library
(`lake env lean tcb/Audit.lean`; `scripts/check_all.sh` checks the output). -/

#print axioms TCB.Os.allowed_sound
#print axioms TCB.Os.allowed_complete
#print axioms TCB.Os.checkFrom_sound
#print axioms TCB.Os.checkTrace_sound
#print axioms TCB.Os.Clock.frozen_ok

/-!
# Process (TRUSTED: part of the OS interface)

What a single process sees of its creation and end: the command line and
environment it was started with (fixed for the whole run), and its exit
status. CakeML's command-line model (`basis/clFFIScript.sml`) likewise
treats the argument list as fixed input.
-/

namespace TCB.Os

structure Process where
  argv : List String
  env : List (String × String)
  /-- `some e` once the process has called `exit e` -/
  exited : Option Nat
  deriving DecidableEq, Repr

namespace Process

def init (argv : List String) (env : List (String × String) := []) : Process :=
  ⟨argv, env, none⟩

/-- `getenv`: the first binding of the name, as `getenv(3)` returns it. -/
def getenv (p : Process) (name : String) : Option String :=
  (p.env.find? (·.1 == name)).map (·.2)

end Process
end TCB.Os

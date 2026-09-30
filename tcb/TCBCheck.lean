import TCB.Os.Trace

/-! `tcbcheck FILE…`: check traces (`TCB/Os/Trace.lean` format) against
the OS specification (`TCB.Os.checkTrace`, sound by `checkTrace_sound`).
Every trace starts from `OsState.init` (empty root directory, fds 0-2 the
console streams). Prints one TSV row per trace
(`name  verdict  step  line  observed  allowed…`) and a summary on stderr.
Exit code 0 iff no trace is rejected. -/

open TCB.Os TCB.Os.Trace

def main (args : List String) : IO UInt32 := do
  let mut nTraces := 0
  let mut nSteps := 0
  let mut acc := 0
  let mut rej := 0
  let mut spc := 0
  let mut uns := 0
  for f in args do
    let text ← IO.FS.readFile f
    match parseFile text with
    | .error e => IO.eprintln s!"{f}: parse error: {e}"; return 2
    | .ok traces =>
      for t in traces do
        nTraces := nTraces + 1
        nSteps := nSteps + t.steps.length
        match checkTrace (OsState.init) t.steps with
        | .accepted _ =>
          if t.unsupportedAt.isSome then
            uns := uns + 1
            IO.println s!"{t.name}\tunsupported\t{t.unsupportedAt.getD 0}"
          else
            acc := acc + 1
            IO.println s!"{t.name}\taccepted"
        | .special i =>
          spc := spc + 1
          IO.println s!"{t.name}\tspecial\t{i}\t{t.lines.getD i ""}"
        | .rejected i =>
          rej := rej + 1
          -- the allowed returns from the states reached before step i
          let pre := checkTrace OsState.init (t.steps.take i)
          let allowedStr := match pre with
            | .accepted ss => " | ".intercalate ((ss.flatMap fun s => (match t.steps[i]? with | some (c, _) => allowedRets s c | none => [])).eraseDups)
            | _ => "?"
          let line := t.lines.getD i ""
          let observed := match line.splitOn " => " with | [_, r] => r | _ => "?"
          let call := match line.splitOn " => " with | [c, _] => c | _ => line
          IO.println s!"{t.name}\trejected\t{i}\t{call}\t{observed}\t{allowedStr}"
  IO.eprintln s!"traces {nTraces} steps {nSteps} accepted {acc} rejected {rej} special {spc} unsupported {uns}"
  return (if rej == 0 then 0 else 1)

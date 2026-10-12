#!/usr/bin/env python3
"""Round 5 §2b: emit a TRACED copy of `__adddf3`'s and `__subdf3`'s lifted
functions into `RtoCheck.lean`, between the markers
`-- BEGIN rto_trace.py` / `-- END rto_trace.py`.

The copy is mechanical: each generated node `N_<pc> m s r v.. : BitVec 64` of
`Lua/Vm/Fn/<R>/Defs.lean` becomes `T_<pc> m s r v.. : Tr`, where
`Tr = List Ev × BitVec 64`:
* a node prepends `Ev.node pc [live-ins]` to its callee's trace;
* a node whose guard is soft-fp's inexactness test `(X &&& 7) == 0` (or
  `!= 0`; `_FP_ROUND`'s entry) also records `Ev.probe pc X E`, with `X` the
  guard's own operand, evaluated from the node's live-ins, and `E` the
  site's exponent (`SITE_E`, a hand table: every detected site must be in it);
* the round sites the compiler folded into a constant (`FOLDED`) record
  `Ev.folded pc X E`, and the pack join records `Ev.join pc f E`;
* a leaf (a pack) returns `([], value)`.
The value component is the generated `F` bit for bit (checked by `#eval`).
No node body is edited: guards, arguments and leaves are copied verbatim.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[3]
CHECK = ROOT / "abstractions/checks/round5/RtoCheck.lean"
HDR = re.compile(r"^def (N_[0-9a-f]+|F) \(m : Mem\) \(s : Nat\) \(r : BitVec 64\)(.*) : BitVec 64 :=$")
PROBE = re.compile(r"^\(\((.*) &&& sign_extend \(m := 64\) \(0x007#12\)\) [!=]= \(0#64\)\) = true$")

# Per round site: the biased semiraw exponent the probed mantissa is read at
# (an expression over the node's live-ins; read off the node's callees).
# Every auto-detected probe must be listed (the script fails otherwise).
SITE_E = {
    "Adddf3": {
        "0x8002dc60": "v10",            # same exponent, carry: E+1 already
        "0x8002dd48": "v15",            # aligned add, no carry
        "0x8002dbcc": "v15",            # aligned add, carry SRS by 1: E+1 already
        "0x8002da50": "v15 - v10",      # cancellation, renormalised by clz (normal)
        "0x8002d854": "0#64",           # cancellation, renormalised, subnormal (second SRS)
        "0x8002db30": "v15",            # aligned subtract, bit 55 kept
    },
    "Subdf3": {
        "0x8002efc8": "v13",
        "0x8002ee98": "v15",
        "0x8002ed4c": "v15",
        "0x8002ec00": "v15 - v10",
        "0x8002eb28": "0#64",
        "0x8002ecdc": "v15",
    },
}
# Round sites the compiler folded into a constant (no inexactness test): the
# pre-round mantissa is implicit. (pc, mantissa, exponent), read off the body.
FOLDED = {
    "Adddf3": {
        "0x8002d928": ("v13 + 1", "v15"),   # d >= 57, add: sticky 1, then +4
        "0x8002dc4c": ("v30 + 1", "v28"),   # d >= 57, add (swapped operands)
        "0x8002da1c": ("v14", "v15"),       # d >= 57, subtract: A - 1, then +4
    },
    "Subdf3": {
        "0x8002ef7c": ("v29 + 1", "v13"),
        "0x8002ed14": ("v28 + 1", "v15"),
        "0x8002ebe4": ("v29", "v15"),
    },
}
# The pack join (`_FP_PACK_SEMIRAW` entry): (pc, mantissa, exponent).
JOIN = {"Adddf3": ("0x8002d92c", "v13", "v15"), "Subdf3": ("0x8002ea50", "v28", "v15")}
CALL = re.compile(r"^(N_[0-9a-f]+) ")


def arg_names(params: str):
    params = params.strip()
    if not params:
        return []
    m = re.fullmatch(r"\(([v0-9 ]+) : BitVec 64\)", params)
    assert m, params
    return m.group(1).split()


def branch(e: str) -> str:
    e = e.strip()
    if CALL.match(e) or e.startswith("N_"):
        return "T_" + e[2:]
    return f"([], {e})"


def traced(routine: str) -> str:
    src = (ROOT / f"Lua/Vm/Fn/{routine}/Defs.lean").read_text()
    body = src.split("\ndef Nm_", 1)[0]
    defs = re.split(r"\n(?=def )", body)
    out = []
    nprobe = 0
    for d in defs:
        if not d.startswith("def "):
            continue
        lines = [l for l in d.rstrip().split("\n") if l.strip()]
        h = HDR.match(lines[0])
        assert h, lines[0]
        name, params = h.group(1), h.group(2)
        args = arg_names(params)
        pc = "0" if name == "F" else "0x" + name[2:]
        tname = "T_F" if name == "F" else "T_" + name[2:]
        probes = []
        rest = lines[1:]
        if len(rest) == 1:
            e = branch(rest[0])
        else:
            assert len(rest) == 4 and rest[0].startswith("  if ") and rest[0].endswith(" then") \
                and rest[2] == "  else", rest
            cond = rest[0][len("  if "):-len(" then")]
            pm = PROBE.match(cond)
            if pm:
                probes.append(f"Ev.probe {pc} ({pm.group(1)}) ({SITE_E[routine].pop(pc)})")
                nprobe += 1
            e = f"if {cond} then {branch(rest[1])} else {branch(rest[3])}"
        if pc in FOLDED[routine]:
            f, e_ = FOLDED[routine].pop(pc)
            probes.append(f"Ev.folded {pc} ({f}) ({e_})")
        if pc == JOIN[routine][0]:
            probes.append(f"Ev.join {pc} ({JOIN[routine][1]}) ({JOIN[routine][2]})")
        evs = [f"Ev.node {pc} [{', '.join(args)}]"] + probes
        out.append(
            f"def {tname} (m : Mem) (s : Nat) (r : BitVec 64){params} : Tr :=\n"
            f"  let t := {e}\n  ([{', '.join(evs)}] ++ t.1, t.2)\n")
    assert not SITE_E[routine] and not FOLDED[routine], (SITE_E[routine], FOLDED[routine])
    print(f"{routine}: {len(out)} traced nodes, {nprobe} probes", file=sys.stderr)
    return (f"namespace {routine}T\nopen Lua.Vm.Fn.{routine}\n\n" + "\n".join(out)
            + f"\nend {routine}T\n")


def main():
    gen = ("-- BEGIN rto_trace.py (GENERATED from Lua/Vm/Fn/{Adddf3,Subdf3}/Defs.lean; "
           "rerun the script, do not edit)\n"
           + traced("Adddf3") + "\n" + traced("Subdf3") + "-- END rto_trace.py\n")
    text = CHECK.read_text()
    a = text.index("-- BEGIN rto_trace.py")
    b = text.index("-- END rto_trace.py\n") + len("-- END rto_trace.py\n")
    CHECK.write_text(text[:a] + gen + text[b:])


if __name__ == "__main__":
    main()

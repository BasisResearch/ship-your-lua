#!/usr/bin/env python3
"""disasm_to_segment.py — sites TSV (from disasm_to_sites.py) -> DRAFT
segment JSON for gen_segment.py --mode straight.

    python3 scripts/syi/disasm_to_segment.py 0x800069f0 0x80006a0c \
        --sites SITES.tsv [--theorem tr_foo] [--loaded-pred Vsa.Sim.Code.XLoaded]
        [--site-suffix _gen] [--allow-unsupported] [-o out.json]
    python3 scripts/syi/disasm_to_segment.py 0x8001be84 0x8001be98 \
        --from-elf [--path branches.txt] ...     # classify the ELF directly

Takes the classified instruction rows of a range (the disasm_to_sites.py
output, with exactly ONE arm kept per branch) and emits a gen_segment.py
core segment spec with everything mechanical filled in:

  * the step list in address order, each with the right gen_segment class,
    the gen_sites.py site name, and the site-call argument tail laid out in
    the generated batteries' uniform signature order;
  * def-use analysis over the operands:
      - registers READ before written in the segment become the initial
        `pins` list, with auto-named ghost values `v<reg>` (and matching
        `(v<reg> : BitVec 64)` theorem parameters);
      - WRITTEN registers get per-step `rd`/`rd_val` entries — gen_segment's
        pin drop/re-add choreography then handles the bundle automatically;
  * per-class placeholders, every one spelled `TODO(...)` so gen_segment.py
    REFUSES to run until they are filled (its TODO gate):
      - loads: the byte value params + `hlo/hhiram/hhtif/halign/h<j>`
        byte-hypothesis slots,
      - stores: `key`/`key_rw`/`loaded_via` (+ the 4 in-call side conditions),
      - branches: a `pre_lines` guard-fact skeleton feeding `hguard$k`
        (concrete-operand guards can instead use `"guard": "decide"` —
        replace the two TODOs with that option and `$guard` in the call),
      - jal: the link step is emitted complete, followed by a
        `class: call` placeholder step for the callee glue,
      - jr: `pc_val`/`pc_rw`/`htgt`;
  * `pre`/`post`/`pre_bind.obtain`/`post_proof` stay segment-specific:
    `pre`/`post` are TODO, `pre_bind` is emitted with the standard names
    and a TODO obtain pattern.  (Alternatively switch the draft to
    `"boundary": "segst"` by hand — then pre/post/pre_bind/post_proof are
    synthesized and only the value/guard/store TODOs remain.)

The value-annotation slots (`rd_val` rewrites like `li31_val`/`dec1_fwd`,
guard derivations, store-key lemmas) are exactly the residue that
gen_segment.py requires as explicit proof inputs; the draft carries the
raw machine-level value expression for each write in an informational
`"raw_val"` key (ignored by gen_segment.py) so filling `rd_val`/`rw` is a
lookup, not a re-derivation.

ship-your-lua changes (ATTRIBUTION.md):
  * Nothing is dropped. The copy skipped `#UNSUPPORTED` rows as comments
    and so drafted 2 steps for OP_MOVE's 5 instructions. Now an
    `#UNSUPPORTED` row in the range, or an address of the range with no row,
    is an error; `--allow-unsupported` instead drafts such a row as an
    explicit `"class": "UNSUPPORTED"` step whose TODO blocks gen_segment.py.
  * The classes disasm_to_sites.py gained for the luaV_execute arms are
    drafted: `andi ori xori slti sltiu`, `slli srli srai slliw srliw sraiw`,
    `and or xor slt sltu sll srl sra addw sllw srlw sraw`, `lui auipc`,
    `lb lh lhu lwu`, `sh`, `jalr`. A step whose class gen_sites.py has no
    site battery for carries `"site_battery": "TODO(...)"`, and one whose
    class gen_segment.py cannot emit (`sh`, `jalr`) carries
    `"gen_segment": "TODO(...)"`; both block gen_segment.py by its TODO gate.
  * `--from-elf` runs disasm_to_sites.py's classifier on the range itself.
"""

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]   # repository root

# Instruction classes (disasm_to_sites.py's TSV classes), by operand shape.
ALU_IMM = {"alu_addi", "addiw", "andi", "ori", "xori", "slti", "sltiu"}
SHIFT_IMM = {"slli", "srli", "srai", "slliw", "srliw", "sraiw"}
ALU_RR = {"alu_add", "sub", "subw", "and", "or", "xor", "slt", "sltu",
          "sll", "srl", "sra", "addw", "sllw", "srlw", "sraw"}
UTYPE = {"lui", "auipc"}
LOAD_BYTES = {"ld": 8, "lw": 4, "lwu": 4, "lh": 2, "lhu": 2, "lbu": 1,
              "lb": 1}
STORE_BYTES = {"sd": 8, "sw": 4, "sh": 2, "sb": 1}
BRANCH = {"branch_taken", "branch_nottaken"}
KNOWN = ALU_IMM | SHIFT_IMM | ALU_RR | UTYPE | set(LOAD_BYTES) | \
    set(STORE_BYTES) | BRANCH | {"jal", "j", "jr", "jalr"}

# gen_sites TSV class -> gen_segment step class
SEG_CLASS = {**{c: "alu" for c in ALU_IMM | SHIFT_IMM | ALU_RR | UTYPE},
             **{c: "alu" for c in LOAD_BYTES},
             **{c: c for c in STORE_BYTES},
             "branch_taken": "btaken", "branch_nottaken": "bnottaken",
             "jal": "jal", "j": "j", "jr": "jr", "jalr": "jalr"}
# Classes scripts/syi/gen_sites.py has a site battery for (a load through its
# TOTAL class, `TOT_LOAD`).
sys.path.insert(0, str(Path(__file__).resolve().parent))
import gen_sites as _gen_sites  # noqa: E402
_TOT = {"ld": "ld_tot", "lw": "lw_tot", "lbu": "lbu_tot", "lh": "lh_tot",
        "lhu": "lhu_tot", "lwu": "lwu_tot"}
GEN_SITES = {c for c in KNOWN if _TOT.get(c, c) in _gen_sites.CLASS_EMITTERS}
# Step classes scripts/syi/gen_segment.py can emit.
GEN_SEGMENT = {"alu", "sd", "sw", "sh", "sb", "btaken", "bnottaken", "jal", "jr", "jalr",
               "j", "call"}

BITOP = {"andi": "&&&", "ori": "|||", "xori": "^^^",
         "and": "&&&", "or": "|||", "xor": "^^^"}


def sext(value: int, bits: int) -> int:
    if value & (1 << (bits - 1)):
        value -= 1 << bits
    return value


class Instr:
    def __init__(self, addr, word, cls, ops, asm):
        self.addr, self.word, self.cls, self.ops, self.asm = \
            addr, word, cls, ops, asm

    def reads(self) -> list[int]:
        c, o = self.cls, self.ops
        if c in ALU_IMM or c in SHIFT_IMM or c in LOAD_BYTES or c == "jalr":
            rs = [int(o[1])]
        elif c in ALU_RR or c in BRANCH:
            rs = [int(o[1]), int(o[2])]
        elif c in STORE_BYTES:
            rs = [int(o[1]), int(o[0])]     # address base, stored value
        elif c == "jr":
            rs = [int(o[0])]
        else:                               # jal / j / lui / auipc
            rs = []
        return [r for r in dict.fromkeys(rs) if r != 0]

    def writes(self) -> int | None:
        c, o = self.cls, self.ops
        if c in ALU_IMM or c in SHIFT_IMM or c in ALU_RR or c in UTYPE \
                or c in LOAD_BYTES or c in ("jal", "jalr"):
            return int(o[0]) or None
        return None

    def vregs(self) -> list[int]:
        """Registers whose value/pin the site call takes, in battery order."""
        c, o = self.cls, self.ops
        if c in ALU_RR or c in BRANCH:
            rs = o[1:3]
        elif c in ALU_IMM or c in SHIFT_IMM or c in LOAD_BYTES or c == "jalr":
            rs = o[1:2]
        elif c in STORE_BYTES:
            rs = [o[1], o[0]]
        elif c == "jr":
            rs = o[0:1]
        else:
            rs = []
        return [r for r in dict.fromkeys(int(x) for x in rs) if r != 0]

    def raw_val(self) -> str | None:
        """The machine-level written-value expression (informational)."""
        c, o = self.cls, self.ops
        v = lambda r: f"v{r}" if int(r) else "(0#64)"
        imm = f"sign_extend (m := 64) (0x{o[2]}#12)" if len(o) > 2 else ""
        lo32 = lambda x: f"(Sail.BitVec.extractLsb {x} 31 0)"
        sx32 = lambda x: f"(sign_extend (m := 64) {x})"
        if c == "alu_addi":
            return f"({v(o[1])} + {imm})"
        if c == "addiw":
            return sx32(f"(Sail.BitVec.extractLsb ({v(o[1])} + {imm}) 31 0)")
        if c in ("andi", "ori", "xori"):
            return f"({v(o[1])} {BITOP[c]} {imm})"
        if c in ("slti", "sltiu"):
            cmp = "slt" if c == "slti" else "ult"
            return f"(if BitVec.{cmp} {v(o[1])} ({imm}) then 1#64 else 0#64)"
        if c in SHIFT_IMM:
            n = int(o[2], 16)
            x = v(o[1]) if c in ("slli", "srli", "srai") else lo32(v(o[1]))
            e = {"sl": f"({x} <<< {n})", "sr": f"({x} >>> {n})",
                 "sa": f"(BitVec.sshiftRight {x} {n})"}[c[:2]]
            return e if c in ("slli", "srli", "srai") else sx32(e)
        if c == "alu_add":
            return f"({v(o[1])} + {v(o[2])})"
        if c == "sub":
            return f"({v(o[1])} - {v(o[2])})"
        if c in ("and", "or", "xor"):
            return f"({v(o[1])} {BITOP[c]} {v(o[2])})"
        if c in ("slt", "sltu"):
            cmp = "slt" if c == "slt" else "ult"
            return f"(if BitVec.{cmp} {v(o[1])} {v(o[2])} then 1#64 else 0#64)"
        if c in ("sll", "srl", "sra"):
            sh = f"({v(o[2])}.toNat % 64)"
            return {"sll": f"({v(o[1])} <<< {sh})",
                    "srl": f"({v(o[1])} >>> {sh})",
                    "sra": f"(BitVec.sshiftRight {v(o[1])} {sh})"}[c]
        if c in ("addw", "subw"):
            op = "+" if c == "addw" else "-"
            return sx32(f"({lo32(v(o[1]))} {op} {lo32(v(o[2]))})")
        if c in ("sllw", "srlw", "sraw"):
            x, sh = lo32(v(o[1])), f"({v(o[2])}.toNat % 32)"
            return sx32({"sllw": f"({x} <<< {sh})", "srlw": f"({x} >>> {sh})",
                         "sraw": f"(BitVec.sshiftRight {x} {sh})"}[c])
        if c == "lui":
            return f"(0x{sext(int(o[1], 16) << 12, 32) % 2**64:016x}#64)"
        if c == "auipc":
            val = (self.addr + sext(int(o[1], 16) << 12, 32)) % 2**64
            return f"(0x{val:016x}#64)"
        if c in ("ld", "lw", "lh", "lb"):
            return "(sign_extend (m := 64) <loaded bytes>)"
        if c in ("lbu", "lhu", "lwu"):
            return "(zero_extend (m := 64) <loaded bytes>)"
        if c == "jalr":
            return f"(0x{self.addr + 4:016x}#64)"
        return None


class Unsupported:
    """A `#UNSUPPORTED <addr> <word> <asm> [why]` row of disasm_to_sites.py."""

    def __init__(self, addr, word, text):
        self.addr, self.word, self.text = addr, word, text


UNSUP_RE = re.compile(r"^#UNSUPPORTED\s+([0-9a-f]+)\s+([0-9a-f]{8})\s+(.*)$")


def parse_rows(lines, origin: str, lo: int, hi: int,
               allow_unsupported: bool = False) -> list:
    """Rows of [lo, hi) in address order: `Instr`, or `Unsupported` when
    `allow_unsupported`. Otherwise an `#UNSUPPORTED` row in the range, or an
    address of the range without any row, is an error: nothing is dropped."""
    rows: dict[int, list] = {}
    unsup: list[Unsupported] = []
    for lineno, rawline in enumerate(lines, 1):
        line = rawline.strip()
        m = UNSUP_RE.match(line)
        if m:
            addr = int(m.group(1), 16)
            if lo <= addr < hi:
                u = Unsupported(addr, int(m.group(2), 16), m.group(3))
                unsup.append(u)
                rows.setdefault(addr, []).append(u)
            continue
        if not line or line.startswith("#"):
            continue
        body, _, comment = line.partition("#")
        parts = body.split()
        if len(parts) < 3:
            raise ValueError(f"{origin}:{lineno}: expected addr word class ...")
        addr, word, cls = int(parts[0], 16), int(parts[1], 16), parts[2]
        if not (lo <= addr < hi):
            continue
        if cls not in KNOWN:
            raise ValueError(f"{origin}:{lineno}: unknown class {cls}")
        rows.setdefault(addr, []).append(
            Instr(addr, word, cls, parts[3:], comment.strip()))
    if unsup and not allow_unsupported:
        raise ValueError(
            f"{len(unsup)} unsupported instruction(s) in the range; a draft "
            f"without them would be wrong. Extend disasm_to_sites.py, or pass "
            f"--allow-unsupported to draft them as explicit UNSUPPORTED "
            f"steps:\n" + "\n".join(f"  0x{u.addr:08x} {u.word:08x} {u.text}"
                                    for u in unsup))
    missing = [a for a in range(lo, hi, 4) if a not in rows]
    if missing:
        raise ValueError(
            f"no row for {len(missing)} address(es) of the range, e.g. "
            f"0x{missing[0]:08x}: every instruction of a straight-line "
            f"segment must be drafted (edited sites TSV, or a wrong range?)")
    out = []
    for addr in sorted(rows):
        arms = rows[addr]
        if len(arms) > 1:
            raise ValueError(
                f"0x{addr:08x}: {len(arms)} rows (both branch arms?) — keep "
                f"exactly one arm per branch (delete one row or rerun "
                f"disasm_to_sites.py with --path)")
        out.append(arms[0])
    return out


def parse_sites(path: Path, lo: int, hi: int,
                allow_unsupported: bool = False) -> list:
    return parse_rows(path.read_text().splitlines(), str(path), lo, hi,
                      allow_unsupported)


class DraftBuilder:
    def __init__(self, instrs, suffix, loaded_pred):
        self.instrs = instrs
        self.suffix = suffix
        self.loaded_pred = loaded_pred
        self.written: set[int] = set()
        self.pinned: list[int] = []      # read-before-written, first-use order

    # -- def-use ------------------------------------------------------------

    def compute_pins(self):
        for ins in self.instrs:
            if isinstance(ins, Unsupported):
                continue
            for r in ins.reads():
                if r not in self.written and r not in self.pinned:
                    self.pinned.append(r)
            w = ins.writes()
            if w:
                self.written.add(w)

    def tracked(self, r: int) -> bool:
        """Registers resolvable via `$v:`/`$pin:` at emission time: the
        initial pins, plus registers already written by an earlier step —
        gen_segment re-adds those to the bundle under their (to-be-filled)
        `rd_val`, so the placeholders resolve once the TODO values are in."""
        return r in self.pinned or r in self.walk_written

    def V(self, r: int) -> str:
        if r == 0:
            return "(0#64)"
        return f"$v:x{r}" if self.tracked(r) else f"TODO(v-x{r})"

    def H(self, r: int) -> str:
        return f"$pin:x{r}" if self.tracked(r) else f"TODO(hyp-x{r})"

    # -- steps --------------------------------------------------------------

    def build_steps(self):
        self.walk_written: set[int] = set()
        steps = []
        for ins in self.instrs:
            steps.extend(self.build_step(ins))
            w = None if isinstance(ins, Unsupported) else ins.writes()
            if w:
                self.walk_written.add(w)
        return steps

    def build_step(self, ins):
        if isinstance(ins, Unsupported):
            return [{"addr": f"0x{ins.addr:08x}", "class": "UNSUPPORTED",
                     "asm": ins.text,
                     "call": f"TODO(unsupported instruction {ins.word:08x}: "
                             f"classify it in disasm_to_sites.py)"}]
        c, o = ins.cls, ins.ops
        st = {"addr": f"0x{ins.addr:08x}",
              "site": f"site_{ins.addr:08x}{self.suffix}",
              "class": SEG_CLASS[c]}
        if ins.asm:
            st["asm"] = ins.asm
        if c not in GEN_SITES:
            st["site_battery"] = (f"TODO(gen_sites.py has no `{c}` class: "
                                  f"write or generate the site lemma)")
        if SEG_CLASS[c] not in GEN_SEGMENT:
            st["gen_segment"] = (f"TODO(gen_segment.py has no `{SEG_CLASS[c]}` "
                                 f"step class)")
        vregs = ins.vregs()
        vals = " ".join(self.V(r) for r in vregs)
        hyps = " ".join(self.H(r) for r in vregs)
        vals = (vals + " ") if vals else ""
        hyps = (hyps + " ") if hyps else ""

        if c in ALU_IMM or c in SHIFT_IMM or c in ALU_RR or c in UTYPE:
            st["rd"] = f"x{ins.writes()}"
            st["rd_val"] = "TODO"
            st["rw"] = "TODO"
            st["raw_val"] = ins.raw_val()
            st["call"] = f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl $hi"
        elif c in LOAD_BYTES:
            n = LOAD_BYTES[c]
            bs = ("TODO(b)" if n == 1
                  else " ".join(f"TODO(b{j})" for j in range(n)))
            side = "TODO(hlo) TODO(hhiram) TODO(hhtif)" + \
                ("" if n == 1 else " TODO(halign)")
            hbs = ("TODO(hb)" if n == 1
                   else " ".join(f"TODO(h{j})" for j in range(n)))
            st["rd"] = f"x{ins.writes()}"
            st["rd_val"] = "TODO"
            st["raw_val"] = ins.raw_val()
            st["call"] = (f"$vmi {vals}{bs} $hG $hpc $hmi {hyps}$hmem rfl "
                          f"{side} {hbs} $hi")
        elif c in STORE_BYTES:
            side = "TODO(halo) TODO(hahiram) TODO(hahiwin) TODO(haalign)" \
                if c != "sb" else "TODO(hlo) TODO(hhiram) TODO(hhiwin)"
            st["key"] = "TODO"
            st["key_rw"] = "TODO"
            st["src_val"] = self.V(int(o[0]))
            if c == "sb":
                st["data_rw"] = "stData_zext"
            st["loaded_via"] = "TODO"
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"{side} $hi")
        elif c in BRANCH:
            imm = int(o[3], 16)
            if c == "branch_taken":
                st["imm"] = f"0x{imm:04x}#13"
                st["target"] = f"0x{(ins.addr + sext(imm, 13)) % 2**64:08x}"
            st["pre_lines"] = ["have hguard$k : TODO := TODO"]
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"hguard$k $hi")
        elif c in ("jal", "jalr"):
            if c == "jal":
                imm = int(o[1], 16)
                st["imm"] = f"0x{imm:06x}#21"
                st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
                st["call"] = "$vmi $hG $hpc $hmi $hmem rfl $hi"
            else:                    # indirect: target is a register value
                st["pc_val"] = "TODO"
                st["pc_rw"] = "TODO"
                st["raw_val"] = ins.raw_val()
                st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                              f"TODO(htgt) $hi")
            if ins.writes() is None:     # jalr x0: indirect tail jump
                return [st]
            st["rd"] = f"x{ins.writes()}"
            call_st = {
                "class": "call", "callee": "TODO",
                "args": "TODO", "pre_fields": ["TODO"],
                "post_obtain": "TODO", "post_good": "TODO",
                "post_pc": "TODO", "post_tick": "TODO",
                "pc_val": "TODO", "pins_drop": ["TODO"], "pins_add": [],
                "write_set": ["TODO"], "frame_hyp": "TODO",
                "loaded_lines": ["have hload$k : TODO := TODO"],
            }
            return [st, call_st]
        elif c == "j":
            imm = int(o[0], 16)
            st["imm"] = f"0x{imm:06x}#21"
            st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
            # htgt is over the literal pc: decidable
            st["call"] = "$vmi $hG $hpc $hmi $hmem rfl (by decide) $hi"
        elif c == "jr":
            st["pc_val"] = "TODO"
            st["pc_rw"] = "TODO"
            st["call"] = (f"$vmi {vals}$hG $hpc $hmi {hyps}$hmem rfl "
                          f"TODO(htgt) $hi")
        else:
            raise ValueError(f"0x{ins.addr:08x}: no draft rule for {c}")
        return [st]

    # -- whole spec ----------------------------------------------------------

    def build(self, theorem: str, imports: list[str]):
        self.compute_pins()
        steps = self.build_steps()
        has_mem = any(getattr(i, "cls", None) in LOAD_BYTES or
                      getattr(i, "cls", None) in STORE_BYTES
                      for i in self.instrs)
        params = ["TODO: extra ghost binders (region facts, callee params, ...)"]
        if self.pinned:
            params.append("(" + " ".join(f"v{r}" for r in self.pinned)
                          + " : BitVec 64)")
        params.append("(m0 : Std.ExtHashMap Nat (BitVec 8))")
        pins = [{"reg": f"x{r}", "val": f"v{r}", "hyp": f"hv{r}"}
                for r in self.pinned]
        n_pin = len(pins)
        n_site = sum(1 for s in steps if s["class"] != "call")
        obtain = ("⟨hgood, hloaded, hpc, "
                  + ", ".join(f"hv{r}" for r in self.pinned)
                  + (", " if self.pinned else "")
                  + "⟨vmi, hmi⟩, htick, hmemeq, TODO(rest)⟩")
        return {
            "theorem": theorem,
            "doc": f"DRAFT (disasm_to_segment.py) — segment "
                   f"0x{self.instrs[0].addr:08x} → "
                   f"0x{self.instrs[-1].addr + 4:08x}, {len(self.instrs)} "
                   f"instructions, {n_site} site steps + "
                   f"{len(steps) - n_site} call steps, "
                   f"{n_pin} read-before-written pins. Fill every TODO.",
            "namespace": "Vsa.Sim",
            "imports": imports,
            "params": params,
            "pre": "TODO",
            "post": "TODO",
            "loaded_pred": self.loaded_pred,
            "pre_bind": {
                "obtain": obtain,
                "good": "hgood", "pc": "hpc", "minstret_var": "vmi",
                "minstret": "hmi", "tick": "htick", "loaded": "hloaded",
                "mem0": "m0", "memeq": "hmemeq",
            },
            "pins": pins,
            "prelude": ["-- TODO: hand facts (region bounds, hkey lemmas, ...)"]
            if has_mem else [],
            "steps": steps,
            "post_proof": ["TODO"],
        }


# ---------------------------------------------------------------------------
# ship-your-lua: COMPLETE `"boundary": "segst"` specs (no TODO)
#
# Every slot the draft leaves as a TODO is mechanical once the segment is
# stated over `SegSt` with its side conditions as NAMED HYPOTHESES:
#   * values: a symbolic register file tracks each write as the exact term
#     the site lemma produces (the `hwr` value of its execute lemma), so
#     `rd_val` needs no rewrite; loads read the TOTAL bytes (`*_tot` classes)
#     of the running memory expression (`rw` by the previous `hmemE`);
#   * stores: key `ea.toNat`, source value, and `.text` survival from the
#     store window (`survival` templates, e.g. `TextLoaded.writeMap8`);
#   * load/store address side conditions, branch guards and `jr` target
#     alignment: theorem hypotheses `h<kind>_<k>` over the entry values, to be
#     discharged by whoever instantiates the segment (the arm proof).

TOT_LOAD = {"ld": "ld_tot", "lw": "lw_tot", "lbu": "lbu_tot",
            "lh": "lh_tot", "lhu": "lhu_tot", "lwu": "lwu_tot"}
SIGNED_LOAD = {"ld", "lw", "lh", "lb"}
ALIGNED_TOT = {"lh", "lhu", "lwu"}          # exec_*_tot take the alignment


def site_class(ins: "Instr") -> str:
    """The scripts/syi/gen_sites.py class that proves this instruction."""
    return TOT_LOAD.get(ins.cls, ins.cls)


def site_name(ins: "Instr", suffix: str = "") -> str:
    arm = {"branch_taken": "_taken", "branch_nottaken": "_nottaken"}.get(ins.cls, "")
    return f"site_{ins.addr:08x}{arm}{suffix}"


class SegStBuilder:
    """A complete `boundary: segst` spec for one straight-line segment."""

    def __init__(self, instrs, theorem: str, loaded_pred: str, namespace: str,
                 imports: list[str], survival: dict[str, str], suffix: str = "",
                 keep: list[int] | None = None, output: bool = False):
        self.instrs, self.theorem = instrs, theorem
        self.loaded_pred, self.namespace = loaded_pred, namespace
        self.imports, self.survival, self.suffix = imports, survival, suffix
        self.keep, self.output = keep or [], output

    def build(self) -> dict:
        import gen_sites as gs                       # same directory
        instrs = self.instrs
        for ins in instrs:
            if isinstance(ins, Unsupported) or site_class(ins) not in gs.CLASS_EMITTERS:
                raise ValueError(f"0x{ins.addr:08x}: no site class for {ins}")
        pinned, written = [], set()
        for ins in instrs:
            for r in ins.reads():
                if r not in written and r not in pinned:
                    pinned.append(r)
            if ins.writes():
                written.add(ins.writes())
        # keep: registers carried through unchanged unless written (the
        # caller's invariant registers), pinned after the read ones
        pinned += [r for r in self.keep if r not in pinned]
        val = {r: f"v{r}" for r in pinned}
        V = lambda r: "(0#64)" if r == 0 else val[r]
        mem = "m0"
        hyps: list[str] = []
        steps = []
        for k, ins in enumerate(instrs, 1):
            c, o = ins.cls, ins.ops
            st = {"addr": f"0x{ins.addr:08x}", "site": site_name(ins, self.suffix),
                  "class": SEG_CLASS[c]}
            if ins.asm:
                st["asm"] = ins.asm
            vregs = ins.vregs()
            vals = "".join(f"$v:x{r} " for r in vregs)
            pins = "".join(f"$pin:x{r} " for r in vregs)
            pre = f"$vmi {vals}$hG $hpc $hmi {pins}$hmem rfl "
            rd = ins.writes()
            if c in LOAD_BYTES:
                n = LOAD_BYTES[c]
                ea = f"({V(int(o[1]))} + sign_extend (m := 64) (0x{o[2]}#12))"
                names = [f"hlo_{k}", f"hhi_{k}", f"hht_{k}"]
                hyps += [f"({names[0]} : 0x80000000 ≤ {ea}.toNat)",
                         f"({names[1]} : {ea}.toNat + {n} ≤ 0x100000000)",
                         f"({names[2]} : {ea}.toNat + {n} ≤ tohostAddr ∨ "
                         f"tohostAddr + 8 ≤ {ea}.toNat)"]
                if c in ALIGNED_TOT:
                    names.append(f"hal_{k}")
                    hyps.append(f"(hal_{k} : {ea}.toNat % {n} = 0)")
                ext = "sign_extend" if c in SIGNED_LOAD else "zero_extend"
                value = (f"({ext} (m := 64) (bytesT{n} ({mem}) {ea}.toNat : "
                         f"BitVec (8 * {n})))")
                st.update(rd=f"x{rd}", rd_val=value, rw="$memeq",
                          call=pre + " ".join(names) + " $hi")
                val[rd] = value
            elif c in STORE_BYTES:
                n = STORE_BYTES[c]
                if c not in ("sd", "sw", "sh", "sb"):
                    raise ValueError(f"0x{ins.addr:08x}: no store class {c}")
                ea = f"({V(int(o[1]))} + sign_extend (m := 64) (0x{o[2]}#12))"
                key = f"{ea}.toNat"
                names = [f"hlo_{k}", f"hhi_{k}", f"hwin_{k}"]
                hyps += [f"(hlo_{k} : 0x80000000 ≤ {key})",
                         f"(hhi_{k} : {key} + {n} ≤ 0x100000000)",
                         f"(hwin_{k} : tohostAddr + 16 ≤ {key})"]
                if c != "sb":
                    names.append(f"hal_{k}")
                    hyps.append(f"(hal_{k} : {key} % {n} = 0)")
                src = V(int(o[0]))
                if c == "sb":
                    src = f"(stData 1 {src})"
                    mem = f"(({mem}).insert ({key}) ({src}))"
                else:
                    fn, data = {"sd": ("writeMap8", "sdData_val"),
                                "sw": ("writeMap4", "swData"),
                                "sh": ("writeMap2", "shData")}[c]
                    mem = f"{fn} ({mem}) ({key}) ({data} {src})"
                st.update(key=key, src_val=src,
                          loaded_via=self.survival[c].format(hwin=f"hwin_{k}"),
                          call=pre + " ".join(names) + " $hi")
            elif c in BRANCH:
                bop = o[0]
                v1, v2 = V(int(o[1])), V(int(o[2]))
                guard = gs.BRANCH_OPS[bop][1].format(v1=v1, v2=v2)
                taken = c == "branch_taken"
                hyps.append(f"(hg_{k} : {guard} = {'true' if taken else 'false'})")
                if taken:
                    imm = int(o[3], 16)
                    st["imm"] = f"0x{imm:04x}#13"
                    st["target"] = f"0x{(ins.addr + sext(imm, 13)) % 2**64:08x}"
                st["call"] = pre + f"hg_{k} $hi"
            elif c == "jal":
                imm = int(o[1], 16)
                st["imm"] = f"0x{imm:06x}#21"
                st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
                st["rd"] = f"x{rd}"
                st["call"] = "$vmi $hG $hpc $hmi $hmem rfl $hi"
                val[rd] = f"(0x{ins.addr + 4:08x}#64 : BitVec 64)"
            elif c == "j":
                imm = int(o[0], 16)
                st["imm"] = f"0x{imm:06x}#21"
                st["target"] = f"0x{(ins.addr + sext(imm, 21)) % 2**64:08x}"
                st["call"] = "$vmi $hG $hpc $hmi $hmem rfl (by decide) $hi"
            elif c == "jr":
                upd = (f"(BitVec.update ({V(int(o[0]))} + sign_extend (m := 64) "
                       f"(0x000#12)) 0 0#1)")
                hyps.append(f"(htgt_{k} : {upd}.toNat % 4 = 0)")
                st["pc_val"] = upd
                st["call"] = pre + f"htgt_{k} $hi"
            elif c == "jalr":                        # an indirect call
                upd = (f"(BitVec.update ({V(int(o[1]))} + sign_extend (m := 64) "
                       f"(0x{o[2]}#12)) 0 0#1)")
                hyps.append(f"(htgt_{k} : {upd}.toNat % 4 = 0)")
                st["pc_val"] = upd
                st["rd"] = f"x{rd}"
                st["call"] = pre + f"htgt_{k} $hi"
                val[rd] = f"(0x{ins.addr + 4:08x}#64 : BitVec 64)"
            else:                                    # register write
                value = self.alu_value(ins, V, gs)
                st.update(rd=f"x{rd}", rd_val=value, call=pre + "$hi")
                val[rd] = value
            steps.append(st)
        params = []
        if pinned:
            params.append("(" + " ".join(f"v{r}" for r in pinned) + " : BitVec 64)")
        params.append("(m0 : Std.ExtHashMap Nat (BitVec 8))")
        if self.output:
            params.append("(o0 : Array String)")
        params += hyps
        n = len(instrs)
        extra = {"output": "o0"} if self.output else {}
        return {**extra,
            "theorem": self.theorem,
            "doc": (f"`0x{instrs[0].addr:08x}`–`0x{instrs[-1].addr + 4:08x}` "
                    f"({n} instruction{'s' if n > 1 else ''}), from "
                    f"`SegSt` to `SegSt`; side conditions are the `h*_<step>` "
                    f"hypotheses."),
            "namespace": self.namespace,
            "imports": self.imports,
            "boundary": "segst",
            "entry": f"0x{instrs[0].addr:08x}",
            "mem_param": "m0",
            "params": params,
            "loaded_pred": self.loaded_pred,
            "pins": [{"reg": f"x{r}", "val": f"v{r}", "hyp": f"hv{r}"}
                     for r in pinned],
            "steps": steps,
        }

    @staticmethod
    def alu_value(ins: "Instr", V, gs) -> str:
        """The value gen_sites.py's site lemma for `ins` writes, over `V`."""
        c, o = ins.cls, ins.ops
        a = V(int(o[1])) if c not in UTYPE else None
        E = gs.Emitter
        if c == "alu_addi":
            return f"({a} + sign_extend (m := 64) (0x{o[2]}#12))"
        if c == "addiw":
            return (f"(sign_extend (m := 64) (Sail.BitVec.extractLsb ({a} + "
                    f"sign_extend (m := 64) (0x{o[2]}#12)) 31 0))")
        if c in E.ITYPE_VAL:
            return E.ITYPE_VAL[c].format(v=a, imm=f"0x{o[2]}#12")
        if c in ("slli", "srli", "srai"):
            return (f"({E.SHIFT_FN[c[:3]]} {a} (Sail.BitVec.extractLsb "
                    f"(0x{int(o[2], 16):02x}#6) 5 0))")
        if c in ("slliw", "srliw", "sraiw"):
            return (f"(sign_extend (m := 64) ({E.SHIFT_FN[c[:3]]} "
                    f"(Sail.BitVec.extractLsb {a} 31 0) (0x{int(o[2], 16):02x}#5)))")
        b = V(int(o[2])) if c in ALU_RR else None
        if c == "alu_add":
            return f"({a} + {b})"
        if c == "sub":
            return f"({a} - {b})"
        if c == "subw":
            return (f"(sign_extend (m := 64) ((Sail.BitVec.extractLsb {a} 31 0) - "
                    f"(Sail.BitVec.extractLsb {b} 31 0)))")
        if c in E.RTYPE_VAL:
            return E.RTYPE_VAL[c].format(a=a, b=b)
        if c in E.RTYPEW_VAL:
            return E.RTYPEW_VAL[c].format(a=a, b=b)
        if c == "lui":
            return f"(sign_extend (m := 64) ((0x{int(o[1], 16):05x}#20) +++ 0x000#12))"
        if c == "auipc":
            return (f"((0x{ins.addr:08x}#64) + sign_extend (m := 64) "
                    f"((0x{int(o[1], 16):05x}#20) +++ 0x000#12))")
        raise ValueError(f"0x{ins.addr:08x}: no value rule for {c}")


def site_rows(instrs) -> list[str]:
    """gen_sites.py TSV rows (loads as their TOTAL classes) for `instrs`."""
    rows = []
    for ins in instrs:
        ops = ins.ops
        rows.append("\t".join([f"{ins.addr:08x}", f"{ins.word:08x}",
                               site_class(ins)] + [str(x) for x in ops]))
    return rows


def complete(lo: int, hi: int, lines: list[str], origin: str, theorem: str,
             loaded_pred: str, namespace: str, imports: list[str],
             survival: dict[str, str], suffix: str = "",
             keep: list[int] | None = None,
             output: bool = False) -> tuple[dict, list[str]]:
    """The complete segst spec of [lo, hi) and the site rows it needs.
    `keep`: registers pinned at entry and carried through (the post value is
    the entry value unless a step writes the register); `output`: the payload
    also carries `σ.sailOutput = o0`."""
    instrs = parse_rows(lines, origin, lo, hi)
    if not instrs:
        raise ValueError("no site rows in range")
    spec = SegStBuilder(instrs, theorem, loaded_pred, namespace, imports,
                        survival, suffix, keep, output).build()
    return spec, site_rows(instrs)


def rows_from_elf(lo: int, hi: int, path_file: Path | None) -> list[str]:
    """disasm_to_sites.py's TSV lines for [lo, hi) of the Lua ELF."""
    sys.path.insert(0, str(Path(__file__).resolve().parent))
    import disasm_to_sites as d2s
    path = d2s.read_path(path_file) if path_file else {}
    lines = []
    for addr, word, raw in d2s.disassemble(d2s.DEFAULT_OBJDUMP,
                                           d2s.DEFAULT_ELF, lo, hi):
        lines += [r.tsv() for r in d2s.classify(addr, word, raw, path)]
    return lines


def draft(lo: int, hi: int, lines: list[str], origin: str, theorem: str,
          loaded_pred: str = "TODO", suffix: str = "",
          imports: list[str] | None = None,
          allow_unsupported: bool = False) -> dict:
    instrs = parse_rows(lines, origin, lo, hi, allow_unsupported)
    if not instrs:
        raise ValueError("no site rows in range")
    imports = imports or ["TODO(site battery module)", "Vsa.Sim.RegPins"]
    return DraftBuilder(instrs, suffix, loaded_pred).build(theorem, imports)


def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("start", help="range start address (hex)")
    ap.add_argument("stop", help="range stop address (hex, exclusive)")
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--sites", type=Path,
                     help="site TSV from disasm_to_sites.py (one branch arm "
                          "per branch)")
    src.add_argument("--from-elf", action="store_true",
                     help="classify the range of c/lua-riscv-htif.elf with "
                          "disasm_to_sites.py (branch arms from --path)")
    ap.add_argument("--path", type=Path, default=None,
                    help="with --from-elf: `<addr-hex> taken|nottaken` lines")
    ap.add_argument("--theorem", default="tr_draft")
    ap.add_argument("--loaded-pred", default="TODO",
                    help="fully-qualified code byte-pin predicate")
    ap.add_argument("--site-suffix", default="",
                    help="suffix of the gen_sites.py battery theorem names")
    ap.add_argument("--imports", default=None,
                    help="comma-separated import list (default: TODO + RegPins)")
    ap.add_argument("--allow-unsupported", action="store_true",
                    help="draft #UNSUPPORTED rows as explicit UNSUPPORTED "
                         "steps instead of failing")
    ap.add_argument("-o", "--output", type=Path, default=None)
    args = ap.parse_args()

    lo, hi = int(args.start, 16), int(args.stop, 16)
    try:
        if args.from_elf:
            lines, origin = rows_from_elf(lo, hi, args.path), "<elf>"
        else:
            lines, origin = args.sites.read_text().splitlines(), str(args.sites)
        spec = draft(lo, hi, lines, origin, args.theorem, args.loaded_pred,
                     args.site_suffix,
                     args.imports.split(",") if args.imports else None,
                     args.allow_unsupported)
    except ValueError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    text = json.dumps(spec, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(text)
        n_todo = text.count("TODO")
        print(f"wrote {args.output} ({len(spec['steps'])} steps, "
              f"{len(spec['pins'])} pins, {n_todo} TODO slots)",
              file=sys.stderr)
    else:
        sys.stdout.write(text)
    return 0


if __name__ == "__main__":
    sys.exit(main())

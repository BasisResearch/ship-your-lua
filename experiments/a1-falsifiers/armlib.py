"""Shared: disassemble the CURRENT c/lua-riscv-htif.elf, recover luaV_execute's
jump table (as experiments/census/tools/arms.py does, but from the ELF bytes
directly), and name the arms.  Read-only.

The dispatch head in this build (gcc 15.2, -O2 -march=rv64i):
    HEAD_TRAP:  bnez s5,<traceexec>         ; vmfetch's `if (trap)`
    HEAD:       lw   s4,0(s11)              ; i = *pc
                addi s3,s11,4               ; pc++      (s3 = pc after fetch)
                andi a4,s4,127 ; bltu s1(=81),a4,<default>
                slli/add/lw/add ; jr a5     ; the only `jr` in luaV_execute
Arms return with `j HEAD_TRAP` or `beqz s5,HEAD` (s11 = next pc)."""
import os, re, sys, struct, subprocess, collections

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(REPO, "experiments/census/tools"))
from lib import parse_disasm, Elf, BRANCHES, BIN  # noqa: E402

LUA_ELF = os.environ.get("LUA_ELF", REPO + "/c/lua-riscv-htif.elf")
LUA_SRC = REPO + "/vendor/lua-5.4.7/src"
import tempfile
CACHE = os.environ.get("DISASM", os.path.join(tempfile.gettempdir(), "a1f_lua_disasm.txt"))


def load():
    if not os.path.exists(CACHE) or os.path.getmtime(CACHE) < os.path.getmtime(LUA_ELF):
        with open(CACHE, "w") as f:
            subprocess.run([BIN + "objdump", "-d", LUA_ELF], stdout=f, check=True)
    funcs, by_addr = parse_disasm(CACHE)
    elf = Elf(LUA_ELF)
    F = funcs["luaV_execute"]
    I = F["insts"]
    jrs = [i for i in I if i.mn == "jr"]
    assert len(jrs) == 1, "expected one dispatch jr"
    JR = jrs[0].addr
    # table base: the auipc/addi pair that materialises the register added in
    # front of the jr (s8 in this build)
    k = I.index(jrs[0])
    basereg = I[k - 1].opl()[1]
    base = None
    for j, i in enumerate(I):
        if i.mn == "addi" and i.opl()[0] == basereg and I[j - 1].mn == "auipc" and i.cmt_addr():
            base = i.cmt_addr()
    bound = None
    for i in I[k - 10:k]:
        if i.mn == "bltu":
            bound_reg = i.opl()[0]
            default = i.target()
            head = i.addr
    # bound value: li <bound_reg>,N in the prologue
    for i in I:
        if i.mn == "li" and i.opl()[0] == bound_reg:
            bound = int(i.opl()[1], 0)
            break
    # fetch head: the `lw s4,0(s11)` at the start of the dispatch block
    j = I.index(jrs[0])
    while not (I[j].mn == "lw" and I[j].opl()[1].startswith("0(") and I[j + 1].mn == "addi"
               and I[j + 1].opl()[1] == I[j].opl()[1][2:-1] and I[j + 1].opl()[2] == "4"):
        j -= 1
    HEAD = I[j].addr
    HEAD_TRAP = I[j - 1].addr if I[j - 1].mn == "bnez" else HEAD
    targets = [base + elf.s32(base + 4 * n) for n in range(bound + 1)]
    src = open(LUA_SRC + "/lopcodes.h").read()
    enum = src[src.index("typedef enum {\n/*----"):src.index("} OpCode;")]
    ops = [o[3:] for o in re.findall(r"^(OP_[A-Z0-9]+)", enum, re.M)]
    arm_target = {op: (targets[n] if n < len(targets) else default) for n, op in enumerate(ops)}
    return dict(funcs=funcs, by_addr=by_addr, F=F, I=I, JR=JR, table=base, bound=bound,
                default=default, HEAD=HEAD, HEAD_TRAP=HEAD_TRAP, arm_target=arm_target,
                ops=ops, starts={f["start"]: n for n, f in funcs.items()})


def f1_ops():
    s = open(REPO + "/Lua/Fragment.lean").read()
    b = s[s.index("def OpCode.fragment"):s.index("=> .F1")]
    return re.findall(r"\.([A-Z0-9]+)", b)


NORET = {"luaD_throw", "luaG_callerror", "luaG_concaterror", "luaG_errormsg",
         "luaG_forerror", "luaG_opinterror", "luaG_ordererror", "luaG_runerror",
         "luaG_tointerror", "luaG_typeerror", "luaM_toobig"}

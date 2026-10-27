#!/usr/bin/env python3
"""Inspect existing boot data for unwind planning; this is not a Lean proof."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]
layout = dict((k, int(v, 0)) for k, v in re.findall(
    r'^def (\w+) : Nat := (0x[0-9a-f]+|\d+)$',
    (ROOT / 'Lua/Vm/Layout.lean').read_text(), re.M))
for path in sorted((ROOT / 'Lua/Vm/Boot/Gen').glob('*.lean')):
    text = path.read_text()
    state = re.search(r'^def L : Nat := (0x[0-9a-f]+)$', text, re.M)
    if state is None:
        continue
    mem = {}
    for addr, count, packed in re.findall(
            r'\(\.leaf ⟨(0x[0-9a-f]+), (\d+), (0x[0-9a-f]+)⟩\)', text):
        addr, count, packed = int(addr, 16), int(count), int(packed, 16)
        for k in range(count):
            mem[addr + k] = (packed >> (32 * k + 24)) & 255

    def read(addr, width=8):
        return sum(mem[addr + k] << (8 * k) for k in range(width))

    state = int(state[1], 16)
    stack = read(state + layout['stateStackOff'])
    base = state + layout['stateBaseCiOff']
    values = {field: read(base + layout['ci' + field + 'Off'], width)
              for field, width in [('Func', 8), ('Top', 8), ('Previous', 8),
                                   ('Next', 8), ('Callstatus', 2)]}
    print(path.stem, 'stack=' + hex(stack),
          ' '.join(k + '=' + hex(v) for k, v in values.items()),
          'top_slots=' + str((values['Top'] - stack) // layout['stackValueSize']))

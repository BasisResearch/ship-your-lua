# Lane float-sf4: `__divdf3` on the `SfRef` route

The base is main `8b6928d`.

`__divdf3` is proved at both levels:

- **Level (a)**: `Lua.Vm.Fn.Divdf3.sum`, the machine computes the lifted
  function `Divdf3.F`.
- **Level (b)**: `Lua.Vm.Fn.Divdf3.spec_proved : F m s r a b = F64.div a b`.

It is **not** in `gen_lua_at.py`'s `FPROVED`/`FCALLS`. Another lane edits
`gen_lua_at.py` while an integration agent merges two float lanes, so the
`FCALLS` wiring (and `FPROVED`) is left to the DIV/DIVK arm lane.

## What is proved

| level | theorem | how |
|---|---|---|
| (a) | `Divdf3.sum` | 77 nodes over 140 generated segments; `__udivdi3`, `__umoddi3`, `__muldi3`, `__clzdi2` as call nodes |
| (b2) | `SfRef.div_eq : SfRef.div a b = F64.div a b` | `Lua/Num/SfRefDiv.lean` |
| (b1) | `Divdf3.F_eq_ref : F m s r a b = SfRef.div a b` | `Lua/Vm/Fn/SfRefDiv.lean`: stage lemmas and 25 class-pair chambers |
| both | `Divdf3.spec_proved` | `F_eq_ref`, then `div_eq` |

The axioms of every new theorem are `[propext, Classical.choice, Quot.sound]`.
`scripts/check.sh` stage 6 lists `udivdi3_sumT`, `umoddi3_sum`, `Divdf3.sum`,
`SfRef.udivQrnnd_eq`, `SfRef.round_jam`, `SfRef.round_refine`, `SfRef.div_eq`,
`Divdf3.g_e114`, `Divdf3.F_eq_ref` and `Divdf3.spec_proved`. There are no
`sorry`, `axiom`, `native_decide` or `bv_decide`, and no raised limits.

## Level (a): the four refusals of float-sf3

1. **Call nodes and the divisor.** The task asked for a path-fact
   precondition on call nodes, discharged from the node's guard facts. That
   is not what `__divdf3` needs. The divisor `s0 = (Y << 8) >> 32` is
   nonzero because the unpacking sets bit 55 of `Y` (`or` with `1 << 55`, or
   `__clzdi2`'s shift of a nonzero fraction). No guard on the path states
   it: the guards before `0x8002e114` only fix the class codes. Discharging
   it there would put level (b)'s unpacking lemma inside level (a).
   Instead, the call nodes run summaries that hold for **every** divisor:
   - `udivdi3_sumT` (`Kit/Umoddi3.lean`) returns `a0 = udivT n d` (`-1` for
     `d = 0`, the loop's `li a0, -1; beqz a2`) and `a1 = n % d`;
   - `umoddi3_sum` returns `a0 = n % d`.
   The obligation `d ≠ 0` moves to level (b), where `nf_udivT` uses it.
2. **`__umoddi3`.** `umoddi3_sum` runs from the routine's own entry
   `0x8002f77c` (`gen_lua_arms.py` now starts the `__umoddi3` helper there,
   with `__divdi3`'s fix-ups as roots; no existing segment changed). Its
   return through `t0` clobbers `t0`, which the generator models as
   `Callee.clobbers` (`{5: "{r}"}`). Across `__udivdi3`, `t0` is carried
   only for callers that read it: `PASS_THROUGH` plus `PASS_THROUGH_FOR`
   (`__divdf3` only), so `Hfwrite_r` and `Hdivdi3` are unchanged.
3. **Jump tables.** `gen_lua_fn.py`'s `JUMPS` names the two class-switch
   tables, `(0x80054040, 16)` and `(0x80054080, 15)`, with the index
   register `a4`.
   - The `jr` node has one polarity per entry, read off the ELF by the
     generator. Its lifted function is a chain on `idx.toNat = k`.
   - The predecessor's not-taken bound check `bltu n-1, idx` gives the node
     its fact `hjt : idx.toNat < n` (`fn_jt_bound`).
   - The node lemma enumerates the index (`fn_jt_split`, `fn_jt_zero`), and
     each entry is its own declaration. All sixteen in one declaration
     exceed the heartbeat budget.
   - Each entry's target is checked against `.rodata` by
     `fn_jt_tgt`/`rodWord_eq` (`Kit/FnCall.lean`; one `decide +kernel`).
   - The targets are roots (`gen_lua_arms.py` `FN_ROOTS`).
4. **Callee-saved registers reassigned mid-body.** `gen_lua_fn.py`'s `saves`
   is a dataflow over the nodes:
   - A register stored to its slot (`sd s<i>`, the caller's value) and then
     written is a live register of the nodes until its restore.
   - Those nodes carry the save slot's fact
     `hsv<off> : bytesT8 m slot = g.<s>`, which `fn_ra_patch` discharges.
   - The restore `ld s<i>` is the caller's value (`fn_sv_ld`).
   - The memory functions take the caller's frame `g`, because they store
     it.
   - A merge with different spill states, a write before the save, or a
     return while spilled is refused.

One more cut was needed. In `0x8002e1ec`, a spill and a reload of another
slot share a segment, so the reload read memory through the store. The root
`0x8002e1f0` splits them (`FN_ROOTS`), and every lifted function after the
entry reads no memory.

## Level (b)

**(b2) `SfRef.div`** transcribes `_FP_DIV` (class cases),
`_FP_DIV_MEAT_1_udiv_norm` (`divMeat`: `Y << 8`, the dividend `X : 0` or
`(X >> 1) : (X << 63)`, `R_f = q | (r != 0)`) and `__udiv_qrnnd_c`
(`qrHalf`, `udivQrnnd`: every word operation mod `2^64`). Its laws:

- **Knuth D.** `QrSetup` holds the facts of one digit's estimate.
  `qr_fix` gives the corrections, and from them come `qrHalf_eq` and
  `udivQrnnd_eq` (`= (n / d, n % d)` for a normalised `d` and `n1 < d`).
- **The remainder sticky bit.** `jam n d` is `rto` generalised to any
  divisor (`rto_eq_jam`). `round_jam` (W1 for a quotient) shows that two or
  more bits below the rounding position, `jam` rounds as the quotient with
  its round and sticky bits.
- **A quotient's rounding depends only on its rational.**
  - `shr_quot`: `shr` of a quotient with its bits is the quotient by the
    scaled divisor.
  - `quot_cross`: two quotients of one rational have the same floor and
    bits.
  - `target_refine` and `round_refine`: refining by `k` bits rounds the same.
  - `divCore_round`: `F64.divCore`'s coarse quotient equals the 56-bit one.
- `divNorm_eq`, `divFields_fin` and `div_eq` follow, reusing `packCanon_eq`
  and `unpack_bounds`.

**(b1)** is in `Lua/Vm/Fn/SfRefDiv.lean`:

- **Pack stage.** `g_e258`, `g_pack` and `g_e22c` give `packCanon`, by
  `sm_go`/`sm_close` from `__muldf3`.
- **Word lens.** `nf_wsub`, `nf_wadd`, `nf_wmul`, `nf_udivT`, `nf_umod`,
  `nf_sll32`, `nf_dec1/2` and `nf_carry` produce the reference's own
  word forms.
- **Difference-only reads.** `e22c_sub` and `e1c4_sub`: the corrections'
  four leaves differ only in their remainder words.
- **The machine's corrections.** `qr_fix_m` checks `R ≥ m`, then
  `R + d ≥ m`, then the carry, with the carry test abstracted
  (`carry_lo`/`carry_hi`). One lemma serves both halves.
- **Digit stages.** The low digit is `g_e1c4` and the high digit is
  `g_e178`. The divide's entry is `g_e114` (`= packCanon … (divMeat X Y)`,
  by `divMeat_digits`/`digits_scaled`).
- **Chambers.** The class-pair chamber generator `sdc_chambers` emits 25
  chambers, `G_eq` and `F_eq_ref`:
  - `sdc_spec` handles a special operand through the jump tables;
  - `sdc_fin` handles finite operands through `g_e114`;
  - `sdc_go` collapses a jump node's chain on its literal index before the
    normaliser sees its sixteen successors.
- **Rule R18** now covers `Lua/Vm/Fn/SfRefDiv*.lean`.

## Numbers

- **Lines** count non-blank, non-comment lines.
- **CPU** is user seconds of one `lake env lean <file>` with its imports
  built, at Lean's default thread count.
- **Peak** is maximum resident memory.

| file | lines | CPU (user s) | wall | peak |
|---|---|---|---|---|
| `Lua/Num/SfRefDiv.lean` (b2) | 610 | 6.1 | 0:03 | 0.81 GB |
| `Lua/Vm/Fn/SfRefDiv.lean` (lens, stages, 25 chambers) | 525 | 651 | 0:50 | 3.49 GB |
| `Lua/Vm/Sim/Kit/Umoddi3.lean` (new) | 52 | 2.8 | 0:02 | 1.88 GB |
| `Lua/Vm/Sim/Kit/FnCall.lean` (+64 lines: jump tables, save slots) | — | 1.4 | 0:02 | 1.86 GB |
| generated `Divdf3/{Defs,L0,L1}` (level (a)) | 2780 (generated) | 2.3 / 99.8 / 134.4 | 0:02 / 0:14 / 0:30 | 2.75 GB |
| generated `Arms/Segs/Hdivdf3` | 10430 (generated) | 86.7 | 0:13 | 3.05 GB |
| **hand-written total** | **1187** (+ `DivTest` 38: 1.3 s) | | | |

The generator diffs are `gen_lua_fn.py` +241/−23 lines and
`gen_lua_arms.py` +32 lines.

## Tests

`Lua/Vm/Fn/DivTest.lean` runs on 10,356 pairs. The machine's `Divdf3.F`,
`SfRef.div`, `F64.div` and the host's `/` agree on every pair: all three
lines print `[]`.

- The pairs combine edge values (zeros, subnormals, the subnormal and
  normal boundaries, the largest finite value, infinities, NaNs, and
  `1/3`, `π`, `0.1`).
- They include random raw bits.
- They include random pairs whose quotient lands near the overflow and
  underflow boundaries.

`F` reads no memory: the jump tables are cased on the index, and their
targets are checked against `.rodata` in the proof (`fn_jt_tgt`). So
`.rodata` needs no negative control here.

## Obstacles met (for the next lane)

- **`omega` and large coefficients.** `omega` reaches "maximum recursion
  depth" on a goal or hypothesis that equates terms in which an atom
  carries a large coefficient. Examples are `u * 2^32 = q * d1 * 2^32 + …`
  and `q1 * 2^32 + q0 < 2^64` from `q1 < 2^32`. The fixes:
  - name the product as an atom first (`obtain ⟨X, hX⟩ : ∃ X, q1 * 2^32 = X`);
  - keep such equalities out of `omega`'s context (`qr_setup`,
    `knuth_num`, `digits_lt`);
  - never use `generalize` over goals with `2^64` literals (use
    `obtain … ⟨_, rfl⟩` and `rw`).
- **`decide` and `simp … at h`** on hypotheses with `2^32` blew the memory
  cap twice. Bounds are now built by `Nat.mul_lt_mul_of_pos_right` and
  `Nat.div_lt_iff_lt_mul`.
- **The heartbeat budget is per declaration.** A sixteen-entry jump node in
  one declaration timed out after five entries. One declaration per entry
  fixes it.

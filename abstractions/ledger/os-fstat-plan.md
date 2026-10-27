# Console fstat boundary

Source/ELF audit, 2026-10-27; this is a task map, not a proof.

The console `_write` and `_read` boundaries are reviewed. The remaining
console syscall is `_fstat`, at `0x80000e9c`. For fd 0/1/2, initialized
kinds 1/2/3 take the non-file branch. The lazy path performs the same
five initialization stores as `_write` and `_read`. The function saves
RA at `sp-8`, calls `memset(st,0,104)` at `0x80000f10`, writes mode
`S_IFCHR` at offset 4 and nlink 1 at offset 8, then returns zero.

`Kit/Setup.lean` already proves `fstat_sum`, but at `_fstat_r`'s entry,
for fd 1 before initialization and the specific buffer `sp+24`. The
callee-context generator inlines the memset using constant bounds.
This is not a summary at the OS decoder's `_fstat` entry. Reuse its
generated execution shape and memory laws instead of changing the PC
in that theorem or assuming a callee run.

The struct is 104 bytes (`Layout.statSize`). Its caller buffer is
8 modulo 16 in the existing newlib path. The current calloc zeroing lane
uses a 16-aligned pointer, so its result alone cannot justify this caller.
For an arbitrary 8-aligned stat buffer, generated context variants with
residue 0 and 8 modulo 16 cover both paths; constant-size unrolling is
already supported by the generator. A hand unrolled store proof is not.

`Htif.StatAt` asks presence-level mode, nlink and size reads. The TCB
`osFstat` stream result is `Stats(chr,0,1)` with unchanged abstract state.
The bridge needs the actual machine entry, a live stream descriptor,
ABI decoding/return bounds, entry console agreement, and honest writable
output/stack separation. Preserve exact optional bytes outside the output,
saved RA and conditional initialization stores. This local boundary will
not establish the persistent `HtifRepr` or the full filesystem contract.

# Integration gate, 2026-10-27

The main batch through proof head `7893933` and host harness fix `35e68a4`
passes all stages of `scripts/check.sh`. Later commits contain task,
probe and status documentation, not additional proof changes.

Command, in the root checkout:

```sh
scripts/lean-capped.sh env LEAN_NUM_THREADS=2 taskset -c 17,25 bash scripts/check.sh
```

The wrapper enforces a 12 GB scope and one Lean run in the checkout.
The full first Lean build passed, with peak scope memory 11.8 GiB and no
OOM events. Two pairs of large elaborations were temporarily serialized
under the same cap; all processes resumed and completed normally.
Its OS stage exposed an inherited host fd 8; the driver-only fix closes
extra child descriptors and isolates stdio without releasing the parent
lock or changing the model/expected verdicts. The full retry exits zero.

- All generator drift checks and the pinned ELF hash pass; no ecall.
- Forbidden-token, 17-rule discipline, abstraction and copied-layer checks pass.
- Full `Lua Vsa VsaIris` plus explicit Bfree ownership build passes.
- Linux: 329 traces, 5069 steps, 324 accepted, 0 rejected, 5 special.
- HTIF: 329 traces, 4488 steps, 264 accepted, 0 rejected, 4 special, 61 unsupported.
- Console HTIF: 26 traces, 35 steps, 25 accepted, 0 rejected, 1 special.
- All 933 axiom reports use only `propext`, `Classical.choice`, `Quot.sound`.

The local full retry log is `/tmp/syi-main-retry-check.log`. The next and
queue integration branches have separate pending gates; their focused
proof results are not a claim that the combined batches have passed.
`endToEnd_lua` still has the open premises listed in `PHASES.md`.
